/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeAlgorithmMeasurable
import ArlibCommunity.Algorithms.CV18.Analysis.TapeRefines
import ArlibCommunity.Algorithms.CV18.Analysis.OracleProgramTheorem

/-!
# The run of `Program.estimator` on the random tape

Assembles the analysis of `Model/Run.lean`'s run:

* **value and calls** (`estimator_val`, `estimator_queryCount_le`): on the oracle
  `Oracle.ofTape member t`, `Program.estimator q` returns the result of the tape program
  `Tape.medianOfRuns q` on `t`, after at most `confidenceRepetitions q · queryBudget q`
  membership calls;
* **output law** (`estimate_eq`): on a correct oracle, the output law `estimate q I oracle`
  is the law of the program tree `cv18Program q`, through `TapeProgram.tapeLaw_map_exec`
  (the tape is fresh randomness) and `Tape.medianOfRuns_refines` (the point draws);
* **query bound** (`execution_queryCount_le`): at most `⌈queryRate q⌉` calls on every tape.
-/

set_option autoImplicit false

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations
open Arlib.Computation
open Program TapeProgram

variable {n : ℕ} {α β : Type}

/-! ## Running the program's monad -/

theorem Program.runFrom_orElse (X Y : M n α) (s : ℕ × Oracle n) :
    runFrom (X <|> Y) s = runFrom X s >>= fun p =>
      match p.1 with
      | some a => Pure.pure (some a, p.2)
      | none => runFrom Y p.2 := by
  simp only [runFrom, OptionT.run, HOrElse.hOrElse, OrElse.orElse, Alternative.orElse,
    OptionT.orElse, OptionT.mk, StateT.run, Bind.bind, StateT.bind]
  congr 1
  funext p
  rcases p with ⟨_ | a, s'⟩ <;> rfl

theorem Program.val_runFrom_reset (X : M n α) (B : ℕ) (s : ℕ × Oracle n) :
    (runFrom (do let (_, o) ← get; set (B, o); X) s).val = (runFrom X (B, s.2)).val := rfl

theorem Program.cost_runFrom_reset (X : M n α) (B : ℕ) (s : ℕ × Oracle n) :
    (runFrom (do let (_, o) ← get; set (B, o); X) s).cost = (runFrom X (B, s.2)).cost := by
  show 0 + (0 + (runFrom X (B, s.2)).cost) = _
  simp

/-! ## A computation that runs a tape program -/

/-- **`X` runs the tape program `p`, with at most `k` membership calls**: from any budget
and the oracle `Oracle.ofTape member t`, `X` returns `p`'s result on `t` and leaves the
oracle on the tape `p` leaves, having made at most `k` calls. -/
def SimRun (member : AmbientSpace n → Bool) (X : M n α) (p : TapeProgram n α) (k : ℕ) :
    Prop :=
  ∀ b t, (runFrom X (b, Oracle.ofTape member t)).val.1 = some (exec member p t).1 ∧
    (runFrom X (b, Oracle.ofTape member t)).val.2.2 = Oracle.ofTape member (exec member p t).2 ∧
    queryCount (runFrom X (b, Oracle.ofTape member t)).cost ≤ k

variable {member : AmbientSpace n → Bool}

theorem SimRun.pure (a : α) :
    SimRun member (Pure.pure a : M n α) (TapeProgram.pure a) 0 := fun _ _ =>
  ⟨rfl, rfl, le_rfl⟩

theorem SimRun.mono {X : M n α} {p : TapeProgram n α} {k k' : ℕ} (h : SimRun member X p k)
    (hk : k ≤ k') : SimRun member X p k' := fun b t =>
  ⟨(h b t).1, (h b t).2.1, (h b t).2.2.trans hk⟩

theorem SimRun.bind {X : M n α} {p : TapeProgram n α} {k₁ : ℕ} {F : α → M n β}
    {f : α → TapeProgram n β} {k₂ : ℕ} (hX : SimRun member X p k₁)
    (hF : ∀ a, SimRun member (F a) (f a) k₂) :
    SimRun member (X >>= F) (p >>= f) (k₁ + k₂) := by
  intro b t
  obtain ⟨h1, h2, h3⟩ := hX b t
  set r := runFrom X (b, Oracle.ofTape member t) with hr
  have hval : r.val = (some (exec member p t).1, (r.val.2.1, Oracle.ofTape member
      (exec member p t).2)) := Prod.ext h1 (Prod.ext rfl h2)
  obtain ⟨g1, g2, g3⟩ := hF (exec member p t).1 r.val.2.1 (exec member p t).2
  have hrun : runFrom (X >>= F) (b, Oracle.ofTape member t) = r >>= fun p' =>
      match p'.1 with
      | none => Pure.pure (none, p'.2)
      | some a => runFrom (F a) p'.2 := runFrom_bind X F _
  have hexec : exec member (p >>= f) t =
      exec member (f (exec member p t).1) (exec member p t).2 := exec_bind member p f t
  rw [hrun, hexec]
  refine ⟨?_, ?_, ?_⟩
  · rw [Charged.val_bind, hval]
    exact g1
  · rw [Charged.val_bind, hval]
    exact g2
  · rw [Charged.cost_bind, hval]
    change queryCount r.cost + queryCount _ ≤ _
    exact add_le_add h3 g3

/-! ## The capped run, and the whole algorithm -/

variable (q : VolumeParams) {m : AmbientSpace q.n → Bool}

theorem cappedRun_simRun :
    SimRun m (Program.cappedRun q) (Tape.cappedRun q) (queryBudget q) := by
  intro b t
  set B := queryBudget q
  have hval : (runFrom (Program.cappedRun q) (b, Oracle.ofTape m t)).val =
      (runFrom (Program.figureOneRun q <|> Pure.pure 0) (B, Oracle.ofTape m t)).val :=
    Program.val_runFrom_reset _ _ _
  have hcost : (runFrom (Program.cappedRun q) (b, Oracle.ofTape m t)).cost =
      (runFrom (Program.figureOneRun q <|> Pure.pure 0) (B, Oracle.ofTape m t)).cost :=
    Program.cost_runFrom_reset _ _ _
  have hfig := interp_run_val m (Tape.figureOneRun q) B t
  have hq := interp_run_queryCount m (Tape.figureOneRun q) B t
  rw [Tape.figureOneRun_interp] at hfig hq
  have hexec : exec m (Tape.cappedRun q) t =
      (((execB m (Tape.figureOneRun q) B t).1).getD 0,
        (execB m (Tape.figureOneRun q) B t).2.2) := by
    simp only [Tape.cappedRun, TapeProgram.bind_eq, exec_bind, exec_withQueryCap]
    rfl
  have hle : queryCount (runFrom (Program.figureOneRun q) (B, Oracle.ofTape m t)).cost ≤ B := by
    omega
  rw [hval, hcost, Program.runFrom_orElse, Charged.val_bind, Charged.cost_bind, hfig, hexec]
  rcases execB m (Tape.figureOneRun q) B t with ⟨_ | v, b', t'⟩
  · refine ⟨rfl, rfl, ?_⟩
    show queryCount (runFrom (Program.figureOneRun q) (B, Oracle.ofTape m t)).cost + 0 ≤ B
    simpa using hle
  · refine ⟨rfl, rfl, ?_⟩
    show queryCount (runFrom (Program.figureOneRun q) (B, Oracle.ofTape m t)).cost + 0 ≤ B
    simpa using hle

theorem repeatIndependently_simRun {X : M n ℝ} {p : TapeProgram n ℝ} {k : ℕ}
    (h : SimRun member X p k) :
    ∀ r : ℕ, SimRun member (Program.repeatIndependently X r) (Tape.repeatIndependently p r)
      (r * k)
  | 0 => (SimRun.pure _).mono (by simp)
  | r + 1 => by
      refine (SimRun.bind h fun first =>
        SimRun.bind (repeatIndependently_simRun h r) fun rest => SimRun.pure _).mono ?_
      rw [add_zero, add_mul, one_mul, add_comm]

theorem medianOfRuns_simRun :
    SimRun m (Program.medianOfRuns q) (Tape.medianOfRuns q)
      (confidenceRepetitions q * queryBudget q) :=
  (SimRun.bind (repeatIndependently_simRun (cappedRun_simRun q) _) fun _ =>
    SimRun.pure _).mono (by simp)

/-- **The estimate of one execution** is the result of the tape program
`Tape.medianOfRuns q` on the tape. -/
theorem execution_val (m : AmbientSpace q.n → Bool) (t : Tape q.n) :
    (execution q m t).val = (exec m (Tape.medianOfRuns q) t).1 := by
  have h := (medianOfRuns_simRun q (m := m) 0 t).1
  show ((runFrom (Program.medianOfRuns q) (0, Oracle.ofTape m t)).val.1).getD 0 = _
  rw [h]
  rfl

/-- **The calls of one execution**: at most `confidenceRepetitions q · queryBudget q`. -/
theorem execution_queryCount_le_budget (m : AmbientSpace q.n → Bool) (t : Tape q.n) :
    queryCount (execution q m t).cost ≤ confidenceRepetitions q * queryBudget q := by
  have h := (medianOfRuns_simRun q (m := m) 0 t).2.2
  show queryCount (runFrom (Program.medianOfRuns q) (0, Oracle.ofTape m t)).cost + 0 ≤ _
  simpa using h

/-! ## Measurability of the run -/

theorem measurable_fin_cons {r : ℕ} :
    Measurable fun p : ℝ × (Fin r → ℝ) => (Fin.cons p.1 p.2 : Fin (r + 1) → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_exec_cappedRun (hm : Measurable m) :
    Measurable fun t => exec m (Tape.cappedRun q) t := by
  have hfig := Tape.figureOneRun_meas q hm
  have hrun : Measurable fun t : Tape q.n => execB m (Tape.figureOneRun q) (queryBudget q) t :=
    Measurable.comp hfig ((measurable_const (a := ())).prodMk
      ((measurable_const (a := queryBudget q)).prodMk measurable_id))
  have hexec : (fun t => exec m (Tape.cappedRun q) t) = fun t =>
      (((execB m (Tape.figureOneRun q) (queryBudget q) t).1).getD 0,
        (execB m (Tape.figureOneRun q) (queryBudget q) t).2.2) := by
    funext t
    simp only [Tape.cappedRun, TapeProgram.bind_eq, exec_bind, exec_withQueryCap]
    rfl
  rw [hexec]
  exact ((measurable_optionGetD 0).comp hrun.fst).prodMk hrun.snd.snd

theorem measurable_exec_repeat {p : TapeProgram q.n ℝ}
    (hp : Measurable fun t => exec m p t) :
    ∀ r : ℕ, Measurable fun t => exec m (Tape.repeatIndependently p r) t
  | 0 => measurable_const.prodMk measurable_id
  | r + 1 => by
      have ih := measurable_exec_repeat hp r
      have hexec : (fun t => exec m (Tape.repeatIndependently p (r + 1)) t) = fun t =>
          ((Fin.cons (exec m p t).1
              (exec m (Tape.repeatIndependently p r) (exec m p t).2).1 : Fin (r + 1) → ℝ),
            (exec m (Tape.repeatIndependently p r) (exec m p t).2).2) := by
        funext t
        simp only [Tape.repeatIndependently, TapeProgram.bind_eq, exec_bind]
        rfl
      rw [hexec]
      exact (measurable_fin_cons.comp (hp.fst.prodMk (ih.comp hp.snd).fst)).prodMk
        (ih.comp hp.snd).snd

theorem measurable_exec_medianOfRuns (hm : Measurable m) :
    Measurable fun t => (exec m (Tape.medianOfRuns q) t).1 := by
  have hrep := measurable_exec_repeat q (measurable_exec_cappedRun q hm)
    (confidenceRepetitions q)
  have hexec : (fun t => (exec m (Tape.medianOfRuns q) t).1) = fun t =>
      Arlib.Probability.medianOf (exec m (Tape.repeatIndependently (Tape.cappedRun q)
        (confidenceRepetitions q)) t).1 := by
    funext t
    simp only [Tape.medianOfRuns, TapeProgram.bind_eq, exec_bind]
    rfl
  rw [hexec]
  exact (measurable_medianOf _).comp hrep.fst

/-! ## The output law and the query bound -/

/-- **The output law of the algorithm on the random tape** is the law of the program tree
`cv18Program q`. -/
theorem estimate_eq (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    estimate q I oracle = volumeAlgorithmLaw cv18Program q I oracle := by
  have hm := oracle.measurable_query
  have hmeas : (cv18Program q).StronglyMeasurable oracle.query := by
    rw [cv18Program_eq]
    exact (amplifyOracleProgram_semantics figureOneFinalScheduledCappedValueProgram q
      oracle.query (figureOneFinalScheduledCappedValueProgram_stronglyMeasurable q I oracle)).1
  unfold estimate volumeAlgorithmLaw
  simp_rw [execution_val]
  rw [tapeLaw_map_exec _ _ (measurable_exec_medianOfRuns q hm),
    (Tape.medianOfRuns_refines q).runEstimate_eq oracle.query hmeas]

/-- The `confidenceRepetitions q` runs, each capped at `⌈C₀ · rate q⌉` calls, make at most
`⌈9 (C₀ + 1) · rate q · protectedLog (1/p)⌉` calls together. -/
private theorem amplifiedCalls_le_of_rate (rate : VolumeParams → ℝ) (hrate : ∀ q, 1 ≤ rate q)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (q : VolumeParams) {B : ℕ}
    (hB : B ≤ Nat.ceil (C₀ * rate q)) :
    confidenceRepetitions q * B ≤
      Nat.ceil (9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p))) := by
  let R : ℝ := rate q
  let L : ℝ := protectedLog (1 / q.p)
  let m : ℕ := confidenceRepetitions q
  have hR : 1 ≤ R := hrate q
  have hL : 1 ≤ L := le_max_left _ _
  have hm_nonneg : 0 ≤ 8 * L := by positivity
  have hm_real : (m : ℝ) ≤ 9 * L := by
    have hceil : (m : ℝ) < 8 * L + 1 := by
      simpa [m, confidenceRepetitions, L] using Nat.ceil_lt_add_one hm_nonneg
    linarith
  have hraw_nonneg : 0 ≤ C₀ * R := mul_nonneg hC₀.le (by linarith)
  have hceil_real : ((Nat.ceil (C₀ * R) : ℕ) : ℝ) < C₀ * R + 1 := by
    simpa using Nat.ceil_lt_add_one hraw_nonneg
  have hB_real : (B : ℝ) ≤ (C₀ + 1) * R := by
    have hB' : B ≤ Nat.ceil (C₀ * R) := by simpa [R] using hB
    have hBceil : (B : ℝ) ≤ (Nat.ceil (C₀ * R) : ℝ) := by
      exact_mod_cast hB'
    nlinarith
  have hreal : ((m * B : ℕ) : ℝ) ≤ 9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p)) := by
    rw [Nat.cast_mul]
    calc
      (m : ℝ) * (B : ℝ) ≤ (9 * L) * ((C₀ + 1) * R) :=
        mul_le_mul hm_real hB_real (Nat.cast_nonneg _) (by positivity)
      _ = 9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p)) := by
        dsimp [R, L]
        ring
  exact_mod_cast le_trans hreal
    (Nat.le_ceil (9 * (C₀ + 1) * (rate q * protectedLog (1 / q.p))))

/-- **The query bound**: every execution, on every tape and whatever answers membership,
makes at most `⌈queryRate q⌉` membership calls. -/
theorem execution_queryCount_le (m : AmbientSpace q.n → Bool) (t : Tape q.n) :
    queryCount (execution q m t).cost ≤ Nat.ceil (queryRate q) := by
  refine (execution_queryCount_le_budget q m t).trans ?_
  have hcalls := amplifiedCalls_le_of_rate runRate runRate_one_le (64 * runCostConstant)
    (mul_pos (by norm_num) runCostConstant_pos) q (B := queryBudget q) le_rfl
  have hconst : 9 * (64 * runCostConstant + 1) * (runRate q * protectedLog (1 / q.p)) =
      queryRate q := by
    unfold queryRate queryConstant runCostConstant
    ring
  rw [hconst] at hcalls
  exact hcalls

end ArlibCommunity.Algorithms.CV18
