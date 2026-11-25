/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeProgram

/-!
# The law of a tape program on the random tape

The tape of `Model/Run.lean` is a sequence of independent rounds.  This file proves that
a tape program run on it has the output law of the same program with each random number
drawn from its law when it is read (`TapeProgram.tapeLaw_map_exec`): `law member p`.  This is the statement that the tape is the oracle model's "every random
number is fresh".

The proof splits the tape into its first round and the rest (`tapeLaw_eq_map_cons`): the
two are independent, and the rest is again a tape.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

variable {n : ℕ}

/-- The tape with first round `r` followed by `t`. -/
def Tape.cons (r : Round n) (t : Tape n) : Tape n
  | 0 => r
  | j + 1 => t j

@[simp] theorem Tape.cons_zero (r : Round n) (t : Tape n) : Tape.cons r t 0 = r := rfl

@[simp] theorem Tape.tail_cons (r : Round n) (t : Tape n) : (Tape.cons r t).tail = t := rfl

theorem measurable_tape_cons :
    Measurable fun p : Round n × Tape n => Tape.cons p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  cases i with
  | zero => exact measurable_fst
  | succ j => exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_tape_tail : Measurable fun t : Tape n => t.tail :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)

instance tapeLaw_isProbabilityMeasure : IsProbabilityMeasure (tapeLaw n) := by
  unfold tapeLaw
  infer_instance

/-- **The tape is its first round followed by an independent tape.** -/
theorem tapeLaw_eq_map_cons :
    tapeLaw n = ((roundLaw n).prod (tapeLaw n)).map fun p => Tape.cons p.1 p.2 := by
  symm
  refine Measure.eq_infinitePi _ fun s A hA => ?_
  classical
  let s' : Finset ℕ := s.preimage Nat.succ Nat.succ_injective.injOn
  have hpre : (fun p : Round n × Tape n => Tape.cons p.1 p.2) ⁻¹' (s : Set ℕ).pi A =
      (if 0 ∈ s then A 0 else univ) ×ˢ (s' : Set ℕ).pi fun j => A (j + 1) := by
    ext ⟨r, t⟩
    simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, s', Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun j hj => h (j + 1) hj⟩
      split_ifs with h0
      · exact h 0 h0
      · exact mem_univ _
    · rintro ⟨h0, ht⟩ i hi
      cases i with
      | zero => simpa [hi] using h0
      | succ j => exact ht j hi
  have hmeas : MeasurableSet ((s : Set ℕ).pi A) :=
    MeasurableSet.pi s.countable_toSet fun i _ => hA i
  rw [Measure.map_apply measurable_tape_cons hmeas, hpre, Measure.prod_prod, tapeLaw,
    Measure.infinitePi_pi _ fun j _ => hA (j + 1)]
  have hsplit : ∏ i ∈ s, roundLaw n (A i) =
      (if 0 ∈ s then roundLaw n (A 0) else 1) * ∏ j ∈ s', roundLaw n (A (j + 1)) := by
    have himage : s.erase 0 = s'.map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_map, Function.Embedding.coeFn_mk, s',
        Finset.mem_preimage]
      constructor
      · rintro ⟨hi0, hi⟩
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        exact ⟨j, hi, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨Nat.succ_ne_zero j, hj⟩
    have hrest : ∏ i ∈ s.erase 0, roundLaw n (A i) = ∏ j ∈ s', roundLaw n (A (j + 1)) := by
      rw [himage, Finset.prod_map]
      rfl
    split_ifs with h0
    · rw [← Finset.mul_prod_erase s _ h0, hrest]
    · rw [Finset.erase_eq_of_notMem h0] at hrest
      rw [hrest, one_mul]
  rw [hsplit]
  congr 1
  split_ifs <;> simp

/-- A measure of a set of tapes: average over the first round of the measure of the
section through the rest. -/
theorem tapeLaw_apply_eq_lintegral {A : Set (Tape n)} (hA : MeasurableSet A) :
    tapeLaw n A = ∫⁻ r, tapeLaw n {t | Tape.cons r t ∈ A} ∂roundLaw n := by
  conv_lhs => rw [tapeLaw_eq_map_cons]
  rw [Measure.map_apply measurable_tape_cons hA,
    Measure.prod_apply (measurable_tape_cons hA)]
  rfl

namespace TapeProgram

variable {α : Type} [MeasurableSpace α]

/-- One random draw: reading a component `π` of the first round, with law `μ`, then
continuing with `k`, has the law of drawing from `μ` and continuing. -/
private theorem draw_case {X : Type} [MeasurableSpace X] (member : State n → Bool)
    (π : Round n → X) (hπ : Measurable π) (μ : Measure X) (hμ : (roundLaw n).map π = μ)
    (σ : X → Round n) (hσ : Measurable σ) (hσπ : ∀ x, π (σ x) = x)
    (k : X → TapeProgram n α) (R : X → Measure α)
    (hk : Measurable fun t : Tape n => (exec member (k (π (t 0))) t.tail).1)
    (ih : ∀ x, Measurable (fun t => (exec member (k x) t).1) →
      ∀ S, MeasurableSet S → tapeLaw n ((fun t => (exec member (k x) t).1) ⁻¹' S) = R x S)
    {S : Set α} (hS : MeasurableSet S) :
    tapeLaw n ((fun t : Tape n => (exec member (k (π (t 0))) t.tail).1) ⁻¹' S) =
      (μ.bind R) S := by
  -- the joint map `(x, t) ↦ exec (k x) t`
  let H : X × Tape n → α := fun p => (exec member (k p.1) p.2).1
  have hH : Measurable H := by
    have : H = (fun t : Tape n => (exec member (k (π (t 0))) t.tail).1) ∘
        fun p : X × Tape n => Tape.cons (σ p.1) p.2 := by
      funext p
      simp only [H, Function.comp_apply, Tape.cons_zero, Tape.tail_cons, hσπ]
    rw [this]
    exact hk.comp (measurable_tape_cons.comp ((hσ.comp measurable_fst).prodMk measurable_snd))
  have hsec : ∀ x, Measurable fun t : Tape n => (exec member (k x) t).1 := fun x =>
    hH.comp (measurable_const.prodMk measurable_id)
  have hR : ∀ x S, MeasurableSet S →
      R x S = tapeLaw n (Prod.mk x ⁻¹' (H ⁻¹' S)) := fun x S hS =>
    (ih x (hsec x) S hS).symm
  have hRmeas : Measurable R := by
    refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
    simp_rw [hR _ S hS]
    exact measurable_measure_prodMk_left (hH hS)
  rw [Measure.bind_apply hS hRmeas.aemeasurable, ← hμ,
    lintegral_map (f := fun x => R x S) ((Measure.measurable_coe hS).comp hRmeas) hπ,
    tapeLaw_apply_eq_lintegral (hk hS)]
  refine lintegral_congr fun r => ?_
  rw [hR _ S hS]
  rfl

/-- **The law of a tape program on the random tape** is the law of drawing each random
number from its law when it is read. -/
theorem tapeLaw_preimage_exec (member : State n → Bool) (p : TapeProgram n α)
    (hp : Measurable fun t => (exec member p t).1) {S : Set α} (hS : MeasurableSet S) :
    tapeLaw n ((fun t => (exec member p t).1) ⁻¹' S) = law member p S := by
  induction p generalizing S with
  | pure a =>
      simp only [exec, law]
      by_cases ha : a ∈ S
      · rw [preimage_const_of_mem ha, measure_univ, Measure.dirac_apply_of_mem ha]
      · rw [preimage_const_of_notMem ha, measure_empty,
          Measure.dirac_apply' _ hS, indicator_of_notMem ha]
  | query x k ih => exact ih (member x) hp hS
  | gaussian k ih =>
      exact draw_case member (fun r => r.1) measurable_fst (standardGaussian n)
        (by simp [roundLaw, Measure.map_fst_prod]) (fun g => (g, 0))
        (measurable_id.prodMk measurable_const) (fun _ => rfl) k _ hp
        (fun g hg S hS => ih g hg hS) hS
  | unit k ih =>
      exact draw_case member (fun r => r.2) measurable_snd uniformUnit
        (by simp [roundLaw, Measure.map_snd_prod]) (fun v => (0, v))
        (measurable_const.prodMk measurable_id) (fun _ => rfl) k _ hp
        (fun v hv S hS => ih v hv hS) hS

/-- **The output law of a tape program on the random tape**: the tape law pushed through
the result of `exec` is `law member p`. -/
theorem tapeLaw_map_exec (member : State n → Bool) (p : TapeProgram n α)
    (hp : Measurable fun t => (exec member p t).1) :
    (tapeLaw n).map (fun t => (exec member p t).1) = law member p := by
  ext S hS
  rw [Measure.map_apply hp hS, tapeLaw_preimage_exec member p hp hS]

/-- A tape program whose run is measurable in the tape has a probability law. -/
theorem isProbabilityMeasure_law (member : State n → Bool) (p : TapeProgram n α)
    (hp : Measurable fun t => (exec member p t).1) : IsProbabilityMeasure (law member p) := by
  rw [← tapeLaw_map_exec member p hp]
  exact (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).2 inferInstance

/-- **A jointly measurable family of tape programs has a measurable law.** -/
theorem measurable_law {A : Type} [MeasurableSpace A] (member : State n → Bool)
    (f : A → TapeProgram n α)
    (hf : Measurable fun q : A × Tape n => (exec member (f q.1) q.2).1) :
    Measurable fun a => law member (f a) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : ∀ a, law member (f a) S =
      tapeLaw n (Prod.mk a ⁻¹' ((fun q : A × Tape n => (exec member (f q.1) q.2).1) ⁻¹' S)) :=
    fun a => (tapeLaw_preimage_exec member (f a)
      (hf.comp (measurable_const.prodMk measurable_id)) hS).symm
  simp_rw [h]
  exact measurable_measure_prodMk_left (hf hS)

/-- The run after reading a component `π` of the first round, as a function of what was
read and the rest of the tape, is the run of the whole program on the reassembled tape. -/
private theorem joint_of_read {X : Type} [MeasurableSpace X] {γ : Type} [MeasurableSpace γ]
    (F : Tape n → γ) (hF : Measurable F) (σ : X → Round n) (hσ : Measurable σ) :
    Measurable fun q : X × Tape n => F (Tape.cons (σ q.1) q.2) :=
  hF.comp (measurable_tape_cons.comp ((hσ.comp measurable_fst).prodMk measurable_snd))

/-- **The law of a sequence** is the law of the first program bound into the laws of the
second, when the runs are measurable. -/
theorem law_bind {β : Type} [MeasurableSpace β] (member : State n → Bool)
    (p : TapeProgram n α) (f : α → TapeProgram n β)
    (hp : Measurable fun t => exec member p t)
    (hf : Measurable fun q : α × Tape n => (exec member (f q.1) q.2).1) :
    law member (p.bind f) = (law member p).bind fun a => law member (f a) := by
  have hlf := measurable_law member f hf
  induction p with
  | pure a => exact (Measure.dirac_bind hlf a).symm
  | query x k ih => exact ih (member x) hp
  | gaussian k ih =>
      have hk : Measurable fun q : State n × Tape n => exec member (k q.1) q.2 :=
        joint_of_read (fun t => exec member (TapeProgram.gaussian k) t) hp (fun g => (g, 0))
          (measurable_id.prodMk measurable_const)
      have hsec : ∀ g, Measurable fun t => exec member (k g) t := fun g =>
        hk.comp (measurable_const.prodMk measurable_id)
      have hlk := measurable_law member k hk.fst
      show (standardGaussian n).bind (fun g => law member ((k g).bind f)) = _
      simp_rw [fun g => ih g (hsec g)]
      exact (Measure.bind_bind hlk.aemeasurable hlf.aemeasurable).symm
  | unit k ih =>
      have hk : Measurable fun q : ℝ × Tape n => exec member (k q.1) q.2 :=
        joint_of_read (fun t => exec member (TapeProgram.unit k) t) hp (fun v => (0, v))
          (measurable_const.prodMk measurable_id)
      have hsec : ∀ v, Measurable fun t => exec member (k v) t := fun v =>
        hk.comp (measurable_const.prodMk measurable_id)
      have hlk := measurable_law member k hk.fst
      show uniformUnit.bind (fun v => law member ((k v).bind f)) = _
      simp_rw [fun v => ih v (hsec v)]
      exact (Measure.bind_bind hlk.aemeasurable hlf.aemeasurable).symm

end TapeProgram

end ArlibCommunity.Algorithms.HitAndRun
