import Esa22Copy.Model.Prelude
import Esa22Copy.Interface.Pseudocode
import Arlib.Prelude
import Mathlib.Algebra.Order.Field.GeomSum
import Esa22Copy.Analysis.FailProbLe
import Esa22Copy.Analysis.Alg2
import Esa22Copy.Analysis.Alg2Dominated
import Esa22Copy.Analysis.YLawChernoff

/-!
# Claim claim:errfail — a non-⊥ answer is outside `[(1-ε)F0, (1+ε)F0]` w.p. ≤ δ/2

`errfail_prob_le` bounds the mass that `Pseudocode.outputLaw A ε δ` puts on
answers `some c` with `c ∉ [(1-ε)F0, (1+ε)F0]` by `δ/2`
(esa22-final.tex:512-521, 541-774).

The paper's route: off ⊥, Algorithm 1 agrees with Algorithm 2 (Algorithm 1 with
the ⊥ test removed), so `Pr[Error ∩ ¬Fail] ≤ Pr[Error₂]`; Algorithm 2's state is
coupled with Algorithm 3's sets `Y_{k,j}`, each a product-Bernoulli(`2^{-k}`)
subset of the distinct items seen; Chernoff bounds the event that the final
level exceeds `ℓ = ⌊log₂(4F0/thresh)⌋` and the event that the estimate at a level
`q ≤ ℓ` is inaccurate.

Known paper defects to route around (proof charter):
* when `F0 < thresh/4`, `ℓ < 0` and the paper's `Pr[Bad] ≤ δ/4` is false; in
  that regime the run never halves `p` (the sample never reaches `thresh`)
  and the answer is exactly `F0`;
* the paper's `E|Y_{ℓ,j}| ≤ thresh/4` (esa22-final.tex:732) has the wrong
  direction: `F0/2^ℓ ∈ [thresh/4, thresh/2)`; use `t = thresh/μ - 1 ≥ 1`.

## How it is proved here

The paper asserts the coupling `X_j = Y_{p_j, j}` (esa22-final.tex:678) without
proof.  What the bound consumes is only its consequence, the per-level
domination of Algorithm 2 by Algorithm 3's `Y_k`
(`Alg2.loop2_level_eq_le_yLaw`, `Alg2.loop2_level_gt_le`, in
`Alg2Dominated.lean`, which records the inductive invariant that proves it),
plus Chernoff tails for `|Y_k|` (`Alg2.yLaw_card_ge_le`, `Alg2.yLaw_card_dev_le`,
in `YLawChernoff.lean`).  This file proves:

* `Errfail.loop_running_le_loop2` — `Pr[Error ∩ ¬Fail] ≤ Pr[Error₂]` by induction on
  the stream (Algorithm 1 = Algorithm 2 then a `check` that only halts);
* `Errfail.alg2_err_le` — Claim lm:error-fail from the domination, the tails and
  the arithmetic (`Errfail.numerics`), with the two repairs above;
* `errfail_prob_le` — their composition.
-/

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Interface.Pseudocode

namespace Errfail

open Esa22Copy.Analysis.Alg2 MeasureTheory

variable {n : ℕ}

/-- From a running state, an Algorithm 1 iteration is an Algorithm 2 iteration followed by
the ⊥ test of line 8.
INTERNAL: "Algorithm 2 is Algorithm 1 with line 8 removed".
TEXLINE: esa22-final.tex:545 -/
theorem step_eq_map_check (L thr : ℕ) (s : State n) (a : Fin n) (hs : s.running = true) :
    step L thr s a = (step2 L thr s a).map (check thr) := by
  rw [step, if_pos hs, step2, PMF.map_bind]
  congr 1; funext u
  by_cases hf : full thr u = true
  · rw [if_pos hf, if_pos hf, PMF.map_comp]; rfl
  · rw [if_neg hf, if_neg hf, PMF.pure_map, check, if_neg hf]

/-- **`Pr[Error ∩ ¬Fail] ≤ Pr[Error₂]`**, for any event read off `(X, level)`: Algorithm 1
ends running with the event no more often than Algorithm 2 ends with it.
PAPER: esa22-final.tex:547-553 -/
theorem loop_running_le_loop2 (L thr : ℕ) (R : Finset (Fin n) → ℕ → Prop) (A : List (Fin n))
    (s : State n) :
    (loop L thr A s).toOuterMeasure {t | t.running = true ∧ R t.X t.level}
      ≤ (loop2 L thr A s).toOuterMeasure {t | R t.X t.level} := by
  induction A generalizing s with
  | nil => exact measure_mono fun t ht => ht.2
  | cons a A ih =>
    cases hs : s.running
    · rw [Fail.loop_of_halted _ _ _ s hs, PMF.toOuterMeasure_pure_apply,
        if_neg (by simp [hs])]
      exact bot_le
    · rw [loop, loop2, step_eq_map_check L thr s a hs, PMF.bind_map,
        PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl ?_
      simp only [Function.comp]
      by_cases hf : full thr u = true
      · rw [check, if_pos hf, Fail.loop_of_halted _ _ _ _ rfl, PMF.toOuterMeasure_pure_apply,
          if_neg (by simp)]
        exact bot_le
      · rw [check, if_neg hf]
        exact ih u

/-- A Bernoulli(1) coin is always `true`.
INTERNAL: `Y_0` keeps every item. -/
theorem bernoulli_one (h : (1 : NNReal) ≤ 1) : PMF.bernoulli 1 h = PMF.pure true := by
  ext b; cases b <;> simp [PMF.bernoulli_apply]

/-- `Y_0` keeps every item: from `Y`, it ends at `Y ∪ S`.
INTERNAL: the level-0 case of Claim cl:loop. -/
theorem yRun_zero (A : List (Fin n)) (Y : Finset (Fin n)) :
    yRun 0 A Y = PMF.pure (Y ∪ A.toFinset) := by
  induction A generalizing Y with
  | nil => simp [yRun]
  | cons a A ih =>
    have hk : keepProb 0 = 1 := by simp [keepProb]
    rw [yRun, yStep]
    simp only [hk] at *
    rw [bernoulli_one, PMF.pure_map, PMF.pure_bind, if_pos rfl, ih]
    congr 1
    ext b; simp; tauto

/-- `Y_{0,m} = S_m` surely.
INTERNAL: the level-0 case of Claim cl:loop. -/
theorem yLaw_zero (A : List (Fin n)) : yLaw 0 A = PMF.pure A.toFinset := by
  rw [yLaw, yRun_zero, Finset.empty_union]


/-- `e^{-ε²·thresh/12} ≤ δ/(8m)`, from `thresh ≥ (12/ε²)·log₂(8m/δ)` and `ln ≤ log₂`.
INTERNAL: the numeric core of `4e^{-ε²thresh/12} ≤ 4(δ/8)^{log e}`.
TEXLINE: esa22-final.tex:761 -/
theorem exp_le_of_thresh (m : ℕ) (hm : 1 ≤ m) (ε δ : ℝ) (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    Real.exp (-(ε ^ 2 * (thresh ε δ m : ℝ) / 12)) ≤ δ / (8 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set y : ℝ := 8 * (m : ℝ) / δ
  have hy1 : 1 ≤ y := by rw [le_div_iff₀ hδ0]; nlinarith
  have hy0 : 0 < y := by linarith
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlogb : Real.log y ≤ Real.logb 2 y := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    nlinarith
  have hthr : (12 / ε ^ 2) * Real.logb 2 y ≤ (thresh ε δ m : ℝ) := Nat.le_ceil _
  have hc : Real.logb 2 y ≤ ε ^ 2 * (thresh ε δ m : ℝ) / 12 := by
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hε2] at hthr
    rw [le_div_iff₀ (by norm_num)]; linarith
  calc Real.exp (-(ε ^ 2 * (thresh ε δ m : ℝ) / 12)) ≤ Real.exp (-Real.log y) :=
        Real.exp_le_exp.2 (by linarith)
    _ = δ / (8 * m) := by
        rw [Real.exp_neg, Real.exp_log hy0]
        simp only [y]; field_simp

/-- The final arithmetic: `m·e^{-thresh/6} + Σ_{q ≤ ℓ} 2e^{-ε²F0/(3·2^q)} ≤ δ/8 + 2δ/7 ≤ δ/2`
when `2^ℓ·thresh ≤ 4F0` (the geometric decay in `ℓ - q` replaces the paper's
`Σ_q ≤ 4e^{-…}` step).
INTERNAL: the numeric bookkeeping of Claim lm:error-fail.
TEXLINE: esa22-final.tex:733-761 -/
theorem numerics (m ℓ F thr : ℕ) (hm : 1 ≤ m) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hℓ : 2 ^ ℓ * thr ≤ 4 * F)
    (hx : Real.exp (-(ε ^ 2 * (thr : ℝ) / 12)) ≤ δ / (8 * m)) :
    m * Real.exp (-(thr : ℝ) / 6)
      + ∑ q ∈ Finset.range (ℓ + 1), 2 * Real.exp (-(ε ^ 2 * ((F : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3)
      ≤ δ / 2 := by
  set x := Real.exp (-(ε ^ 2 * (thr : ℝ) / 12)) with hxdef
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx8 : x ≤ δ / 8 := hx.trans (div_le_div_of_nonneg_left hδ0.le (by norm_num) (by linarith))
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hthr0 : (0 : ℝ) ≤ thr := Nat.cast_nonneg _
  -- the `Bad` term
  have h1 : (m : ℝ) * Real.exp (-(thr : ℝ) / 6) ≤ δ / 8 := by
    have : Real.exp (-(thr : ℝ) / 6) ≤ x := Real.exp_le_exp.2 (by nlinarith)
    calc (m : ℝ) * Real.exp (-(thr : ℝ) / 6) ≤ m * (δ / (8 * m)) := by gcongr; linarith
      _ = δ / 8 := by field_simp
  -- the `Error_{2,q}` terms
  have hterm : ∀ q ∈ Finset.range (ℓ + 1),
      2 * Real.exp (-(ε ^ 2 * ((F : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3) ≤ 2 * x ^ (ℓ - q + 1) := by
    intro q hq
    have hqℓ : q ≤ ℓ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    obtain ⟨d, rfl⟩ : ∃ d, ℓ = q + d := ⟨ℓ - q, by omega⟩
    rw [Nat.add_sub_cancel_left]
    gcongr
    rw [hxdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hd : ((d + 1 : ℕ) : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
    have hF : (2 : ℝ) ^ q * 2 ^ d * thr ≤ 4 * F := by
      have := hℓ; rw [pow_add] at this; exact_mod_cast this
    have hq2 : (0 : ℝ) < 2 ^ q := by positivity
    have hFq : (F : ℝ) * (2⁻¹ : ℝ) ^ q = F / 2 ^ q := by rw [inv_pow, div_eq_mul_inv]
    rw [hFq]
    have key : 2 ^ d * (thr : ℝ) / 4 ≤ F / 2 ^ q := by
      rw [le_div_iff₀ hq2]; nlinarith
    have hε20 : 0 ≤ ε ^ 2 := sq_nonneg ε
    have : ((d + 1 : ℕ) : ℝ) * (ε ^ 2 * thr / 12) ≤ ε ^ 2 * (F / 2 ^ q) / 3 := by
      calc ((d + 1 : ℕ) : ℝ) * (ε ^ 2 * thr / 12) ≤ 2 ^ d * (ε ^ 2 * thr / 12) := by
            gcongr
        _ = ε ^ 2 * (2 ^ d * thr / 4) / 3 := by ring
        _ ≤ ε ^ 2 * (F / 2 ^ q) / 3 := by gcongr
    push_cast at this ⊢
    linarith
  have hx1 : x < 1 := by linarith
  have h2 : ∑ q ∈ Finset.range (ℓ + 1), 2 * x ^ (ℓ - q + 1) ≤ 2 * (x / (1 - x)) := by
    have hre : ∑ q ∈ Finset.range (ℓ + 1), 2 * x ^ (ℓ - q + 1)
        = ∑ i ∈ Finset.range (ℓ + 1), 2 * x ^ (i + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i < ℓ + 1 := Finset.mem_range.1 hi
      congr 2; omega
    rw [hre, ← Finset.mul_sum]
    gcongr
    have := geom_sum_Ico_le_of_lt_one (m := 1) (n := ℓ + 2) hx0 hx1
    rw [Finset.sum_Ico_eq_sum_range] at this
    simpa [add_comm, pow_one] using this
  have h3 : 2 * (x / (1 - x)) ≤ 2 * δ / 7 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  calc _ ≤ δ / 8 + 2 * δ / 7 := by
        gcongr
        exact (Finset.sum_le_sum hterm).trans (h2.trans h3)
    _ ≤ δ / 2 := by linarith


/-- `thresh > 0` on a nonempty stream.
INTERNAL: side condition for the Chernoff upper tail. -/
theorem thresh_pos (m : ℕ) (hm : 1 ≤ m) (ε δ : ℝ) (hε0 : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < thresh ε δ m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  apply Nat.ceil_pos.2
  apply mul_pos (by positivity)
  apply Real.logb_pos (by norm_num)
  rw [lt_div_iff₀ hδ0]; nlinarith

/-- `|X|·2^q ∈ [(1-ε)F0, (1+ε)F0]` iff `|X| ∈ [(1-ε)F0/2^q, (1+ε)F0/2^q]`.
INTERNAL: the rescaling in `Error_{2,q}`.
TEXLINE: esa22-final.tex:748 -/
theorem mem_relErr_iff (ε : ℝ) (c q : ℕ) (F : ℝ) :
    ((c * 2 ^ q : ℕ) : ℝ) ∈ Arlib.relErr ε F ↔
      (c : ℝ) ∈ Set.Icc ((1 - ε) * (F * (2⁻¹ : ℝ) ^ q)) ((1 + ε) * (F * (2⁻¹ : ℝ) ^ q)) := by
  have h : (0 : ℝ) < 2 ^ q := by positivity
  have e : ∀ a : ℝ, a * (F * (2⁻¹ : ℝ) ^ q) = a * F / 2 ^ q := by
    intro a; rw [inv_pow]; ring
  simp only [Set.mem_Icc, e, div_le_iff₀ h, le_div_iff₀ h]
  push_cast
  rfl

/-- `|S_j| ≤ F0`.
INTERNAL: the prefix of a stream has no more distinct items. -/
theorem toFinset_take_card_le (A : List (Fin n)) (k : ℕ) :
    (A.take k).toFinset.card ≤ A.toFinset.card := by
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset] at hx ⊢
  exact List.mem_of_mem_take hx

/-- `Error₂` on Algorithm 2's final state: `|X|/p ∉ [(1-ε)F0, (1+ε)F0]`.
PAPER: esa22-final.tex:556-558 -/
def Bad2 (ε : ℝ) (F : ℕ) : Set (State n) :=
  {t | ((t.X.card * 2 ^ t.level : ℕ) : ℝ) ∉ Arlib.relErr ε (F : ℝ)}

/-- **Claim lm:error-fail.** `Pr[Error₂] ≤ δ/2`.  Split on `F0 < thresh` (then the level
stays `0` and the answer is exactly `F0`; the paper's `ℓ < 0` case) and `F0 ≥ thresh`
(`ℓ` with `thresh/4 ≤ F0/2^ℓ < thresh/2`; `Bad` via `loop2_level_gt_le` and
`yLaw_card_ge_le`, `Error_{2,q}` via `loop2_level_eq_le_yLaw` and `yLaw_card_dev_le`).
PAPER: esa22-final.tex:694-774 -/
theorem alg2_err_le (A : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (loop2 (A.length + 1) (thresh ε δ A.length) A init).toOuterMeasure (Bad2 ε (F0 A))
      ≤ ENNReal.ofReal (δ / 2) := by
  set L := A.length + 1
  set thr := thresh ε δ A.length
  have hL : A.length ≤ L := Nat.le_succ _
  have hF0 : F0 A = A.toFinset.card := rfl
  rcases Nat.eq_zero_or_pos A.length with h0 | hm
  · rw [List.length_eq_zero_iff.1 h0]
    rw [loop2, PMF.toOuterMeasure_pure_apply, if_neg]
    · exact bot_le
    · simp [Bad2, init, F0]
  set F := A.toFinset.card
  have hthr : 0 < thr := thresh_pos _ hm ε δ hε0 hδ0 hδ1
  by_cases hF : F < thr
  · -- the sample never reaches `thresh`: the level stays `0` and the answer is `F0`
    have hcover : Bad2 ε (F0 A) ⊆ {t : State n | 0 < t.level} ∪
        {t | t.level = 0 ∧ t.X ∈ {U : Finset (Fin n) | ((U.card * 2 ^ 0 : ℕ) : ℝ) ∉
          Arlib.relErr ε (F0 A : ℝ)}} := by
      intro t ht
      rcases Nat.eq_zero_or_pos t.level with h | h
      · exact Or.inr ⟨h, by simpa [Bad2, h] using ht⟩
      · exact Or.inl h
    refine (measure_mono hcover).trans ((measure_union_le _ _).trans ?_)
    have e1 := loop2_level_gt_le L thr A hL 0
    have e2 := loop2_level_eq_le_yLaw L thr A hL 0
      {U : Finset (Fin n) | ((U.card * 2 ^ 0 : ℕ) : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)}
    have z1 : ∑ j ∈ Finset.range A.length,
        (yLaw 0 (A.take (j + 1))).toOuterMeasure {U : Finset (Fin n) | U.card = thr} = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [yLaw_zero, PMF.toOuterMeasure_pure_apply, if_neg]
      have := toFinset_take_card_le A (j + 1)
      simp only [Set.mem_setOf_eq]; omega
    have z2 : (yLaw 0 A).toOuterMeasure
        {U : Finset (Fin n) | ((U.card * 2 ^ 0 : ℕ) : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)} = 0 := by
      rw [yLaw_zero, PMF.toOuterMeasure_pure_apply, if_neg]
      simp only [Set.mem_setOf_eq, pow_zero, mul_one, not_not, Arlib.mem_relErr, hF0]
      constructor <;> nlinarith [(Nat.cast_nonneg F : (0 : ℝ) ≤ F)]
    calc _ ≤ (0 : ENNReal) + 0 := add_le_add (e1.trans z1.le) (e2.trans z2.le)
      _ ≤ _ := by simp
  · push_neg at hF
    -- `ℓ` with `thresh/4 ≤ F0/2^ℓ < thresh/2`
    obtain ⟨ℓ, hℓ1, hℓ2⟩ : ∃ ℓ : ℕ, 2 ^ ℓ * thr ≤ 4 * F ∧ 4 * F < 2 ^ (ℓ + 1) * thr := by
      refine ⟨Nat.log 2 (4 * F / thr), ?_, ?_⟩
      · calc 2 ^ Nat.log 2 (4 * F / thr) * thr ≤ 4 * F / thr * thr :=
              Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 (by
                have : 1 ≤ 4 * F / thr := (Nat.le_div_iff_mul_le hthr).2 (by omega)
                omega))
          _ ≤ 4 * F := Nat.div_mul_le_self _ _
      · calc 4 * F < 4 * F / thr * thr + thr := Nat.lt_div_mul_add hthr
          _ = (4 * F / thr + 1) * thr := by ring
          _ ≤ 2 ^ (Nat.log 2 (4 * F / thr) + 1) * thr :=
              Nat.mul_le_mul_right _ (Nat.lt_pow_succ_log_self (by norm_num) _)
    set 𝓑 : ℕ → Set (Finset (Fin n)) := fun q =>
      {U | ((U.card * 2 ^ q : ℕ) : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)}
    have hcover : Bad2 ε (F0 A) ⊆ {t : State n | ℓ < t.level} ∪
        ⋃ q ∈ Finset.range (ℓ + 1), {t : State n | t.level = q ∧ t.X ∈ 𝓑 q} := by
      intro t ht
      rcases lt_or_ge ℓ t.level with h | h
      · exact Or.inl h
      · refine Or.inr (Set.mem_biUnion (x := t.level) ?_ ⟨rfl, ht⟩)
        simp only [Finset.coe_range, Set.mem_Iio]; omega
    refine (measure_mono hcover).trans ((measure_union_le _ _).trans ?_)
    -- `Bad`: the level passes `ℓ`
    have hbad : (loop2 L thr A init).toOuterMeasure {t | ℓ < t.level}
        ≤ ENNReal.ofReal (A.length * Real.exp (-(thr : ℝ) / 6)) := by
      refine (loop2_level_gt_le L thr A hL ℓ).trans ?_
      calc _ ≤ ∑ j ∈ Finset.range A.length, ENNReal.ofReal (Real.exp (-(thr : ℝ) / 6)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine (measure_mono (show {U : Finset (Fin n) | U.card = thr} ⊆ {U | thr ≤ U.card} from
              fun U (hU : U.card = thr) => (show thr ≤ U.card by omega))).trans ?_
            apply yLaw_card_ge_le ℓ thr _ hthr
            have hc : ((A.take (j + 1)).toFinset.card : ℝ) ≤ F := by
              exact_mod_cast toFinset_take_card_le A (j + 1)
            have h2 : (4 * F : ℝ) < 2 ^ (ℓ + 1) * thr := by exact_mod_cast hℓ2
            have hp : (0 : ℝ) < 2 ^ ℓ := by positivity
            rw [inv_pow, ← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ hp]
            rw [pow_succ] at h2
            nlinarith
        _ = _ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast]
    -- `Error_{2,q}` for `q ≤ ℓ`
    have herr : ∀ q ∈ Finset.range (ℓ + 1),
        (loop2 L thr A init).toOuterMeasure {t : State n | t.level = q ∧ t.X ∈ 𝓑 q}
          ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * ((F : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3)) := by
      intro q _
      refine (loop2_level_eq_le_yLaw L thr A hL q (𝓑 q)).trans ?_
      refine le_trans (measure_mono fun U hU => ?_) (yLaw_card_dev_le q A ε hε0 hε1.le)
      simp only [𝓑, Set.mem_setOf_eq, mem_relErr_iff, hF0] at hU ⊢
      exact hU
    calc _ ≤ ENNReal.ofReal (A.length * Real.exp (-(thr : ℝ) / 6))
          + ∑ q ∈ Finset.range (ℓ + 1),
              ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * ((F : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3)) :=
          add_le_add hbad ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum herr))
      _ = ENNReal.ofReal (A.length * Real.exp (-(thr : ℝ) / 6)
          + ∑ q ∈ Finset.range (ℓ + 1), 2 * Real.exp (-(ε ^ 2 * ((F : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3)) := by
          rw [ENNReal.ofReal_add (by positivity)
            (Finset.sum_nonneg fun q _ => by positivity), ENNReal.ofReal_sum_of_nonneg
            (fun q _ => by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (numerics A.length ℓ F thr hm ε δ hε0 hε1 hδ0 hδ1 hℓ1
            (exp_le_of_thresh A.length hm ε δ hε0 hδ0 hδ1))


end Errfail

/-- **Claim claim:errfail.** `Pr[Error ∩ ¬Fail] ≤ δ/2`: the law of Algorithm 1's
answer puts mass at most `δ/2` on non-⊥ answers outside the relative-error
window `[(1-ε)F0, (1+ε)F0]`.
PAPER: esa22-final.tex:512-521 -/
theorem errfail_prob_le {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (outputLaw A ε δ).toOuterMeasure
        {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)}
      ≤ ENNReal.ofReal (δ / 2) := by
  have hpre : (answer ⁻¹' {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)}
      : Set (State n)) = {t | t.running = true ∧
        (fun X q => ((X.card * 2 ^ q : ℕ) : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)) t.X t.level} := by
    ext t; cases ht : t.running <;> simp [answer, ht]
  rw [outputLaw, answerLaw, PMF.toOuterMeasure_map_apply, hpre, stateLaw]
  exact (Errfail.loop_running_le_loop2 (A.length + 1) (thresh ε δ A.length)
    (fun X q => ((X.card * 2 ^ q : ℕ) : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)) A init).trans
    (Errfail.alg2_err_le A ε δ hε0 hε1 hδ0 hδ1)

end Esa22Copy.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · Claim lm:error-fail with the two paper repairs (`F0 < thresh` exact case; mean in `[thresh/4, thresh/2)`), via `Alg2Dominated` and `YLawChernoff`
-/
