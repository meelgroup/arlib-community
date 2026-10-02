import Esa22Copy.Model.Prelude
import Esa22Copy.Interface.Pseudocode
import Mathlib.Data.Finset.Interval

/-!
# Claim lm:fail — Algorithm 1 outputs ⊥ with probability at most δ/8

`fail_prob_le` bounds the mass that `Pseudocode.outputLaw A ε δ` puts on `none`
(⊥) by `δ/8` (esa22-final.tex:523-538).  The paper's argument: at iteration `j`
the run outputs ⊥ only if `|X| = thresh` and the thinning pass keeps all `thresh`
elements, which has probability at most `2^{-thresh}` (the paper writes `=`;
it is `≤`, since the test at line 5 need not fire); a union bound over the `m`
iterations gives `m · 2^{-thresh}`, and `thresh ≥ log₂(8m/δ)` makes this `≤ δ/8`.
-/

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Interface.Pseudocode

namespace Fail

variable {n : ℕ}

/-- A uniform random subset of `Fin n` contains a fixed `X` with probability at most
`2^{-|X|}` (it is exactly that).
INTERNAL: the per-element coin computation behind "none thrown away".
TEXLINE: esa22-final.tex:530 -/
theorem uniform_superset_le (X : Finset (Fin n)) :
    (PMF.uniformOfFintype (Finset (Fin n))).toOuterMeasure {h | X ⊆ h} ≤ (2⁻¹ : ENNReal) ^ X.card := by
  have hset : {h : Finset (Fin n) | X ⊆ h} = ((Finset.Icc X Finset.univ : Finset (Finset (Fin n))) : Set _) := by
    ext h; simp
  rw [hset, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, Fintype.card_finset,
    Fintype.card_fin]
  rw [Finset.card_Icc_finset (Finset.subset_univ X), Finset.card_univ, Fintype.card_fin]
  have hk : X.card ≤ n := by simpa using Finset.card_le_univ X
  generalize X.card = k at hk ⊢
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, mul_right_comm,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, ENNReal.inv_pow]


/-- The ⊥ event on pseudocode states: the run has halted.
INTERNAL: the event `Fail` read on the final state.
TEXLINE: esa22-final.tex:512 -/
def Halted : Set (State n) := {t | t.running = false}

/-- Lines 5-8 on a running state with the pick already made output ⊥ w.p. `≤ 2^{-thresh}`.
INTERNAL: the event `Fail_j` given the post-pick state.
TEXLINE: esa22-final.tex:527-530 -/
theorem inner_fail_le (thr : ℕ) (u : State n) (hu : u.running = true) :
    (if full thr u then (throw u).map (fun s => check thr (halve s)) else PMF.pure u).toOuterMeasure
      Halted ≤ (2⁻¹ : ENNReal) ^ thr := by
  by_cases hf : full thr u = true
  · rw [if_pos hf]
    unfold Esa22Copy.Interface.Pseudocode.throw
    rw [PMF.map_comp, PMF.toOuterMeasure_map_apply]
    have hcard : u.X.card = thr := by simpa [full] using hf
    calc _ ≤ (PMF.uniformOfFintype (Finset (Fin n))).toOuterMeasure {h | u.X ⊆ h} := by
          apply MeasureTheory.measure_mono
          intro h hh
          simp only [Set.mem_preimage, Function.comp, Halted, Set.mem_setOf_eq, check, halve,
            full] at hh
          by_cases h1 : (u.X.filter (· ∈ h)).card = thr
          · intro x hx
            exact Finset.filter_card_eq (h1.trans hcard.symm) x hx
          · simp [h1, hu] at hh
      _ ≤ _ := hcard ▸ uniform_superset_le u.X
  · rw [if_neg hf, PMF.toOuterMeasure_pure_apply, if_neg (by simp [Halted, hu])]
    exact bot_le

/-- One iteration from a running state outputs ⊥ with probability `≤ 2^{-thresh}`.
INTERNAL: `Pr[Fail_j] ≤ 2^{-thresh}` (the paper writes `=`).
TEXLINE: esa22-final.tex:527-530 -/
theorem step_fail_le (L thr : ℕ) (s : State n) (a : Fin n) (hs : s.running = true) :
    (step L thr s a).toOuterMeasure Halted ≤ (2⁻¹ : ENNReal) ^ thr := by
  rw [step, if_pos hs, pick, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' bits, (PMF.uniformOfFintype (Fin L → Bool)) bits * (2⁻¹ : ENNReal) ^ thr := by
        refine ENNReal.tsum_le_tsum fun bits => ?_
        gcongr
        apply inner_fail_le
        simp only [Function.comp]
        split_ifs <;> simpa [drop] using hs
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


/-- A halted run is frozen: the rest of the loop leaves it as it is.
INTERNAL: the pseudocode's halt-after-⊥ semantics. -/
theorem loop_of_halted (L thr : ℕ) (A : List (Fin n)) (s : State n) (hs : s.running = false) :
    loop L thr A s = PMF.pure s := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [loop, step, if_neg (by simp [hs]), PMF.pure_bind, ih]

/-- Union bound over the iterations: from a running state, the loop over `A` outputs ⊥
with probability `≤ |A| · 2^{-thresh}`.
INTERNAL: `Pr[Fail] ≤ Σ_j Pr[Fail_j]`.
TEXLINE: esa22-final.tex:532-535 -/
theorem loop_fail_le (L thr : ℕ) (A : List (Fin n)) (s : State n) (hs : s.running = true) :
    (loop L thr A s).toOuterMeasure Halted ≤ A.length * (2⁻¹ : ENNReal) ^ thr := by
  induction A generalizing s with
  | nil =>
    rw [loop, PMF.toOuterMeasure_pure_apply, if_neg (by simp [Halted, hs])]
    exact bot_le
  | cons a A ih =>
    set r : ENNReal := (2⁻¹ : ENNReal) ^ thr
    rw [loop, PMF.toOuterMeasure_bind_apply]
    have hpt : ∀ t : State n, (loop L thr A t).toOuterMeasure Halted ≤
        A.length * r + Halted.indicator 1 t := by
      intro t
      cases ht : t.running
      · rw [Set.indicator_of_mem (by simp [Halted, ht])]
        exact ((MeasureTheory.measure_mono (Set.subset_univ _)).trans
          (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)))).trans
          le_add_self
      · exact (ih t ht).trans le_self_add
    calc _ ≤ ∑' t, (step L thr s a) t * (A.length * r + Halted.indicator 1 t) :=
          ENNReal.tsum_le_tsum fun t => by gcongr; exact hpt t
      _ = A.length * r + (step L thr s a).toOuterMeasure Halted := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun t => ?_
          by_cases ht : t ∈ Halted <;> simp [ht]
      _ ≤ A.length * r + r := by gcongr; exact step_fail_le L thr s a hs
      _ = (a :: A).length * r := by simp [add_mul]

/-- `m · 2^{-thresh} ≤ δ/8`, from `thresh ≥ log₂(8m/δ)`.
INTERNAL: the last inequality of Claim lm:fail.
TEXLINE: esa22-final.tex:534 -/
theorem count_le (m : ℕ) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (m : ENNReal) * (2⁻¹ : ENNReal) ^ thresh ε δ m ≤ ENNReal.ofReal (δ / 8) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hconv : (m : ENNReal) * (2⁻¹ : ENNReal) ^ thresh ε δ m =
      ENNReal.ofReal (m * (2⁻¹ : ℝ) ^ thresh ε δ m) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  set x : ℝ := 8 * (m : ℝ) / δ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : 1 ≤ x := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hcoef : (1 : ℝ) ≤ 12 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hthr : Real.logb 2 x ≤ (thresh ε δ m : ℝ) :=
    calc Real.logb 2 x ≤ 12 / ε ^ 2 * Real.logb 2 x := le_mul_of_one_le_left hlog hcoef
      _ ≤ _ := Nat.le_ceil _
  have hpow : x ≤ (2 : ℝ) ^ thresh ε δ m := by
    calc x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (thresh ε δ m : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hthr
      _ = _ := Real.rpow_natCast _ _
  rw [inv_pow]
  have h2 : (0 : ℝ) < 2 ^ thresh ε δ m := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ h2]
  have : 8 * (m : ℝ) ≤ δ * 2 ^ thresh ε δ m := by
    have := hpow; rw [div_le_iff₀ hδ0] at this; linarith
  linarith


end Fail

/-- **Claim lm:fail.** `Pr[Fail] ≤ δ/8`: the law of Algorithm 1's answer puts mass
at most `δ/8` on ⊥.
PAPER: esa22-final.tex:523-538 -/
theorem fail_prob_le {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (outputLaw A ε δ).toOuterMeasure {none} ≤ ENNReal.ofReal (δ / 8) := by
  have hpre : (answer ⁻¹' {none} : Set (State n)) = Fail.Halted := by
    ext t; cases ht : t.running <;> simp [answer, Fail.Halted, ht]
  rw [outputLaw, answerLaw, PMF.toOuterMeasure_map_apply, hpre, stateLaw]
  exact (Fail.loop_fail_le _ _ A init rfl).trans (Fail.count_le A.length ε δ hε0 hε1 hδ0 hδ1)

end Esa22Copy.Analysis
