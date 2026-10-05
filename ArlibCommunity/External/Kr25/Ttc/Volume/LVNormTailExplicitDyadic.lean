/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailDyadic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # An explicit logarithmic shell count for the LV norm tail -/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib
open scoped ENNReal

variable {n : ℕ}

/-- The literal base-two logarithmic shell count. -/
noncomputable def explicitDyadicTailIndex (eta : ℝ) : ℕ :=
  ⌈Real.logb 2 (1 / eta)⌉₊

theorem explicitDyadicTailIndex_pos {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < explicitDyadicTailIndex eta := by
  rw [explicitDyadicTailIndex, Nat.ceil_pos]
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  exact (lt_div_iff₀ heta0).2 (by simpa using heta1)

/-- The explicit shell count is sufficient for relative tail `eta`. -/
theorem inv_two_pow_explicitDyadicTailIndex_le {eta : ℝ}
    (heta0 : 0 < eta) (_heta1 : eta < 1) :
    1 / (2 : ℝ) ^ explicitDyadicTailIndex eta ≤ eta := by
  have hinv : 0 < (1 / eta : ℝ) := by positivity
  have hlog : Real.logb 2 (1 / eta) ≤ (explicitDyadicTailIndex eta : ℝ) := by
    exact Nat.le_ceil _
  have hpow : 1 / eta ≤ (2 : ℝ) ^ explicitDyadicTailIndex eta := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hinv).1 hlog
  have hpow0 : 0 < (2 : ℝ) ^ explicitDyadicTailIndex eta := by positivity
  apply (div_le_iff₀ hpow0).2
  have := (mul_le_mul_of_nonneg_right hpow heta0.le)
  field_simp [heta0.ne'] at this ⊢
  exact this

/-- Casting the explicit ceiling loses less than one shell. -/
theorem explicitDyadicTailIndex_lt_logb_add_one {eta : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    (explicitDyadicTailIndex eta : ℝ) < Real.logb 2 (1 / eta) + 1 := by
  apply Nat.ceil_lt_add_one
  exact (Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    ((lt_div_iff₀ heta0).2 (by simpa using heta1))).le

/-- A natural-number upper bound with a second ceiling, useful to instantiate finite loops. -/
theorem explicitDyadicTailIndex_le_ceil_logb_add_one {eta : ℝ}
    (_heta0 : 0 < eta) (_heta1 : eta < 1) :
    explicitDyadicTailIndex eta ≤ ⌈Real.logb 2 (1 / eta)⌉₊ + 1 := by
  simp [explicitDyadicTailIndex]

/-- Explicit logarithmic moment-truncation radius. -/
noncomputable def explicitDyadicMomentRadius (M eta : ℝ) : ℝ :=
  Real.sqrt M *
    (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * explicitDyadicTailIndex eta)

theorem body_normTail_explicit_dyadic
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M eta : ℝ} (hM : 0 < M) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    (∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) |
        explicitDyadicMomentRadius M eta < ‖y‖}.indicator (fun _ => (1 : ℝ)) x -
        1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) ≤ 0 := by
  simpa only [explicitDyadicMomentRadius] using
    body_normTail_dyadic_sub_nonpos hn hKc hKcl hKb hM
      (explicitDyadicTailIndex eta) (explicitDyadicTailIndex_pos heta0 heta1) hmoment

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.inv_two_pow_explicitDyadicTailIndex_le
#print axioms Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one
#print axioms Ttc.CVAdaptive.body_normTail_explicit_dyadic
