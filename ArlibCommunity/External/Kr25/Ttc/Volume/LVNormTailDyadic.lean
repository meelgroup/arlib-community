/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailBody

/-! # Choosing the dyadic shell count from a requested error -/

namespace Ttc.CVAdaptive

open MeasureTheory Set

variable {n : ℕ}

noncomputable def dyadicTailIndex (eta : ℝ) (heta : 0 < eta) : ℕ :=
  Classical.choose (exists_pow_lt_of_lt_one heta (by norm_num : (2 : ℝ)⁻¹ < 1)) + 1

theorem dyadicTailIndex_pos (eta : ℝ) (heta : 0 < eta) : 0 < dyadicTailIndex eta heta := by
  simp [dyadicTailIndex]

theorem inv_two_pow_dyadicTailIndex_le {eta : ℝ} (heta : 0 < eta) :
    1 / (2 : ℝ) ^ dyadicTailIndex eta heta ≤ eta := by
  let k := Classical.choose (exists_pow_lt_of_lt_one heta (by norm_num : (2 : ℝ)⁻¹ < 1))
  have hk : ((2 : ℝ)⁻¹) ^ k < eta :=
    Classical.choose_spec (exists_pow_lt_of_lt_one heta (by norm_num : (2 : ℝ)⁻¹ < 1))
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  have hpow0 : 0 ≤ ((2 : ℝ)⁻¹) ^ k := pow_nonneg hhalf _
  have hs : ((2 : ℝ)⁻¹) ^ (k + 1) ≤ ((2 : ℝ)⁻¹) ^ k := by
    rw [pow_succ]
    nlinarith
  have : ((2 : ℝ)⁻¹) ^ dyadicTailIndex eta heta ≤ eta := by
    dsimp [dyadicTailIndex, k] at *
    exact hs.trans hk.le
  simpa [inv_pow] using this

/-- Requested-error version of the body tail, retaining the explicit chosen shell count and
therefore its logarithmic radius. -/
theorem body_normTail_chosen_dyadic
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M eta : ℝ} (hM : 0 < M) (heta : 0 < eta)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    (∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) |
        Real.sqrt M * (1 + Real.sqrt 2 +
          4 * Real.sqrt 3 * dyadicTailIndex eta heta) < ‖y‖}.indicator
          (fun _ => (1 : ℝ)) x -
        1 / (2 : ℝ) ^ dyadicTailIndex eta heta) ≤ 0 :=
  body_normTail_dyadic_sub_nonpos hn hKc hKcl hKb hM (dyadicTailIndex eta heta)
    (dyadicTailIndex_pos eta heta) hmoment

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.inv_two_pow_dyadicTailIndex_le
#print axioms Ttc.CVAdaptive.body_normTail_chosen_dyadic
