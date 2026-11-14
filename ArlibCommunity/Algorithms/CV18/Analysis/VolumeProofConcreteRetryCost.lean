/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGeometricRetryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledParameters

/-! # Concrete retry-cost contraction for the scheduled parameters -/

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal

theorem maxRetries_ge_128 (q : VolumeParams) :
    128 ≤ maxRetries q := by
  have hlog : (1 : ℝ) ≤
      protectedLog (4 / sampleMixingError q) := le_max_left _ _
  have hceil : 128 * protectedLog
      (4 / sampleMixingError q) ≤
      (maxRetries q : ℝ) := Nat.le_ceil _
  exact_mod_cast (show (128 : ℝ) ≤ maxRetries q by
    nlinarith)

/-- At the concrete safe retry count, one scheduled block contributes at
most `1/128` additional rejection mass. -/
theorem figureOneCorrectedBlockBudget_safe_le_one_div_128
    (q : VolumeParams) :
    figureOneCorrectedBlockBudget q (maxRetries q - 1) ≤
      ENNReal.ofReal (1 / 128 : ℝ) := by
  unfold figureOneCorrectedBlockBudget
  apply ENNReal.ofReal_le_ofReal
  unfold blockMixingError
  have hNpos := maxRetries_pos q
  have hcast : ((maxRetries q - 1 : ℕ) : ℝ) + 1 =
      maxRetries q := by
    exact_mod_cast Nat.sub_add_cancel hNpos
  rw [hcast]
  have hN : (128 : ℝ) ≤ maxRetries q := by
    exact_mod_cast maxRetries_ge_128 q
  have hden : (0 : ℝ) < 4 * maxRetries q := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [sampleMixingError_le_one q]

/-- Stationary rejection plus the scheduled block approximation is bounded
by `61/64`, uniformly in dimension and accuracy. -/
theorem figureOneScheduled_retryContinuationMass_le_nearBalanced
    (q : VolumeParams) {rejectMass : ENNReal}
    (hreject : rejectMass ≤ ENNReal.ofReal (121 / 128 : ℝ)) :
    rejectMass + figureOneCorrectedBlockBudget q
        (maxRetries q - 1) ≤
      ENNReal.ofReal (61 / 64 : ℝ) :=
  balancedRejectMass_add_error_le_nearBalanced hreject
    (figureOneCorrectedBlockBudget_safe_le_one_div_128 q)

/-- Consequently every concrete finite retry loop has the uniform `64/3`
expected-trial multiplier used by the whole-run cost proof. -/
theorem finiteRetryExpectedCost_figureOneScheduled_le
    (q : VolumeParams) (trialCost : ENNReal) :
    finiteRetryExpectedCost trialCost (ENNReal.ofReal (61 / 64 : ℝ))
        (maxRetries q) ≤
      trialCost * ENNReal.ofReal (64 / 3 : ℝ) :=
  finiteRetryExpectedCost_nearBalanced_le trialCost _

#print axioms figureOneCorrectedBlockBudget_safe_le_one_div_128
#print axioms figureOneScheduled_retryContinuationMass_le_nearBalanced

end ArlibCommunity.Algorithms.CV18
