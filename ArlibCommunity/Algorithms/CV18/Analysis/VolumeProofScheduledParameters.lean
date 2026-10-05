/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryKernel
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRetryTailBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedGlobalCap

/-! # Concrete global parameters for the scheduled balanced sampler -/

namespace ArlibCommunity.Algorithms.CV18

/-- The scheduled replacement for the old global balanced parameters.
The proposal cap remains exactly the shared outer cutoff, the stride uses the
new accuracy logarithm, and the retry count is the proved geometric-tail
deadline. -/
noncomputable def figureOneScheduledBalancedParameters :
    BalancedCoolingParameters where
  proposalCap := fun q _ => figureOneGlobalQueryBudget q
  properStride := fun q sigma2 =>
    figureOneScheduledCorrectedProperStride q sigma2
      (figureOneSafeRetryCount q - 1)
  retryLimit := fun q _ => figureOneSafeRetryCount q

@[simp] theorem figureOneScheduledBalancedParameters_proposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneScheduledBalancedParameters.proposalCap q sigma2 =
      figureOneGlobalQueryBudget q := rfl

@[simp] theorem figureOneScheduledBalancedParameters_properStride
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneScheduledBalancedParameters.properStride q sigma2 =
      figureOneScheduledCorrectedProperStride q sigma2
        (figureOneSafeRetryCount q - 1) := rfl

@[simp] theorem figureOneScheduledBalancedParameters_retryLimit
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneScheduledBalancedParameters.retryLimit q sigma2 =
      figureOneSafeRetryCount q := rfl

theorem figureOneScheduledBalancedParameters_proposalCap_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneScheduledBalancedParameters.proposalCap q sigma2 := by
  simp only [figureOneScheduledBalancedParameters_proposalCap]
  exact figureOneGlobalQueryBudget_pos q

theorem figureOneScheduledBalancedParameters_properStride_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneScheduledBalancedParameters.properStride q sigma2 := by
  simp only [figureOneScheduledBalancedParameters_properStride]
  exact figureOneScheduledCorrectedProperStride_pos q sigma2 _

theorem figureOneScheduledBalancedParameters_retryLimit_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneScheduledBalancedParameters.retryLimit q sigma2 := by
  simp only [figureOneScheduledBalancedParameters_retryLimit]
  exact figureOneSafeRetryCount_pos q

theorem figureOneScheduledBalancedParameters_attempts_add_one
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneScheduledBalancedParameters.retryLimit q sigma2 - 1 + 1 =
      figureOneSafeRetryCount q := by
  simp only [figureOneScheduledBalancedParameters_retryLimit]
  exact Nat.sub_add_cancel (figureOneSafeRetryCount_pos q)

/-- Local proper blocks request one query beyond the shared cap.  Therefore
local exhaustion remains invisible until the outer globally capped execution
has already attempted its first forbidden query. -/
theorem figureOneScheduled_localRawCap_eq_outer_add_one
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneScheduledBalancedParameters.proposalCap q sigma2 + 1 =
      figureOneGlobalQueryBudget q + 1 := by
  rfl

/-- Safe retry arithmetic in the exact attempts convention used by the
finite transition recursion. -/
theorem figureOneScheduled_retryTail_le
    (q : VolumeParams) (sigma2 : ℝ) {rejectMass : ENNReal}
    (hreject : rejectMass ≤ ENNReal.ofReal (121 / 128 : ℝ)) :
    rejectMass ^
        (figureOneScheduledBalancedParameters.retryLimit q sigma2 - 1 + 1) ≤
      figureOneCorrectedRetryTailBudget q := by
  simpa only [figureOneScheduledBalancedParameters_retryLimit] using
    figureOneSafeRetryTail_le q hreject

#print axioms figureOneScheduledBalancedParameters_attempts_add_one
#print axioms figureOneScheduled_retryTail_le

end ArlibCommunity.Algorithms.CV18
