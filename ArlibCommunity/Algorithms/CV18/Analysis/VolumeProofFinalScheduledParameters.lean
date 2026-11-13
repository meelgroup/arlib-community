/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRateCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledWorkComparison

/-! # Final global-cap parameters for the scheduled executable

The proposal cap is derived from the same scheduled soft-O rate used by the
expected-cost theorem.  In particular, it is not the obsolete cap derived
from `volumeBaseComplexityRate`.
-/

namespace ArlibCommunity.Algorithms.CV18

theorem figureOneFinalScheduledExpectedCostConstant_pos :
    0 < figureOneFinalScheduledExpectedCostConstant := by
  norm_num [figureOneFinalScheduledExpectedCostConstant]

theorem figureOneFinalScheduledQueryBudget_pos (q : VolumeParams) :
    0 < figureOneFinalScheduledQueryBudget q := by
  unfold figureOneFinalScheduledQueryBudget globalQueryBudgetOfRate
  apply Nat.ceil_pos.mpr
  positivity [figureOneFinalScheduledExpectedCostConstant_pos,
    volumeScheduledBaseComplexityRate_pos q]

@[simp] theorem figureOneFinalScheduledBalancedParameters_proposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 =
      figureOneFinalScheduledLocalProposalCap q sigma2 := rfl

@[simp] theorem figureOneFinalScheduledBalancedParameters_properStride
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.properStride q sigma2 =
      figureOneScheduledCorrectedProperStride q sigma2
        (figureOneSafeRetryCount q - 1) := rfl

@[simp] theorem figureOneFinalScheduledBalancedParameters_retryLimit
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.retryLimit q sigma2 =
      figureOneSafeRetryCount q := rfl

theorem figureOneFinalScheduledBalancedParameters_attempts_add_one
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.retryLimit q sigma2 - 1 + 1 =
      figureOneSafeRetryCount q := by
  simp only [figureOneFinalScheduledBalancedParameters_retryLimit]
  exact Nat.sub_add_cancel (figureOneSafeRetryCount_pos q)

theorem figureOneFinalScheduled_outerBudget_le_localProposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledQueryBudget q ≤
      figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 := by
  simp [figureOneFinalScheduledLocalProposalCap]

theorem figureOneFinalScheduledBalancedParameters_proposalCap_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 :=
  (figureOneFinalScheduledQueryBudget_pos q).trans_le
    (figureOneFinalScheduled_outerBudget_le_localProposalCap q sigma2)

noncomputable def figureOneFinalScheduledBalancedBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling
    (scheduledBalancedCoolingPrimitives figureOneFinalScheduledBalancedParameters)
    explicitVolumeCoolingSchedule q

/-- Exact expected-cost target for the actual final scheduled executable. -/
def FigureOneFinalScheduledBalancedExpectedQueryCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) : Prop :=
  ∫⁻ outcome, (outcome.2 : ENNReal)
      ∂((figureOneFinalScheduledBalancedBaseProgram q).run oracle.query) ≤
    ENNReal.ofReal (figureOneFinalScheduledExpectedCostConstant *
      volumeScheduledBaseComplexityRate q)

#print axioms figureOneFinalScheduledBalancedParameters_attempts_add_one

end ArlibCommunity.Algorithms.CV18
