/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRateCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledWorkComparison

/-! # Final global-cap parameters for the scheduled executable

The proposal cap is derived from the same scheduled soft-O rate used by the
expected-cost theorem.  In particular, it is not the obsolete cap derived
from `baseRate`.
-/

namespace ArlibCommunity.Algorithms.CV18

theorem runCostConstant_pos :
    0 < runCostConstant := by
  norm_num [runCostConstant]

theorem queryBudget_pos (q : VolumeParams) :
    0 < queryBudget q := by
  unfold queryBudget budgetOfRate
  apply Nat.ceil_pos.mpr
  positivity [runCostConstant_pos,
    runRate_pos q]

@[simp] theorem figureOneFinalScheduledBalancedParameters_proposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 =
      maxProposals q sigma2 := rfl

@[simp] theorem figureOneFinalScheduledBalancedParameters_properStride
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.properStride q sigma2 =
      strideFor q sigma2
        (maxRetries q - 1) := rfl

@[simp] theorem figureOneFinalScheduledBalancedParameters_retryLimit
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.retryLimit q sigma2 =
      maxRetries q := rfl

theorem figureOneFinalScheduledBalancedParameters_attempts_add_one
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledBalancedParameters.retryLimit q sigma2 - 1 + 1 =
      maxRetries q := by
  simp only [figureOneFinalScheduledBalancedParameters_retryLimit]
  exact Nat.sub_add_cancel (maxRetries_pos q)

theorem figureOneFinalScheduled_outerBudget_le_localProposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    queryBudget q ≤
      figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 := by
  simp [maxProposals]

theorem figureOneFinalScheduledBalancedParameters_proposalCap_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 :=
  (queryBudget_pos q).trans_le
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
    ENNReal.ofReal (runCostConstant *
      runRate q)

#print axioms figureOneFinalScheduledBalancedParameters_attempts_add_one

end ArlibCommunity.Algorithms.CV18
