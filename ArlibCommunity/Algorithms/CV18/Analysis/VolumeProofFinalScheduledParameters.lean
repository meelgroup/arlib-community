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

/-- A deliberately slack absolute constant for the complete scheduled base
run.  Its slack absorbs endpoint and rejection queries and the finite retry
multiplier without altering the CV18 soft-O rate. -/
noncomputable def figureOneFinalScheduledExpectedCostConstant : ℝ := 10 ^ 30

theorem figureOneFinalScheduledExpectedCostConstant_pos :
    0 < figureOneFinalScheduledExpectedCostConstant := by
  norm_num [figureOneFinalScheduledExpectedCostConstant]

noncomputable def figureOneFinalScheduledQueryBudget (q : VolumeParams) : ℕ :=
  globalQueryBudgetOfRate figureOneFinalScheduledExpectedCostConstant
    volumeScheduledBaseComplexityRate q

theorem figureOneFinalScheduledQueryBudget_pos (q : VolumeParams) :
    0 < figureOneFinalScheduledQueryBudget q := by
  unfold figureOneFinalScheduledQueryBudget globalQueryBudgetOfRate
  apply Nat.ceil_pos.mpr
  positivity [figureOneFinalScheduledExpectedCostConstant_pos,
    volumeScheduledBaseComplexityRate_pos q]

/-- The real-valued local block cap required by the cap-loss estimate.  The
factor `16 * speedyAdjacentWarmConstant` is the larger of the first-block and
retry-block warmness constants. -/
noncomputable def figureOneFinalScheduledLocalCapRequirement
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  2 * (figureOneScheduledCorrectedProperStride q sigma2
      (figureOneSafeRetryCount q - 1) : ℝ) *
      (16 * speedyAdjacentWarmConstant q) /
    figureOneCorrectedBlockMixingError q (figureOneSafeRetryCount q - 1)

/-- The local collector cap contains the outer cutoff budget as a prefix and
then adds enough slack to make cap exhaustion cost one corrected block budget.
The outer query cutoff remains a separate global guard. -/
noncomputable def figureOneFinalScheduledLocalProposalCap
    (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  figureOneFinalScheduledQueryBudget q +
    Nat.ceil (figureOneFinalScheduledLocalCapRequirement q sigma2)

/-- The parameters shared by the final cost, mapped-law, and prefix arguments.
Only the global proposal cap differs from the earlier scheduled prototype. -/
noncomputable def figureOneFinalScheduledBalancedParameters :
    BalancedCoolingParameters where
  proposalCap := figureOneFinalScheduledLocalProposalCap
  properStride := fun q sigma2 =>
    figureOneScheduledCorrectedProperStride q sigma2
      (figureOneSafeRetryCount q - 1)
  retryLimit := fun q _ => figureOneSafeRetryCount q

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
