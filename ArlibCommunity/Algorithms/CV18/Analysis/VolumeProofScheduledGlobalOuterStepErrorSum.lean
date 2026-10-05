/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLocalResetDependenceBudget

/-!
# Exact sum of chronological outer-step errors

This module names the Gaussian and terminal law-comparison errors used by the
finite chronological reset recurrence.  Their finite sum, together with the
initial accepted-target correction, is definitionally the global outer-step
error consumed by the final witness constructor.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Law-comparison error charged by Gaussian chronological phase `phase`:
one operational transition, the empirical-average reset, and the accepted
endpoint correction needed by the following phase. -/
noncomputable def figureOneScheduledGaussianOuterStepError
    (q : VolumeParams) (phase : ℕ) : ENNReal :=
  (figureOneCorrectedTransitionBudget q +
      scheduledResetReferenceError q
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) +
    scheduledBalancedStationaryTargetError q

/-- Law-comparison error charged by the terminal chronological phase.  There
is no accepted-endpoint correction after the terminal coordinate. -/
noncomputable def figureOneScheduledTerminalOuterStepError
    (q : VolumeParams) : ENNReal :=
  figureOneCorrectedTransitionBudget q +
    scheduledResetReferenceError q (figureOneSampleCount q - 1)

/-- The initial accepted-target correction, all Gaussian phase errors, and
the terminal phase error are exactly the global chronological comparison
error. -/
theorem figureOneScheduledOuterStepError_sum_eq_global
    (q : VolumeParams) :
    scheduledBalancedStationaryTargetError q +
        (∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOneScheduledGaussianOuterStepError q phase) +
      figureOneScheduledTerminalOuterStepError q =
        figureOneScheduledGlobalOuterStepError q := by
  rfl

/-- Symmetric orientation of `figureOneScheduledOuterStepError_sum_eq_global`,
convenient when rewriting the final accumulated recurrence error. -/
theorem figureOneScheduledGlobalOuterStepError_eq_sum
    (q : VolumeParams) :
    figureOneScheduledGlobalOuterStepError q =
      scheduledBalancedStationaryTargetError q +
          (∑ phase ∈ Finset.range (terminalPhaseSteps q),
            figureOneScheduledGaussianOuterStepError q phase) +
        figureOneScheduledTerminalOuterStepError q :=
  (figureOneScheduledOuterStepError_sum_eq_global q).symm

#print axioms figureOneScheduledOuterStepError_sum_eq_global

end

end ArlibCommunity.Algorithms.CV18
