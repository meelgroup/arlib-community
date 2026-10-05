/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalOuterStepErrorSum
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceConstruction

/-!
# Terminal extension of the global reset invariant

This module exposes the terminal trace reset in the exact form consumed by
the finite Gaussian recurrence.  The implementation in
`VolumeProofScheduledGlobalResetReferenceConstruction` applies the terminal
recorded reset, transports every prior chronological independence fact, and
uses the local dependence budget for the newly created terminal coordinate.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Extend a completed Gaussian-prefix invariant by its terminal coordinate.
The comparison charge is exposed through the named terminal outer-step error
used in the exact global error sum. -/
theorem exists_scheduledTerminalInvariantExtension
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hsource : ScheduledGlobalGaussianPrefixInvariant q I
      (terminalPhaseSteps q) source) :
    ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (source.bind (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)))
        reference (figureOneScheduledTerminalOuterStepError q) ∧
      ScheduledGlobalResetPrefixInvariant q I
        (figureOneDependentPhaseCount q) reference := by
  obtain ⟨reference, hreference, hcomparison, hinvariant⟩ :=
    exists_scheduledTerminalReference_of_gaussianPrefixInvariant
      q I source hsource
  refine ⟨reference, hreference, ?_, hinvariant⟩
  simpa only [figureOneScheduledTerminalOuterStepError] using hcomparison

#print axioms exists_scheduledTerminalInvariantExtension

end

end ArlibCommunity.Algorithms.CV18
