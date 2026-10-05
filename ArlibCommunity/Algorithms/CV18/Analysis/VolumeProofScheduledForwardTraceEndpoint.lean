/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLossPreservingTrace

/-!
# Endpoint identities for the scheduled forward trace

The global reset construction first compares the finite Gaussian iteration
and then appends the terminal phase by `Measure.bind`.  This module records
that this is exactly the public loss-preserving forward trace at the complete
dependent-phase horizon.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The public scheduled trace at a successor horizon is its prefix trace
followed by the phase kernel at the prefix length. -/
theorem scheduledBalancedForwardTraceLaw_bind_next
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    (scheduledBalancedForwardTraceLaw parameters q I phases).bind
        (scheduledBalancedTracePhaseKernel parameters q I phases) =
      scheduledBalancedForwardTraceLaw parameters q I (phases + 1) := by
  rfl

/-- The Gaussian prefix followed by the terminal phase kernel is exactly the
complete forward trace law used by the final CV18 witness. -/
theorem scheduledBalancedForwardTraceLaw_gaussian_bind_terminal
    (q : VolumeParams) (I : VolumeInput q.n) :
    (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q)).bind
      (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q)) =
      scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q) := by
  rw [scheduledBalancedForwardTraceLaw_bind_next]
  rfl

/-- Expanded `iteratedKernelLaw` form of
`scheduledBalancedForwardTraceLaw_gaussian_bind_terminal`.  This is the
rewrite required after applying the finite-reference recurrence theorem to
the Gaussian prefix. -/
theorem iteratedKernelLaw_scheduledGaussian_bind_terminal_eq_forwardTraceLaw
    (q : VolumeParams) (I : VolumeInput q.n) :
    (iteratedKernelLaw
        (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I)
        ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
            scheduledBalancedInitialTrace)
        (terminalPhaseSteps q)).bind
      (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q)) =
      scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q) := by
  simpa only [scheduledBalancedForwardTraceLaw] using
    scheduledBalancedForwardTraceLaw_gaussian_bind_terminal q I

#print axioms scheduledBalancedForwardTraceLaw_bind_next
#print axioms scheduledBalancedForwardTraceLaw_gaussian_bind_terminal
#print axioms
  iteratedKernelLaw_scheduledGaussian_bind_terminal_eq_forwardTraceLaw

end

end ArlibCommunity.Algorithms.CV18
