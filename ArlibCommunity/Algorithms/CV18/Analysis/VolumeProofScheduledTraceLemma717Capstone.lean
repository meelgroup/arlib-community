/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceMomentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad

/-!
# Concrete Lemma 7.17(c) accuracy capstones

This module connects the paper-faithful good/bad coupling proof of Lemma
7.17(c) to the finite actual-moment assembly.  Approximate independence is
therefore no longer an external premise of the aborting scheduled accuracy
theorem.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Accuracy of the actual aborting scheduled estimator after discharging
CV18 Lemma 7.17(c) by the retained-state good/bad coupling. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  exact
    figureOneFinalScheduledAbortBase_failure_le_of_trace_quantitative_moments
      q I oracle hrounded hsecond (figureOneScheduledTrace_lemma717c q I)
        hrawApprox

/-- Paired-sample form after the concrete Lemma 7.17(c) coupling has been
discharged.  These are the two remaining quantitative phase obligations. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_centered_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hcenter : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace,
          (scheduledBalancedTracePhaseVariable q j trace -
            scheduledFigureOneTraceRawMean q I j) ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (figureOneChronologicalMomentFactor q j - 1) *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  exact
    figureOneFinalScheduledAbortBase_failure_le_of_centered_phase_moments
      q I oracle hrounded hcenter (figureOneScheduledTrace_lemma717c q I)
        hrawApprox

#print axioms figureOneFinalScheduledAbortBase_failure_le_of_trace_moments
#print axioms figureOneFinalScheduledAbortBase_failure_le_of_centered_moments

end ArlibCommunity.Algorithms.CV18
