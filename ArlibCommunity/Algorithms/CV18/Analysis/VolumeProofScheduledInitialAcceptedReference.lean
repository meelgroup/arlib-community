/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction

/-!
# Accepted-target reference for the initial scheduled trace

The executable trace starts from the exact truncated Gaussian.  The outer
chronological reset recurrence instead needs a live trace whose retained
marginal is the normalized accepted target.  Mapping the existing
accepted-target TV comparison through `scheduledBalancedInitialTrace` gives
that reference at exactly the stationary-target error.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib

noncomputable section

/-- Initial live trace sampled from the normalized accepted target at the
initial variance. -/
noncomputable def scheduledBalancedInitialAcceptedTraceReference
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (ScheduledBalancedCoolingTrace q.n) :=
  (figureOneScheduledAcceptedTargetAt q I 0).map
    scheduledBalancedInitialTrace

theorem scheduledBalancedInitialAcceptedTraceReference_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) :
    IsProbabilityMeasure
      (scheduledBalancedInitialAcceptedTraceReference q I) := by
  let _ : IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I 0) :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
  unfold scheduledBalancedInitialAcceptedTraceReference
  exact Measure.isProbabilityMeasure_map
    measurable_scheduledBalancedInitialTrace.aemeasurable

/-- The executable exact-Gaussian initial trace is dominated by the accepted
initial reference at precisely the stationary-target error. -/
theorem scheduledBalancedForwardTraceLaw_zero_leUpTo_initialAcceptedReference
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I 0)
      (scheduledBalancedInitialAcceptedTraceReference q I)
      (scheduledBalancedStationaryTargetError q) := by
  let _ : IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I 0) :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
  let _ : IsProbabilityMeasure
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I
        (initialVariance q)
        (Arlib.MarkovChains.ellGaussianProb
          (figureOneScheduledPhaseBody q I (initialVariance q))
          (figureOneScheduledProposalRadius q (initialVariance q))
          (initialVariance q))) := by
    simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, scheduleValue] using
      (figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0)
  have htv := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I (initialVariance_pos q)
  have hmlu := MeasureLeUpTo.of_tvLe htv.symm
  have hmapped := hmlu.map
    (measurable_scheduledBalancedInitialTrace (n := q.n))
  simpa [scheduledBalancedForwardTraceLaw, iteratedKernelLaw,
    scheduledBalancedInitialAcceptedTraceReference,
    figureOneScheduledAcceptedTargetAt, figureOneScheduledSpeedyPiAt,
    scheduleValue] using hmapped

/-- The retained optional state of the accepted initial trace is exactly the
accepted target supported on `some`. -/
theorem map_scheduledBalancedInitialAcceptedTraceReference_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n) :
    (scheduledBalancedInitialAcceptedTraceReference q I).map
        scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I 0).map some := by
  unfold scheduledBalancedInitialAcceptedTraceReference
  rw [Measure.map_map measurable_scheduledBalancedTraceRetainedOption
    measurable_scheduledBalancedInitialTrace]
  apply Measure.map_congr
  filter_upwards with point
  rfl

/-- Every accepted initial reference trace is a valid length-zero trace. -/
theorem scheduledBalancedInitialAcceptedTraceReference_ae_valid
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ trace ∂scheduledBalancedInitialAcceptedTraceReference q I,
      ScheduledBalancedCoolingTraceValid 0 trace := by
  unfold scheduledBalancedInitialAcceptedTraceReference
  apply (ae_map_iff measurable_scheduledBalancedInitialTrace.aemeasurable
    (measurableSet_scheduledBalancedCoolingTraceValid 0)).2
  filter_upwards with point
  simp [scheduledBalancedInitialTrace, ScheduledBalancedCoolingTraceValid]

/-- The empty initial coordinate sequence is nonnegative. -/
theorem scheduledBalancedInitialAcceptedTraceReference_ae_coordinatesNonnegative
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ trace ∂scheduledBalancedInitialAcceptedTraceReference q I,
      ScheduledBalancedCoolingTraceCoordinatesNonnegative 0 trace := by
  unfold scheduledBalancedInitialAcceptedTraceReference
  apply (ae_map_iff measurable_scheduledBalancedInitialTrace.aemeasurable
    (measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative 0)).2
  filter_upwards with point
  simp [ScheduledBalancedCoolingTraceCoordinatesNonnegative,
    scheduledBalancedInitialTrace,
    BalancedCoolingHistoryHasNonnegativeCoordinates]

#print axioms
  scheduledBalancedForwardTraceLaw_zero_leUpTo_initialAcceptedReference
#print axioms
  map_scheduledBalancedInitialAcceptedTraceReference_retainedOption
#print axioms scheduledBalancedInitialAcceptedTraceReference_ae_valid
#print axioms
  scheduledBalancedInitialAcceptedTraceReference_ae_coordinatesNonnegative

end

end ArlibCommunity.Algorithms.CV18
