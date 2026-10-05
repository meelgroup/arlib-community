/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction

/-! # Terminal uniform phase of the retained-state induction -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open _root_.Arlib _root_.Arlib.MarkovChains

set_option maxHeartbeats 1000000 in
section

/-- The terminal uniform-ratio trace phase has the same retained endpoint as
the complete scheduled collector, with the uniform ratio used only in the
discarded observation coordinate. -/
theorem map_scheduledBalancedTerminalTracePhaseKernel_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    (scheduledBalancedTracePhaseKernel
      figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q) trace).map
          scheduledBalancedTraceRetainedOption =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (terminalVariance q) (uniformRatioWeight (terminalVariance q))
        (figureOneSampleCount q - 1)
        (scheduledBalancedTraceRetainedOption trace) := by
  have hcount : 0 < figureOneSampleCount q := figureOneSampleCount_pos q
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      change ((Measure.dirac none).map
          (scheduledBalancedCoolingTraceAppend (history, false))).map
            scheduledBalancedTraceRetainedOption = Measure.dirac none
      have happ : Measurable
          (scheduledBalancedCoolingTraceAppend (history, false)) :=
        (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_map measurable_scheduledBalancedTraceRetainedOption happ,
        Measure.map_dirac'
          (measurable_scheduledBalancedTraceRetainedOption.comp happ)]
      rfl
  | true =>
      let append := scheduledBalancedCoolingTraceAppend (history, true)
      have happend : Measurable append :=
        (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      let avg := balancedCoolingAverage (n := q.n) (figureOneSampleCount q)
      have havg : Measurable avg :=
        measurable_balancedCoolingAverage (figureOneSampleCount q)
      let collect := scheduledBalancedTransitionCollectLaw q I
        (terminalVariance q) (uniformRatioWeight (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q))
        (figureOneSampleCount q) 0
        (accuracyScaleFactor q • history.2.2.2)
      unfold scheduledBalancedTracePhaseKernel
        scheduledBalancedTracePhaseObservationLaw
      simp only [if_true, lt_self_iff_false, if_false]
      unfold scheduledBalancedCoolingUniformTransitionLaw
        figureOneFinalScheduledCompleteRetainedKernel
      simp only [scheduledBalancedTraceRetainedOption, if_true]
      rw [Nat.sub_add_cancel hcount]
      change ((collect.map avg).map append).map
          scheduledBalancedTraceRetainedOption = collect.map optionSnd
      rw [Measure.map_map measurable_scheduledBalancedTraceRetainedOption happend,
        Measure.map_map
          (measurable_scheduledBalancedTraceRetainedOption.comp happend) havg]
      apply Measure.map_congr
      filter_upwards with result
      simpa [append, avg, scheduledBalancedTraceRetainedOption_append,
        optionSnd_balancedCoolingAverage]

theorem map_bind_scheduledBalancedTerminalTracePhaseKernel_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n)
    (law : Measure (ScheduledBalancedCoolingTrace q.n)) :
    (law.bind (scheduledBalancedTracePhaseKernel
      figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q))).map scheduledBalancedTraceRetainedOption =
      (law.map scheduledBalancedTraceRetainedOption).bind
        (figureOneFinalScheduledCompleteRetainedKernel q I
          (terminalVariance q) (uniformRatioWeight (terminalVariance q))
          (figureOneSampleCount q - 1)) := by
  let traceK := scheduledBalancedTracePhaseKernel
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  let retainedK := figureOneFinalScheduledCompleteRetainedKernel q I
    (terminalVariance q) (uniformRatioWeight (terminalVariance q))
    (figureOneSampleCount q - 1)
  have htraceK := scheduledBalancedTracePhaseKernel_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  have hretainedK :=
    figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
      q I (terminalVariance_pos' q)
      (weight := uniformRatioWeight (terminalVariance q))
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneSampleCount q - 1)
  calc
    (law.bind traceK).map scheduledBalancedTraceRetainedOption =
        law.bind fun trace =>
          (traceK trace).map scheduledBalancedTraceRetainedOption :=
      map_bind_eq_bind_map_of_measurable law htraceK.1
        measurable_scheduledBalancedTraceRetainedOption
    _ = law.bind (retainedK ∘ scheduledBalancedTraceRetainedOption) := by
      apply Measure.bind_congr_right
      filter_upwards with trace
      exact map_scheduledBalancedTerminalTracePhaseKernel_retainedOption q I trace
    _ = (law.map scheduledBalancedTraceRetainedOption).bind retainedK :=
      (map_bind_eq_bind_comp_state law
        measurable_scheduledBalancedTraceRetainedOption hretainedK.1).symm

noncomputable def figureOneScheduledFullRetainedError
    (q : VolumeParams) : ENNReal :=
  figureOneScheduledRetainedError q (terminalPhaseSteps q) +
    figureOneSampleCount q • figureOneCorrectedTransitionBudget q

/-- The retained state after all Gaussian phases and the final uniform phase
is dominated by the terminal accepted target with the complete exact-chance
loss budget. -/
theorem scheduledBalancedFullForwardTraceLaw_retained_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
            scheduledBalancedTraceRetainedOption)
      ((figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q)).map some)
      (figureOneScheduledFullRetainedError q) := by
  let phases := terminalPhaseSteps q
  have hphases : 0 < phases := terminalPhaseSteps_pos q
  let prev := phases - 1
  have hprev : prev < phases := Nat.sub_lt hphases (by omega)
  have hprevSucc : prev + 1 = phases := Nat.sub_add_cancel hphases
  have hstart := scheduledBalancedForwardTraceLaw_retained_leUpTo_target
    q I prev hprev
  let target := figureOneScheduledAcceptedTargetAt q I prev
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I prev
  have hwarm : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (target.map fun x => accuracyScaleFactor q • x)
      (figureOneScheduledSpeedyPiAt q I phases) := by
    simpa [target, phases, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, hprevSucc] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I prev
  have hstep :=
    bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
      q I (terminalVariance_pos' q)
      (weight := uniformRatioWeight (terminalVariance q))
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneSampleCount q - 1)
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phases).map
          scheduledBalancedTraceRetainedOption)
      target (by simpa [phases, hprevSucc] using hstart)
      (by
        dsimp only [phases] at hwarm
        rw [figureOneScheduledSpeedyPiAt,
          scheduleValue_terminalPhaseSteps] at hwarm
        exact hwarm)
  have hcount : 0 < figureOneSampleCount q := figureOneSampleCount_pos q
  rw [Nat.sub_add_cancel hcount] at hstep
  rw [show figureOneDependentPhaseCount q = phases + 1 by
    simp [figureOneDependentPhaseCount, phases]]
  rw [show scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phases + 1) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phases).bind
          (scheduledBalancedTracePhaseKernel
            figureOneFinalScheduledBalancedParameters q I phases) by rfl]
  rw [map_bind_scheduledBalancedTerminalTracePhaseKernel_retainedOption]
  simpa [figureOneDependentPhaseCount, phases, target,
    figureOneScheduledAcceptedTargetAt, figureOneScheduledSpeedyPiAt,
    figureOneScheduledFullRetainedError, scheduleValue_terminalPhaseSteps]
    using hstep

theorem exists_figureOneScheduledFullTraceLiveRetained_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)
    let good := figureOneScheduledAcceptedTargetAt q I
      (terminalPhaseSteps q)
    ∃ bad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceLiveStateLaw law id ≤ good + bad ∧
      bad Set.univ ≤ figureOneScheduledFullRetainedError q := by
  dsimp only
  exact exists_scheduledBalancedTraceLiveStateLaw_good_bad_of_leUpTo
    _ _ (scheduledBalancedFullForwardTraceLaw_retained_leUpTo_target q I)

#print axioms map_scheduledBalancedTerminalTracePhaseKernel_retainedOption
#print axioms scheduledBalancedFullForwardTraceLaw_retained_leUpTo_target
#print axioms exists_figureOneScheduledFullTraceLiveRetained_good_bad

end

end ArlibCommunity.Algorithms.CV18
