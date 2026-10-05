/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.SequentialRecordedKernelPreservation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetReference

/-!
# One chronological CV18 reset step with local independence

This module records a reset phase into the public loss-preserving trace.  It
keeps the full old coordinate-vector law, installs the prescribed joint law
of the new score and retained endpoint, and transports the local Lemma 7.17(c)
independence estimate through the same maximal-coupling reset.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The pair-valued output kernel used by a chronological reset. -/
noncomputable def scheduledResetPairKernel
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    Measure (ℝ × Option (AmbientSpace q.n)) :=
  (scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase trace).map
      scheduledResetPairOutput

theorem scheduledResetPairKernel_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (scheduledResetPairKernel q I phase) ∧
      ∀ trace, IsProbabilityMeasure (scheduledResetPairKernel q I phase trace) := by
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  constructor
  · exact (Measure.measurable_map _ measurable_scheduledResetPairOutput).comp
      hobs.1
  · intro trace
    let _ : IsProbabilityMeasure
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase trace) :=
      hobs.2 trace
    exact Measure.isProbabilityMeasure_map
      measurable_scheduledResetPairOutput.aemeasurable

theorem scheduledResetPairKernel_ae_good
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    ∀ᵐ result ∂scheduledResetPairKernel q I phase trace,
      ScheduledResetPairGood result := by
  apply (ae_map_iff measurable_scheduledResetPairOutput.aemeasurable
    measurableSet_scheduledResetPairGood).2
  filter_upwards [scheduledBalancedTracePhaseObservationLaw_ae_total_nonnegative
    figureOneFinalScheduledBalancedParameters q I phase trace]
      with result hresult
  exact scheduledResetPairOutput_good result hresult

/-- Running the mapped pair kernel is the same as running the public phase
observation kernel and then mapping its returned result. -/
theorem sequentialPairLaw_scheduledResetPairKernel_eq_map
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (source : Measure (ScheduledBalancedCoolingTrace q.n)) :
    sequentialPairLaw source (scheduledResetPairKernel q I phase) =
      (sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
        (fun state => (state.1, scheduledResetPairOutput state.2)) := by
  let observation := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  have hpair : Measurable fun state : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
      (state.1, scheduledResetPairOutput state.2) :=
    measurable_fst.prodMk
      (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hlift : Measurable fun trace : ScheduledBalancedCoolingTrace q.n =>
      (observation trace).map fun result => (trace, result) :=
    measurable_sequentialPairKernel (rho := source) hobs.1 hobs.2
  unfold sequentialPairLaw
  rw [map_bind_eq_bind_map_of_measurable source hlift hpair]
  apply Measure.bind_congr_right
  filter_upwards with trace
  have hconst : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (trace, result) := measurable_const.prodMk measurable_id
  have hconstPair : Measurable fun result : ℝ × Option (AmbientSpace q.n) =>
      (trace, result) := measurable_const.prodMk measurable_id
  rw [show scheduledResetPairKernel q I phase trace =
    (observation trace).map scheduledResetPairOutput by rfl,
    Measure.map_map hconstPair measurable_scheduledResetPairOutput,
    Measure.map_map hpair hconst]
  rfl

theorem sequentialRecordedOutputLaw_scheduledResetPairKernel_eq_bind
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (source : Measure (ScheduledBalancedCoolingTrace q.n)) :
    sequentialRecordedOutputLaw source (scheduledResetPairKernel q I phase)
        (fun trace result => scheduledResetTraceAppend (trace, result)) =
      source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase) := by
  let observation := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  have hpair : Measurable fun state : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
      (state.1, scheduledResetPairOutput state.2) :=
    measurable_fst.prodMk
      (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hlift : Measurable fun trace : ScheduledBalancedCoolingTrace q.n =>
      (observation trace).map fun result => (trace, result) :=
    measurable_sequentialPairKernel (rho := source) hobs.1 hobs.2
  have hpairLift : Measurable fun trace : ScheduledBalancedCoolingTrace q.n =>
      (scheduledResetPairKernel q I phase trace).map
        fun result => (trace, result) :=
    measurable_sequentialPairKernel (rho := source)
      (scheduledResetPairKernel_measurable_and_probability q I phase).1
      (scheduledResetPairKernel_measurable_and_probability q I phase).2
  have hseq : sequentialPairLaw source (scheduledResetPairKernel q I phase) =
      (sequentialPairLaw source observation).map
        (fun state => (state.1, scheduledResetPairOutput state.2)) := by
    unfold sequentialPairLaw
    rw [map_bind_eq_bind_map_of_measurable source hlift hpair]
    apply Measure.bind_congr_right
    filter_upwards with trace
    have hconst : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
        (trace, result) := measurable_const.prodMk measurable_id
    have hconstPair : Measurable fun result : ℝ × Option (AmbientSpace q.n) =>
        (trace, result) := measurable_const.prodMk measurable_id
    rw [show scheduledResetPairKernel q I phase trace =
      (observation trace).map scheduledResetPairOutput by rfl,
      Measure.map_map hconstPair measurable_scheduledResetPairOutput,
      Measure.map_map hpair hconst]
    rfl
  unfold sequentialRecordedOutputLaw
  rw [hseq]
  change Measure.map scheduledResetTraceAppend
    (Measure.map (fun state =>
      (state.1, scheduledResetPairOutput state.2))
      (sequentialPairLaw source observation)) = _
  rw [Measure.map_map measurable_scheduledResetTraceAppend hpair]
  exact map_sequentialPairLaw_scheduledResetTraceAppend_eq_bind
    q I phase source

set_option maxHeartbeats 800000 in
/-- Structural chronological reset with the sharp local `eta + 3 delta`
independence perturbation. -/
theorem exists_scheduledTraceRecordedReset_with_approxIndep
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid phase trace)
    (hcoordinates : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceCoordinatesNonnegative phase trace)
    (retained : Measure (AmbientSpace q.n))
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      retained.map some)
    (target : Measure (ℝ × Option (AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    (htargetGood : ∀ᵐ result ∂target, ScheduledResetPairGood result)
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hnext : Arlib.TVLe
      ((sequentialPairLaw source
        (scheduledResetPairKernel q I phase)).map Prod.snd) target delta)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (holdMeasurable : Measurable oldStatistic)
    (holdAppend : ∀ trace result,
      ScheduledBalancedCoolingTraceValid phase trace → trace.2 = true →
      ScheduledResetPairGood result →
      oldStatistic (scheduledResetTraceAppend (trace, result)) =
        oldStatistic trace)
    {eta : ℝ}
    (hind : ApproxIndepFun eta
      (oldStatistic ∘ Prod.fst) Prod.snd
      (sequentialPairLaw source (scheduledResetPairKernel q I phase))) :
    ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (source.bind (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I phase))
        reference delta ∧
      reference.map (fun trace =>
        (scheduledBalancedTracePhaseVariable q (phase + 1) trace,
          scheduledBalancedTraceRetainedOption trace)) = target ∧
      reference.map (scheduledResetPrefixCoordinates q phase) =
        source.map (scheduledResetPrefixCoordinates q phase) ∧
      ApproxIndepFun (eta + 3 * delta.toReal) oldStatistic
        (scheduledBalancedTracePhaseVariable q (phase + 1)) reference ∧
      (∀ᵐ trace ∂reference,
        ScheduledBalancedCoolingTraceValid (phase + 1) trace ∧
        ScheduledBalancedCoolingTraceCoordinatesNonnegative (phase + 1) trace) := by
  let K := scheduledResetPairKernel q I phase
  let update := fun (trace : ScheduledBalancedCoolingTrace q.n)
      (result : ℝ × Option (AmbientSpace q.n)) =>
    scheduledResetTraceAppend (trace, result)
  let readNew := fun trace : ScheduledBalancedCoolingTrace q.n =>
    (scheduledBalancedTracePhaseVariable q (phase + 1) trace,
      scheduledBalancedTraceRetainedOption trace)
  let observe := fun result : ℝ × Option (AmbientSpace q.n) => result
  let OldGood := fun trace : ScheduledBalancedCoolingTrace q.n =>
    ScheduledBalancedCoolingTraceValid phase trace ∧ trace.2 = true ∧
      ScheduledBalancedCoolingTraceCoordinatesNonnegative phase trace
  let NewGood := ScheduledResetPairGood (n := q.n)
  let Good := fun trace : ScheduledBalancedCoolingTrace q.n =>
    ScheduledBalancedCoolingTraceValid (phase + 1) trace ∧
      ScheduledBalancedCoolingTraceCoordinatesNonnegative (phase + 1) trace
  have hK := scheduledResetPairKernel_measurable_and_probability q I phase
  have hlive := ae_trace_live_of_map_retainedOption_eq_map_some
    source retained hretained
  have hOld : ∀ᵐ trace ∂source, OldGood trace := by
    filter_upwards [hvalid, hlive, hcoordinates] with trace ht hl hc
    exact ⟨ht, hl, hc⟩
  have hNewRaw : ∀ᵐ result ∂((sequentialPairLaw source K).map Prod.snd),
      NewGood result := by
    rw [map_sequentialPairLaw_snd source K hK.1 hK.2]
    apply MeasureTheory.mem_ae_iff.mpr
    rw [Measure.bind_apply measurableSet_scheduledResetPairGood.compl
      hK.1.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with trace
    exact MeasureTheory.mem_ae_iff.mp (scheduledResetPairKernel_ae_good
      q I phase trace)
  have hreadMeas : Measurable readNew :=
    (measurable_scheduledBalancedTracePhaseVariable q (phase + 1)).prodMk
      measurable_scheduledBalancedTraceRetainedOption
  have hprefixMeas := measurable_scheduledResetPrefixCoordinates q phase
  have hOldMeas : MeasurableSet {trace | OldGood trace} := by
    rw [show {trace | OldGood trace} =
        {trace | ScheduledBalancedCoolingTraceValid phase trace} ∩
          scheduledBalancedTraceLiveSet q.n ∩
          {trace |
            ScheduledBalancedCoolingTraceCoordinatesNonnegative phase trace} by
      ext trace
      simp [OldGood, scheduledBalancedTraceLiveSet, and_assoc]]
    exact ((measurableSet_scheduledBalancedCoolingTraceValid phase).inter
      measurableSet_scheduledBalancedTraceLiveSet).inter
        (measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative
          phase)
  have hind' : ApproxIndepFun eta
      (oldStatistic ∘ Prod.fst) (observe ∘ Prod.snd)
      (sequentialPairLaw source K) := by
    have hobserve : observe ∘ Prod.snd =
        (Prod.snd : ScheduledBalancedCoolingTrace q.n ×
          (ℝ × Option (AmbientSpace q.n)) →
            ℝ × Option (AmbientSpace q.n)) := by
      funext state
      rfl
    rw [hobserve]
    simpa only [K] using hind
  obtain ⟨reference, hreferenceProb, hcomparison, hnew, holdPrefix,
      hindPair, hgood⟩ :=
    exists_sequentialRecordedOutputReset_of_tvLe_with_approxIndep_ae
      source K target update observe readNew
      (scheduledResetPrefixCoordinates q phase) oldStatistic
      OldGood NewGood Good hK.1 hK.2
      measurable_scheduledResetTraceAppend measurable_id hreadMeas
      hprefixMeas holdMeasurable
      hOldMeas
      measurableSet_scheduledResetPairGood
      ((measurableSet_scheduledBalancedCoolingTraceValid (phase + 1)).inter
        (measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative
          (phase + 1)))
      hOld hNewRaw htargetGood
      (fun trace result ht hr => by
        apply Prod.ext
        · exact scheduledBalancedTracePhaseVariable_resetAppend_eq_fst_of_good
            q phase hphase trace ht.1 ht.2.1 result hr
        · exact scheduledBalancedTraceRetainedOption_resetAppend
            trace ht.2.1 result)
      (fun trace result ht _ =>
        scheduledResetPrefixCoordinates_resetAppend_eq q phase hphase
          trace ht.1 result)
      (fun trace result ht hr => holdAppend trace result ht.1 ht.2.1 hr)
      (fun trace result ht hr =>
        ⟨ht.1.append (scheduledResetPairToResult result),
          ht.2.2.append (scheduledResetPairToResult_nonnegative result hr)⟩)
      hdelta hnext hind'
  have hcomparison' : MeasureLeUpTo
      (source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase))
      reference delta := by
    rw [← sequentialRecordedOutputLaw_scheduledResetPairKernel_eq_bind
      q I phase source]
    exact hcomparison
  have hindScore : ApproxIndepFun (eta + 3 * delta.toReal)
      oldStatistic (scheduledBalancedTracePhaseVariable q (phase + 1))
      reference := by
    exact hindPair.comp measurable_id measurable_fst
  exact ⟨reference, hreferenceProb, hcomparison', by simpa [readNew, observe] using hnew,
    holdPrefix, hindScore, hgood⟩

#print axioms sequentialRecordedOutputLaw_scheduledResetPairKernel_eq_bind
#print axioms sequentialPairLaw_scheduledResetPairKernel_eq_map
#print axioms exists_scheduledTraceRecordedReset_with_approxIndep

end

end ArlibCommunity.Algorithms.CV18
