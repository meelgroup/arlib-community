/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetReference
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetStep
import ArlibCommunity.Algorithms.CV18.Analysis.Background.SequentialRecordedKernelPreservation
import ArlibCommunity.Algorithms.CV18.Analysis.Background.RecordedKernelResetIndependence

/-!
# Terminal specialization of the chronological trace reset

This module applies the generic public-trace reset to the final uniform-ratio
collector.  It records the terminal score with its exact equation-(6)
moments, preserves every Gaussian coordinate, and transports any local
old-history/new-terminal-score independence estimate across the reset.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- A nonnegative score paired with an almost-surely present endpoint has
the support invariant required by the chronological reset. -/
theorem ae_scheduledResetPairGood_of_map_snd_eq_map_some
    {n : ℕ} (target : Measure (ℝ × Option (AmbientSpace n)))
    (retained : Measure (AmbientSpace n))
    (htargetRetained : target.map Prod.snd = retained.map some)
    (htargetNonnegative : ∀ᵐ result ∂target, 0 ≤ result.1) :
    ∀ᵐ result ∂target, ScheduledResetPairGood result := by
  have hpointTarget : ∀ᵐ result ∂target, result.2 ≠ none := by
    have hsome : ∀ᵐ value ∂retained.map some, value ≠ none :=
      (ae_map_iff measurable_some.aemeasurable
        measurableSet_option_none.compl).2 <|
        ae_of_all _ fun point => by simp
    rw [← htargetRetained] at hsome
    exact (ae_map_iff measurable_snd.aemeasurable
      measurableSet_option_none.compl).1 hsome
  filter_upwards [htargetNonnegative, hpointTarget]
    with result hscore hpoint
  constructor
  · exact hscore
  · rw [liveRaw_scheduledResetPairToResult]
    simp [hpoint, max_eq_right hscore]

/-- The raw terminal independence theorem descends through the public trace
append map.  The only statistic-specific premise is the expected one: the
old statistic is unchanged almost surely by appending the terminal result. -/
theorem approxIndepFun_oldStatistic_terminal_traceAppend_of_accepted
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid (terminalPhaseSteps q) trace)
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (holdMeas : Measurable oldStatistic)
    (holdAppend : ∀ᵐ state ∂sequentialPairLaw source
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q)),
      oldStatistic (scheduledResetTraceAppend
        (state.1, scheduledResetPairOutput state.2)) =
          oldStatistic state.1) :
    ApproxIndepFun
      (2 * figureOneCorrectedTransitionBudget q).toReal
      oldStatistic
      (scheduledBalancedTracePhaseVariable q
        (terminalPhaseSteps q + 1))
      (source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q))) := by
  let phase := terminalPhaseSteps q
  let K := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let raw := sequentialPairLaw source K
  let append : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) →
        ScheduledBalancedCoolingTrace q.n := fun state =>
    scheduledResetTraceAppend (state.1, scheduledResetPairOutput state.2)
  have hphase : phase < figureOneDependentPhaseCount q := by
    dsimp only [phase]
    rw [figureOneDependentPhaseCount]
    omega
  have hK :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  have hrawFst : raw.map Prod.fst = source :=
    map_sequentialPairLaw_fst source K hK.1 hK.2
  have hvalidRaw : ∀ᵐ state ∂raw,
      ScheduledBalancedCoolingTraceValid phase state.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_scheduledBalancedCoolingTraceValid phase)).1
    rw [hrawFst]
    simpa only [phase] using hvalid
  have hliveSource : ∀ᵐ trace ∂source, trace.2 = true :=
    ae_trace_live_of_map_retainedOption_eq_map_some source
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)) hretained
  have hliveRaw : ∀ᵐ state ∂raw, state.1.2 = true := by
    apply (ae_map_iff measurable_fst.aemeasurable
      measurableSet_scheduledBalancedTraceLiveSet).1
    rw [hrawFst]
    simpa [scheduledBalancedTraceLiveSet] using hliveSource
  let bad : Set (Option (ℝ × AmbientSpace q.n)) :=
    {result | ¬ ScheduledCollectedTotalNonnegative result}
  have hbadMeas : MeasurableSet bad := by
    dsimp only [bad]
    change MeasurableSet
      ({result | ScheduledCollectedTotalNonnegative result}ᶜ)
    exact measurableSet_scheduledCollectedTotalNonnegative.compl
  have htotalBind : ∀ᵐ result ∂source.bind K,
      ScheduledCollectedTotalNonnegative result := by
    apply ae_iff.mpr
    change (source.bind K) bad = 0
    rw [Measure.bind_apply hbadMeas hK.1.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with trace
    exact ae_iff.mp <|
      scheduledBalancedTracePhaseObservationLaw_ae_total_nonnegative
        figureOneFinalScheduledBalancedParameters q I phase trace
  have htotalRaw : ∀ᵐ state ∂raw,
      ScheduledCollectedTotalNonnegative state.2 := by
    apply (ae_map_iff measurable_snd.aemeasurable
      measurableSet_scheduledCollectedTotalNonnegative).1
    rw [map_sequentialPairLaw_snd source K hK.1 hK.2]
    exact htotalBind
  have hnewAppend : ∀ᵐ state ∂raw,
      scheduledBalancedTracePhaseVariable q (phase + 1) (append state) =
        figureOneScheduledTraceLiveRawOutput state.2 := by
    filter_upwards [hvalidRaw, hliveRaw, htotalRaw]
      with state hstateValid hstateLive htotal
    dsimp only [append]
    unfold scheduledResetTraceAppend
    rw [scheduledResetPairToResult_pairOutput_eq state.2 htotal]
    rw [scheduledBalancedTracePhaseVariable_append_eq_rawOutput
      q phase hphase state.1 hstateValid]
    simp only [hstateLive, if_true]
  have hrawInd :=
    approxIndepFun_oldStatistic_terminal_liveRaw_of_accepted
      q I source hretained oldStatistic holdMeas
  have happend : Measurable append := by
    dsimp only [append]
    exact measurable_scheduledResetTraceAppend.comp <|
      measurable_fst.prodMk
        (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hjoint : raw.map (fun state =>
      (oldStatistic state.1,
        figureOneScheduledTraceLiveRawOutput state.2)) =
    raw.map (fun state =>
      (oldStatistic (append state),
        scheduledBalancedTracePhaseVariable q (phase + 1)
          (append state))) := by
    apply Measure.map_congr
    filter_upwards [show ∀ᵐ state ∂raw,
        oldStatistic (append state) = oldStatistic state.1 by
          simpa only [raw, K, append, phase] using holdAppend,
      hnewAppend] with state hold hnew
    exact Prod.ext hold.symm hnew.symm
  have hindComposed : ApproxIndepFun
      (2 * figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ append)
      ((scheduledBalancedTracePhaseVariable q (phase + 1)) ∘ append) raw := by
    apply ApproxIndepFun.of_map_pair_eq
      (holdMeas.comp measurable_fst)
      (measurable_figureOneScheduledTraceLiveRawOutput.comp measurable_snd)
      (holdMeas.comp happend)
      ((measurable_scheduledBalancedTracePhaseVariable q (phase + 1)).comp
        happend)
      hjoint
    simpa only [raw, K, phase, two_mul] using hrawInd
  have hmapped := hindComposed.map append happend oldStatistic
    (scheduledBalancedTracePhaseVariable q (phase + 1)) holdMeas
      (measurable_scheduledBalancedTracePhaseVariable q (phase + 1))
  rw [show raw.map append = source.bind
      (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase) by
    simpa only [raw, K, append] using
      map_sequentialPairLaw_scheduledResetTraceAppend_eq_bind
        q I phase source] at hmapped
  simpa only [phase] using hmapped

/-- The terminal history/output independence estimate in the pair-valued
kernel representation consumed by the prefix-preserving reset theorem. -/
theorem approxIndepFun_oldStatistic_terminal_resetPair_of_accepted
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (holdMeas : Measurable oldStatistic) :
    ApproxIndepFun
      (2 * figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ Prod.fst) Prod.snd
      (sequentialPairLaw source
        (scheduledResetPairKernel q I (terminalPhaseSteps q))) := by
  let previous := terminalPhaseSteps q - 1
  have hsucc : previous + 1 = terminalPhaseSteps q := by
    dsimp only [previous]
    exact Nat.sub_add_cancel (terminalPhaseSteps_pos q)
  let accepted := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure accepted :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  have hwarm := map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
    q I previous
  rw [hsucc] at hwarm
  have hraw := approxIndepFun_terminal_phase_of_accepted_retained
    q I source accepted (by simpa only [accepted, previous] using hretained)
      hwarm
  have hpost := hraw.comp holdMeas
    (measurable_scheduledResetPairOutput (n := q.n))
  let pairMap : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) →
        ScheduledBalancedCoolingTrace q.n ×
          (ℝ × Option (AmbientSpace q.n)) := fun state =>
    (state.1, scheduledResetPairOutput state.2)
  have hpairMap : Measurable pairMap :=
    measurable_fst.prodMk
      (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hmapped := hpost.map pairMap hpairMap
    (oldStatistic ∘ Prod.fst) Prod.snd
    (holdMeas.comp measurable_fst) measurable_snd
  rw [← sequentialPairLaw_scheduledResetPairKernel_eq_map
    q I (terminalPhaseSteps q) source] at hmapped
  simpa only [pairMap, Function.comp_apply, two_mul] using hmapped

/-- The complete terminal chronological reset step.  Its law-comparison
charge is precisely one transition budget plus the terminal fixed-reset
budget. -/
theorem exists_scheduledTerminalTraceRecordedReset
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid (terminalPhaseSteps q) trace)
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (holdMeas : Measurable oldStatistic)
    (holdAppend : ∀ᵐ state ∂sequentialPairLaw source
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q)),
      oldStatistic (scheduledResetTraceAppend
        (state.1, scheduledResetPairOutput state.2)) =
          oldStatistic state.1) :
    ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (source.bind (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)))
        reference
        (figureOneCorrectedTransitionBudget q +
          scheduledResetReferenceError q (figureOneSampleCount q - 1)) ∧
      reference.map scheduledBalancedTraceRetainedOption =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      MemLp (scheduledBalancedTracePhaseVariable q
        (terminalPhaseSteps q + 1)) 2 reference ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1) trace ∂reference) =
        figureOneChronologicalRawMean q I (terminalPhaseSteps q + 1) ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1) trace ^ 2 ∂reference) ≤
        (figureOneChronologicalMomentFactor q
            (terminalPhaseSteps q + 1) +
          figureOneExecutableMomentSlack q / 8) *
            figureOneChronologicalRawMean q I
              (terminalPhaseSteps q + 1) ^ 2 ∧
      (∀ j, 1 ≤ j → j ≤ terminalPhaseSteps q →
        reference.map (scheduledBalancedTracePhaseVariable q j) =
          source.map (scheduledBalancedTracePhaseVariable q j)) ∧
      ApproxIndepFun
        ((2 * figureOneCorrectedTransitionBudget q).toReal + 3 *
          (figureOneCorrectedTransitionBudget q +
            scheduledResetReferenceError q
              (figureOneSampleCount q - 1)).toReal)
        oldStatistic
        (scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1)) reference := by
  obtain ⟨target, htargetProb, htarget, htargetRetained,
      htargetNonnegative, htargetMem, htargetMean, htargetSecond⟩ :=
    exists_scheduledTerminalPairTarget q I
  let _ : IsProbabilityMeasure target := htargetProb
  let phase := terminalPhaseSteps q
  let delta := figureOneCorrectedTransitionBudget q +
    scheduledResetReferenceError q (figureOneSampleCount q - 1)
  have hphase : phase < figureOneDependentPhaseCount q := by
    dsimp only [phase]
    rw [figureOneDependentPhaseCount]
    omega
  have hdelta : delta ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · simp [figureOneCorrectedTransitionBudget]
    · exact scheduledResetReferenceError_ne_top q
        (figureOneSampleCount q - 1)
  have houtput := measurable_scheduledResetPairOutput (n := q.n)
  have hpairMap : Measurable
      (fun state : ScheduledBalancedCoolingTrace q.n ×
          Option (ℝ × AmbientSpace q.n) =>
        (state.1, scheduledResetPairOutput state.2)) :=
    measurable_fst.prodMk (houtput.comp measurable_snd)
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  let raw := sequentialPairLaw source
    (scheduledBalancedTracePhaseObservationLaw
      figureOneFinalScheduledBalancedParameters q I phase)
  have hrawProb : IsProbabilityMeasure raw :=
    sequentialPairLaw_isProbabilityMeasure source hobs.1 hobs.2
  let _ : IsProbabilityMeasure raw := hrawProb
  have hpairedProb : IsProbabilityMeasure (raw.map
      (fun state => (state.1, scheduledResetPairOutput state.2))) :=
    Measure.isProbabilityMeasure_map hpairMap.aemeasurable
  let _ : IsProbabilityMeasure (raw.map
      (fun state => (state.1, scheduledResetPairOutput state.2))) := hpairedProb
  have hpairedSndProb : IsProbabilityMeasure
      ((raw.map
        (fun state => (state.1, scheduledResetPairOutput state.2))).map
          Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let _ : IsProbabilityMeasure
      ((raw.map
        (fun state => (state.1, scheduledResetPairOutput state.2))).map
          Prod.snd) := hpairedSndProb
  have hoper := sequentialPairLaw_terminal_output_leUpTo_of_accepted
    q I source hretained
  have hrawPair : MeasureLeUpTo
      (((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
          (fun state => (state.1, scheduledResetPairOutput state.2))).map
            Prod.snd)
      target delta := by
    have hmapped := hoper.map houtput
    have hcombined : MeasureLeUpTo
        (((sequentialPairLaw source
          (scheduledBalancedTracePhaseObservationLaw
            figureOneFinalScheduledBalancedParameters q I phase)).map
              Prod.snd).map scheduledResetPairOutput)
        target delta := by
      exact hmapped.trans htarget
    rw [Measure.map_map measurable_snd hpairMap]
    change MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
            (scheduledResetPairOutput ∘ Prod.snd)) target delta
    rw [← Measure.map_map houtput measurable_snd]
    exact hcombined
  obtain ⟨reference, hreferenceProb, hcomparison, hreferenceRetained,
      hnewLaw, holdLaw⟩ :=
    exists_scheduledTraceRecordedReset q I phase hphase source hvalid
      (figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q - 1))
      hretained target
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase))
      (by simpa only [scheduledRetainedExactSome] using htargetRetained)
      htargetNonnegative hdelta hrawPair.to_tvLe
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hactualProb : IsProbabilityMeasure
      (source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase)) := by
    exact MeasureTheory.isProbabilityMeasure_bind
      (scheduledBalancedTracePhaseKernel_measurable_and_probability
        figureOneFinalScheduledBalancedParameters q I phase).1.aemeasurable
      (ae_of_all _
        (scheduledBalancedTracePhaseKernel_measurable_and_probability
          figureOneFinalScheduledBalancedParameters q I phase).2)
  let _ : IsProbabilityMeasure
      (source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase)) := hactualProb
  have hmoments := coordinate_moments_of_map_eq target reference
    Prod.fst (scheduledBalancedTracePhaseVariable q (phase + 1))
    measurable_fst
    (measurable_scheduledBalancedTracePhaseVariable q (phase + 1))
    hnewLaw htargetMem
  have hindActual :=
    approxIndepFun_oldStatistic_terminal_traceAppend_of_accepted
      q I source hvalid hretained oldStatistic holdMeas holdAppend
  have hindReference : ApproxIndepFun
      ((2 * figureOneCorrectedTransitionBudget q).toReal + 3 * delta.toReal)
      oldStatistic (scheduledBalancedTracePhaseVariable q (phase + 1))
      reference :=
    ApproxIndepFun.of_measureLeUpTo_symm
      (source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase))
      reference hdelta oldStatistic
      (scheduledBalancedTracePhaseVariable q (phase + 1)) holdMeas
      (measurable_scheduledBalancedTracePhaseVariable q (phase + 1))
      hcomparison (by simpa only [phase] using hindActual)
  refine ⟨reference, hreferenceProb, ?_, ?_, hmoments.1, ?_, ?_, ?_, ?_⟩
  · simpa only [phase, delta] using hcomparison
  · exact hreferenceRetained.trans htargetRetained
  · exact hmoments.2.1.trans htargetMean
  · exact hmoments.2.2.trans_le htargetSecond
  · simpa only [phase] using holdLaw
  · simpa only [phase, delta] using hindReference

/-- Prefix-preserving form of the terminal chronological reset.  In addition
to the equation-(6) moments, it retains the complete joint law of all
Gaussian coordinates and the support invariant required by the final
recurrence. -/
theorem exists_scheduledTerminalTraceRecordedReset_with_prefix
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid (terminalPhaseSteps q) trace)
    (hcoordinates : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceCoordinatesNonnegative
        (terminalPhaseSteps q) trace)
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (holdMeas : Measurable oldStatistic)
    (holdAppend : ∀ trace result,
      ScheduledBalancedCoolingTraceValid (terminalPhaseSteps q) trace →
      trace.2 = true → ScheduledResetPairGood result →
      oldStatistic (scheduledResetTraceAppend (trace, result)) =
        oldStatistic trace) :
    ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (source.bind (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)))
        reference
        (figureOneCorrectedTransitionBudget q +
          scheduledResetReferenceError q (figureOneSampleCount q - 1)) ∧
      reference.map scheduledBalancedTraceRetainedOption =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      reference.map
          (scheduledResetPrefixCoordinates q (terminalPhaseSteps q)) =
        source.map
          (scheduledResetPrefixCoordinates q (terminalPhaseSteps q)) ∧
      MemLp (scheduledBalancedTracePhaseVariable q
        (terminalPhaseSteps q + 1)) 2 reference ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1) trace ∂reference) =
        figureOneChronologicalRawMean q I (terminalPhaseSteps q + 1) ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1) trace ^ 2 ∂reference) ≤
        (figureOneChronologicalMomentFactor q
            (terminalPhaseSteps q + 1) +
          figureOneExecutableMomentSlack q / 8) *
            figureOneChronologicalRawMean q I
              (terminalPhaseSteps q + 1) ^ 2 ∧
      ApproxIndepFun
        ((2 * figureOneCorrectedTransitionBudget q).toReal + 3 *
          (figureOneCorrectedTransitionBudget q +
            scheduledResetReferenceError q
              (figureOneSampleCount q - 1)).toReal)
        oldStatistic
        (scheduledBalancedTracePhaseVariable q
          (terminalPhaseSteps q + 1)) reference ∧
      (∀ᵐ trace ∂reference,
        ScheduledBalancedCoolingTraceValid
            (terminalPhaseSteps q + 1) trace ∧
          ScheduledBalancedCoolingTraceCoordinatesNonnegative
            (terminalPhaseSteps q + 1) trace) := by
  obtain ⟨target, htargetProb, htarget, htargetRetained,
      htargetNonnegative, htargetMem, htargetMean, htargetSecond⟩ :=
    exists_scheduledTerminalPairTarget q I
  let _ : IsProbabilityMeasure target := htargetProb
  let phase := terminalPhaseSteps q
  let delta := figureOneCorrectedTransitionBudget q +
    scheduledResetReferenceError q (figureOneSampleCount q - 1)
  have hphase : phase < figureOneDependentPhaseCount q := by
    dsimp only [phase]
    rw [figureOneDependentPhaseCount]
    omega
  have hdelta : delta ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · simp [figureOneCorrectedTransitionBudget]
    · exact scheduledResetReferenceError_ne_top q
        (figureOneSampleCount q - 1)
  have htargetGood : ∀ᵐ result ∂target,
      ScheduledResetPairGood result :=
    ae_scheduledResetPairGood_of_map_snd_eq_map_some target
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase))
      (by simpa only [scheduledRetainedExactSome] using htargetRetained)
      htargetNonnegative
  have houtput := measurable_scheduledResetPairOutput (n := q.n)
  have hpairMap : Measurable
      (fun state : ScheduledBalancedCoolingTrace q.n ×
          Option (ℝ × AmbientSpace q.n) =>
        (state.1, scheduledResetPairOutput state.2)) :=
    measurable_fst.prodMk (houtput.comp measurable_snd)
  have hoper := sequentialPairLaw_terminal_output_leUpTo_of_accepted
    q I source hretained
  have hrawPair : MeasureLeUpTo
      ((sequentialPairLaw source (scheduledResetPairKernel q I phase)).map
        Prod.snd) target delta := by
    rw [sequentialPairLaw_scheduledResetPairKernel_eq_map,
      Measure.map_map measurable_snd hpairMap]
    change MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
            (scheduledResetPairOutput ∘ Prod.snd)) target delta
    rw [← Measure.map_map houtput measurable_snd]
    exact (hoper.map houtput).trans htarget
  have hind :=
    approxIndepFun_oldStatistic_terminal_resetPair_of_accepted
      q I source hretained oldStatistic holdMeas
  have hpairKernel :=
    scheduledResetPairKernel_measurable_and_probability q I phase
  let _ : IsProbabilityMeasure
      (sequentialPairLaw source (scheduledResetPairKernel q I phase)) :=
    sequentialPairLaw_isProbabilityMeasure source hpairKernel.1 hpairKernel.2
  let _ : IsProbabilityMeasure
      ((sequentialPairLaw source
        (scheduledResetPairKernel q I phase)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  obtain ⟨reference, hreferenceProb, hcomparison, hnewLaw, holdLaw,
      hindReference, hsupport⟩ :=
    exists_scheduledTraceRecordedReset_with_approxIndep
      q I phase hphase source (by simpa only [phase] using hvalid)
      (by simpa only [phase] using hcoordinates)
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)) hretained target htargetGood hdelta
      hrawPair.to_tvLe oldStatistic holdMeas
      (by simpa only [phase] using holdAppend) hind
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hnewFst :
      reference.map (scheduledBalancedTracePhaseVariable q (phase + 1)) =
        target.map Prod.fst := by
    calc
      reference.map (scheduledBalancedTracePhaseVariable q (phase + 1)) =
          (reference.map (fun trace =>
            (scheduledBalancedTracePhaseVariable q (phase + 1) trace,
              scheduledBalancedTraceRetainedOption trace))).map Prod.fst := by
            rw [Measure.map_map measurable_fst
              ((measurable_scheduledBalancedTracePhaseVariable q
                (phase + 1)).prodMk
                  measurable_scheduledBalancedTraceRetainedOption)]
            rfl
      _ = target.map Prod.fst := by rw [hnewLaw]
  have hmoments := coordinate_moments_of_map_eq target reference
    Prod.fst (scheduledBalancedTracePhaseVariable q (phase + 1))
    measurable_fst
    (measurable_scheduledBalancedTracePhaseVariable q (phase + 1))
    hnewFst htargetMem
  have hreferenceRetained :
      reference.map scheduledBalancedTraceRetainedOption =
        scheduledRetainedExactSome q I phase := by
    calc
      reference.map scheduledBalancedTraceRetainedOption =
          (reference.map (fun trace =>
            (scheduledBalancedTracePhaseVariable q (phase + 1) trace,
              scheduledBalancedTraceRetainedOption trace))).map Prod.snd := by
            rw [Measure.map_map measurable_snd
              ((measurable_scheduledBalancedTracePhaseVariable q
                (phase + 1)).prodMk
                  measurable_scheduledBalancedTraceRetainedOption)]
            rfl
      _ = target.map Prod.snd := by rw [hnewLaw]
      _ = scheduledRetainedExactSome q I phase := by
        simpa only [scheduledRetainedExactSome] using htargetRetained
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, hmoments.1,
    ?_, ?_, ?_, ?_⟩
  · simpa only [phase, delta] using hcomparison
  · simpa only [phase] using hreferenceRetained
  · simpa only [phase] using holdLaw
  · exact hmoments.2.1.trans htargetMean
  · exact hmoments.2.2.trans_le htargetSecond
  · simpa only [phase, delta] using hindReference
  · simpa only [phase] using hsupport

#print axioms exists_scheduledTerminalTraceRecordedReset
#print axioms exists_scheduledTerminalTraceRecordedReset_with_prefix
#print axioms
  approxIndepFun_oldStatistic_terminal_traceAppend_of_accepted

end

end ArlibCommunity.Algorithms.CV18
