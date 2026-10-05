/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCompleteEndpointWarm

/-! # Retained-state exact-chance induction on the scheduled trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open _root_.Arlib _root_.Arlib.MarkovChains

set_option maxHeartbeats 1000000 in
section

/-- Optional retained point of the loss-preserving trace. -/
def scheduledBalancedTraceRetainedOption
    (trace : ScheduledBalancedCoolingTrace n) : Option (AmbientSpace n) :=
  if trace.2 then some trace.1.2.2.2 else none

theorem measurable_scheduledBalancedTraceRetainedOption :
    Measurable (scheduledBalancedTraceRetainedOption (n := n)) := by
  unfold scheduledBalancedTraceRetainedOption
  exact Measurable.ite
    ((measurable_snd : Measurable fun trace :
      ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton true))
    (measurable_some.comp measurable_scheduledBalancedTraceRetainedState)
    measurable_const

theorem scheduledBalancedTraceRetainedOption_append
    (trace : ScheduledBalancedCoolingTrace n)
    (result : Option (ℝ × AmbientSpace n)) :
    scheduledBalancedTraceRetainedOption
        (scheduledBalancedCoolingTraceAppend trace result) =
      if trace.2 then optionSnd result else none := by
  rcases trace with ⟨history, live⟩
  cases live <;> cases result <;>
    simp [scheduledBalancedTraceRetainedOption,
      scheduledBalancedCoolingTraceAppend, balancedCoolingHistoryAppend,
      optionSnd]

theorem optionSnd_balancedCoolingAverage
    (samples : ℕ) (result : Option (ℝ × AmbientSpace n)) :
    optionSnd (balancedCoolingAverage samples result) = optionSnd result := by
  cases result <;> rfl

/-- During a Gaussian cooling phase, the trace retained marginal follows
exactly the complete retained collector kernel. -/
theorem map_scheduledBalancedTracePhaseKernel_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    (scheduledBalancedTracePhaseKernel
      figureOneFinalScheduledBalancedParameters q I phase trace).map
        scheduledBalancedTraceRetainedOption =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
        (scheduledBalancedTraceRetainedOption trace) := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  have hcount : 0 < count := by
    unfold count figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hcountEq : count - 1 + 1 = count := Nat.sub_add_cancel hcount
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
      let append := scheduledBalancedCoolingTraceAppend
        (history, true)
      have happend : Measurable append :=
        (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      let avg := balancedCoolingAverage (n := q.n) count
      have havg : Measurable avg := measurable_balancedCoolingAverage count
      let collect := scheduledBalancedTransitionCollectLaw q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase)) count 0
          (accuracyScaleFactor q • history.2.2.2)
      have hcollect : IsProbabilityMeasure collect :=
        (scheduledBalancedTransitionCollectLaw_measurable_and_probability
          q I (scheduleValue_pos q phase)
          (measurable_gaussianRatioWeight _ _)
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase)) count).2 _ _
      unfold scheduledBalancedTracePhaseKernel
        scheduledBalancedTracePhaseObservationLaw
      simp only [if_true, hphase]
      unfold scheduledBalancedCoolingRatioTransitionLaw
      unfold figureOneFinalScheduledCompleteRetainedKernel
      simp only [scheduledBalancedTraceRetainedOption, if_true]
      rw [show figureOnePhaseSampleCount q (scheduleValue q phase) - 1 + 1 =
          figureOnePhaseSampleCount q (scheduleValue q phase) by
        simpa [count] using hcountEq]
      change ((collect.map avg).map append).map
          scheduledBalancedTraceRetainedOption =
        (collect.map optionSnd)
      rw [Measure.map_map measurable_scheduledBalancedTraceRetainedOption happend,
        Measure.map_map
          (measurable_scheduledBalancedTraceRetainedOption.comp happend) havg]
      apply Measure.map_congr
      filter_upwards with result
      simpa [append, avg,
        scheduledBalancedTraceRetainedOption_append,
        optionSnd_balancedCoolingAverage]

/-- Integrated form: mapping a trace law through one Gaussian trace phase
commutes with mapping to the retained option and applying the complete phase
kernel. -/
theorem map_bind_scheduledBalancedTracePhaseKernel_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n)) :
    (law.bind (scheduledBalancedTracePhaseKernel
      figureOneFinalScheduledBalancedParameters q I phase)).map
        scheduledBalancedTraceRetainedOption =
      (law.map scheduledBalancedTraceRetainedOption).bind
        (figureOneFinalScheduledCompleteRetainedKernel q I
          (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) := by
  let traceK := scheduledBalancedTracePhaseKernel
    figureOneFinalScheduledBalancedParameters q I phase
  let retainedK := figureOneFinalScheduledCompleteRetainedKernel q I
    (scheduleValue q phase)
    (gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1)))
    (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
  have htraceK := scheduledBalancedTracePhaseKernel_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
  have hretainedK :=
    figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
        (weight := gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
  calc
    (law.bind traceK).map scheduledBalancedTraceRetainedOption =
        law.bind fun trace =>
          (traceK trace).map scheduledBalancedTraceRetainedOption :=
      map_bind_eq_bind_map_of_measurable law htraceK.1
        measurable_scheduledBalancedTraceRetainedOption
    _ = law.bind (retainedK ∘ scheduledBalancedTraceRetainedOption) := by
      apply Measure.bind_congr_right
      filter_upwards with trace
      exact map_scheduledBalancedTracePhaseKernel_retainedOption
        q I phase hphase trace
    _ = (law.map scheduledBalancedTraceRetainedOption).bind retainedK :=
      (map_bind_eq_bind_comp_state law
        measurable_scheduledBalancedTraceRetainedOption hretainedK.1).symm

/-! ## Chronological retained-target induction -/

/-- The scheduled speedy stationary law at chronological Gaussian phase
`phase`. -/
noncomputable def figureOneScheduledSpeedyPiAt
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (AmbientSpace q.n) :=
  ellGaussianProb
    (figureOneScheduledPhaseBody q I (scheduleValue q phase))
    (figureOneScheduledProposalRadius q (scheduleValue q phase))
    (scheduleValue q phase)

/-- The normalized accepted target retained after chronological Gaussian
phase `phase`. -/
noncomputable def figureOneScheduledAcceptedTargetAt
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (AmbientSpace q.n) :=
  scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I
    (scheduleValue q phase) (figureOneScheduledSpeedyPiAt q I phase)

theorem figureOneScheduledSpeedyPiAt_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (figureOneScheduledSpeedyPiAt q I phase) := by
  let sigma2 := scheduleValue q phase
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  have hsigma2 : 0 < sigma2 := scheduleValue_pos q phase
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  simpa [figureOneScheduledSpeedyPiAt, sigma2, K, delta] using
    (isProbabilityMeasure_ellGaussianProb hmass0 hmasstop)

theorem figureOneScheduledAcceptedTargetAt_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I phase) := by
  let _ : IsProbabilityMeasure (figureOneScheduledSpeedyPiAt q I phase) :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I phase
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I (scheduleValue q phase)
        (figureOneScheduledSpeedyPiAt q I phase) Set.univ := by
    simpa [figureOneScheduledSpeedyPiAt] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I
        (scheduleValue_pos q phase)
  exact
    scheduledBalancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I (scheduleValue_pos q phase)
        (figureOneScheduledSpeedyPiAt q I phase) haccepted

/-- Exact-chance loss after completing the first `phases` Gaussian phases. -/
noncomputable def figureOneScheduledRetainedError
    (q : VolumeParams) (phases : ℕ) : ENNReal :=
  scheduledBalancedStationaryTargetError q +
    ∑ phase ∈ Finset.range phases,
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q

theorem map_scheduledBalancedInitialTrace_retainedOption
    (q : VolumeParams) (I : VolumeInput q.n) :
    ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        scheduledBalancedInitialTrace).map
          scheduledBalancedTraceRetainedOption =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some := by
  rw [Measure.map_map measurable_scheduledBalancedTraceRetainedOption
    measurable_scheduledBalancedInitialTrace]
  apply Measure.map_congr
  filter_upwards with point
  rfl

theorem scheduledBalancedInitialRetained_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      (((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
          scheduledBalancedInitialTrace).map
            scheduledBalancedTraceRetainedOption)
      ((figureOneScheduledAcceptedTargetAt q I 0).map some)
      (scheduledBalancedStationaryTargetError q) := by
  let _ : IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I 0) :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
  let _ : IsProbabilityMeasure
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I
        (initialVariance q)
        (ellGaussianProb
          (figureOneScheduledPhaseBody q I (initialVariance q))
          (figureOneScheduledProposalRadius q (initialVariance q))
          (initialVariance q))) := by
    simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, scheduleValue] using
      (figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0)
  rw [map_scheduledBalancedInitialTrace_retainedOption]
  have htv := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I (initialVariance_pos q)
  have hmlu := MeasureLeUpTo.of_tvLe htv.symm
  have hmapped := hmlu.map measurable_some
  simpa [figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt, scheduleValue] using hmapped

/-- After `phase + 1` Gaussian phases, the retained optional state is
dominated by the current normalized accepted target plus exactly the sum of
the KLS initialization error and complete-phase transition budgets. -/
theorem scheduledBalancedForwardTraceLaw_retained_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ phase, phase < terminalPhaseSteps q →
      MeasureLeUpTo
        ((scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
            scheduledBalancedTraceRetainedOption)
        ((figureOneScheduledAcceptedTargetAt q I phase).map some)
        (figureOneScheduledRetainedError q (phase + 1)) := by
  intro phase hphase
  induction phase with
  | zero =>
      let target := figureOneScheduledAcceptedTargetAt q I 0
      let _ : IsProbabilityMeasure target :=
        figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
      have hstart := scheduledBalancedInitialRetained_leUpTo_target q I
      have hwarm8 := initialContractedAcceptedTarget_isWarm_eight q I
      have hwarm : IsWarm
          (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
          (target.map fun x => accuracyScaleFactor q • x)
          (figureOneScheduledSpeedyPiAt q I 0) := by
        apply hwarm8.mono
        rw [← ENNReal.ofReal_ofNat 8]
        exact ENNReal.ofReal_le_ofReal <| by
          nlinarith [speedyAdjacentWarmConstant_one_le q]
      have hstep :=
        bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
          q I (scheduleValue_pos q 0)
          (measurable_gaussianRatioWeight (scheduleValue q 0)
            (scheduleValue q 1))
          (figureOnePhaseSampleCount q (scheduleValue q 0) - 1)
          (((truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
              scheduledBalancedInitialTrace).map
                scheduledBalancedTraceRetainedOption)
          target hstart hwarm
      rw [show scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I 1 =
          (scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I 0).bind
              (scheduledBalancedTracePhaseKernel
                figureOneFinalScheduledBalancedParameters q I 0) by rfl]
      rw [map_bind_scheduledBalancedTracePhaseKernel_retainedOption
        q I 0 (terminalPhaseSteps_pos q)]
      have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q 0) := by
        unfold figureOnePhaseSampleCount
        split_ifs
        · exact figureOneFixedSampleCount_pos q
        · exact figureOneSampleCount_pos q
      rw [Nat.sub_add_cancel hcount] at hstep
      rw [show scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I 0 =
          (truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
              scheduledBalancedInitialTrace by rfl]
      simpa only [target, figureOneScheduledAcceptedTargetAt,
        figureOneScheduledSpeedyPiAt, figureOneScheduledRetainedError,
        scheduleValue, Function.iterate_zero_apply, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add] using hstep
  | succ phase ih =>
      have hprev : phase < terminalPhaseSteps q :=
        Nat.lt_of_succ_lt hphase
      have hih := ih hprev
      let target := figureOneScheduledAcceptedTargetAt q I phase
      let _ : IsProbabilityMeasure target :=
        figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
      have hwarm : IsWarm
          (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
          (target.map fun x => accuracyScaleFactor q • x)
          (figureOneScheduledSpeedyPiAt q I (phase + 1)) := by
        simpa [target, figureOneScheduledAcceptedTargetAt,
          figureOneScheduledSpeedyPiAt] using
          map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I phase
      have hstep :=
        bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
          q I (scheduleValue_pos q (phase + 1))
          (measurable_gaussianRatioWeight (scheduleValue q (phase + 1))
            (scheduleValue q (phase + 2)))
          (figureOnePhaseSampleCount q (scheduleValue q (phase + 1)) - 1)
          ((scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
              scheduledBalancedTraceRetainedOption)
          target hih hwarm
      rw [show scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I (phase + 1 + 1) =
          (scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I (phase + 1)).bind
              (scheduledBalancedTracePhaseKernel
                figureOneFinalScheduledBalancedParameters q I (phase + 1)) by rfl]
      rw [map_bind_scheduledBalancedTracePhaseKernel_retainedOption
        q I (phase + 1) hphase]
      have hcount : 0 < figureOnePhaseSampleCount q
          (scheduleValue q (phase + 1)) := by
        unfold figureOnePhaseSampleCount
        split_ifs
        · exact figureOneFixedSampleCount_pos q
        · exact figureOneSampleCount_pos q
      rw [Nat.sub_add_cancel hcount] at hstep
      have herr : figureOneScheduledRetainedError q (phase + 1) +
          figureOnePhaseSampleCount q (scheduleValue q (phase + 1)) •
            figureOneCorrectedTransitionBudget q =
          figureOneScheduledRetainedError q (phase + 1 + 1) := by
        simp only [figureOneScheduledRetainedError, Finset.sum_range_succ]
        ac_rfl
      rw [← herr]
      simpa only [target, figureOneScheduledAcceptedTargetAt,
        figureOneScheduledSpeedyPiAt, Nat.add_assoc] using hstep

/-! ## Extracting the live marginal and its error witness -/

def scheduledRetainedSomeSet (n : ℕ) : Set (Option (AmbientSpace n)) :=
  ({none} : Set (Option (AmbientSpace n)))ᶜ

theorem measurableSet_scheduledRetainedSomeSet :
    MeasurableSet (scheduledRetainedSomeSet n) :=
  measurableSet_option_none.compl

def scheduledRetainedGetDZero :
    Option (AmbientSpace n) → AmbientSpace n
  | none => 0
  | some point => point

theorem measurable_scheduledRetainedGetDZero :
    Measurable (scheduledRetainedGetDZero (n := n)) := by
  convert Measurable.optionElim (0 : AmbientSpace n) measurable_id using 1
  funext state
  cases state <;> rfl

/-- Restricting the optional retained marginal to `some` and extracting its
point is exactly the live retained-state submeasure of the trace. -/
theorem scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome
    (law : Measure (ScheduledBalancedCoolingTrace n)) :
    scheduledBalancedTraceLiveStateLaw law id =
      (((law.map scheduledBalancedTraceRetainedOption).restrict
        (scheduledRetainedSomeSet n)).map scheduledRetainedGetDZero) := by
  have hretained := measurable_scheduledBalancedTraceRetainedOption (n := n)
  have hget := measurable_scheduledRetainedGetDZero (n := n)
  have hpre : scheduledBalancedTraceRetainedOption ⁻¹'
      scheduledRetainedSomeSet n = scheduledBalancedTraceLiveSet n := by
    ext trace
    rcases trace with ⟨history, live⟩
    cases live <;> simp [scheduledBalancedTraceRetainedOption,
      scheduledRetainedSomeSet, scheduledBalancedTraceLiveSet]
  rw [Measure.restrict_map hretained
      (measurableSet_scheduledRetainedSomeSet (n := n)), hpre,
    Measure.map_map hget hretained]
  unfold scheduledBalancedTraceLiveStateLaw
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem
    (measurableSet_scheduledBalancedTraceLiveSet (n := n))] with trace htrace
  rcases trace with ⟨history, live⟩
  cases live
  · simp [scheduledBalancedTraceLiveSet] at htrace
  · rfl

theorem map_some_restrict_extract_eq
    (mu : Measure (AmbientSpace n)) :
    (((mu.map some).restrict (scheduledRetainedSomeSet n)).map
      scheduledRetainedGetDZero) = mu := by
  have hsome : Measurable (some : AmbientSpace n → Option (AmbientSpace n)) :=
    measurable_some
  have hget := measurable_scheduledRetainedGetDZero (n := n)
  have hpre : (some : AmbientSpace n → Option (AmbientSpace n)) ⁻¹'
      scheduledRetainedSomeSet n = Set.univ := by
    ext point
    simp [scheduledRetainedSomeSet]
  rw [Measure.restrict_map hsome
      (measurableSet_scheduledRetainedSomeSet (n := n)), hpre,
    Measure.restrict_univ, Measure.map_map hget hsome]
  have hfun : scheduledRetainedGetDZero ∘
      (some : AmbientSpace n → Option (AmbientSpace n)) = id := by
    funext point
    rfl
  rw [hfun, Measure.map_id]

/-- An optional retained exact-chance bound supplies the concrete good/bad
decomposition of the live retained marginal. -/
theorem exists_scheduledBalancedTraceLiveStateLaw_good_bad_of_leUpTo
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (good : Measure (AmbientSpace n)) {errorBudget : ENNReal}
    (h : MeasureLeUpTo
      (law.map scheduledBalancedTraceRetainedOption)
      (good.map some) errorBudget) :
    ∃ bad : Measure (AmbientSpace n),
      scheduledBalancedTraceLiveStateLaw law id ≤ good + bad ∧
      bad Set.univ ≤ errorBudget := by
  obtain ⟨error, hle, hmass⟩ := h
  let someSet := scheduledRetainedSomeSet n
  let get := scheduledRetainedGetDZero (n := n)
  let bad := (error.restrict someSet).map get
  refine ⟨bad, ?_, ?_⟩
  · rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome]
    have hrestrict :
        (law.map scheduledBalancedTraceRetainedOption).restrict someSet ≤
          ((good.map some + error).restrict someSet) :=
      Measure.restrict_mono Set.Subset.rfl hle
    have hmapped := Measure.map_mono hrestrict
      (measurable_scheduledRetainedGetDZero (n := n))
    rw [Measure.restrict_add,
      Measure.map_add _ _ (measurable_scheduledRetainedGetDZero (n := n)),
      map_some_restrict_extract_eq] at hmapped
    exact hmapped
  · dsimp only [bad]
    rw [Measure.map_apply
      (measurable_scheduledRetainedGetDZero (n := n)) MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    exact (measure_mono (Set.subset_univ someSet)).trans hmass

/-- Concrete phasewise good/bad retained marginal.  The good law is the
paper's normalized accepted target; all cap/mixing/KLS losses are isolated in
a positive bad submeasure with the exact cumulative error bound. -/
theorem exists_figureOneScheduledTraceLiveRetained_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let good := figureOneScheduledAcceptedTargetAt q I phase
    ∃ bad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceLiveStateLaw law id ≤ good + bad ∧
      bad Set.univ ≤ figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  exact exists_scheduledBalancedTraceLiveStateLaw_good_bad_of_leUpTo
    _ _ (scheduledBalancedForwardTraceLaw_retained_leUpTo_target
      q I phase hphase)

/-- Phase-input form used by the next collector and by its expected-cost
bound: rescale the live retained marginal, while preserving the bad mass and
the exact adjacent-phase warmness of the good part. -/
theorem exists_figureOneScheduledTraceScaledLiveRetained_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
    ∃ bad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceLiveStateLaw law scale ≤ good + bad ∧
      IsWarm (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
        (figureOneScheduledSpeedyPiAt q I (phase + 1)) ∧
      bad Set.univ ≤ figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  obtain ⟨bad, hle, hbad⟩ :=
    exists_figureOneScheduledTraceLiveRetained_good_bad q I phase hphase
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  have hscale : Measurable scale := by fun_prop
  let scaledBad := bad.map scale
  refine ⟨scaledBad, ?_, ?_, ?_⟩
  · have hmapped := Measure.map_mono hle hscale
    rw [Measure.map_add _ _ hscale] at hmapped
    dsimp only [scaledBad]
    unfold scheduledBalancedTraceLiveStateLaw at hmapped ⊢
    rw [Measure.map_map hscale
      ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
        (measurable_scheduledBalancedTraceRetainedState (n := q.n)))] at hmapped
    simpa only [Function.comp_def, id_eq] using hmapped
  · simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, scale] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I phase
  · dsimp only [scaledBad]
    rw [Measure.map_apply hscale MeasurableSet.univ,
      Set.preimage_univ]
    exact hbad

#print axioms map_scheduledBalancedTracePhaseKernel_retainedOption
#print axioms map_bind_scheduledBalancedTracePhaseKernel_retainedOption
#print axioms scheduledBalancedForwardTraceLaw_retained_leUpTo_target
#print axioms exists_figureOneScheduledTraceLiveRetained_good_bad
#print axioms exists_figureOneScheduledTraceScaledLiveRetained_good_bad

end

end ArlibCommunity.Algorithms.CV18
