/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledPhaseCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCostComposition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryAppend

/-! # A retained-state interpreter for final scheduled cost accounting -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- One Gaussian phase, retaining only the endpoint needed by the next phase.
This erases only query-free estimator coordinates. -/
noncomputable def figureOneFinalScheduledRetainedGaussianPhaseProgram
    (q : VolumeParams) (phase : ℕ) :
    Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | none => .pure none
  | some point =>
      (scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase))
        (figureOnePhaseSampleCount q (scheduleValue q phase))
        (accuracyScaleFactor q • point)).bind fun result =>
          .pure (optionSnd result)

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).CountedStronglyMeasurable
        oracle.query := by
  let collect (point : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
      (gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
      (accuracyScaleFactor q • point)
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point := by fun_prop
  have hcollectBase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
  have hcollectMeas : Measurable fun point => (collect point).run oracle.query :=
    hcollectBase.1.comp hscale
  have hcollect : ∀ point, (collect point).CountedStronglyMeasurable oracle.query :=
    fun point => hcollectBase.2 (accuracyScaleFactor q • point)
  have hsome := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query collect (fun z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n) => optionSnd z.2)
      hcollectMeas hcollect (measurable_optionSnd.comp measurable_snd)
  constructor
  · convert Measurable.optionElim
      (Measure.dirac ((none : Option (AmbientSpace q.n)), 0)) hsome.1 using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none => trivial
    | some point => exact hsome.2 point

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (state : Option (AmbientSpace q.n)) :
    countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
          oracle.query) =
      match state with
      | none => 0
      | some point => countedQueryCost
          ((scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
            (gaussianRatioWeight (scheduleValue q phase)
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (scheduleValue q phase))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase))
            (figureOnePhaseSampleCount q (scheduleValue q phase))
            (accuracyScaleFactor q • point)).run oracle.query) := by
  cases state with
  | none =>
      exact MembershipOracleProgram.countedQueryCost_pure oracle.query none
  | some point =>
      unfold figureOneFinalScheduledRetainedGaussianPhaseProgram
      exact MembershipOracleProgram.countedQueryCost_bind_pure_eq
        oracle.query _ optionSnd measurable_optionSnd
          ((scheduledBalancedAccuracyRetryCollect_countedMeasurable
            q I oracle (scheduleValue_pos q phase)
              (measurable_gaussianRatioWeight (scheduleValue q phase)
                (scheduleValue q (phase + 1)))
              (figureOneFinalScheduledBalancedParameters.proposalCap q
                (scheduleValue q phase))
              (figureOneFinalScheduledBalancedParameters.properStride q
                (scheduleValue q phase))
              (figureOneFinalScheduledBalancedParameters.retryLimit q
                (scheduleValue q phase))
              (figureOnePhaseSampleCount q (scheduleValue q phase))).2 _)

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (state : Option (AmbientSpace q.n)) :
    (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
        oracle.query =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) state := by
  cases state with
  | none => rfl
  | some point =>
      have hcollect := (scheduledBalancedAccuracyRetryCollect_countedMeasurable
        q I oracle (scheduleValue_pos q phase)
          (measurable_gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase))
          (figureOnePhaseSampleCount q (scheduleValue q phase))).2
            (accuracyScaleFactor q • point)
      unfold figureOneFinalScheduledRetainedGaussianPhaseProgram
      have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q phase) := by
        unfold figureOnePhaseSampleCount
        split_ifs
        · exact figureOneFixedSampleCount_pos q
        · exact figureOneSampleCount_pos q
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
        hcollect.stronglyMeasurable]
      · rw [scheduledBalancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
          q I oracle (scheduleValue_pos q phase)
            (measurable_gaussianRatioWeight (scheduleValue q phase)
              (scheduleValue q (phase + 1)))]
        simp only [MembershipOracleProgram.runEstimate]
        rw [Measure.bind_dirac_eq_map _ measurable_optionSnd]
        unfold figureOneFinalScheduledCompleteRetainedKernel
        rw [Nat.sub_add_cancel hcount]
        rw [scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological]
      · intro result
        trivial
      · simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp measurable_optionSnd

/-- A Gaussian ratio observation and the retained phase kernel give the same
expectation to every measurable function that depends only on the endpoint.
This is the measure-level form of erasing the ratio coordinate. -/
theorem lintegral_optionSnd_scheduledRatioTransition_eq_retainedKernel
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (point : AmbientSpace q.n) (f : Option (AmbientSpace q.n) → ENNReal)
    (hf : Measurable f) :
    (∫⁻ result, f (optionSnd result)
      ∂(scheduledBalancedCoolingRatioTransitionLaw
        figureOneFinalScheduledBalancedParameters q I
          (scheduleValue q phase) (scheduleValue q (phase + 1)) point)) =
      ∫⁻ state, f state
        ∂(figureOneFinalScheduledCompleteRetainedKernel q I
          (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
          (some point)) := by
  have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q phase) := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  let collect := scheduledBalancedTransitionCollectLaw q I
    (scheduleValue q phase)
    (gaussianRatioWeight (scheduleValue q phase) (scheduleValue q (phase + 1)))
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (scheduleValue q phase))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (scheduleValue q phase))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (scheduleValue q phase))
    (figureOnePhaseSampleCount q (scheduleValue q phase)) 0
    (accuracyScaleFactor q • point)
  let average := balancedCoolingAverage
    (n := q.n) (figureOnePhaseSampleCount q (scheduleValue q phase))
  have havg : Measurable average := measurable_balancedCoolingAverage _
  have hcollect : IsProbabilityMeasure collect :=
    (scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (scheduleValue_pos q phase)
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase))
        (figureOnePhaseSampleCount q (scheduleValue q phase))).2 _ _
  unfold scheduledBalancedCoolingRatioTransitionLaw
    figureOneFinalScheduledCompleteRetainedKernel
  rw [Nat.sub_add_cancel hcount]
  change (∫⁻ result, f (optionSnd result) ∂collect.map average) =
    ∫⁻ state, f state ∂collect.map optionSnd
  change (∫⁻ result, (f ∘ optionSnd) result ∂collect.map average) =
    ∫⁻ state, f state ∂collect.map optionSnd
  rw [lintegral_map (hf.comp measurable_optionSnd) havg]
  rw [lintegral_map hf measurable_optionSnd]
  apply lintegral_congr
  intro result
  change f (optionSnd (balancedCoolingAverage
    (figureOnePhaseSampleCount q (scheduleValue q phase)) result)) = _
  rw [optionSnd_balancedCoolingAverage]

/-- Execute a consecutive block of Gaussian phases while retaining only the
optional endpoint. -/
noncomputable def figureOneFinalScheduledRetainedGaussianChain
    (q : VolumeParams) : ℕ → ℕ → Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | _, 0, state => .pure state
  | phase, steps + 1, state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).bind
        (figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps)

theorem figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps,
      (Measurable fun state =>
        (figureOneFinalScheduledRetainedGaussianChain q phase steps state).run
          oracle.query) ∧
      ∀ state,
        (figureOneFinalScheduledRetainedGaussianChain q phase steps state).CountedStronglyMeasurable
          oracle.query := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      constructor
      · simp only [figureOneFinalScheduledRetainedGaussianChain,
          MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const)
      · intro state
        trivial
  | succ steps ih =>
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have htail := ih (phase + 1)
      simp only [figureOneFinalScheduledRetainedGaussianChain]
      constructor
      · exact MembershipOracleProgram.measurable_run_bind_param oracle.query
          (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)
          (fun z => figureOneFinalScheduledRetainedGaussianChain q
            (phase + 1) steps z.2)
          hphase.1 hphase.2 (htail.1.comp measurable_snd)
          (fun z => htail.2 z.2)
      · intro state
        exact (hphase.2 state).bind htail.2 htail.1

/-- Recursive chronological sum of the Gaussian phase costs. -/
noncomputable def figureOneFinalScheduledGaussianPhaseCostTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ℕ → ℕ → ENNReal
  | _, 0 => 0
  | phase, steps + 1 =>
      figureOneFinalScheduledGaussianPhaseExpectedCost q I oracle phase +
        figureOneFinalScheduledGaussianPhaseCostTail q I oracle
          (phase + 1) steps

/-- One front step of the retained chain contributes its local expected cost,
then transports the remaining cost through the exact retained endpoint
kernel. -/
theorem lintegral_figureOneFinalScheduledRetainedGaussianChain_succ
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase steps : ℕ) (mu : Measure (Option (AmbientSpace q.n))) :
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q phase (steps + 1)
          state).run oracle.query) ∂mu) =
      (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
          oracle.query) ∂mu) +
      ∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
          state).run oracle.query)
        ∂(mu.bind (figureOneFinalScheduledCompleteRetainedKernel q I
          (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1))) := by
  let phaseProgram := figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
  let tailProgram := figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
  let retainedKernel := figureOneFinalScheduledCompleteRetainedKernel q I
    (scheduleValue q phase)
    (gaussianRatioWeight (scheduleValue q phase) (scheduleValue q (phase + 1)))
    (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
  have hphase :=
    figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
      q I oracle phase
  have htail := figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
    q I oracle (phase + 1) steps
  have hphaseCost : Measurable fun state =>
      countedQueryCost ((phaseProgram state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hphase.1
  have htailCost : Measurable fun state =>
      countedQueryCost ((tailProgram state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      htail.1
  have hpoint : ∀ state,
      countedQueryCost
          (((phaseProgram state).bind tailProgram).run oracle.query) =
        countedQueryCost ((phaseProgram state).run oracle.query) +
          ∫⁻ next, countedQueryCost ((tailProgram next).run oracle.query)
            ∂((phaseProgram state).runEstimate oracle.query) := by
    intro state
    exact MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
      (phaseProgram state) tailProgram (hphase.2 state) htail.2 htail.1
  simp only [figureOneFinalScheduledRetainedGaussianChain]
  rw [lintegral_congr hpoint, lintegral_add_left hphaseCost]
  rw [Measure.lintegral_bind]
  · congr 1
    apply lintegral_congr
    intro state
    rw [show (phaseProgram state).runEstimate oracle.query =
        retainedKernel state from
      figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
        q I oracle phase state]
  · exact (figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)).1.aemeasurable
  · exact htailCost.aemeasurable

/-- The retained law after one more Gaussian phase is exactly the next trace
marginal. -/
theorem figureOneFinalScheduledTraceRetained_succ
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    ((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase).map
        scheduledBalancedTraceRetainedOption).bind
      (figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
          scheduledBalancedTraceRetainedOption := by
  rw [show scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1) =
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I phase).bind
            (scheduledBalancedTracePhaseKernel
              figureOneFinalScheduledBalancedParameters q I phase) by rfl]
  exact (map_bind_scheduledBalancedTracePhaseKernel_retainedOption
    q I phase hphase _).symm

/-- Exact additive accounting for any suffix of the chronological Gaussian
schedule, started from its true optional retained-state marginal. -/
theorem lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps, phase + steps ≤ terminalPhaseSteps q →
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q phase steps state).run
          oracle.query)
      ∂((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phase).map
          scheduledBalancedTraceRetainedOption)) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle phase steps := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro _
      simp only [figureOneFinalScheduledRetainedGaussianChain,
        figureOneFinalScheduledGaussianPhaseCostTail,
        MembershipOracleProgram.countedQueryCost_pure]
      simp
  | succ steps ih =>
      intro hbound
      have hphase : phase < terminalPhaseSteps q := by omega
      rw [lintegral_figureOneFinalScheduledRetainedGaussianChain_succ]
      rw [figureOneFinalScheduledTraceRetained_succ q I phase hphase]
      rw [ih (phase + 1) (by omega)]
      rw [figureOneFinalScheduledGaussianPhaseCostTail]
      congr 1
      unfold figureOneFinalScheduledGaussianPhaseExpectedCost
      apply lintegral_congr
      intro state
      exact figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
        q I oracle phase state

/-- Averaging the retained Gaussian chain over its true phase-start marginal
produces exactly the later chronological retained marginal. -/
theorem bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps, phase + steps ≤ terminalPhaseSteps q →
    ((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase).map
        scheduledBalancedTraceRetainedOption).bind (fun state =>
      (figureOneFinalScheduledRetainedGaussianChain q phase steps state).runEstimate
        oracle.query) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (phase + steps)).map
          scheduledBalancedTraceRetainedOption := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro _
      simp only [figureOneFinalScheduledRetainedGaussianChain,
        MembershipOracleProgram.runEstimate, add_zero]
      simp
  | succ steps ih =>
      intro hbound
      have hphaseLt : phase < terminalPhaseSteps q := by omega
      let mu := (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phase).map
          scheduledBalancedTraceRetainedOption
      let phaseProgram :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
      let tailProgram :=
        figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
      let retainedKernel := figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have htail := figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
        q I oracle (phase + 1) steps
      have hphaseEstimate : Measurable fun state =>
          (phaseProgram state).runEstimate oracle.query := by
        rw [show (fun state => (phaseProgram state).runEstimate oracle.query) =
            fun state => ((phaseProgram state).run oracle.query).map Prod.fst by
          funext state
          exact (phaseProgram state).runEstimate_eq_map_fst_run oracle.query
            (hphase.2 state).executionMeasurable]
        exact measurable_measure_map_param_variable hphase.1
          (fun state => MembershipOracleProgram.run_isProbabilityMeasure
            oracle.query (phaseProgram state)
              (hphase.2 state).executionMeasurable)
          (measurable_fst.comp measurable_snd)
      have htailEstimate : Measurable fun state =>
          (tailProgram state).runEstimate oracle.query := by
        rw [show (fun state => (tailProgram state).runEstimate oracle.query) =
            fun state => ((tailProgram state).run oracle.query).map Prod.fst by
          funext state
          exact (tailProgram state).runEstimate_eq_map_fst_run oracle.query
            (htail.2 state).executionMeasurable]
        exact measurable_measure_map_param_variable htail.1
          (fun state => MembershipOracleProgram.run_isProbabilityMeasure
            oracle.query (tailProgram state)
              (htail.2 state).executionMeasurable)
          (measurable_fst.comp measurable_snd)
      have hrun : ∀ state,
          ((phaseProgram state).bind tailProgram).runEstimate oracle.query =
            ((phaseProgram state).runEstimate oracle.query).bind fun next =>
              (tailProgram next).runEstimate oracle.query := by
        intro state
        exact MembershipOracleProgram.runEstimate_bind oracle.query
          (phaseProgram state) tailProgram (hphase.2 state).stronglyMeasurable
            (fun next => (htail.2 next).stronglyMeasurable) htailEstimate
      simp only [figureOneFinalScheduledRetainedGaussianChain]
      rw [show (fun state =>
          (((phaseProgram state).bind tailProgram).runEstimate oracle.query)) =
          fun state => ((phaseProgram state).runEstimate oracle.query).bind
            (fun next => (tailProgram next).runEstimate oracle.query) by
        funext state
        exact hrun state]
      have hphaseLaw : (fun state =>
          (phaseProgram state).runEstimate oracle.query) = retainedKernel := by
        funext state
        exact figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
          q I oracle phase state
      change mu.bind (fun state =>
          ((phaseProgram state).runEstimate oracle.query).bind
            (fun next => (tailProgram next).runEstimate oracle.query)) = _
      calc
        _ = (mu.bind fun state =>
              (phaseProgram state).runEstimate oracle.query).bind
                (fun next => (tailProgram next).runEstimate oracle.query) :=
          (Measure.bind_bind hphaseEstimate.aemeasurable
            htailEstimate.aemeasurable).symm
        _ = (mu.bind retainedKernel).bind
                (fun next => (tailProgram next).runEstimate oracle.query) := by
          rw [hphaseLaw]
        _ = ((scheduledBalancedForwardTraceLaw
              figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
                scheduledBalancedTraceRetainedOption).bind
                  (fun next => (tailProgram next).runEstimate oracle.query) := by
          rw [show mu.bind retainedKernel =
              (scheduledBalancedForwardTraceLaw
                figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
                  scheduledBalancedTraceRetainedOption from
            figureOneFinalScheduledTraceRetained_succ q I phase hphaseLt]
        _ = _ := by
          simpa only [tailProgram, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (phase + 1) (by omega)

/-- Terminal uniform collector retaining only its endpoint. -/
noncomputable def figureOneFinalScheduledRetainedTerminalProgram
    (q : VolumeParams) : Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | none => .pure none
  | some point =>
      (scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
        (uniformRatioWeight (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q))
        (figureOneSampleCount q) (accuracyScaleFactor q • point)).bind
          fun result => .pure (optionSnd result)

theorem figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedTerminalProgram q state).run oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedTerminalProgram q state).CountedStronglyMeasurable
        oracle.query := by
  let collect (point : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
      (uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q) (accuracyScaleFactor q • point)
  have hbase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q)) (figureOneSampleCount q)
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point := by fun_prop
  have hcollectMeas : Measurable fun point => (collect point).run oracle.query :=
    hbase.1.comp hscale
  have hcollect : ∀ point, (collect point).CountedStronglyMeasurable oracle.query :=
    fun point => hbase.2 (accuracyScaleFactor q • point)
  have hsome := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query collect (fun z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n) => optionSnd z.2)
      hcollectMeas hcollect (measurable_optionSnd.comp measurable_snd)
  constructor
  · convert Measurable.optionElim
      (Measure.dirac ((none : Option (AmbientSpace q.n)), 0)) hsome.1 using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none => trivial
    | some point => exact hsome.2 point

theorem figureOneFinalScheduledRetainedTerminalProgram_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (state : Option (AmbientSpace q.n)) :
    countedQueryCost
        ((figureOneFinalScheduledRetainedTerminalProgram q state).run
          oracle.query) =
      match state with
      | none => 0
      | some point => countedQueryCost
          ((scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
            (uniformRatioWeight (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (terminalVariance q))
            (figureOneSampleCount q) (accuracyScaleFactor q • point)).run
              oracle.query) := by
  cases state with
  | none =>
      exact MembershipOracleProgram.countedQueryCost_pure oracle.query none
  | some point =>
      unfold figureOneFinalScheduledRetainedTerminalProgram
      exact MembershipOracleProgram.countedQueryCost_bind_pure_eq
        oracle.query _ optionSnd measurable_optionSnd
          ((scheduledBalancedAccuracyRetryCollect_countedMeasurable
            q I oracle (terminalVariance_pos' q)
              (measurable_uniformRatioWeight (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.proposalCap q
                (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.properStride q
                (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.retryLimit q
                (terminalVariance q)) (figureOneSampleCount q)).2 _)

/-- Retained-state cost interpreter for all Gaussian phases followed by the
terminal uniform phase. -/
noncomputable def figureOneFinalScheduledRetainedFullCostProgram
    (q : VolumeParams) (state : Option (AmbientSpace q.n)) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  (figureOneFinalScheduledRetainedGaussianChain q 0
    (terminalPhaseSteps q) state).bind
      (figureOneFinalScheduledRetainedTerminalProgram q)

theorem figureOneFinalScheduledRetainedFullCostProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedFullCostProgram q state).run oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedFullCostProgram q state).CountedStronglyMeasurable
        oracle.query := by
  have hgaussian :=
    figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
      q I oracle 0 (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  unfold figureOneFinalScheduledRetainedFullCostProgram
  constructor
  · exact MembershipOracleProgram.measurable_run_bind_param oracle.query
      (figureOneFinalScheduledRetainedGaussianChain q 0 (terminalPhaseSteps q))
      (fun z => figureOneFinalScheduledRetainedTerminalProgram q z.2)
      hgaussian.1 hgaussian.2 (hterminal.1.comp measurable_snd)
        (fun z => hterminal.2 z.2)
  · intro state
    exact (hgaussian.2 state).bind hterminal.2 hterminal.1

/-- Exact whole-run expected cost of the retained interpreter: the recursive
sum of all Gaussian phase costs plus the terminal phase cost. -/
theorem lintegral_figureOneFinalScheduledRetainedFullCostProgram_eq
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedFullCostProgram q state).run
          oracle.query)
      ∂((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I 0).map
          scheduledBalancedTraceRetainedOption)) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle := by
  let mu0 := (scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I 0).map
      scheduledBalancedTraceRetainedOption
  let gaussian := figureOneFinalScheduledRetainedGaussianChain q 0
    (terminalPhaseSteps q)
  let terminal := figureOneFinalScheduledRetainedTerminalProgram q
  have hgaussian :=
    figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
      q I oracle 0 (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have hgaussianCost : Measurable fun state =>
      countedQueryCost ((gaussian state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hgaussian.1
  have hterminalCost : Measurable fun state =>
      countedQueryCost ((terminal state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hterminal.1
  have hpoint : ∀ state,
      countedQueryCost (((gaussian state).bind terminal).run oracle.query) =
        countedQueryCost ((gaussian state).run oracle.query) +
          ∫⁻ next, countedQueryCost ((terminal next).run oracle.query)
            ∂((gaussian state).runEstimate oracle.query) := by
    intro state
    exact MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
      (gaussian state) terminal (hgaussian.2 state) hterminal.2 hterminal.1
  unfold figureOneFinalScheduledRetainedFullCostProgram
  change (∫⁻ state, countedQueryCost
      (((gaussian state).bind terminal).run oracle.query) ∂mu0) = _
  rw [lintegral_congr hpoint, lintegral_add_left hgaussianCost]
  have hgaussianEstimate : Measurable fun state =>
      (gaussian state).runEstimate oracle.query := by
    rw [show (fun state => (gaussian state).runEstimate oracle.query) =
        fun state => ((gaussian state).run oracle.query).map Prod.fst by
      funext state
      exact (gaussian state).runEstimate_eq_map_fst_run oracle.query
        (hgaussian.2 state).executionMeasurable]
    exact measurable_measure_map_param_variable hgaussian.1
      (fun state => MembershipOracleProgram.run_isProbabilityMeasure
        oracle.query (gaussian state) (hgaussian.2 state).executionMeasurable)
      (measurable_fst.comp measurable_snd)
  rw [← Measure.lintegral_bind hgaussianEstimate.aemeasurable
    hterminalCost.aemeasurable]
  rw [lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
    q I oracle 0 (terminalPhaseSteps q) (by omega)]
  have hout :=
    bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
      q I oracle 0 (terminalPhaseSteps q) (by omega)
  have hout' : mu0.bind (fun state =>
      (gaussian state).runEstimate oracle.query) =
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)).map
              scheduledBalancedTraceRetainedOption := by
    simpa only [mu0, gaussian, zero_add] using hout
  rw [hout']
  congr 1
  unfold figureOneFinalScheduledTerminalExpectedCost
  apply lintegral_congr
  intro state
  exact figureOneFinalScheduledRetainedTerminalProgram_cost q I oracle state

private theorem scheduledVarianceSegment_pos
    (q : VolumeParams) (offset steps : ℕ) :
    ∀ sigma2 ∈ scheduledVarianceSegment q offset steps, 0 < sigma2 := by
  intro sigma2 hsigma2
  rw [scheduledVarianceSegment, List.mem_ofFn'] at hsigma2
  obtain ⟨i, rfl⟩ := hsigma2
  exact scheduleValue_pos q _

@[simp] theorem figureOneFinalScheduledRetainedGaussianChain_none
    (q : VolumeParams) : ∀ phase steps,
    figureOneFinalScheduledRetainedGaussianChain q phase steps none =
      .pure none := by
  intro phase steps
  induction steps generalizing phase with
  | zero => rfl
  | succ steps ih =>
      simp only [figureOneFinalScheduledRetainedGaussianChain,
        figureOneFinalScheduledRetainedGaussianPhaseProgram]
      exact ih (phase + 1)

/-- Erasing all Gaussian ratio/product coordinates preserves the complete
expected query cost, pointwise in the initial point. -/
theorem figureOneFinalScheduledCoolingProduct_cost_eq_retainedChain
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps (point : AmbientSpace q.n),
    countedQueryCost
        ((coolingProduct
          (scheduledBalancedCoolingPrimitives
            figureOneFinalScheduledBalancedParameters) q
          (scheduledVarianceSegment q phase steps) point).run oracle.query) =
      countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q phase steps
          (some point)).run oracle.query) := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro point
      simp only [scheduledVarianceSegment_zero, coolingProduct,
        figureOneFinalScheduledRetainedGaussianChain]
      rw [MembershipOracleProgram.countedQueryCost_pure,
        MembershipOracleProgram.countedQueryCost_pure]
  | succ steps ih =>
      intro point
      let parameters := figureOneFinalScheduledBalancedParameters
      let sigma2 := scheduleValue q phase
      let tau2 := scheduleValue q (phase + 1)
      let rest := (scheduledVarianceSegment q (phase + 1) steps).tail
      let ratioProgram := scheduledBalancedCoolingRatioEstimate parameters q
        sigma2 tau2 point
      let tailCooling (nextPoint : AmbientSpace q.n) :=
        coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
          (scheduledVarianceSegment q (phase + 1) steps) nextPoint
      let retainedPhase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram q phase (some point)
      let retainedTail :=
        figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
      let multiply (ratio : ℝ) (tail : Option (ℝ × AmbientSpace q.n)) :=
        balancedCoolingProductCons ratio tail
      let actualNext : Option (ℝ × AmbientSpace q.n) →
          MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
        | none => .pure none
        | some value =>
            (tailCooling value.2).bind fun tail =>
              .pure (multiply value.1 tail)
      have hratio := scheduledBalancedCoolingRatioEstimate_countedMeasurable
        parameters q I oracle (scheduleValue_pos q phase) tau2
      have htail := scheduledBalancedCoolingProduct_countedMeasurable
        parameters q I oracle (scheduledVarianceSegment q (phase + 1) steps)
          (scheduledVarianceSegment_pos q (phase + 1) steps)
      have hmultiply : Measurable fun z :
          (ℝ × AmbientSpace q.n) × Option (ℝ × AmbientSpace q.n) =>
          multiply z.1.1 z.2 := by
        exact measurable_balancedCoolingProductCons.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have hsome := MembershipOracleProgram.countedMeasurable_bind_pure
        oracle.query (fun value : ℝ × AmbientSpace q.n =>
          tailCooling value.2)
        (fun z : (ℝ × AmbientSpace q.n) ×
          Option (ℝ × AmbientSpace q.n) => multiply z.1.1 z.2)
        (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
          hmultiply
      have hactualNextRun : Measurable fun result =>
          (actualNext result).run oracle.query := by
        convert Measurable.optionElim
          (Measure.dirac ((none : Option (ℝ × AmbientSpace q.n)), 0))
          hsome.1 using 1
        funext result
        cases result <;> rfl
      have hactualNext : ∀ result,
          (actualNext result).CountedStronglyMeasurable oracle.query := by
        intro result
        cases result with
        | none => trivial
        | some value => exact hsome.2 value
      have hretainedPhase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have hretainedTail :=
        figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
          q I oracle (phase + 1) steps
      have hactualForm :
          coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
              (scheduledVarianceSegment q phase (steps + 1)) point =
            ratioProgram.bind actualNext := by
        rw [scheduledVarianceSegment_succ]
        rw [scheduledVarianceSegment_eq_cons_head_tail q (phase + 1) steps]
        rw [coolingProduct]
        dsimp only [ratioProgram, actualNext, tailCooling, multiply,
          parameters, sigma2, tau2]
        congr 1
        funext result
        cases result with
        | none => rfl
        | some value =>
            rw [← scheduledVarianceSegment_eq_cons_head_tail
              q (phase + 1) steps]
            rcases value with ⟨ratio, nextPoint⟩
            simp only
            congr 1
            funext tail
            cases tail with
            | none => rfl
            | some value =>
                rcases value with ⟨product, lastPoint⟩
                rfl
      have hretainedForm :
          figureOneFinalScheduledRetainedGaussianChain q phase (steps + 1)
              (some point) = retainedPhase.bind retainedTail := by
        rfl
      rw [hactualForm, hretainedForm]
      rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
        ratioProgram actualNext (hratio.2 point) hactualNext hactualNextRun]
      rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
        retainedPhase retainedTail (hretainedPhase.2 (some point))
          hretainedTail.2 hretainedTail.1]
      have hsource : countedQueryCost (ratioProgram.run oracle.query) =
          countedQueryCost (retainedPhase.run oracle.query) := by
        rw [scheduledBalancedCoolingRatioEstimate_countedQueryCost_eq
          parameters q I oracle (scheduleValue_pos q phase) tau2 point]
        symm
        exact figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
          q I oracle phase (some point)
      rw [hsource]
      congr 1
      let futureCost : Option (AmbientSpace q.n) → ENNReal := fun state =>
        countedQueryCost ((retainedTail state).run oracle.query)
      have hfuture : Measurable futureCost :=
        (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
          hretainedTail.1
      have hnextCost : ∀ result,
          countedQueryCost ((actualNext result).run oracle.query) =
            futureCost (optionSnd result) := by
        intro result
        cases result with
        | none =>
            simp only [actualNext, futureCost, optionSnd]
            rw [show retainedTail none =
                (MembershipOracleProgram.pure none :
                  MembershipOracleProgram q.n (Option (AmbientSpace q.n))) from
              figureOneFinalScheduledRetainedGaussianChain_none q
                (phase + 1) steps]
            rw [MembershipOracleProgram.countedQueryCost_pure,
              MembershipOracleProgram.countedQueryCost_pure]
        | some value =>
            unfold actualNext
            rw [MembershipOracleProgram.countedQueryCost_bind_pure_eq
              oracle.query (tailCooling value.2) (multiply value.1)]
            · exact ih (phase + 1) value.2
            · exact (measurable_balancedCoolingProductCons (n := q.n)).comp
                (measurable_const.prodMk measurable_id)
            · exact htail.2 value.2
      rw [lintegral_congr hnextCost]
      rw [scheduledBalancedCoolingRatioEstimate_runEstimate_eq_transitionLaw
        parameters q I oracle (scheduleValue_pos q phase) tau2 point]
      rw [lintegral_optionSnd_scheduledRatioTransition_eq_retainedKernel
        q I phase point futureCost hfuture]
      have hretainedLaw :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
          q I oracle phase (some point)
      rw [hretainedLaw]

theorem optionSnd_balancedCoolingHistoryOutput_traceProject
    (trace : ScheduledBalancedCoolingTrace n) :
    optionSnd
        (balancedCoolingHistoryOutput
          (scheduledBalancedCoolingTraceProject trace)) =
      scheduledBalancedTraceRetainedOption trace := by
  rcases trace with ⟨history, live⟩
  cases live <;> rfl

/-- After averaging over the exact truncated-Gaussian initializer, the
endpoint of the executable Gaussian cooling product is the retained marginal
of the loss-preserving chronological trace. -/
theorem map_bind_figureOneFinalScheduledCoolingProduct_optionSnd_eq_trace
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind fun point =>
      (coolingProduct
        (scheduledBalancedCoolingPrimitives
          figureOneFinalScheduledBalancedParameters) q
        (explicitVolumeCoolingSchedule q).variances point).runEstimate
          oracle.query).map optionSnd) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q)).map
            scheduledBalancedTraceRetainedOption := by
  let target : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let coolingLaw (point : AmbientSpace q.n) :=
    (coolingProduct
      (scheduledBalancedCoolingPrimitives
        figureOneFinalScheduledBalancedParameters) q
      (explicitVolumeCoolingSchedule q).variances point).runEstimate oracle.query
  let fromPoint := scheduledBalancedForwardHistoryLawFromPoint
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  have hcooling := scheduledExecutableCoolingProduct_measurable_and_strong
    figureOneFinalScheduledBalancedParameters q I oracle
      (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hfromPoint : Measurable fromPoint := by
    unfold fromPoint scheduledBalancedForwardHistoryLawFromPoint
    exact (iteratedKernelLaw_dirac_measurable_and_probability
      (scheduledBalancedForwardPhaseKernel
        figureOneFinalScheduledBalancedParameters q I)
      (fun phase =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          figureOneFinalScheduledBalancedParameters q I phase).1)
      (fun phase history =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          figureOneFinalScheduledBalancedParameters q I phase).2 history)
      (terminalPhaseSteps q)).1.comp measurable_balancedCoolingInitialHistory
  have hpoint : ∀ point, (coolingLaw point).map optionSnd =
      (fromPoint point).map
        (optionSnd ∘ balancedCoolingHistoryOutput) := by
    intro point
    unfold coolingLaw
    rw [scheduledExecutableFigureOneCoolingProduct_runEstimate_eq_history_map
      figureOneFinalScheduledBalancedParameters q I oracle point]
    rw [map_scheduledExecutableFigureOneCoolingHistory_output_eq_forward]
    rw [Measure.map_map measurable_optionSnd
      measurable_balancedCoolingHistoryOutput]
  have hcoolingProb : ∀ point, IsProbabilityMeasure (coolingLaw point) := by
    intro point
    exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      (hcooling.2 point).estimateMeasurable
  calc
    (target.bind coolingLaw).map optionSnd =
        target.bind fun point => (coolingLaw point).map optionSnd :=
      map_bind_eq_bind_map_of_measurable target hcooling.1 measurable_optionSnd
    _ = target.bind fun point =>
        (fromPoint point).map
          (optionSnd ∘ balancedCoolingHistoryOutput) := by
      apply Measure.bind_congr_right
      filter_upwards with point
      exact hpoint point
    _ = (target.bind fromPoint).map
          (optionSnd ∘ balancedCoolingHistoryOutput) :=
      (map_bind_eq_bind_map_of_measurable target hfromPoint
        (measurable_optionSnd.comp
          measurable_balancedCoolingHistoryOutput)).symm
    _ = (scheduledBalancedForwardHistoryLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)).map
          (optionSnd ∘ balancedCoolingHistoryOutput) := by
      rw [scheduledBalancedForwardHistoryLaw_bind_fromPoint]
    _ = ((scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)).map
          scheduledBalancedCoolingTraceProject).map
            (optionSnd ∘ balancedCoolingHistoryOutput) := by
      rw [map_scheduledBalancedForwardTraceLaw_project]
    _ = (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)).map
          ((optionSnd ∘ balancedCoolingHistoryOutput) ∘
            scheduledBalancedCoolingTraceProject) := by
      rw [Measure.map_map
        (measurable_optionSnd.comp measurable_balancedCoolingHistoryOutput)
        measurable_scheduledBalancedCoolingTraceProject]
    _ = _ := by
      apply Measure.map_congr
      filter_upwards with trace
      exact optionSnd_balancedCoolingHistoryOutput_traceProject trace

/-- The public scalar terminal wrapper, isolated from the Gaussian product. -/
noncomputable def figureOneFinalScheduledScalarTerminalTail
    (q : VolumeParams) : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ
  | none => .pure 0
  | some (gaussianProduct, lastPoint) =>
      (scheduledBalancedCoolingUniformRatioEstimate
        figureOneFinalScheduledBalancedParameters q
        (terminalVariance q) lastPoint).bind fun finalRatio =>
          .pure <| match finalRatio with
          | some uniformRatio =>
              initialGaussianIntegral q * gaussianProduct * uniformRatio
          | none => 0

theorem figureOneFinalScheduledScalarTerminalTail_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun product =>
      (figureOneFinalScheduledScalarTerminalTail q product).run oracle.query) ∧
    ∀ product,
      (figureOneFinalScheduledScalarTerminalTail q product).CountedStronglyMeasurable
        oracle.query := by
  let uniformProgram (value : ℝ × AmbientSpace q.n) :=
    scheduledBalancedCoolingUniformRatioEstimate
      figureOneFinalScheduledBalancedParameters q (terminalVariance q) value.2
  let finish (z : (ℝ × AmbientSpace q.n) × Option ℝ) : ℝ :=
    match z.2 with
    | some uniformRatio => initialGaussianIntegral q * z.1.1 * uniformRatio
    | none => 0
  have huniform := scheduledBalancedCoolingUniformRatioEstimate_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
      (terminalVariance_pos' q)
  have hfinish : Measurable finish := by
    have hnone : Measurable fun _ : ℝ × AmbientSpace q.n => (0 : ℝ) :=
      measurable_const
    have hsome : Measurable fun z : (ℝ × AmbientSpace q.n) × ℝ =>
        initialGaussianIntegral q * z.1.1 * z.2 := by fun_prop
    convert Measurable.optionElimParam hnone hsome using 1
    funext z
    rcases z with ⟨p, value⟩
    cases value <;> rfl
  have hsome := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query uniformProgram finish
      (huniform.1.comp measurable_snd)
      (fun value => huniform.2 value.2) hfinish
  constructor
  · convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hsome.1 using 1
    funext product
    cases product <;> rfl
  · intro product
    cases product with
    | none => trivial
    | some value => exact hsome.2 value

/-- The scalar/product coordinates in the terminal wrapper are query-free;
its cost depends only on the optional retained endpoint. -/
theorem figureOneFinalScheduledScalarTerminalTail_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (product : Option (ℝ × AmbientSpace q.n)) :
    countedQueryCost
        ((figureOneFinalScheduledScalarTerminalTail q product).run oracle.query) =
      countedQueryCost
        ((figureOneFinalScheduledRetainedTerminalProgram q
          (optionSnd product)).run oracle.query) := by
  cases product with
  | none =>
      simp only [figureOneFinalScheduledScalarTerminalTail, optionSnd,
        figureOneFinalScheduledRetainedTerminalProgram]
      rw [MembershipOracleProgram.countedQueryCost_pure,
        MembershipOracleProgram.countedQueryCost_pure]
  | some value =>
      rcases value with ⟨gaussianProduct, lastPoint⟩
      unfold figureOneFinalScheduledScalarTerminalTail
      rw [MembershipOracleProgram.countedQueryCost_bind_pure_eq]
      · rw [scheduledBalancedCoolingUniformRatioEstimate_countedQueryCost_eq
          figureOneFinalScheduledBalancedParameters q I oracle
            (terminalVariance_pos' q) lastPoint]
        rw [scheduledBalancedCoolingUniformEstimateWithState_countedQueryCost_eq
          figureOneFinalScheduledBalancedParameters q I oracle
            (terminalVariance_pos' q) lastPoint]
        symm
        exact figureOneFinalScheduledRetainedTerminalProgram_cost
          q I oracle (some lastPoint)
      · have hnone : Measurable fun _ : Unit => (0 : ℝ) := measurable_const
        have hsome : Measurable fun z : Unit × ℝ =>
            initialGaussianIntegral q * gaussianProduct * z.2 := by fun_prop
        have hparam : Measurable fun z : Unit × Option ℝ =>
            match z.2 with
            | some uniformRatio =>
                initialGaussianIntegral q * gaussianProduct * uniformRatio
            | none => 0 := by
          convert Measurable.optionElimParam hnone hsome using 1
          funext z
          rcases z with ⟨u, result⟩
          cases result <;> rfl
        exact hparam.comp
          ((show Measurable fun result : Option ℝ => ((() : Unit), result) from
            measurable_const.prodMk measurable_id))
      · exact (scheduledBalancedCoolingUniformRatioEstimate_countedMeasurable
          figureOneFinalScheduledBalancedParameters q I oracle
            (terminalVariance_pos' q)).2 lastPoint

/-- Averaging the executable Gaussian cooling cost over the normalized initial
law gives exactly the retained chronological Gaussian cost sum. -/
theorem lintegral_figureOneFinalScheduledCoolingProduct_cost_eq_costTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ point, countedQueryCost
        ((coolingProduct
          (scheduledBalancedCoolingPrimitives
            figureOneFinalScheduledBalancedParameters) q
          (explicitVolumeCoolingSchedule q).variances point).run oracle.query)
      ∂(truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q))) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
        (terminalPhaseSteps q) := by
  let target : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let retained := figureOneFinalScheduledRetainedGaussianChain q 0
    (terminalPhaseSteps q)
  have hretained := figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
    q I oracle 0 (terminalPhaseSteps q)
  have hretainedCost : Measurable fun state =>
      countedQueryCost ((retained state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hretained.1
  have hmu0 :
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I 0).map
          scheduledBalancedTraceRetainedOption = target.map some := by
    simpa only [scheduledBalancedForwardTraceLaw, iteratedKernelLaw, target] using
      map_scheduledBalancedInitialTrace_retainedOption q I
  calc
    _ = ∫⁻ point, countedQueryCost ((retained (some point)).run oracle.query)
          ∂target := by
      apply lintegral_congr
      intro point
      rw [explicitScheduleVariances_eq_scheduledVarianceSegment]
      exact figureOneFinalScheduledCoolingProduct_cost_eq_retainedChain
        q I oracle 0 (terminalPhaseSteps q) point
    _ = ∫⁻ state, countedQueryCost ((retained state).run oracle.query)
          ∂target.map some := by
      symm
      simpa only [Function.comp_apply] using
        lintegral_map hretainedCost measurable_some
    _ = ∫⁻ state, countedQueryCost ((retained state).run oracle.query)
          ∂((scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I 0).map
              scheduledBalancedTraceRetainedOption) := by rw [hmu0]
    _ = _ := lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
      q I oracle 0 (terminalPhaseSteps q) (by omega)

/-- Averaging the terminal wrapper cost over the executable cooling endpoint
law gives exactly the terminal retained-state cost. -/
theorem lintegral_figureOneFinalScheduledTerminalTail_cost_eq
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ point,
        (∫⁻ product, countedQueryCost
            ((figureOneFinalScheduledScalarTerminalTail q product).run
              oracle.query)
          ∂(coolingProduct
            (scheduledBalancedCoolingPrimitives
              figureOneFinalScheduledBalancedParameters) q
            (explicitVolumeCoolingSchedule q).variances point).runEstimate
              oracle.query)
      ∂(truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q))) =
      figureOneFinalScheduledTerminalExpectedCost q I oracle := by
  let target : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let cooling (point : AmbientSpace q.n) :=
    coolingProduct
      (scheduledBalancedCoolingPrimitives
        figureOneFinalScheduledBalancedParameters) q
      (explicitVolumeCoolingSchedule q).variances point
  let tail := figureOneFinalScheduledScalarTerminalTail q
  let futureCost (state : Option (AmbientSpace q.n)) :=
    countedQueryCost
      ((figureOneFinalScheduledRetainedTerminalProgram q state).run oracle.query)
  have hcooling := scheduledBalancedCoolingProduct_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
      (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have htail := figureOneFinalScheduledScalarTerminalTail_countedMeasurable
    q I oracle
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have htailCost : Measurable fun product =>
      countedQueryCost ((tail product).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      htail.1
  have hfutureCost : Measurable futureCost :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hterminal.1
  have hcoolingEstimate : Measurable fun point =>
      (cooling point).runEstimate oracle.query := by
    rw [show (fun point => (cooling point).runEstimate oracle.query) =
        fun point => ((cooling point).run oracle.query).map Prod.fst by
      funext point
      exact (cooling point).runEstimate_eq_map_fst_run oracle.query
        (hcooling.2 point).executionMeasurable]
    exact measurable_measure_map_param_variable hcooling.1
      (fun point => MembershipOracleProgram.run_isProbabilityMeasure
        oracle.query (cooling point) (hcooling.2 point).executionMeasurable)
      (measurable_fst.comp measurable_snd)
  calc
    _ = ∫⁻ product, countedQueryCost ((tail product).run oracle.query)
          ∂(target.bind fun point => (cooling point).runEstimate oracle.query) := by
      symm
      exact Measure.lintegral_bind hcoolingEstimate.aemeasurable
        htailCost.aemeasurable
    _ = ∫⁻ product, futureCost (optionSnd product)
          ∂(target.bind fun point => (cooling point).runEstimate oracle.query) := by
      apply lintegral_congr
      intro product
      exact figureOneFinalScheduledScalarTerminalTail_cost q I oracle product
    _ = ∫⁻ state, futureCost state
          ∂(target.bind fun point =>
            (cooling point).runEstimate oracle.query).map optionSnd := by
      symm
      simpa only [Function.comp_apply] using
        lintegral_map hfutureCost measurable_optionSnd
    _ = ∫⁻ state, futureCost state
          ∂(scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I
              (terminalPhaseSteps q)).map
                scheduledBalancedTraceRetainedOption := by
      rw [map_bind_figureOneFinalScheduledCoolingProduct_optionSnd_eq_trace
        q I oracle]
    _ = _ := by
      unfold figureOneFinalScheduledTerminalExpectedCost futureCost
      apply lintegral_congr
      intro state
      exact figureOneFinalScheduledRetainedTerminalProgram_cost q I oracle state

/-- The complete executable post-initial continuation has exactly the retained
chronological expected cost: all estimator/product coordinates are query-free. -/
theorem lintegral_scheduledBalancedFigureOnePointContinuation_cost_eq
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ point, countedQueryCost
        ((scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point).run oracle.query)
      ∂(truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q))) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle := by
  let cooling (point : AmbientSpace q.n) :=
    coolingProduct
      (scheduledBalancedCoolingPrimitives
        figureOneFinalScheduledBalancedParameters) q
      (explicitVolumeCoolingSchedule q).variances point
  let tail := figureOneFinalScheduledScalarTerminalTail q
  have hcooling := scheduledBalancedCoolingProduct_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
      (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have htail := figureOneFinalScheduledScalarTerminalTail_countedMeasurable
    q I oracle
  have hcoolingCost : Measurable fun point =>
      countedQueryCost ((cooling point).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hcooling.1
  have hpoint : ∀ point,
      countedQueryCost
          ((scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).run
              oracle.query) =
        countedQueryCost ((cooling point).run oracle.query) +
          ∫⁻ product, countedQueryCost ((tail product).run oracle.query)
            ∂(cooling point).runEstimate oracle.query := by
    intro point
    have hprogram :
        scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point =
          (cooling point).bind tail := by
      rfl
    rw [hprogram]
    exact MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
      (cooling point) tail (hcooling.2 point) htail.2 htail.1
  rw [lintegral_congr hpoint, lintegral_add_left hcoolingCost]
  rw [lintegral_figureOneFinalScheduledCoolingProduct_cost_eq_costTail
    q I oracle]
  rw [lintegral_figureOneFinalScheduledTerminalTail_cost_eq q I oracle]

#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
#print axioms lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
#print axioms bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
#print axioms figureOneFinalScheduledRetainedTerminalProgram_cost
#print axioms lintegral_figureOneFinalScheduledRetainedFullCostProgram_eq
#print axioms figureOneFinalScheduledCoolingProduct_cost_eq_retainedChain
#print axioms map_bind_figureOneFinalScheduledCoolingProduct_optionSnd_eq_trace
#print axioms figureOneFinalScheduledScalarTerminalTail_cost
#print axioms lintegral_figureOneFinalScheduledCoolingProduct_cost_eq_costTail
#print axioms lintegral_figureOneFinalScheduledTerminalTail_cost_eq
#print axioms lintegral_scheduledBalancedFigureOnePointContinuation_cost_eq

end ArlibCommunity.Algorithms.CV18
