/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedChronologicalContinuation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostChain
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortAccuracy

/-! # Exact ideal-prefix inputs for counted scheduled phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

/-- The exact retained endpoint marginal from which chronological phase
`phase` is charged.  Phase zero starts from target zero; every later phase
starts from the preceding accepted target. -/
noncomputable def figureOneFinalScheduledIdealPhaseStart
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (Option (AmbientSpace q.n)) :=
  if phase = 0 then (figureOneScheduledAcceptedTargetAt q I 0).map some
  else (figureOneScheduledAcceptedTargetAt q I (phase - 1)).map some

theorem figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (figureOneFinalScheduledIdealPhaseStart q I phase) := by
  unfold figureOneFinalScheduledIdealPhaseStart
  split_ifs
  · let _ : IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I 0) :=
      figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  · let _ : IsProbabilityMeasure
        (figureOneScheduledAcceptedTargetAt q I (phase - 1)) :=
      figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

private theorem finalIdealWarmConstant_le_ninetySix (q : VolumeParams) :
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 96 := by
  calc
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 8 * 12 := by
      gcongr
      rw [← ENNReal.ofReal_ofNat 12]
      exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_le_twelve q)
    _ = 96 := by norm_num

/-- The contracted live part of every exact ideal phase start has the one
constant warmness used by the cap-independent phase-cost estimate. -/
theorem figureOneFinalScheduledIdealPhaseStart_scaled_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let target : Measure (AmbientSpace q.n) :=
      if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
      else figureOneScheduledAcceptedTargetAt q I (phase - 1)
    IsWarm (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase) := by
  dsimp only
  by_cases hzero : phase = 0
  · subst phase
    simp only [if_pos]
    have hwarm8 := initialContractedAcceptedTarget_isWarm_eight q I
    apply hwarm8.mono
    have hC : (1 : ENNReal) ≤ ENNReal.ofReal (speedyAdjacentWarmConstant q) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_one_le q)
    calc
      (8 : ENNReal) = 8 * 1 := by norm_num
      _ ≤ 8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) := by gcongr
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous

/-- A Gaussian phase run from its exact chronological ideal marginal incurs
only the warm-start term.  In particular there is no local-cap multiple of a
retained approximation error. -/
theorem figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∂figureOneFinalScheduledIdealPhaseStart q I phase) ≤
      ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase)) : ℕ) : ENNReal) := by
  let target : Measure (AmbientSpace q.n) :=
    if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
    else figureOneScheduledAcceptedTargetAt q I (phase - 1)
  let _ : IsProbabilityMeasure target := by
    dsimp only [target]
    split_ifs
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  have hideal : figureOneFinalScheduledIdealPhaseStart q I phase =
      target.map some := by
    unfold figureOneFinalScheduledIdealPhaseStart target
    split_ifs <;> rfl
  have hwarm := figureOneFinalScheduledIdealPhaseStart_scaled_isWarm q I phase
  have hbound :=
    lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
      q I oracle (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledIdealPhaseStart q I phase) target
      (by rw [hideal]; exact MeasureLeUpTo.refl (target.map some))
      hwarm (finalIdealWarmConstant_le_ninetySix q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
      (figureOneScheduledCorrectedProperStride_pos q (scheduleValue q phase)
        (figureOneSafeRetryCount q - 1))
  have hcost : (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∂figureOneFinalScheduledIdealPhaseStart q I phase) =
      ∫⁻ state, match state with
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
              (accuracyScaleFactor q • point)).run oracle.query)
        ∂figureOneFinalScheduledIdealPhaseStart q I phase := by
    apply lintegral_congr
    intro state
    exact figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
      q I oracle phase state
  rw [hcost]
  exact hbound.trans (by push_cast; simp [mul_comm, mul_left_comm, mul_assoc])

/-- One exact ideal start followed by the executable retained phase has the
next accepted-target marginal up to exactly the per-sample transition loss. -/
theorem figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    MeasureLeUpTo
      ((figureOneFinalScheduledIdealPhaseStart q I phase).bind fun state =>
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
          oracle.query)
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      (figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q) := by
  let target : Measure (AmbientSpace q.n) :=
    if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
    else figureOneScheduledAcceptedTargetAt q I (phase - 1)
  let _ : IsProbabilityMeasure target := by
    dsimp only [target]
    split_ifs
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  have hideal : figureOneFinalScheduledIdealPhaseStart q I phase =
      target.map some := by
    unfold figureOneFinalScheduledIdealPhaseStart target
    split_ifs <;> rfl
  have hwarm := figureOneFinalScheduledIdealPhaseStart_scaled_isWarm q I phase
  have hwarm' : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q phase))
        (figureOneScheduledProposalRadius q (scheduleValue q phase))
        (scheduleValue q phase)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    simpa [figureOneScheduledSpeedyPiAt] using hwarm
  have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q phase) := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hphase := bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
    q I (scheduleValue_pos q phase)
    (measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1)))
    (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
    (figureOneFinalScheduledIdealPhaseStart q I phase) target
    (priorError := 0)
    (by rw [hideal]; exact MeasureLeUpTo.refl (target.map some)) hwarm'
  have hrun : (fun state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
        oracle.query) =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) := by
    funext state
    exact figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
      q I oracle phase state
  rw [hrun]
  simpa [figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt, Nat.sub_add_cancel hcount] using hphase

/-- The paper-faithful aborting initial sample differs from the normalized
truncated Gaussian retained law only by the rejected Gaussian tail mass. -/
theorem figureOneAbortInitialRetained_leUpTo_truncated
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      ((initialGaussianSamplingMeasure q).map (initialTruncatedOption q I))
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some)
      (ENNReal.ofReal (q.eps / 64)) := by
  let actual := (initialGaussianSamplingMeasure q).map
    (initialTruncatedOption q I)
  let target := (truncatedGaussianProbability q I (initialVariance q)
    (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some
  let _ : IsProbabilityMeasure actual :=
    Measure.isProbabilityMeasure_map
      (measurable_initialTruncatedOption q I).aemeasurable
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply MeasureLeUpTo.of_tvLe
  apply Arlib.tvLe_of_forall_le
  intro event hevent
  have h := initialTruncatedOption_bind_apply_le q I
    (Measure.dirac (none : Option (AmbientSpace q.n))) inferInstance
    (fun point => Measure.dirac (some point))
    (Measure.measurable_dirac.comp measurable_some)
    (fun _ => inferInstance) event hevent
  have hleft :
      ((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind (fun initialPoint =>
          match initialPoint with
          | none => Measure.dirac none
          | some point => Measure.dirac (some point)) = actual := by
    have hkernel : (fun initialPoint : Option (AmbientSpace q.n) =>
        match initialPoint with
        | none => Measure.dirac none
        | some point => Measure.dirac (some point)) = Measure.dirac := by
      funext initialPoint
      cases initialPoint <;> rfl
    rw [hkernel, Measure.bind_dirac]
  have hright :
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          (fun point => Measure.dirac (some point)) = target := by
    rw [Measure.bind_dirac_eq_map _ measurable_some]
  change actual event ≤ target event + ENNReal.ofReal (q.eps / 64)
  calc
    actual event =
        (((initialGaussianSamplingMeasure q).map
          (initialTruncatedOption q I)).bind (fun initialPoint =>
            match initialPoint with
            | none => Measure.dirac none
            | some point => Measure.dirac (some point))) event := by
      rw [hleft]
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
            (fun point => Measure.dirac (some point))) event +
          ENNReal.ofReal (q.eps / 64) := h
    _ = target event + ENNReal.ofReal (q.eps / 64) := by
      rw [hright]

/-- The counted aborting initial sampler has the exact first ideal marginal
up to the one truncation-tail loss and one stationary-target loss. -/
theorem figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    MeasureLeUpTo ((figureOneAbortInitialSample q).run oracle.query).fst
      (figureOneFinalScheduledIdealPhaseStart q I 0)
      (ENNReal.ofReal (q.eps / 64) +
        scheduledBalancedStationaryTargetError q) := by
  have habort := figureOneAbortInitialRetained_leUpTo_truncated q I
  have hstationary := scheduledBalancedInitialRetained_leUpTo_target q I
  rw [map_scheduledBalancedInitialTrace_retainedOption] at hstationary
  have hrun : ((figureOneAbortInitialSample q).run oracle.query).fst =
      (figureOneAbortInitialSample q).runEstimate oracle.query := by
    exact ((figureOneAbortInitialSample q).runEstimate_eq_map_fst_run
      oracle.query
      (figureOneAbortInitialSample_countedStronglyMeasurable
        q I oracle).executionMeasurable).symm
  rw [hrun, runEstimate_figureOneAbortInitialSample q I oracle]
  simpa [figureOneFinalScheduledIdealPhaseStart] using
    habort.trans hstationary

/-- The counted transition kernel for chronological retained Gaussian
phases. -/
noncomputable def figureOneFinalScheduledGaussianCountedKernel
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool) (phase : ℕ) :=
  countedContinuation oracle
    (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)

/-- Forward-associated executable prefix.  This presentation is
definitionally aligned with `iteratedKernelLaw`; later associativity can
identify it with the tail-recursive Figure-1 presentation. -/
noncomputable def figureOneFinalScheduledRetainedGaussianPrefixProgram
    (q : VolumeParams) : ℕ →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | 0 => figureOneAbortInitialSample q
  | steps + 1 =>
      (figureOneFinalScheduledRetainedGaussianPrefixProgram q steps).bind
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q steps)

theorem figureOneFinalScheduledRetainedGaussianPrefixProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ steps,
      (figureOneFinalScheduledRetainedGaussianPrefixProgram q steps).CountedStronglyMeasurable
        oracle.query := by
  intro steps
  induction steps with
  | zero =>
      exact figureOneAbortInitialSample_countedStronglyMeasurable q I oracle
  | succ steps ih =>
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle steps
      unfold figureOneFinalScheduledRetainedGaussianPrefixProgram
      exact ih.bind hphase.2 hphase.1

/-- Exact counted law of the forward executable Gaussian prefix. -/
theorem figureOneFinalScheduledRetainedGaussianPrefixProgram_run
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ steps,
      (figureOneFinalScheduledRetainedGaussianPrefixProgram q steps).run
          oracle.query =
        iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          ((figureOneAbortInitialSample q).run oracle.query) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hprefix :=
        figureOneFinalScheduledRetainedGaussianPrefixProgram_countedMeasurable
          q I oracle steps
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle steps
      unfold figureOneFinalScheduledRetainedGaussianPrefixProgram
      rw [MembershipOracleProgram.run_bind_counted oracle.query _ _
        hprefix hphase.2 hphase.1, ih]
      rfl

/-- Appending the chronologically next retained phase to a retained tail
chain extends that chain by one phase. -/
theorem figureOneFinalScheduledRetainedGaussianChain_bind_next
    (q : VolumeParams) : ∀ phase steps
      (state : Option (AmbientSpace q.n)),
      (figureOneFinalScheduledRetainedGaussianChain q phase steps state).bind
          (figureOneFinalScheduledRetainedGaussianPhaseProgram q
            (phase + steps)) =
        figureOneFinalScheduledRetainedGaussianChain q phase (steps + 1)
          state := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro state
      simp only [figureOneFinalScheduledRetainedGaussianChain, Nat.add_zero]
      exact (MembershipOracleProgram.bind_pure_right_cv18
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state)).symm
  | succ steps ih =>
      intro state
      simp only [figureOneFinalScheduledRetainedGaussianChain]
      rw [MembershipOracleProgram.bind_assoc_counted_cv18]
      congr 1
      funext nextState
      have hindex : phase + (steps + 1) = (phase + 1) + steps := by omega
      rw [hindex]
      exact ih (phase + 1) nextState

/-- The forward-associated retained Gaussian prefix is the same oracle
program as the initial sampler followed by the tail-recursive retained
Gaussian chain. -/
theorem figureOneFinalScheduledRetainedGaussianPrefixProgram_eq_bind_chain
    (q : VolumeParams) : ∀ steps,
      figureOneFinalScheduledRetainedGaussianPrefixProgram q steps =
        (figureOneAbortInitialSample q).bind
          (figureOneFinalScheduledRetainedGaussianChain q 0 steps) := by
  intro steps
  induction steps with
  | zero =>
      simp only [figureOneFinalScheduledRetainedGaussianPrefixProgram,
        figureOneFinalScheduledRetainedGaussianChain]
      exact (MembershipOracleProgram.bind_pure_right_cv18
        (figureOneAbortInitialSample q)).symm
  | succ steps ih =>
      simp only [figureOneFinalScheduledRetainedGaussianPrefixProgram]
      rw [ih, MembershipOracleProgram.bind_assoc_counted_cv18]
      congr 1
      funext state
      simpa using
        figureOneFinalScheduledRetainedGaussianChain_bind_next q 0 steps state

/-- Erasing the ratio coordinate after one executable Gaussian estimator
gives exactly the retained phase's full result-and-count law. -/
theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_run_eq_map_ratio
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (point : AmbientSpace q.n) :
    (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
        (some point)).run oracle.query =
      ((scheduledBalancedCoolingRatioEstimate
        figureOneFinalScheduledBalancedParameters q
        (scheduleValue q phase) (scheduleValue q (phase + 1)) point).run
          oracle.query).map fun outcome => (optionSnd outcome.1, outcome.2) := by
  let raw := scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
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
  have hraw := (scheduledBalancedAccuracyRetryCollect_countedMeasurable
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
  have hretained :
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
          (some point)).run oracle.query =
        (raw.run oracle.query).map fun outcome =>
          (optionSnd outcome.1, outcome.2) := by
    unfold figureOneFinalScheduledRetainedGaussianPhaseProgram raw
    exact MembershipOracleProgram.run_bind_pure_eq_map oracle.query _
      optionSnd measurable_optionSnd hraw
  have hratio :
      (scheduledBalancedCoolingRatioEstimate
        figureOneFinalScheduledBalancedParameters q
        (scheduleValue q phase) (scheduleValue q (phase + 1)) point).run
          oracle.query =
        (raw.run oracle.query).map fun outcome =>
          (balancedCoolingAverage
            (figureOnePhaseSampleCount q (scheduleValue q phase)) outcome.1,
            outcome.2) := by
    unfold scheduledBalancedCoolingRatioEstimate raw
    exact MembershipOracleProgram.run_bind_pure_eq_map oracle.query _
      (balancedCoolingAverage
        (figureOnePhaseSampleCount q (scheduleValue q phase)))
      (measurable_balancedCoolingAverage _) hraw
  rw [hretained, hratio, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards with outcome
    simp only [Function.comp_apply]
    rw [optionSnd_balancedCoolingAverage]
  · exact (measurable_optionSnd.comp measurable_fst).prodMk measurable_snd
  · exact ((measurable_balancedCoolingAverage _).comp measurable_fst).prodMk
      measurable_snd

/-- Erasing every ratio/product coordinate from a Gaussian cooling block
preserves its complete endpoint-and-query-count law. -/
theorem figureOneFinalScheduledRetainedGaussianChain_run_eq_map_coolingProduct
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps (point : AmbientSpace q.n),
      (figureOneFinalScheduledRetainedGaussianChain q phase steps
          (some point)).run oracle.query =
        ((coolingProduct
          (scheduledBalancedCoolingPrimitives
            figureOneFinalScheduledBalancedParameters) q
          (scheduledVarianceSegment q phase steps) point).run
            oracle.query).map fun outcome =>
              (optionSnd outcome.1, outcome.2) := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro point
      simp only [scheduledVarianceSegment_zero, coolingProduct,
        figureOneFinalScheduledRetainedGaussianChain,
        MembershipOracleProgram.run]
      rw [Measure.map_dirac'
        (f := fun outcome : Option (ℝ × AmbientSpace q.n) × ℕ =>
          (optionSnd outcome.1, outcome.2))
        ((measurable_optionSnd.comp measurable_fst).prodMk measurable_snd)]
      rfl
  | succ steps ih =>
      intro point
      let parameters := figureOneFinalScheduledBalancedParameters
      let sigma2 := scheduleValue q phase
      let tau2 := scheduleValue q (phase + 1)
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
          (by
            intro variance hvariance
            rw [scheduledVarianceSegment, List.mem_ofFn'] at hvariance
            obtain ⟨i, rfl⟩ := hvariance
            exact scheduleValue_pos q _)
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
      have hnext : ∀ result,
          (retainedTail (optionSnd result)).run oracle.query =
            ((actualNext result).run oracle.query).map fun outcome =>
              (optionSnd outcome.1, outcome.2) := by
        intro result
        cases result with
        | none =>
            change (retainedTail none).run oracle.query =
              ((actualNext none).run oracle.query).map fun outcome =>
                (optionSnd outcome.1, outcome.2)
            dsimp only [retainedTail, actualNext]
            rw [figureOneFinalScheduledRetainedGaussianChain_none q
              (phase + 1) steps]
            simp only [MembershipOracleProgram.run]
            rw [Measure.map_dirac'
              (f := fun outcome : Option (ℝ × AmbientSpace q.n) × ℕ =>
                (optionSnd outcome.1, outcome.2))
              ((measurable_optionSnd.comp measurable_fst).prodMk
                measurable_snd)]
            rfl
        | some value =>
            rcases value with ⟨ratio, nextPoint⟩
            change (retainedTail (some nextPoint)).run oracle.query =
              ((actualNext (some (ratio, nextPoint))).run oracle.query).map
                fun outcome => (optionSnd outcome.1, outcome.2)
            dsimp only [retainedTail, actualNext]
            have htailRun := htail.2 nextPoint
            have hpure := MembershipOracleProgram.run_bind_pure_eq_map
              oracle.query (tailCooling nextPoint) (multiply ratio)
              (measurable_balancedCoolingProductCons.comp
                (measurable_const.prodMk measurable_id)) htailRun
            rw [ih (phase + 1) nextPoint, hpure, Measure.map_map]
            · apply Measure.map_congr
              filter_upwards with outcome
              rcases outcome with ⟨tail, count⟩
              cases tail with
              | none => rfl
              | some value =>
                  rcases value with ⟨product, lastPoint⟩
                  rfl
            · exact (measurable_optionSnd.comp measurable_fst).prodMk
                measurable_snd
            · exact ((measurable_balancedCoolingProductCons.comp
                (measurable_const.prodMk measurable_id)).comp
                  measurable_fst).prodMk measurable_snd
      have hcompose :=
        MembershipOracleProgram.map_bind_countedContinuation_simulation
          oracle.query (ratioProgram.run oracle.query)
          optionSnd measurable_optionSnd optionSnd measurable_optionSnd
          actualNext retainedTail hactualNextRun hactualNext
          hretainedTail.1 hretainedTail.2 hnext
      rw [hretainedForm,
        MembershipOracleProgram.run_bind_counted oracle.query _ _
          (hretainedPhase.2 (some point)) hretainedTail.2 hretainedTail.1,
        figureOneFinalScheduledRetainedGaussianPhaseProgram_run_eq_map_ratio
          q I oracle phase point]
      rw [hactualForm,
        MembershipOracleProgram.run_bind_counted oracle.query _ _
          (hratio.2 point) hactualNext hactualNextRun]
      exact hcompose

/-- Retaining or forgetting the terminal phase's estimator coordinates does
not change its complete query-count distribution. -/
theorem figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_uniform
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    ((figureOneFinalScheduledRetainedTerminalProgram q (some point)).run
      oracle.query).map Prod.snd =
    ((scheduledBalancedCoolingUniformRatioEstimate
      figureOneFinalScheduledBalancedParameters q (terminalVariance q)
      point).run oracle.query).map Prod.snd := by
  let raw := scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
    (uniformRatioWeight (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (terminalVariance q))
    (figureOneSampleCount q) (accuracyScaleFactor q • point)
  have hraw := (scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q)).2 (accuracyScaleFactor q • point)
  let withState := scheduledBalancedCoolingUniformEstimateWithState
    figureOneFinalScheduledBalancedParameters q (terminalVariance q) point
  have hwithState :=
    (scheduledBalancedCoolingUniformEstimateWithState_countedMeasurable
      figureOneFinalScheduledBalancedParameters q I oracle
      (terminalVariance_pos' q)).2 point
  calc
    ((figureOneFinalScheduledRetainedTerminalProgram q (some point)).run
        oracle.query).map Prod.snd =
        (raw.run oracle.query).map Prod.snd := by
      unfold figureOneFinalScheduledRetainedTerminalProgram raw
      exact MembershipOracleProgram.map_snd_run_bind_pure oracle.query _
        optionSnd measurable_optionSnd hraw
    _ = (withState.run oracle.query).map Prod.snd := by
      unfold withState scheduledBalancedCoolingUniformEstimateWithState raw
      symm
      exact MembershipOracleProgram.map_snd_run_bind_pure oracle.query _
        (balancedCoolingAverage (figureOneSampleCount q))
        (measurable_balancedCoolingAverage _) hraw
    _ = ((scheduledBalancedCoolingUniformRatioEstimate
        figureOneFinalScheduledBalancedParameters q (terminalVariance q)
        point).run oracle.query).map Prod.snd := by
      unfold scheduledBalancedCoolingUniformRatioEstimate
      symm
      exact MembershipOracleProgram.map_snd_run_bind_pure oracle.query _
        balancedCoolingForgetState measurable_balancedCoolingForgetState
        hwithState

/-- The retained terminal collector and the public scalar terminal wrapper
have exactly the same query-count distribution, for every optional Gaussian
product. -/
theorem figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_scalarTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (product : Option (ℝ × AmbientSpace q.n)) :
    ((figureOneFinalScheduledRetainedTerminalProgram q
      (optionSnd product)).run oracle.query).map Prod.snd =
      ((figureOneFinalScheduledScalarTerminalTail q product).run
        oracle.query).map Prod.snd := by
  cases product with
  | none =>
      simp only [optionSnd, figureOneFinalScheduledRetainedTerminalProgram,
        figureOneFinalScheduledScalarTerminalTail,
        MembershipOracleProgram.run]
      rw [Measure.map_dirac' measurable_snd,
        Measure.map_dirac' measurable_snd]
  | some value =>
      rcases value with ⟨gaussianProduct, lastPoint⟩
      let finish : Option ℝ → ℝ
        | none => 0
        | some uniformRatio =>
            initialGaussianIntegral q * gaussianProduct * uniformRatio
      have hfinish : Measurable finish := by
        have hsome : Measurable fun uniformRatio : ℝ =>
            initialGaussianIntegral q * gaussianProduct * uniformRatio := by
          fun_prop
        convert Measurable.optionElim (0 : ℝ) hsome using 1
        funext result
        cases result <;> rfl
      have huniform :=
        (scheduledBalancedCoolingUniformRatioEstimate_countedMeasurable
          figureOneFinalScheduledBalancedParameters q I oracle
            (terminalVariance_pos' q)).2 lastPoint
      calc
        ((figureOneFinalScheduledRetainedTerminalProgram q
            (optionSnd (some (gaussianProduct, lastPoint)))).run
              oracle.query).map Prod.snd =
            ((scheduledBalancedCoolingUniformRatioEstimate
              figureOneFinalScheduledBalancedParameters q
              (terminalVariance q) lastPoint).run oracle.query).map
                Prod.snd := by
          simpa only [optionSnd] using
            figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_uniform
              q I oracle lastPoint
        _ = ((figureOneFinalScheduledScalarTerminalTail q
            (some (gaussianProduct, lastPoint))).run oracle.query).map
              Prod.snd := by
          have hform : figureOneFinalScheduledScalarTerminalTail q
              (some (gaussianProduct, lastPoint)) =
              (scheduledBalancedCoolingUniformRatioEstimate
              figureOneFinalScheduledBalancedParameters q
              (terminalVariance q) lastPoint).bind fun result =>
                .pure (finish result) := by
            simp only [figureOneFinalScheduledScalarTerminalTail]
            congr 1
            funext result
            cases result <;> rfl
          rw [hform]
          symm
          exact MembershipOracleProgram.map_snd_run_bind_pure oracle.query _
            finish hfinish huniform

/-- From a fixed initial point, the complete retained interpreter and the
public scalar Figure-1 continuation have exactly the same query-count law. -/
theorem figureOneFinalScheduledRetainedFullCostProgram_map_snd_eq_pointContinuation
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    ((figureOneFinalScheduledRetainedFullCostProgram q (some point)).run
      oracle.query).map Prod.snd =
      ((scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point).run
          oracle.query).map Prod.snd := by
  let cooling := coolingProduct
    (scheduledBalancedCoolingPrimitives
      figureOneFinalScheduledBalancedParameters) q
    (explicitVolumeCoolingSchedule q).variances point
  let actualNext := figureOneFinalScheduledScalarTerminalTail q
  let mappedNext := figureOneFinalScheduledRetainedTerminalProgram q
  have hcooling := scheduledBalancedCoolingProduct_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
      (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hactual :=
    figureOneFinalScheduledScalarTerminalTail_countedMeasurable q I oracle
  have hmapped :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have hchain :=
    figureOneFinalScheduledRetainedGaussianChain_run_eq_map_coolingProduct
      q I oracle 0 (terminalPhaseSteps q) point
  rw [← explicitScheduleVariances_eq_scheduledVarianceSegment q] at hchain
  have hcompose :=
    MembershipOracleProgram.map_snd_bind_countedContinuation_eq
      oracle.query (cooling.run oracle.query)
      optionSnd measurable_optionSnd actualNext mappedNext
      hactual.1 hactual.2 hmapped.1 hmapped.2
      (figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_scalarTail
        q I oracle)
  have hpointForm :
      scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point =
        cooling.bind actualNext := by
    unfold scheduledBalancedFigureOnePointContinuation cooling actualNext
      figureOneFinalScheduledScalarTerminalTail
    congr 1
  unfold figureOneFinalScheduledRetainedFullCostProgram
  rw [MembershipOracleProgram.run_bind_counted oracle.query _ _
    ((figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
      q I oracle 0 (terminalPhaseSteps q)).2 (some point))
    hmapped.2 hmapped.1]
  rw [hchain]
  rw [hpointForm, MembershipOracleProgram.run_bind_counted oracle.query _ _
    (hcooling.2 point) hactual.2 hactual.1]
  exact hcompose

/-- Finite chronological reference for every prefix of Gaussian phases.
The reference has the exact ideal retained-point marginal, additive
exact-chance loss, and only the sum of warm expected phase costs. -/
theorem exists_figureOneFinalScheduledGaussianCountedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (steps : ℕ) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          ((figureOneAbortInitialSample q).run oracle.query) steps)
        reference
        ((ENNReal.ofReal (q.eps / 64) +
            scheduledBalancedStationaryTargetError q) +
          ∑ phase ∈ Finset.range steps,
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) ∧
      reference.fst = figureOneFinalScheduledIdealPhaseStart q I steps ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range steps,
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) := by
  have hinitialStrong :=
    figureOneAbortInitialSample_countedStronglyMeasurable q I oracle
  let _ : IsProbabilityMeasure
      ((figureOneAbortInitialSample q).run oracle.query) :=
    MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
      hinitialStrong.executionMeasurable
  let ideal := figureOneFinalScheduledIdealPhaseStart q I
  let phaseCost : ℕ → ENNReal := fun phase =>
    ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase)) : ℕ) : ENNReal)
  have hreference := exists_countedReference_iteratedKernelLaw
    (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
    ((figureOneAbortInitialSample q).run oracle.query) ideal
    (fun phase => figureOnePhaseSampleCount q (scheduleValue q phase) •
      figureOneCorrectedTransitionBudget q)
    phaseCost
    (fun phase => by
      let _ : IsProbabilityMeasure (ideal phase) := by
        exact figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I phase
      infer_instance)
    (figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart q I oracle)
    (fun phase => by
      unfold figureOneFinalScheduledGaussianCountedKernel
      exact measurable_countedContinuation oracle.query _
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).1
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).2)
    (fun phase state => by
      unfold figureOneFinalScheduledGaussianCountedKernel countedContinuation
      let _ : IsProbabilityMeasure
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram
            q phase state.1).run oracle.query) :=
        MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
            q I oracle phase).2 state.1).executionMeasurable
      exact Measure.isProbabilityMeasure_map (by fun_prop))
    (fun phase rho _hrho hmarginal => by
      have hprogram :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have hnext : ideal (phase + 1) =
          (figureOneScheduledAcceptedTargetAt q I phase).map some := by
        simp [ideal, figureOneFinalScheduledIdealPhaseStart]
      apply MembershipOracleProgram.countedContinuation_step oracle.query rho
        (ideal phase) (ideal (phase + 1))
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)
        hprogram.1 hprogram.2 hmarginal
      · rw [hnext]
        exact figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
          q I oracle phase
      · exact figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
          q I oracle phase)
    steps
  obtain ⟨reference, hdom, hmarginal, hcost⟩ := hreference
  refine ⟨reference, hdom, hmarginal, ?_⟩
  apply hcost.trans
  gcongr
  simpa only [countedQueryCost, Nat.cast_one] using
    (figureOneAbortInitialSample_queryBound q).lintegral_queryCount_le
      hinitialStrong

/-- Program-level form of the Gaussian-prefix counted reference. -/
theorem exists_figureOneFinalScheduledGaussianPrefixProgram_countedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (steps : ℕ) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        ((figureOneFinalScheduledRetainedGaussianPrefixProgram q steps).run
          oracle.query)
        reference
        ((ENNReal.ofReal (q.eps / 64) +
            scheduledBalancedStationaryTargetError q) +
          ∑ phase ∈ Finset.range steps,
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) ∧
      reference.fst = figureOneFinalScheduledIdealPhaseStart q I steps ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range steps,
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) := by
  rw [figureOneFinalScheduledRetainedGaussianPrefixProgram_run q I oracle steps]
  exact exists_figureOneFinalScheduledGaussianCountedReference q I oracle steps

/-- At the exact final Gaussian endpoint, the terminal Gaussian-to-uniform
collector also pays only its warm-start term. -/
theorem figureOneFinalScheduledTerminalIdealExpectedCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedTerminalProgram q state).run
        oracle.query)
      ∂figureOneFinalScheduledIdealPhaseStart q I (terminalPhaseSteps q)) ≤
      ((384 * (figureOneSampleCount q *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q) *
        figureOneFinalScheduledBalancedParameters.properStride q
          (terminalVariance q)) : ℕ) : ENNReal) := by
  have hsteps : 0 < terminalPhaseSteps q := terminalPhaseSteps_pos q
  obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero hsteps.ne'
  let target := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  have hideal : figureOneFinalScheduledIdealPhaseStart q I
      (terminalPhaseSteps q) = target.map some := by
    simp [figureOneFinalScheduledIdealPhaseStart, target, hprevious]
  have hwarmBase :=
    figureOneFinalScheduledIdealPhaseStart_scaled_isWarm q I
      (terminalPhaseSteps q)
  have hsub : terminalPhaseSteps q - 1 = previous := by omega
  have hwarm : IsWarm
      (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (terminalVariance q))
        (figureOneScheduledProposalRadius q (terminalVariance q))
        (terminalVariance q)) := by
    simpa [figureOneScheduledSpeedyPiAt, scheduleValue_terminalPhaseSteps,
      target, hsteps.ne', hsub] using hwarmBase
  have hbound :=
    lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
      q I oracle (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledIdealPhaseStart q I (terminalPhaseSteps q)) target
      (by rw [hideal]; exact MeasureLeUpTo.refl (target.map some))
      hwarm (finalIdealWarmConstant_le_ninetySix q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q)
      (figureOneScheduledCorrectedProperStride_pos q (terminalVariance q)
        (figureOneSafeRetryCount q - 1))
  have hcost : (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedTerminalProgram q state).run
        oracle.query)
      ∂figureOneFinalScheduledIdealPhaseStart q I (terminalPhaseSteps q)) =
      ∫⁻ state, match state with
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
              (figureOneSampleCount q)
              (accuracyScaleFactor q • point)).run oracle.query)
        ∂figureOneFinalScheduledIdealPhaseStart q I
          (terminalPhaseSteps q) := by
    apply lintegral_congr
    intro state
    exact figureOneFinalScheduledRetainedTerminalProgram_cost q I oracle state
  rw [hcost]
  exact hbound.trans (by push_cast; simp [mul_comm, mul_left_comm, mul_assoc])

/-- Forward-associated retained execution through the terminal collector. -/
noncomputable def figureOneFinalScheduledRetainedCompleteProgram
    (q : VolumeParams) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  (figureOneFinalScheduledRetainedGaussianPrefixProgram q
    (terminalPhaseSteps q)).bind
      (figureOneFinalScheduledRetainedTerminalProgram q)

/-- Complete retained counted reference, including the terminal collector. -/
theorem exists_figureOneFinalScheduledRetainedComplete_countedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        ((figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query)
        reference
        ((ENNReal.ofReal (q.eps / 64) +
            scheduledBalancedStationaryTargetError q) +
          ∑ phase ∈ Finset.range (terminalPhaseSteps q),
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) +
          ((384 * (figureOneSampleCount q *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (terminalVariance q) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (terminalVariance q)) : ℕ) : ENNReal) := by
  obtain ⟨gaussianReference, hgaussianDom, hgaussianMarginal,
      hgaussianCost⟩ :=
    exists_figureOneFinalScheduledGaussianPrefixProgram_countedReference
      q I oracle (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable
      q I oracle
  let terminalContinuation := countedContinuation oracle.query
    (figureOneFinalScheduledRetainedTerminalProgram q)
  let reference := gaussianReference.bind terminalContinuation
  refine ⟨reference, ?_, ?_⟩
  · have hbind := hgaussianDom.bind_same
      (measurable_countedContinuation oracle.query _ hterminal.1 hterminal.2)
      (fun state => by
        dsimp only [terminalContinuation, countedContinuation]
        let _ : IsProbabilityMeasure
            ((figureOneFinalScheduledRetainedTerminalProgram q state.1).run
              oracle.query) :=
          MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
            (hterminal.2 state.1).executionMeasurable
        exact Measure.isProbabilityMeasure_map (by fun_prop))
    unfold figureOneFinalScheduledRetainedCompleteProgram
    rw [MembershipOracleProgram.run_bind_counted oracle.query _ _
      (figureOneFinalScheduledRetainedGaussianPrefixProgram_countedMeasurable
        q I oracle (terminalPhaseSteps q)) hterminal.2 hterminal.1]
    exact hbind
  · have hcostEq :=
      MembershipOracleProgram.countedQueryCost_bind_countedContinuation
        oracle.query gaussianReference
        (figureOneFinalScheduledRetainedTerminalProgram q)
        hterminal.1 hterminal.2
    change countedQueryCost reference ≤ _
    rw [hcostEq, hgaussianMarginal]
    exact add_le_add hgaussianCost
      (figureOneFinalScheduledTerminalIdealExpectedCost_le q I oracle)

/-- The explicit cost envelope carried by the retained chronological
reference is the warm-shadow work already bounded by the scheduled rate. -/
theorem figureOneFinalScheduledRetainedCompleteCostEnvelope_le
    (q : VolumeParams) :
    1 + ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) +
        ((384 * (figureOneSampleCount q *
          figureOneFinalScheduledBalancedParameters.retryLimit q
            (terminalVariance q) *
          figureOneFinalScheduledBalancedParameters.properStride q
            (terminalVariance q)) : ℕ) : ENNReal) ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q) := by
  calc
    _ = (1 : ENNReal) +
        ((384 * (figureOneSafeRetryCount q *
          figureOneScheduledProperWork q) : ℕ) : ENNReal) := by
      simp only [figureOneFinalScheduledBalancedParameters_retryLimit,
        figureOneScheduledProperWork, Nat.cast_add, Nat.cast_mul,
        figureOneScheduledBalancedParameters_properStride,
        figureOneFinalScheduledBalancedParameters_properStride]
      push_cast
      simp only [Finset.mul_sum, mul_add]
      ring_nf
      ac_rfl
    _ ≤ _ := one_add_figureOneWarmShadowScheduledWork_le q

/-- The exact-chance budget is substantially smaller than the coarse
`1/64` accuracy-transfer slot; this sharper form is used only for the global
query-cap transfer. -/
theorem figureOne_exactChance_countReference_budget_le
    (q : VolumeParams) :
    (figureOneDependentMaxSampleCount q *
      figureOneDependentPhaseCount q) •
        ENNReal.ofReal (figureOnePerSampleMixingError q) ≤
      ENNReal.ofReal (1 / 1280 : ℝ) := by
  let error := (figureOneDependentMaxSampleCount q *
      figureOneDependentPhaseCount q) •
        ENNReal.ofReal (figureOnePerSampleMixingError q)
  have herrTop : error ≠ ⊤ := by
    dsimp [error]
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top
  rw [← ENNReal.toReal_le_toReal herrTop ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 1280)]
  have heq : 3 * error.toReal = figureOneDependentEpsilon q := by
    simpa [error] using figureOne_exactChance_budget q
  have hdep0 := figureOneDependentEpsilon_nonneg q
  have ha := figureOneDependentAlpha_ge_1024 q
  have ha8 : (8 : ℝ) ≤ figureOneDependentAlpha q := by linarith
  have hpow : (512 : ℝ) ≤ figureOneDependentAlpha q ^ 3 := by
    calc
      (512 : ℝ) = 8 ^ 3 := by norm_num
      _ ≤ figureOneDependentAlpha q ^ 3 :=
        pow_le_pow_left₀ (by norm_num) ha8 3
  have hsmall := figureOneDependent_smallness q
  have hscaled :
      4 * figureOneDependentEpsilon q * (320 / 3 : ℝ) ≤
        4 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 3 := by
    have h320 : (320 / 3 : ℝ) ≤
        figureOneDependentAlpha q ^ 3 := by
      norm_num at hpow ⊢
      linarith
    exact mul_le_mul_of_nonneg_left h320
      (mul_nonneg (by norm_num) hdep0)
  have hdep : figureOneDependentEpsilon q ≤ (3 / 1280 : ℝ) := by
    nlinarith
  nlinarith

/-- The stationary initial-target replacement plus every Gaussian phase
replacement fits into the single exact-chance count-reference budget. -/
theorem figureOneFinalScheduledCountReferenceError_le
    (q : VolumeParams) :
    scheduledBalancedStationaryTargetError q +
        ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≤
      ENNReal.ofReal (1 / 1280 : ℝ) := by
  let delta := figureOneCorrectedTransitionBudget q
  let maxSamples := figureOneDependentMaxSampleCount q
  have hstationary : scheduledBalancedStationaryTargetError q ≤ delta := by
    calc
      scheduledBalancedStationaryTargetError q ≤
          figureOneCorrectedTargetBudget q :=
        scheduledBalancedStationaryTargetError_le_targetBudget q
      _ ≤ delta := by
        unfold figureOneCorrectedTargetBudget
        apply (ENNReal.div_le_iff_le_mul
          (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
        calc
          delta = delta * 1 := by simp
          _ ≤ delta * 4 := by gcongr <;> norm_num
  have hdeltaMax : delta ≤ maxSamples • delta := by
    rw [nsmul_eq_mul]
    calc
      delta = 1 * delta := by simp
      _ ≤ (maxSamples : ENNReal) * delta := by
        gcongr
        exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hsum :
      (∑ phase ∈ Finset.range (terminalPhaseSteps q),
        figureOnePhaseSampleCount q (scheduleValue q phase) • delta) ≤
      ∑ phase ∈ Finset.range (terminalPhaseSteps q),
        maxSamples • delta := by
    apply Finset.sum_le_sum
    intro phase hphase
    gcongr
    exact figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  calc
    scheduledBalancedStationaryTargetError q +
        ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≤
      delta + ∑ phase ∈ Finset.range (terminalPhaseSteps q),
        maxSamples • delta := add_le_add hstationary hsum
    _ ≤ maxSamples • delta +
        ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          maxSamples • delta := add_le_add hdeltaMax le_rfl
    _ = (maxSamples * figureOneDependentPhaseCount q) • delta := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        figureOneDependentPhaseCount]
      push_cast
      ring_nf
    _ ≤ ENNReal.ofReal (1 / 1280 : ℝ) := by
      simpa only [delta, maxSamples, figureOneCorrectedTransitionBudget] using
        figureOne_exactChance_countReference_budget_le q

/-- Forgetting the numerical volume output, the retained chronological
interpreter and the actual aborting Figure-1 base program have exactly the
same complete query-count distribution. -/
theorem figureOneFinalScheduledRetainedCompleteProgram_map_snd_eq_abortBase
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ((figureOneFinalScheduledRetainedCompleteProgram q).run
      oracle.query).map Prod.snd =
      ((figureOneFinalScheduledAbortBaseProgram q).run
        oracle.query).map Prod.snd := by
  let actualNext : Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ
    | none => .pure 0
    | some point => scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point
  let mappedNext := figureOneFinalScheduledRetainedFullCostProgram q
  have hpoint := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  have hactualRun : Measurable fun state =>
      (actualNext state).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hpoint.1 using 1
    funext state
    cases state <;> rfl
  have hactual : ∀ state,
      (actualNext state).CountedStronglyMeasurable oracle.query := by
    intro state
    cases state with
    | none => trivial
    | some point => exact hpoint.2 point
  have hmapped :=
    figureOneFinalScheduledRetainedFullCostProgram_countedMeasurable
      q I oracle
  have hnext : ∀ state,
      ((mappedNext state).run oracle.query).map Prod.snd =
        ((actualNext state).run oracle.query).map Prod.snd := by
    intro state
    cases state with
    | none =>
        have hnone : mappedNext none =
            (MembershipOracleProgram.pure none :
              MembershipOracleProgram q.n
                (Option (AmbientSpace q.n))) := by
          unfold mappedNext figureOneFinalScheduledRetainedFullCostProgram
          rw [figureOneFinalScheduledRetainedGaussianChain_none q 0
            (terminalPhaseSteps q)]
          rfl
        rw [hnone]
        dsimp only [actualNext]
        simp only [MembershipOracleProgram.run]
        rw [Measure.map_dirac' measurable_snd,
          Measure.map_dirac' measurable_snd]
    | some point =>
        exact
          figureOneFinalScheduledRetainedFullCostProgram_map_snd_eq_pointContinuation
            q I oracle point
  let initialLaw := (figureOneAbortInitialSample q).run oracle.query
  have hcompose :=
    MembershipOracleProgram.map_snd_bind_countedContinuation_eq
      oracle.query initialLaw id measurable_id actualNext mappedNext
      hactualRun hactual hmapped.1 hmapped.2 hnext
  have hid : initialLaw.map
      (fun outcome => (id outcome.1, outcome.2)) = initialLaw := by
    rw [show (fun outcome : Option (AmbientSpace q.n) × ℕ =>
      (id outcome.1, outcome.2)) = id by
        funext outcome
        rfl]
    exact Measure.map_id
  have hretainedForm :
      figureOneFinalScheduledRetainedCompleteProgram q =
        (figureOneAbortInitialSample q).bind mappedNext := by
    unfold figureOneFinalScheduledRetainedCompleteProgram mappedNext
    rw [figureOneFinalScheduledRetainedGaussianPrefixProgram_eq_bind_chain]
    rw [MembershipOracleProgram.bind_assoc_counted_cv18]
    rfl
  have hactualForm : figureOneFinalScheduledAbortBaseProgram q =
      (figureOneAbortInitialSample q).bind actualNext := by
    unfold figureOneFinalScheduledAbortBaseProgram baseVolumeCooling actualNext
    congr 1
    funext state
    cases state with
    | none => rfl
    | some point =>
        exact scheduledBalancedAbort_pointContinuation_eq
          figureOneFinalScheduledBalancedParameters q point
  rw [hretainedForm,
    MembershipOracleProgram.run_bind_counted oracle.query _ _
      (figureOneAbortInitialSample_countedStronglyMeasurable q I oracle)
      hmapped.2 hmapped.1]
  rw [hactualForm,
    MembershipOracleProgram.run_bind_counted oracle.query _ _
      (figureOneAbortInitialSample_countedStronglyMeasurable q I oracle)
      hactual hactualRun]
  rw [hid] at hcompose
  exact hcompose

#print axioms figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
#print axioms figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
#print axioms figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart
#print axioms exists_figureOneFinalScheduledGaussianCountedReference
#print axioms
  figureOneFinalScheduledRetainedGaussianPrefixProgram_run
#print axioms figureOneFinalScheduledRetainedGaussianChain_bind_next
#print axioms
  figureOneFinalScheduledRetainedGaussianPrefixProgram_eq_bind_chain
#print axioms
  figureOneFinalScheduledRetainedGaussianPhaseProgram_run_eq_map_ratio
#print axioms
  figureOneFinalScheduledRetainedGaussianChain_run_eq_map_coolingProduct
#print axioms
  figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_uniform
#print axioms
  figureOneFinalScheduledRetainedTerminalProgram_map_snd_eq_scalarTail
#print axioms
  figureOneFinalScheduledRetainedFullCostProgram_map_snd_eq_pointContinuation
#print axioms
  exists_figureOneFinalScheduledGaussianPrefixProgram_countedReference
#print axioms figureOneFinalScheduledTerminalIdealExpectedCost_le
#print axioms
  exists_figureOneFinalScheduledRetainedComplete_countedReference
#print axioms figureOneFinalScheduledRetainedCompleteCostEnvelope_le
#print axioms figureOne_exactChance_countReference_budget_le
#print axioms figureOneFinalScheduledCountReferenceError_le
#print axioms
  figureOneFinalScheduledRetainedCompleteProgram_map_snd_eq_abortBase

end ArlibCommunity.Algorithms.CV18
