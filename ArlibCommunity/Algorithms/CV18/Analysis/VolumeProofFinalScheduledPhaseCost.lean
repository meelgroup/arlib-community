/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledOptionalPhaseCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostArithmetic

/-! # Concrete expected-cost bounds at every final scheduled phase -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

/-- Expected collector cost at a Gaussian cooling phase, under the exact
optional retained-state law after all preceding phases. -/
noncomputable def figureOneFinalScheduledGaussianPhaseExpectedCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) : ENNReal :=
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
    ∂((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase).map
        scheduledBalancedTraceRetainedOption)

/-- Expected terminal uniform collector cost under the retained-state law
after all Gaussian cooling phases. -/
noncomputable def figureOneFinalScheduledTerminalExpectedCost
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : ENNReal :=
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
    ∂((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (terminalPhaseSteps q)).map scheduledBalancedTraceRetainedOption)

private theorem initialAcceptedTarget_scaled_isWarm_final
    (q : VolumeParams) (I : VolumeInput q.n) :
    IsWarm (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      ((figureOneScheduledAcceptedTargetAt q I 0).map fun point =>
        accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I 0) := by
  have hwarm8 := initialContractedAcceptedTarget_isWarm_eight q I
  apply hwarm8.mono
  have hC : (1 : ENNReal) ≤ ENNReal.ofReal (speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_one_le q)
  calc
    (8 : ENNReal) = 8 * 1 := by norm_num
    _ ≤ 8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) := by gcongr

private theorem finalWarmConstant_le_ninetySix (q : VolumeParams) :
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 96 := by
  calc
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 8 * 12 := by
      gcongr
      rw [← ENNReal.ofReal_ofNat 12]
      exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_le_twelve q)
    _ = 96 := by norm_num

/-- Sharp expected-cost envelope for every Gaussian cooling phase. -/
theorem figureOneFinalScheduledGaussianPhaseExpectedCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (hphase : phase < terminalPhaseSteps q) :
    figureOneFinalScheduledGaussianPhaseExpectedCost q I oracle phase ≤
      ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase)) : ℕ) : ENNReal) +
      ((figureOnePhaseSampleCount q (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase) *
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (scheduleValue q phase) + 2) : ℕ) : ENNReal) *
        figureOneScheduledRetainedError q phase := by
  let mu := (scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I phase).map
      scheduledBalancedTraceRetainedOption
  let target : Measure (AmbientSpace q.n) :=
    if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
    else figureOneScheduledAcceptedTargetAt q I (phase - 1)
  have htargetProb : IsProbabilityMeasure target := by
    dsimp only [target]
    split_ifs with hzero
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  let _ : IsProbabilityMeasure target := htargetProb
  have happrox : MeasureLeUpTo mu (target.map some)
      (figureOneScheduledRetainedError q phase) := by
    by_cases hzero : phase = 0
    · subst phase
      simpa [mu, target, figureOneScheduledRetainedError,
        scheduledBalancedForwardTraceLaw, iteratedKernelLaw] using
        scheduledBalancedInitialRetained_leUpTo_target q I
    · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hprevious : previous < terminalPhaseSteps q := by omega
      simpa [mu, target] using
        scheduledBalancedForwardTraceLaw_retained_leUpTo_target
          q I previous hprevious
  have hwarm : IsWarm (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase) := by
    by_cases hzero : phase = 0
    · subst phase
      simpa [target] using initialAcceptedTarget_scaled_isWarm_final q I
    · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      simpa [target, figureOneScheduledAcceptedTargetAt,
        figureOneScheduledSpeedyPiAt] using
        map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous
  unfold figureOneFinalScheduledGaussianPhaseExpectedCost
  change (∫⁻ state, _ ∂mu) ≤ _
  exact
    lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
      q I oracle (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1))) mu target happrox hwarm
      (finalWarmConstant_le_ninetySix q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
      (figureOneScheduledCorrectedProperStride_pos q (scheduleValue q phase)
        (figureOneSafeRetryCount q - 1))

/-- Sharp expected-cost envelope for the terminal Gaussian-to-uniform phase. -/
theorem figureOneFinalScheduledTerminalExpectedCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    figureOneFinalScheduledTerminalExpectedCost q I oracle ≤
      ((384 * (figureOneSampleCount q *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q) *
        figureOneFinalScheduledBalancedParameters.properStride q
          (terminalVariance q)) : ℕ) : ENNReal) +
      ((figureOneSampleCount q *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q) *
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (terminalVariance q) + 2) : ℕ) : ENNReal) *
        figureOneScheduledRetainedError q (terminalPhaseSteps q) := by
  have hsteps : 0 < terminalPhaseSteps q := terminalPhaseSteps_pos q
  obtain ⟨previous, hpreviousEq⟩ := Nat.exists_eq_succ_of_ne_zero hsteps.ne'
  have hprevious : previous < terminalPhaseSteps q := by omega
  let mu := (scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (terminalPhaseSteps q)).map scheduledBalancedTraceRetainedOption
  let target := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  have happrox : MeasureLeUpTo mu (target.map some)
      (figureOneScheduledRetainedError q (terminalPhaseSteps q)) := by
    simpa [mu, target, hpreviousEq] using
      scheduledBalancedForwardTraceLaw_retained_leUpTo_target
        q I previous hprevious
  have hwarm : IsWarm (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (terminalVariance q))
        (figureOneScheduledProposalRadius q (terminalVariance q))
        (terminalVariance q)) := by
    have h := map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
      q I previous
    have hindex : previous + 1 = terminalPhaseSteps q := by omega
    have hschedule : scheduleValue q (previous + 1) = terminalVariance q := by
      rw [hindex, scheduleValue_terminalPhaseSteps]
    simpa [target, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, hschedule] using h
  unfold figureOneFinalScheduledTerminalExpectedCost
  change (∫⁻ state, _ ∂mu) ≤ _
  exact
    lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
      q I oracle (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q)) mu target happrox
      hwarm (finalWarmConstant_le_ninetySix q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q)
      (figureOneScheduledCorrectedProperStride_pos q (terminalVariance q)
        (figureOneSafeRetryCount q - 1))

#print axioms figureOneFinalScheduledGaussianPhaseExpectedCost_le
#print axioms figureOneFinalScheduledTerminalExpectedCost_le

end ArlibCommunity.Algorithms.CV18
