/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryNonnegative
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAdjacentTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledWarmSixteenTransition

/-! # Lemma 7.17(c) from an additive good/bad retained marginal

This form is designed for a capped chronological prefix.  It does not
normalize the live part of the prefix and therefore does not enlarge the KLS
warm-start constant.  Instead, the finite failure/coupling mass is carried as
the additive `bad` measure accepted by the scheduled adjacent-transition
theorem.
-/

open MeasureTheory ProbabilityTheory
open _root_.Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

/-- Paper-faithful complete-phase form of CV18 Lemma 7.17(c) for a prefix
whose (scaled) retained marginal is the preceding speedy target plus a small
positive error measure.  Conditioning on a half-probability past event is
handled inside the generic Lemma 7.17(b) proof; the scheduled transition
theorem charges `2 * eta` without renormalizing the good component. -/
theorem approxIndepFun_figureOneFinalScheduledCompletePhase_of_good_bad
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (bad : Measure (AmbientSpace q.n)) [IsFiniteMeasure bad]
    {eta : ENNReal} (heta : eta ≠ ⊤)
    (hstateDom :
      history.map (fun h => accuracyScaleFactor q • state h) ≤
        figureOneScheduledSpeedyPiAt q I phase + bad)
    (hbad : bad Set.univ ≤ eta)
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (hbudget :
      ((figureOneCorrectedTransitionBudget q + 2 * eta) +
        (figureOneCorrectedTransitionBudget q + 2 * eta)).toReal ≤
          figureOneDependentEpsilon q) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          scheduledBalancedTransitionCollectLaw q I
            (scheduleValue q (phase + 1))
            (gaussianRatioWeight (scheduleValue q (phase + 1))
              (scheduleValue q (phase + 2)))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q (phase + 1)))
            (figureOnePhaseSampleCount q (scheduleValue q (phase + 1)))
            0 current) ∘
          (fun h => accuracyScaleFactor q • state h))) := by
  let scaledState : H → AmbientSpace q.n := fun h =>
    accuracyScaleFactor q • state h
  have hscaledState : Measurable scaledState := by
    dsimp only [scaledState]
    fun_prop
  let rho := history.map scaledState
  let _ : IsProbabilityMeasure rho :=
    Measure.isProbabilityMeasure_map hscaledState.aemeasurable
  let target : Measure (Option (AmbientSpace q.n)) :=
    (truncatedGaussianProbability q I (scheduleValue q (phase + 1))
      (scheduleValue_pos q (phase + 1)) :
        Measure (AmbientSpace q.n)).map some
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let delta := figureOneCorrectedTransitionBudget q + 2 * eta
  have hdelta : delta ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · simp [figureOneCorrectedTransitionBudget]
    · exact ENNReal.mul_ne_top (by norm_num) heta
  have hfirst : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo
        (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I
          (scheduleValue q (phase + 1))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q (phase + 1)))))
        target delta := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    simpa [rho, target, delta, figureOneScheduledSpeedyPiAt] using
      bind_figureOneFinalScheduledAdjacentTransition_leUpTo_of_good_bad
        q I phase rho mu bad hwarm
          (by
            simpa [rho, scaledState, figureOneScheduledSpeedyPiAt] using
              hstateDom)
          hbad
  have hresult :=
    approxIndepFun_scheduledBalancedCompletePhase_of_warm_first
      q I (scheduleValue_pos q (phase + 1))
      (measurable_gaussianRatioWeight (scheduleValue q (phase + 1))
        (scheduleValue q (phase + 2)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q (phase + 1)))
      (figureOnePhaseSampleCount q (scheduleValue q (phase + 1)) - 1)
      history scaledState hscaledState target hdelta hfirst pastProduct
      nextEstimator hpastProduct hnextEstimator
      (figureOneDependentMaxSampleCount q)
      (figureOneDependentPhaseCount q)
      (figureOnePerSampleMixingError q)
      (by
        rw [figureOne_lemma717c_budget q]
        exact hbudget)
  have hcount : 0 < figureOnePhaseSampleCount q
      (scheduleValue q (phase + 1)) := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  rw [Nat.sub_add_cancel hcount] at hresult
  rw [figureOne_lemma717c_budget q] at hresult
  simpa [scaledState] using hresult

/-- Concrete retained-target version.  This is the form supplied by the
scheduled trace induction: the live good component is the previous phase's
normalized accepted-target law, rescaled into the next speedy body. -/
theorem approxIndepFun_figureOneFinalScheduledCompletePhase_of_accepted_good_bad
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (bad : Measure (AmbientSpace q.n)) [IsFiniteMeasure bad]
    {eta : ENNReal} (heta : eta ≠ ⊤)
    (hstateDom :
      history.map (fun h => accuracyScaleFactor q • state h) ≤
        (figureOneScheduledAcceptedTargetAt q I phase).map
          (fun x => accuracyScaleFactor q • x) + bad)
    (hbad : bad Set.univ ≤ eta)
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (hbudget :
      ((figureOneCorrectedTransitionBudget q + 2 * eta) +
        (figureOneCorrectedTransitionBudget q + 2 * eta)).toReal ≤
          figureOneDependentEpsilon q) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          scheduledBalancedTransitionCollectLaw q I
            (scheduleValue q (phase + 1))
            (gaussianRatioWeight (scheduleValue q (phase + 1))
              (scheduleValue q (phase + 2)))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q (phase + 1)))
            (figureOnePhaseSampleCount q (scheduleValue q (phase + 1)))
            0 current) ∘
          (fun h => accuracyScaleFactor q • state h))) := by
  let scaledState : H → AmbientSpace q.n := fun h =>
    accuracyScaleFactor q • state h
  have hscaledState : Measurable scaledState := by
    dsimp only [scaledState]
    fun_prop
  let rho := history.map scaledState
  let _ : IsProbabilityMeasure rho :=
    Measure.isProbabilityMeasure_map hscaledState.aemeasurable
  let good := (figureOneScheduledAcceptedTargetAt q I phase).map
    (fun x => accuracyScaleFactor q • x)
  let target : Measure (Option (AmbientSpace q.n)) :=
    (truncatedGaussianProbability q I (scheduleValue q (phase + 1))
      (scheduleValue_pos q (phase + 1)) :
        Measure (AmbientSpace q.n)).map some
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let delta := figureOneCorrectedTransitionBudget q + 2 * eta
  have hdelta : delta ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · simp [figureOneCorrectedTransitionBudget]
    · exact ENNReal.mul_ne_top (by norm_num) heta
  have hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q (phase + 1)))
        (figureOneScheduledProposalRadius q (scheduleValue q (phase + 1)))
        (scheduleValue q (phase + 1))) := by
    simpa [good, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I phase
  have hfirst : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo
        (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I
          (scheduleValue q (phase + 1))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q (phase + 1)))))
        target delta := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    simpa [rho, good, target, delta] using
      bind_figureOneFinalScheduledBalancedTransition_leUpTo_of_good_bad_sharp
        q I (scheduleValue_pos q (phase + 1)) rho mu good bad hwarm
          (by simpa [rho, scaledState, good] using hstateDom) hgood hbad
  have hresult :=
    approxIndepFun_scheduledBalancedCompletePhase_of_warm_first
      q I (scheduleValue_pos q (phase + 1))
      (measurable_gaussianRatioWeight (scheduleValue q (phase + 1))
        (scheduleValue q (phase + 2)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q (phase + 1)))
      (figureOnePhaseSampleCount q (scheduleValue q (phase + 1)) - 1)
      history scaledState hscaledState target hdelta hfirst pastProduct
      nextEstimator hpastProduct hnextEstimator
      (figureOneDependentMaxSampleCount q)
      (figureOneDependentPhaseCount q)
      (figureOnePerSampleMixingError q)
      (by
        rw [figureOne_lemma717c_budget q]
        exact hbudget)
  have hcount : 0 < figureOnePhaseSampleCount q
      (scheduleValue q (phase + 1)) := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  rw [Nat.sub_add_cancel hcount] at hresult
  rw [figureOne_lemma717c_budget q] at hresult
  simpa [scaledState] using hresult

#print axioms approxIndepFun_figureOneFinalScheduledCompletePhase_of_good_bad
#print axioms approxIndepFun_figureOneFinalScheduledCompletePhase_of_accepted_good_bad

end ArlibCommunity.Algorithms.CV18
