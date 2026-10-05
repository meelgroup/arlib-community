/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceBalanced
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule

/-!
# Concrete CV18 phase-wise independence premises

This file instantiates the balanced-retry approximation with the actual
accuracy-phase speedy stationary law and the per-sample error chosen for the
dependent-product argument.  The cap and speedy-mixing errors each receive
half of that budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

theorem figureOnePerSampleMixingError_le_one (q : VolumeParams) :
    figureOnePerSampleMixingError q ≤ 1 := by
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have ha : 1 ≤ figureOneDependentAlpha q :=
    figureOneDependentAlpha_one_le q
  have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  unfold figureOnePerSampleMixingError figureOneDependentEpsilon
  have hden1 : 1 ≤
      4096 * figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ) := by
    have ha4 : 1 ≤ figureOneDependentAlpha q ^ 4 := one_le_pow₀ ha
    nlinarith
  have hden2 : 1 ≤
      3 * (figureOneDependentMaxSampleCount q : ℝ) *
        (figureOneDependentPhaseCount q : ℝ) := by nlinarith
  have hden1pos : 0 <
      4096 * figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ) := lt_of_lt_of_le zero_lt_one hden1
  have hden2pos : 0 <
      3 * (figureOneDependentMaxSampleCount q : ℝ) *
        (figureOneDependentPhaseCount q : ℝ) := lt_of_lt_of_le zero_lt_one hden2
  have hfirst : q.eps ^ 2 /
      (4096 * figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ)) ≤ 1 := by
    rw [div_le_one hden1pos]
    exact he2.trans hden1
  rw [div_le_one hden2pos]
  exact hfirst.trans hden2

theorem figureOneHalfPerSampleMixingError_pos (q : VolumeParams) :
    0 < figureOnePerSampleMixingError q / 2 := by
  positivity [figureOnePerSampleMixingError_pos q]

theorem figureOneHalfPerSampleMixingError_le_one (q : VolumeParams) :
    figureOnePerSampleMixingError q / 2 ≤ 1 := by
  have h := figureOnePerSampleMixingError_le_one q
  nlinarith [figureOnePerSampleMixingError_pos q]

theorem speedyAdjacentWarmConstant_one_le (q : VolumeParams) :
    1 ≤ speedyAdjacentWarmConstant q := by
  have he : 1 ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp (by norm_num)
  have hep : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  unfold speedyAdjacentWarmConstant
  nlinarith

/-- Every `2`-warm conditioning of a base law that is `M`-warm for the
current phase has a capped proper block within the chosen per-sample error of
the current speedy stationary law. -/
theorem balancedAccuracyFirstBlock_leUpTo_figureOnePerSample
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    {M : ℝ} (hM : 1 ≤ M)
    (hbaseWarm : Arlib.IsWarm (ENNReal.ofReal M) rho
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hwalk : 4 * ((Real.log (2 * M) +
        2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
          (properStride : ℝ))
    (hcapBudget : ((properStride : ℕ) : ENNReal) *
        ENNReal.ofReal (2 * M) ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        ENNReal.ofReal (figureOnePerSampleMixingError q / 2)) :
    ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo
        ((mu.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        ((Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2).map some)
        (ENNReal.ofReal (figureOnePerSampleMixingError q)) := by
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  have hwarmPi : Arlib.IsWarm (ENNReal.ofReal (2 * M)) mu pi := by
    have htrans := hwarm.trans hbaseWarm
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    simpa only [pi] using htrans
  have hmixWithin := mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 (M := 2 * M)
      (by nlinarith) hwarmPi
      (figureOneHalfPerSampleMixingError_pos q)
      (figureOneHalfPerSampleMixingError_le_one q) hwalk
  have hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride) pi
      (ENNReal.ofReal (figureOnePerSampleMixingError q / 2)) := by
    simpa [Arlib.MarkovChains.MixesWithin, pi] using hmixWithin
  have hblock :=
    bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
      q I hsigma2 proposalCap properStride hproposalCap mu hwarmPi
        hcapBudget hmix
  have hhalf : 0 ≤ figureOnePerSampleMixingError q / 2 :=
    (figureOneHalfPerSampleMixingError_pos q).le
  have hadd : figureOnePerSampleMixingError q / 2 +
      figureOnePerSampleMixingError q / 2 =
        figureOnePerSampleMixingError q := by ring
  simpa only [pi, ← ENNReal.ofReal_add hhalf hhalf, hadd] using hblock

/-- The normalized stationary rejection branch satisfies the same concrete
per-sample block bound. -/
theorem balancedAccuracyRetryBlock_leUpTo_figureOnePerSample
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    (hwalk : 4 * ((Real.log 2 +
        2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
          (properStride : ℝ))
    (hcapBudget : ((properStride : ℕ) : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        ENNReal.ofReal (figureOnePerSampleMixingError q / 2)) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let rejected := balancedRejectedStateMeasure q I sigma2 pi
    let rejectedProb := Arlib.condOn rejected Set.univ
    MeasureLeUpTo
      ((rejectedProb.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some)
      (ENNReal.ofReal (figureOnePerSampleMixingError q)) := by
  have hblock := balancedRejectedRetryBlock_leUpTo_stationary
    q I hsigma2 proposalCap properStride hproposalCap
      (figureOneHalfPerSampleMixingError_pos q)
      (figureOneHalfPerSampleMixingError_le_one q)
      hwalk hcapBudget
  have hhalf : 0 ≤ figureOnePerSampleMixingError q / 2 :=
    (figureOneHalfPerSampleMixingError_pos q).le
  have hadd : figureOnePerSampleMixingError q / 2 +
      figureOnePerSampleMixingError q / 2 =
        figureOnePerSampleMixingError q := by ring
  simpa only [← ENNReal.ofReal_add hhalf hhalf, hadd] using hblock

/-- Fully concrete phase-wise form of CV18 Lemma 7.17(c).  KLS acceptance
and rejection masses, first-block mixing, and stationary-retry mixing are all
discharged.  The remaining premises are explicit integer cap/walk
inequalities and warmness of the retained history marginal for this phase. -/
theorem approxIndepFun_balancedTransition_history_figureOnePerSample
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    {M : ℝ} (hM : 1 ≤ M)
    (hbaseWarm : Arlib.IsWarm (ENNReal.ofReal M) (history.map state)
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hproposalCap : 0 < proposalCap)
    (hfirstWalk : 4 * ((Real.log (2 * M) +
        2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
          (properStride : ℝ))
    (hfirstCap : ((properStride : ℕ) : ENNReal) *
        ENNReal.ofReal (2 * M) ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (hretryWalk : 4 * ((Real.log 2 +
        2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
          (properStride : ℝ))
    (hretryCap : ((properStride : ℕ) : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (pastProduct : H → ℝ)
    (nextEstimator : Option (AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (hretryAccuracy :
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
      let blockError := ENNReal.ofReal (figureOnePerSampleMixingError q)
      let error := blockError + rejectMass *
        balancedRetryError blockError rejectMass attempts
      (error + error).toReal ≤ figureOneDependentEpsilon q) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1) ∘ state)) := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmass0 := Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (accuracyPhaseTruncatedBody_convex q I sigma2)
    (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
    (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
    (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
    (figureOneProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [pi] using balancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ :=
    balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  let blockError := ENNReal.ofReal (figureOnePerSampleMixingError q)
  have hblockError : blockError ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  let _ : IsProbabilityMeasure (history.map state) :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hfirstBlock :=
    balancedAccuracyFirstBlock_leUpTo_figureOnePerSample
      q I hsigma2 proposalCap properStride hproposalCap
        (history.map state) hM hbaseWarm hfirstWalk hfirstCap
  have hretryBlock :=
    balancedAccuracyRetryBlock_leUpTo_figureOnePerSample
      q I hsigma2 proposalCap properStride hproposalCap
        hretryWalk hretryCap
  have hbudget :
      let rejectMass :=
        balancedRejectedStateMeasure q I sigma2 pi Set.univ
      let error := blockError + rejectMass *
        balancedRetryError blockError rejectMass attempts
      (error + error).toReal ≤
        3 * (figureOneDependentMaxSampleCount q : ℝ) *
          (figureOneDependentPhaseCount q : ℝ) *
            figureOnePerSampleMixingError q := by
    rw [figureOne_lemma717c_budget]
    simpa only [pi, blockError] using hretryAccuracy
  have hresult :=
    approxIndepFun_balancedTransition_history_of_warm_blocks
      q I hsigma2 proposalCap properStride attempts history state hstate pi
        hblockError hblockError hacceptedLower hrejectedLower
        hfirstBlock hretryBlock pastProduct nextEstimator hpastProduct
        hnextEstimator (figureOneDependentMaxSampleCount q)
        (figureOneDependentPhaseCount q)
        (figureOnePerSampleMixingError q) hbudget
  rw [figureOne_lemma717c_budget] at hresult
  simpa only [pi, blockError] using hresult

/-- Adjacent cooling-phase specialization.  The exact speedy-stationary
warm-start theorem discharges the analytic history warmness premise once the
retained state marginal is identified with the preceding phase's stationary
law. -/
theorem approxIndepFun_balancedTransition_history_adjacent_figureOnePerSample
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (proposalCap properStride attempts : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (hstateLaw : history.map state =
      Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I (scheduleValue q phase))
        (figureOneProposalRadius q (scheduleValue q phase))
        (scheduleValue q phase))
    (hproposalCap : 0 < proposalCap)
    (hfirstWalk :
      let M := speedyAdjacentWarmConstant q
      let sigma2 := scheduleValue q (phase + 1)
      4 * ((Real.log (2 * M) +
          2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
        (figureOneProposalRadius q sigma2 * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
            (properStride : ℝ))
    (hfirstCap :
      let M := speedyAdjacentWarmConstant q
      ((properStride : ℕ) : ENNReal) * ENNReal.ofReal (2 * M) ≤
        (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
          ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (hretryWalk :
      let sigma2 := scheduleValue q (phase + 1)
      4 * ((Real.log 2 +
          2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
        (figureOneProposalRadius q sigma2 * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
            (properStride : ℝ))
    (hretryCap : ((properStride : ℕ) : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (pastProduct : H → ℝ)
    (nextEstimator : Option (AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (hretryAccuracy :
      let sigma2 := scheduleValue q (phase + 1)
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
      let blockError := ENNReal.ofReal (figureOnePerSampleMixingError q)
      let error := blockError + rejectMass *
        balancedRetryError blockError rejectMass attempts
      (error + error).toReal ≤ figureOneDependentEpsilon q) :
    let sigma2 := scheduleValue q (phase + 1)
    ApproxIndepFun (figureOneDependentEpsilon q)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1) ∘ state)) := by
  dsimp only
  let M := speedyAdjacentWarmConstant q
  let sigma2 := scheduleValue q (phase + 1)
  have hsigma2 : 0 < sigma2 := scheduleValue_pos q (phase + 1)
  have hbaseWarm : Arlib.IsWarm (ENNReal.ofReal M) (history.map state)
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
    rw [hstateLaw]
    simpa only [M, sigma2] using
      accuracyPhase_speedyStationary_adjacent_isWarm q I phase
  exact approxIndepFun_balancedTransition_history_figureOnePerSample
    q I hsigma2 proposalCap properStride attempts history state hstate
      (speedyAdjacentWarmConstant_one_le q) hbaseWarm hproposalCap
      hfirstWalk hfirstCap hretryWalk hretryCap pastProduct nextEstimator
      hpastProduct hnextEstimator hretryAccuracy

#print axioms figureOnePerSampleMixingError_le_one
#print axioms balancedAccuracyFirstBlock_leUpTo_figureOnePerSample
#print axioms balancedAccuracyRetryBlock_leUpTo_figureOnePerSample
#print axioms approxIndepFun_balancedTransition_history_figureOnePerSample
#print axioms approxIndepFun_balancedTransition_history_adjacent_figureOnePerSample

end ArlibCommunity.Algorithms.CV18
