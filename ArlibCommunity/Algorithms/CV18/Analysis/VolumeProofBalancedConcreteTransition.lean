/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedGlobalCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportance

/-!
# Concrete balanced-transition comparison with the ideal CV18 phase target

This module composes the finite balanced-retry comparison with the KLS
accepted-target comparison.  It also records the precise numerical obstruction
to charging the resulting transition to the existing one-per-sample
`exact-chance` budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The stationary KLS accepted-target error paid after the balanced retry
has produced a successful target-space point. -/
noncomputable def balancedStationaryTargetError (q : VolumeParams) : ENNReal :=
  96 * ENNReal.ofReal (accuracyCoreError q) +
    ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)

theorem balancedStationaryTargetError_pos (q : VolumeParams) :
    0 < balancedStationaryTargetError q := by
  unfold balancedStationaryTargetError
  have hcore : 0 < ENNReal.ofReal (accuracyCoreError q) :=
    ENNReal.ofReal_pos.mpr (accuracyCoreError_pos q)
  positivity

theorem balancedStationaryTargetError_ne_top (q : VolumeParams) :
    balancedStationaryTargetError q ≠ ⊤ := by
  unfold balancedStationaryTargetError
  exact ENNReal.add_ne_top.mpr ⟨
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩

/-- The balanced normalization does not alter the conditional successful
target law; at speedy stationarity it therefore has exactly the existing KLS
comparison with the desired restricted Gaussian.  The inverse homothety in
`balancedAccuracyGaussianAcceptedTargetLaw` is the target-coordinate
rescaling used by the chronological collector. -/
theorem balancedAccuracyGaussianAcceptedTargetLaw_tv_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    Arlib.TVLe
      (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (balancedStationaryTargetError q) := by
  dsimp only
  rw [balancedAccuracyGaussianAcceptedTargetLaw_eq]
  simpa only [balancedStationaryTargetError] using
    accuracyPhase_stationaryAcceptedTargetLaw_tv q I hsigma2

/-- Complete integrated comparison for one finite balanced transition.  The
first two summands are the first-block/retry cost; the final summand is the
paper's KLS accepted-target-to-restricted-Gaussian comparison. -/
theorem bind_balancedTransition_tvLe_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    {firstError retryError : ENNReal}
    (hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      ((Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2).map some) firstError)
    (hretryBlock :
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
    Arlib.TVLe
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (firstError + rejectMass *
          balancedRetryError retryError rejectMass attempts +
        balancedStationaryTargetError q) := by
  dsimp only
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
  have htransition := bind_balancedTransition_tvLe_acceptedTarget
    q I hsigma2 proposalCap properStride attempts rho pi
      hacceptedLower hrejectedLower hfirstBlock hretryBlock
  have htarget :=
    (balancedAccuracyGaussianAcceptedTargetLaw_tv_truncatedGaussian
      q I hsigma2).map measurable_some
  exact htransition.trans htarget

/-- Error delivered by the available finite-block plus KLS comparison when
both proper blocks consume the current full per-sample block budget. -/
noncomputable def figureOneGlobalBalancedTransitionError
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) : ENNReal :=
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let blockError := ENNReal.ofReal (figureOnePerSampleMixingError q)
  let attempts := figureOneGlobalBalancedParameters.retryLimit q sigma2 - 1
  blockError + rejectMass * balancedRetryError blockError rejectMass attempts +
    balancedStationaryTargetError q

/-- Specialization to the global balanced syntax.  The stride deadlines and
positivity of the global cap/retry count are discharged.  The two displayed
cap inequalities remain explicit because the outer global cutoff is not a
per-block failure allocation. -/
theorem bind_figureOneGlobalBalancedTransition_tvLe_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : Arlib.IsWarm (ENNReal.ofReal (speedyAdjacentWarmConstant q)) rho
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hfirstCap :
      ((figureOneGlobalProperStride q sigma2 : ℕ) : ENNReal) *
          ENNReal.ofReal (2 * speedyAdjacentWarmConstant q) ≤
        (ENNReal.ofReal (1 / 2) *
            (figureOneGlobalQueryBudget q : ENNReal)) *
          ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (hretryCap :
      ((figureOneGlobalProperStride q sigma2 : ℕ) : ENNReal) * 2 ≤
        (ENNReal.ofReal (1 / 2) *
            (figureOneGlobalQueryBudget q : ENNReal)) *
          ENNReal.ofReal (figureOnePerSampleMixingError q / 2)) :
    Arlib.TVLe
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2
          (figureOneGlobalBalancedParameters.proposalCap q sigma2)
          (figureOneGlobalBalancedParameters.properStride q sigma2)
          (figureOneGlobalBalancedParameters.retryLimit q sigma2)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneGlobalBalancedTransitionError q I sigma2) := by
  let cap := figureOneGlobalQueryBudget q
  let stride := figureOneGlobalProperStride q sigma2
  let retries := figureOneDependentMaxSampleCount q *
    figureOneDependentPhaseCount q
  let attempts := retries - 1
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let blockError := ENNReal.ofReal (figureOnePerSampleMixingError q)
  have hcapPos : 0 < cap := figureOneGlobalQueryBudget_pos q
  have hM : 1 ≤ speedyAdjacentWarmConstant q :=
    speedyAdjacentWarmConstant_one_le q
  have hfirstWalk :
      4 * ((Real.log (2 * speedyAdjacentWarmConstant q) +
          2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
        (figureOneProposalRadius q sigma2 * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
        (stride : ℝ) := by
    simpa [stride, figureOneGlobalFirstWalkRequirement] using
      figureOneGlobalFirstWalkRequirement_le_stride q sigma2
  have hretryWalk :
      4 * ((Real.log 2 +
          2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
        (figureOneProposalRadius q sigma2 * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
        (stride : ℝ) := by
    simpa [stride, figureOneGlobalRetryWalkRequirement] using
      figureOneGlobalRetryWalkRequirement_le_stride q sigma2
  have hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 cap stride)).map optionSnd)
      (pi.map some) blockError := by
    have hall := balancedAccuracyFirstBlock_leUpTo_figureOnePerSample
      q I hsigma2 cap stride hcapPos rho hM hbaseWarm hfirstWalk
        (by simpa [cap, stride] using hfirstCap)
    exact hall rho inferInstance
      ((Arlib.IsWarm.refl rho).mono (by norm_num))
  have hretryBlock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 cap stride)).map optionSnd)
        (pi.map some) blockError := by
    simpa [cap, stride, pi, blockError] using
      balancedAccuracyRetryBlock_leUpTo_figureOnePerSample
        q I hsigma2 cap stride hcapPos hretryWalk
          (by simpa [cap, stride] using hretryCap)
  have hretriesPos : 0 < retries := by
    exact Nat.mul_pos (figureOneDependentMaxSampleCount_pos q)
      (figureOneDependentPhaseCount_pos q)
  have hretriesEq : attempts + 1 = retries := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hretriesPos.ne')
  have htransition := bind_balancedTransition_tvLe_truncatedGaussian
    q I hsigma2 cap stride attempts rho hfirstBlock hretryBlock
  simpa only [cap, stride, retries, attempts, pi, blockError, hretriesEq,
    figureOneGlobalBalancedParameters, figureOneGlobalBalancedTransitionError]
    using htransition

/-- Adjacent-phase integrated form.  This discharges the schedule warm start
for the preceding speedy stationary law and leaves only the two local-cap
inequalities made explicit above. -/
theorem bind_figureOneGlobalBalancedTransition_adjacent_tvLe
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hfirstCap :
      let sigma2 := scheduleValue q (phase + 1)
      ((figureOneGlobalProperStride q sigma2 : ℕ) : ENNReal) *
          ENNReal.ofReal (2 * speedyAdjacentWarmConstant q) ≤
        (ENNReal.ofReal (1 / 2) *
            (figureOneGlobalQueryBudget q : ENNReal)) *
          ENNReal.ofReal (figureOnePerSampleMixingError q / 2))
    (hretryCap :
      let sigma2 := scheduleValue q (phase + 1)
      ((figureOneGlobalProperStride q sigma2 : ℕ) : ENNReal) * 2 ≤
        (ENNReal.ofReal (1 / 2) *
            (figureOneGlobalQueryBudget q : ENNReal)) *
          ENNReal.ofReal (figureOnePerSampleMixingError q / 2)) :
    let previousSigma2 := scheduleValue q phase
    let sigma2 := scheduleValue q (phase + 1)
    let previousPi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I previousSigma2)
      (figureOneProposalRadius q previousSigma2) previousSigma2
    Arlib.TVLe
      (previousPi.bind
        (balancedAccuracyTransitionLawAux q I sigma2
          (figureOneGlobalBalancedParameters.proposalCap q sigma2)
          (figureOneGlobalBalancedParameters.properStride q sigma2)
          (figureOneGlobalBalancedParameters.retryLimit q sigma2)))
      ((truncatedGaussianProbability q I sigma2
          (scheduleValue_pos q (phase + 1)) :
        Measure (AmbientSpace q.n)).map some)
      (figureOneGlobalBalancedTransitionError q I sigma2) := by
  dsimp only
  let previousSigma2 := scheduleValue q phase
  let sigma2 := scheduleValue q (phase + 1)
  let previousPi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I previousSigma2)
    (figureOneProposalRadius q previousSigma2) previousSigma2
  have hpreviousSigma2 : 0 < previousSigma2 := scheduleValue_pos q phase
  have hpreviousDelta : 0 < figureOneProposalRadius q previousSigma2 :=
    figureOneProposalRadius_pos q hpreviousSigma2
  have hpreviousMass0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I previousSigma2)
      (accuracyPhaseTruncatedBody_convex q I previousSigma2)
      (accuracyPhaseTruncatedBody_isCompact q I previousSigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hpreviousSigma2)
      hpreviousDelta previousSigma2
  have hpreviousMassTop :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I previousSigma2)
      (figureOneProposalRadius q previousSigma2) hpreviousSigma2
  let _ : IsProbabilityMeasure previousPi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb
      hpreviousMass0 hpreviousMassTop
  have hwarm : Arlib.IsWarm
      (ENNReal.ofReal (speedyAdjacentWarmConstant q)) previousPi
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
    simpa only [previousSigma2, sigma2, previousPi] using
      accuracyPhase_speedyStationary_adjacent_isWarm q I phase
  exact bind_figureOneGlobalBalancedTransition_tvLe_truncatedGaussian
    q I (scheduleValue_pos q (phase + 1)) previousPi hwarm
      (by simpa [sigma2] using hfirstCap)
      (by simpa [sigma2] using hretryCap)

/-- The currently available composed transition error is strictly larger
than the entire one-per-sample exact-chance allocation, even before using the
positive retry contribution.  Consequently a theorem bounding this expression
by `figureOnePerSampleMixingError` cannot hold with the present allocation. -/
theorem figureOnePerSampleMixingError_lt_globalBalancedTransitionError
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ENNReal.ofReal (figureOnePerSampleMixingError q) <
      figureOneGlobalBalancedTransitionError q I sigma2 := by
  unfold figureOneGlobalBalancedTransitionError
  dsimp only
  have htarget := balancedStationaryTargetError_pos q
  have hretry : 0 ≤
      balancedRejectedStateMeasure q I sigma2
          (Arlib.MarkovChains.ellGaussianProb
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2) Set.univ *
        balancedRetryError (ENNReal.ofReal (figureOnePerSampleMixingError q))
          (balancedRejectedStateMeasure q I sigma2
            (Arlib.MarkovChains.ellGaussianProb
              (accuracyPhaseTruncatedBody q I sigma2)
              (figureOneProposalRadius q sigma2) sigma2) Set.univ)
          (figureOneGlobalBalancedParameters.retryLimit q sigma2 - 1) :=
    bot_le
  calc
    ENNReal.ofReal (figureOnePerSampleMixingError q) <
      ENNReal.ofReal (figureOnePerSampleMixingError q) +
          balancedStationaryTargetError q :=
      ENNReal.lt_add_right (by simp) htarget.ne'
    _ ≤ ENNReal.ofReal (figureOnePerSampleMixingError q) +
          balancedRejectedStateMeasure q I sigma2
              (Arlib.MarkovChains.ellGaussianProb
                (accuracyPhaseTruncatedBody q I sigma2)
                (figureOneProposalRadius q sigma2) sigma2) Set.univ *
            balancedRetryError
              (ENNReal.ofReal (figureOnePerSampleMixingError q))
              (balancedRejectedStateMeasure q I sigma2
                (Arlib.MarkovChains.ellGaussianProb
                  (accuracyPhaseTruncatedBody q I sigma2)
                  (figureOneProposalRadius q sigma2) sigma2) Set.univ)
              (figureOneGlobalBalancedParameters.retryLimit q sigma2 - 1) +
          balancedStationaryTargetError q := by
      have hbase : ENNReal.ofReal (figureOnePerSampleMixingError q) ≤
          ENNReal.ofReal (figureOnePerSampleMixingError q) +
            balancedRejectedStateMeasure q I sigma2
                (Arlib.MarkovChains.ellGaussianProb
                  (accuracyPhaseTruncatedBody q I sigma2)
                  (figureOneProposalRadius q sigma2) sigma2) Set.univ *
              balancedRetryError
                (ENNReal.ofReal (figureOnePerSampleMixingError q))
                (balancedRejectedStateMeasure q I sigma2
                  (Arlib.MarkovChains.ellGaussianProb
                    (accuracyPhaseTruncatedBody q I sigma2)
                    (figureOneProposalRadius q sigma2) sigma2) Set.univ)
                (figureOneGlobalBalancedParameters.retryLimit q sigma2 - 1) :=
        le_add_right le_rfl
      simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_right hbase (balancedStationaryTargetError q)

#print axioms balancedAccuracyGaussianAcceptedTargetLaw_tv_truncatedGaussian
#print axioms bind_balancedTransition_tvLe_truncatedGaussian
#print axioms bind_figureOneGlobalBalancedTransition_adjacent_tvLe
#print axioms figureOnePerSampleMixingError_lt_globalBalancedTransitionError

end ArlibCommunity.Algorithms.CV18
