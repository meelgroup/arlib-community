/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledFiniteRetry
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledBlockApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledMixing

/-! # Concrete scheduled balanced transition

This file instantiates scheduled speedy mixing, local-cap loss, geometric
retry, and the scheduled accepted-target correction.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

theorem figureOneCorrectedBlockMixingError_le_one
    (q : VolumeParams) (attempts : ℕ) :
    figureOneCorrectedBlockMixingError q attempts ≤ 1 := by
  unfold figureOneCorrectedBlockMixingError
  have h := figureOnePerSampleMixingError_le_one q
  have ha : 0 ≤ (attempts : ℝ) := Nat.cast_nonneg attempts
  have hden : 1 ≤ 4 * (attempts + 1 : ℝ) := by nlinarith
  rw [div_le_one (by nlinarith)]
  exact h.trans hden

theorem figureOneFinalScheduledLocalCapRequirement_le_proposalCap
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneFinalScheduledLocalCapRequirement q sigma2 ≤
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 : ℝ) := by
  calc
    figureOneFinalScheduledLocalCapRequirement q sigma2 ≤
        (Nat.ceil (figureOneFinalScheduledLocalCapRequirement q sigma2) : ℝ) :=
      Nat.le_ceil _
    _ ≤ (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 : ℝ) := by
      rw [figureOneFinalScheduledBalancedParameters_proposalCap,
        figureOneFinalScheduledLocalProposalCap]
      exact_mod_cast Nat.le_add_left _ _

/-- The enlarged final local cap pays the cap-exhaustion half of every first
block comparison. -/
theorem figureOneFinalScheduled_firstCapBudget
    (q : VolumeParams) (sigma2 : ℝ) :
    let attempts := figureOneSafeRetryCount q - 1
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
    (stride : ENNReal) * ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) ≤
      (ENNReal.ofReal (1 / 2) * (cap : ENNReal)) *
        figureOneCorrectedBlockBudget q attempts := by
  dsimp only
  let attempts := figureOneSafeRetryCount q - 1
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let e := figureOneCorrectedBlockMixingError q attempts
  let W := 16 * speedyAdjacentWarmConstant q
  have he : 0 < e := figureOneCorrectedBlockMixingError_pos q attempts
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity [speedyAdjacentWarmConstant_pos q]
  have hs : 0 ≤ (stride : ℝ) := Nat.cast_nonneg stride
  have hcap :
      2 * (stride : ℝ) * W / e ≤ (cap : ℝ) := by
    simpa [figureOneFinalScheduledLocalCapRequirement, attempts, stride, cap,
      e, W, figureOneFinalScheduledBalancedParameters_properStride] using
      figureOneFinalScheduledLocalCapRequirement_le_proposalCap q sigma2
  have hreal : (stride : ℝ) * W ≤ (1 / 2 : ℝ) * (cap : ℝ) * e := by
    rw [div_le_iff₀ he] at hcap
    nlinarith
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul hs,
    ENNReal.ofReal_mul
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (Nat.cast_nonneg cap)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast] at h
  simpa [e, W, stride, cap, attempts, figureOneCorrectedBlockBudget] using h

theorem figureOneFinalScheduled_retryCapBudget
    (q : VolumeParams) (sigma2 : ℝ) :
    let attempts := figureOneSafeRetryCount q - 1
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
    (stride : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (cap : ENNReal)) *
        figureOneCorrectedBlockBudget q attempts := by
  dsimp only
  have htwo : (2 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal <| by
      have hM := speedyAdjacentWarmConstant_one_le q
      nlinarith
  calc
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2 : ENNReal) * 2 ≤
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2 : ENNReal) *
          ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by gcongr
    _ ≤ _ := figureOneFinalScheduled_firstCapBudget q sigma2

theorem scheduledBalancedRejectedStationary_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    Arlib.IsWarm 2
      (Arlib.condOn
        (scheduledBalancedRejectedStateMeasure q I sigma2 pi) Set.univ) pi := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let branch := scheduledBalancedRejectedStateMeasure q I sigma2 pi
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hp : (2 : ENNReal)⁻¹ ≤ branch Set.univ := by
    simpa [branch] using
      scheduledBalancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hle : branch ≤ pi := by
    simpa [branch] using
      scheduledBalancedRejectedStateMeasure_le q I sigma2 pi
  intro A hA
  rw [Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul]
  have hbranch : branch A ≤ pi A := Measure.le_iff.mp hle A hA
  calc
    (branch Set.univ)⁻¹ * branch A ≤
        (branch Set.univ)⁻¹ * pi A := mul_le_mul' le_rfl hbranch
    _ ≤ ((2 : ENNReal)⁻¹)⁻¹ * pi A := by gcongr
    _ = 2 * pi A := by norm_num

/-- Concrete scheduled retry block.  One block budget pays cap exhaustion and
one pays mixing. -/
theorem scheduledBalancedRejectedRetryBlock_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) (hproposalCap : 0 < proposalCap)
    (hwalk : figureOneScheduledCorrectedRetryWalkRequirement
      q sigma2 attempts ≤ (properStride : ℝ))
    (hcapBudget : (properStride : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        figureOneCorrectedBlockBudget q attempts) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
    let rejectedProb := Arlib.condOn rejected Set.univ
    MeasureLeUpTo
      ((rejectedProb.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
  let rejectedProb := Arlib.condOn rejected Set.univ
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hrejectedLower : (2 : ENNReal)⁻¹ ≤ rejected Set.univ := by
    simpa [rejected, pi] using
      scheduledBalancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hrejected0 : rejected Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le hrejectedLower
  have hrejectedTop : rejected Set.univ ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        scheduledBalancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hwarm : Arlib.IsWarm 2 rejectedProb pi := by
    simpa [K, delta, pi, rejected, rejectedProb] using
      scheduledBalancedRejectedStationary_isWarm q I hsigma2
  have hmixWithin := mixesWithin_scheduledPhaseBody_figureOne_cv18
    q I hsigma2 (M := 2)
      (eps := figureOneCorrectedBlockMixingError q attempts)
      (by norm_num) (by simpa using hwarm)
      (figureOneCorrectedBlockMixingError_pos q attempts)
      (figureOneCorrectedBlockMixingError_le_one q attempts) hwalk
  have hmix : Arlib.TVLe
      (iterate
        (lazy (speedyMetropolisGaussian K delta sigma2))
        rejectedProb properStride)
      pi (ENNReal.ofReal (figureOneCorrectedBlockMixingError q attempts)) := by
    simpa [MixesWithin, K, delta, pi, rejected, rejectedProb] using hmixWithin
  have hblock :=
    bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
      q I hsigma2 proposalCap properStride hproposalCap rejectedProb hwarm
        hcapBudget hmix
  have hmixEq : ENNReal.ofReal
      (figureOneCorrectedBlockMixingError q attempts) =
        figureOneCorrectedBlockBudget q attempts := by
    rfl
  simpa [hmixEq, two_mul] using hblock

/-- A two-warm perturbation of a retained law which is itself
`8 * speedyAdjacentWarmConstant`-warm has the `16 *` warmness used by the
scheduled first-block stride. -/
theorem scheduledBalancedFirstBlock_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) (hproposalCap : 0 < proposalCap)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) rho
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hwalk : figureOneScheduledCorrectedFirstWalkRequirement
      q sigma2 attempts ≤ (properStride : ℝ))
    (hcapBudget : (properStride : ENNReal) *
        ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) *
        figureOneCorrectedBlockBudget q attempts) :
    ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo
        ((mu.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        ((ellGaussianProb
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2).map some)
        (2 * figureOneCorrectedBlockBudget q attempts) := by
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hMpos : 0 < speedyAdjacentWarmConstant q :=
    speedyAdjacentWarmConstant_pos q
  have hwarmPi : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) mu pi := by
    have htrans := hwarm.trans hbaseWarm
    convert htrans using 1
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hmixWithin := mixesWithin_scheduledPhaseBody_figureOne_cv18
    q I hsigma2 (M := 16 * speedyAdjacentWarmConstant q)
      (eps := figureOneCorrectedBlockMixingError q attempts)
      (by
        have hM := speedyAdjacentWarmConstant_one_le q
        nlinarith)
      hwarmPi (figureOneCorrectedBlockMixingError_pos q attempts)
      (figureOneCorrectedBlockMixingError_le_one q attempts)
      (by
        change figureOneScheduledWalkRequirement q sigma2
          (16 * speedyAdjacentWarmConstant q)
            (figureOneCorrectedBlockMixingError q attempts) ≤
              (properStride : ℝ) at hwalk
        simpa only [figureOneScheduledWalkRequirement] using hwalk)
  have hmix : Arlib.TVLe
      (iterate
        (lazy (speedyMetropolisGaussian
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2))
        mu properStride)
      pi (ENNReal.ofReal (figureOneCorrectedBlockMixingError q attempts)) := by
    simpa [MixesWithin, pi] using hmixWithin
  have hblock :=
    bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
      q I hsigma2 proposalCap properStride hproposalCap mu hwarmPi
        hcapBudget hmix
  have hmixEq : ENNReal.ofReal
      (figureOneCorrectedBlockMixingError q attempts) =
        figureOneCorrectedBlockBudget q attempts := by rfl
  simpa [hmixEq, two_mul] using hblock

/-- The complete concrete scheduled transition estimate.  Once the retained
law for the phase is `8 * speedyAdjacentWarmConstant`-warm for that phase's
scheduled speedy stationary law, every two-warm input law is within the full
corrected transition budget of the ideal restricted Gaussian observation.
All stride, local-cap, retry-tail, and accepted-target premises are discharged
by the final executable parameters. -/
theorem bind_figureOneFinalScheduledBalancedTransition_tvLe
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) rho
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      Arlib.TVLe
        (mu.bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2
            (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
            (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
        ((truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n)).map some)
        (figureOneCorrectedTransitionBudget q) := by
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  let attempts := figureOneSafeRetryCount q - 1
  let proposalCap :=
    figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let properStride :=
    figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hproposalCap : 0 < proposalCap := by
    simpa [proposalCap] using
      figureOneFinalScheduledBalancedParameters_proposalCap_pos q sigma2
  have hfirst : MeasureLeUpTo
      ((mu.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    exact scheduledBalancedFirstBlock_leUpTo_stationary
      q I hsigma2 proposalCap properStride attempts hproposalCap rho
        hbaseWarm
        (by
          simpa [properStride, attempts,
            figureOneFinalScheduledBalancedParameters_properStride] using
            figureOneScheduledCorrectedFirstWalkRequirement_le_stride
              q sigma2 attempts)
        (by
          simpa [properStride, proposalCap, attempts] using
            figureOneFinalScheduled_firstCapBudget q sigma2)
        mu hmu hwarm
  have hretry :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    simpa [K, delta, pi] using
      scheduledBalancedRejectedRetryBlock_leUpTo_stationary
        q I hsigma2 proposalCap properStride attempts hproposalCap
          (by
            simpa [properStride, attempts,
              figureOneFinalScheduledBalancedParameters_properStride] using
              figureOneScheduledCorrectedRetryWalkRequirement_le_stride
                q sigma2 attempts)
          (by
            simpa [properStride, proposalCap, attempts] using
              figureOneFinalScheduled_retryCapBudget q sigma2)
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 := by
    dsimp [K]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ := by
    dsimp [K]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [K, delta, pi] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hreject :
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ ≤
        ENNReal.ofReal (121 / 128 : ℝ) :=
    scheduledBalancedRejectedStateMeasure_mass_le
      q I hsigma2 pi haccepted
  have htail :
      (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ) ^
          (attempts + 1) ≤ figureOneCorrectedRetryTailBudget q := by
    simpa [attempts] using figureOneSafeRetryTail_le q hreject
  have htv :=
    bind_scheduledBalancedTransition_tvLe_truncatedGaussian_corrected
      q I hsigma2 proposalCap properStride attempts mu hfirst hretry htail
  simpa [proposalCap, properStride, attempts,
    Nat.sub_add_cancel (figureOneSafeRetryCount_pos q)] using htv

#print axioms figureOneFinalScheduled_firstCapBudget
#print axioms figureOneFinalScheduled_retryCapBudget
#print axioms bind_figureOneFinalScheduledBalancedTransition_tvLe

end ArlibCommunity.Algorithms.CV18
