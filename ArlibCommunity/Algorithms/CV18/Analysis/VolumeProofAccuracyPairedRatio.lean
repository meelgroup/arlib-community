/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyTVL2
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPairedProgram

/-! # One-phase paired ratio analysis for CV18

This file turns the paired numerator/denominator collector into the local
ratio estimate used by a cooling phase.  The analytic core below records the
stationary denominator floor and centers the shared numerator exactly at the
accepted KLS mean.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Stationary mean of the executable acceptance denominator. -/
noncomputable def accuracyStationaryAcceptanceMean
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) : ℝ :=
  ∫ x, accuracyAcceptanceWeight q I sigma2 x
    ∂Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2

/-- Stationary mean of a target observable after the KLS accepted-output
normalization. -/
noncomputable def accuracyStationaryAcceptedMean
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) : ℝ :=
  ∫ y, weight y
    ∂accuracyGaussianAcceptedTargetLaw q I sigma2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)

/-- The normalized speedy stationary law of every positive accuracy phase is
a probability measure. -/
theorem accuracyPhase_ellGaussianProb_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsProbabilityMeasure
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
  apply Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb
  · exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      (figureOneProposalRadius_pos q hsigma2) sigma2
  · exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      (figureOneProposalRadius q sigma2) hsigma2

/-- The real denominator mean retains the proved KLS `7/64` floor. -/
theorem accuracyStationaryAcceptanceMean_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    7 / 64 ≤ accuracyStationaryAcceptanceMean q I sigma2 := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let p := (pi.withDensity
    (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmassTop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  have hpTop : p ≠ ⊤ := by
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <| by
      dsimp [p]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      calc
        (∫⁻ x, accuracyGaussianRejectionAcceptance q I sigma2 x ∂pi) ≤
            ∫⁻ _x, (1 : ENNReal) ∂pi := by
          exact lintegral_mono <|
            accuracyGaussianRejectionAcceptance_le_one q I hsigma2
        _ = pi Set.univ := lintegral_one
  have hfloor : ENNReal.ofReal (7 / 64 : ℝ) ≤ p := by
    simpa [p, pi, K, delta] using
      accuracyPhase_stationary_acceptance_ge q I hsigma2
  have hreal := ENNReal.toReal_mono hpTop hfloor
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 7 / 64)] at hreal
  have hden := integral_accuracyAcceptanceWeight_eq_mass
    q I hsigma2 pi
  simpa [accuracyStationaryAcceptanceMean, pi, K, delta, p, hden] using hreal

theorem accuracyStationaryAcceptanceMean_pos
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < accuracyStationaryAcceptanceMean q I sigma2 :=
  (by norm_num : (0 : ℝ) < 7 / 64).trans_le
    (accuracyStationaryAcceptanceMean_ge q I hsigma2)

theorem accuracyStationaryAcceptanceMean_nonneg
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    0 ≤ accuracyStationaryAcceptanceMean q I sigma2 := by
  unfold accuracyStationaryAcceptanceMean
  exact integral_nonneg fun x =>
    accuracyAcceptanceWeight_nonneg q I sigma2 x

theorem accuracyStationaryAcceptanceMean_le_one
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    accuracyStationaryAcceptanceMean q I sigma2 ≤ 1 := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let _ : IsProbabilityMeasure pi :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  change (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂pi) ≤ 1
  have haint : Integrable (accuracyAcceptanceWeight q I sigma2) pi :=
    Arlib.integrable_of_forall_mem_Icc
      (measurable_accuracyAcceptanceWeight q I sigma2)
      (accuracyAcceptanceWeight_nonneg q I sigma2)
      (accuracyAcceptanceWeight_le_one q I hsigma2)
  calc
    (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂pi) ≤
        ∫ _x, (1 : ℝ) ∂pi := by
      apply integral_mono haint (integrable_const 1)
      exact accuracyAcceptanceWeight_le_one q I hsigma2
    _ = 1 := by simp

/-- The denominator observable is centered and bounded by one. -/
theorem accuracyAcceptanceWeight_sub_stationaryMean_abs_le_one
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (x : AmbientSpace q.n) :
    |accuracyAcceptanceWeight q I sigma2 x -
      accuracyStationaryAcceptanceMean q I sigma2| ≤ 1 := by
  have ha0 := accuracyAcceptanceWeight_nonneg q I sigma2 x
  have ha1 := accuracyAcceptanceWeight_le_one q I hsigma2 x
  have hp0 := accuracyStationaryAcceptanceMean_nonneg q I sigma2
  have hp1 := accuracyStationaryAcceptanceMean_le_one q I hsigma2
  rw [abs_le]
  constructor <;> linarith

theorem integral_accuracyAcceptanceWeight_sub_stationaryMean_eq_zero
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ∫ x, accuracyAcceptanceWeight q I sigma2 x -
        accuracyStationaryAcceptanceMean q I sigma2
      ∂Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 = 0 := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let p := accuracyStationaryAcceptanceMean q I sigma2
  let _ : IsProbabilityMeasure pi :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  have hmem : MemLp (fun x => accuracyAcceptanceWeight q I sigma2 x - p)
      2 pi := by
    apply MemLp.of_bound
      ((measurable_accuracyAcceptanceWeight q I sigma2).sub
        measurable_const).aestronglyMeasurable 1
    filter_upwards with x
    simpa [Real.norm_eq_abs, p] using
      accuracyAcceptanceWeight_sub_stationaryMean_abs_le_one
        q I hsigma2 x
  have haint : Integrable (accuracyAcceptanceWeight q I sigma2) pi :=
    Arlib.integrable_of_forall_mem_Icc
      (measurable_accuracyAcceptanceWeight q I sigma2)
      (accuracyAcceptanceWeight_nonneg q I sigma2)
      (accuracyAcceptanceWeight_le_one q I hsigma2)
  have hp : (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂pi) = p := by
    rfl
  rw [integral_sub haint (integrable_const p), hp]
  simp

theorem accuracyAcceptanceWeight_sub_stationaryMean_memLp
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    MemLp (fun x => accuracyAcceptanceWeight q I sigma2 x -
      accuracyStationaryAcceptanceMean q I sigma2) 2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
  let _ : IsProbabilityMeasure
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  apply MemLp.of_bound
    ((measurable_accuracyAcceptanceWeight q I sigma2).sub
      measurable_const).aestronglyMeasurable 1
  filter_upwards with x
  simpa [Real.norm_eq_abs] using
    accuracyAcceptanceWeight_sub_stationaryMean_abs_le_one
      q I hsigma2 x

/-- A continuous target observable becomes globally bounded after the KLS
acceptance indicator, even when it is unbounded on the ambient space. -/
theorem exists_accuracyImportanceWeight_abs_sub_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (m : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |accuracyImportanceWeight q I sigma2 weight x - m| ≤ B := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  have hK : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have habs : Continuous fun y => |weight y| := hweight.abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image habs.continuousOn
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    refine ⟨unitBall_subset_truncatedBody q I
      (Metric.mem_closedBall_self zero_le_one), ?_⟩
    exact Metric.mem_closedBall_self (accuracyPhaseRadius_pos q hsigma2).le
  have hC0 : 0 ≤ C :=
    (abs_nonneg (weight 0)).trans (hC <| Set.mem_image_of_mem _ hzero)
  refine ⟨C + |m|, add_nonneg hC0 (abs_nonneg m), ?_⟩
  intro x
  let target : AmbientSpace q.n := (accuracyScaleFactor q)⁻¹ • x
  by_cases ht : target ∈ K
  · have hwC : |weight target| ≤ C :=
      hC (Set.mem_image_of_mem (fun y => |weight y|) ht)
    have ha0 : 0 ≤ accuracyAcceptanceWeight q I sigma2 x :=
      accuracyAcceptanceWeight_nonneg q I sigma2 x
    have ha1 : accuracyAcceptanceWeight q I sigma2 x ≤ 1 :=
      accuracyAcceptanceWeight_le_one q I hsigma2 x
    calc
      |accuracyImportanceWeight q I sigma2 weight x - m| ≤
          |accuracyImportanceWeight q I sigma2 weight x| + |m| :=
        abs_sub _ _
      _ = accuracyAcceptanceWeight q I sigma2 x * |weight target| + |m| := by
        simp [accuracyImportanceWeight, target, abs_mul, abs_of_nonneg ha0]
      _ ≤ 1 * C + |m| := by gcongr
      _ = C + |m| := by ring
  · have haccept : accuracyAcceptanceWeight q I sigma2 x = 0 := by
      simp [accuracyAcceptanceWeight, accuracyGaussianRejectionAcceptance,
        target, K, ht]
    rw [accuracyImportanceWeight, haccept, zero_mul, zero_sub, abs_neg]
    linarith [abs_nonneg m]

/-- The paired numerator centered at the stationary accepted mean has exact
mean zero under speedy stationarity. -/
theorem integral_accuracyImportanceWeight_sub_acceptedMean_eq_zero
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) :
    ∫ x, accuracyImportanceWeight q I sigma2
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) x
      ∂Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 = 0 := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let accepted := accuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let r := accuracyStationaryAcceptedMean q I sigma2 weight
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  change (∫ x, accuracyImportanceWeight q I sigma2
      (fun y => weight y - r) x ∂pi) = 0
  let _ : IsProbabilityMeasure pi :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  let _ : IsProbabilityMeasure accepted :=
    accuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_stationary q I hsigma2
  have hwarm : Arlib.IsWarm 64 accepted nu := by
    simpa [accepted, nu, pi] using
      stationary_accuracyAcceptedTarget_isWarm q I hsigma2
  have hle : accepted ≤ (64 : ENNReal) • nu :=
    (Arlib.MarkovChains.isWarm_iff_le_smul _ _).1 hwarm
  have hmemAccepted : MemLp weight 2 accepted :=
    (hmem.smul_measure (by norm_num : (64 : ENNReal) ≠ ⊤)).mono_measure hle
  have hint : Integrable weight accepted := hmemAccepted.integrable (by norm_num)
  have hr : r = ∫ y, weight y ∂accepted := by
    rfl
  have hcenter : ∫ y, weight y - r ∂accepted = 0 := by
    rw [integral_sub hint (integrable_const r), integral_const, hr]
    simp
  have hp0 :
      (pi.withDensity (accuracyGaussianRejectionAcceptance q I sigma2))
        Set.univ ≠ 0 := by
    have h := accuracyPhase_stationary_acceptance_ge q I hsigma2
    exact ne_of_gt <| (by norm_num :
      0 < ENNReal.ofReal (7 / 64 : ℝ)).trans_le (by simpa [pi] using h)
  have hformula := integral_accuracyImportanceWeight_eq_acceptance_mul
    q I hsigma2 pi (weight := fun y => weight y - r)
      (hweight.sub measurable_const) hp0
  rw [hformula]
  change _ * (∫ y, weight y - r ∂accepted) = 0
  rw [hcenter, mul_zero]

/-- The centered paired numerator is square-integrable under speedy
stationarity.  Compactness of the accepted core supplies the global bound
required by the Markov empirical theorem. -/
theorem accuracyImportanceWeight_sub_acceptedMean_memLp
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight) :
    MemLp (fun x => accuracyImportanceWeight q I sigma2
      (fun y => weight y -
        accuracyStationaryAcceptedMean q I sigma2 weight) x) 2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
  let r := accuracyStationaryAcceptedMean q I sigma2 weight
  let _ : IsProbabilityMeasure
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  obtain ⟨B, hB, hbound⟩ :=
    exists_accuracyImportanceWeight_abs_sub_le q I hsigma2
      (hweight.sub continuous_const) (0 : ℝ)
  apply MemLp.of_bound
    (measurable_accuracyImportanceWeight q I sigma2
      (hweight.measurable.sub measurable_const)).aestronglyMeasurable B
  filter_upwards with x
  rw [Real.norm_eq_abs]
  simpa [r] using hbound x

/-- The stationary numerator variance is at most four times the exact-target
second moment about the accepted mean. -/
theorem varianceReal_accuracyImportanceWeight_sub_acceptedMean_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) :
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (fun x => accuracyImportanceWeight q I sigma2
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) x) ≤
      4 * ∫ y, (weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n)) := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let r := accuracyStationaryAcceptedMean q I sigma2 weight
  let observable := fun x => accuracyImportanceWeight q I sigma2
    (fun y => weight y - r) x
  let _ : IsProbabilityMeasure pi :=
    accuracyPhase_ellGaussianProb_isProbabilityMeasure q I hsigma2
  have hsource : MemLp observable 2 pi := by
    simpa [observable, r, pi] using
      accuracyImportanceWeight_sub_acceptedMean_memLp q I hsigma2 hweight
  have htarget : MemLp (fun y => weight y - r) 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) :=
    hmem.sub (memLp_const r)
  have hvar := Arlib.MarkovChains.varianceReal_le_integral_sub_sq
    hsource.aestronglyMeasurable 0
  have hmom :=
    integral_stationary_accuracyImportance_centered_sq_le_four_target
      q I hsigma2 hweight.measurable r hsource htarget
  change Arlib.MarkovChains.varianceReal pi observable ≤ _
  calc
    Arlib.MarkovChains.varianceReal pi observable ≤
        ∫ x, (observable x - 0) ^ 2 ∂pi := hvar
    _ = ∫ x, observable x ^ 2 ∂pi := by simp
    _ ≤ 4 * ∫ y, (weight y - r) ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n)) := by
      simpa [observable] using hmom
    _ = _ := by rfl

/-- Changing the centering constant adds exactly the squared displacement of
that constant from the true mean. -/
theorem integral_sub_sq_eq_integral_sub_mean_sq_add
    {S : Type*} [MeasurableSpace S]
    {mu : Measure S} [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : MemLp f 2 mu) (c : ℝ) :
    (∫ x, (f x - c) ^ 2 ∂mu) =
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) +
        ((∫ y, f y ∂mu) - c) ^ 2 := by
  have hfint : Integrable f mu := hf.integrable (by norm_num)
  have hfc : MemLp (fun x => f x - c) 2 mu := hf.sub (memLp_const c)
  have hcenter :
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) =
        Arlib.MarkovChains.varianceReal mu f := by
    symm
    exact ProbabilityTheory.variance_eq_integral hf.aemeasurable
  have hshift : Arlib.MarkovChains.varianceReal mu (fun x => f x - c) =
      Arlib.MarkovChains.varianceReal mu f := by
    exact ProbabilityTheory.variance_sub_const hf.aestronglyMeasurable c
  have hsub := Arlib.MarkovChains.varianceReal_eq_sub hfc
  have hint : (∫ x, f x - c ∂mu) = (∫ x, f x ∂mu) - c := by
    rw [integral_sub hfint (integrable_const c)]
    simp
  rw [hint, hshift] at hsub
  rw [hcenter]
  nlinarith

/-- A relative second-moment estimate is exactly a centered-variance estimate
after subtracting one from its factor. -/
theorem integral_sub_mean_sq_le_of_relativeSecondMoment
    {S : Type*} [MeasurableSpace S]
    {mu : Measure S} [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : MemLp f 2 mu)
    {factor : ℝ}
    (hmean : 0 < ∫ x, f x ∂mu)
    (hfactor :
      (∫ x, f x ^ 2 ∂mu) / (∫ x, f x ∂mu) ^ 2 ≤ factor) :
    (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) ≤
      (factor - 1) * (∫ x, f x ∂mu) ^ 2 := by
  let mean := ∫ x, f x ∂mu
  let second := ∫ x, f x ^ 2 ∂mu
  have hmeanSq : 0 < mean ^ 2 := sq_pos_of_pos hmean
  have hsecond : second ≤ factor * mean ^ 2 := by
    rw [div_le_iff₀ hmeanSq] at hfactor
    simpa [mean, second] using hfactor
  have hcenter : (∫ x, (f x - mean) ^ 2 ∂mu) = second - mean ^ 2 := by
    calc
      (∫ x, (f x - mean) ^ 2 ∂mu) =
          Arlib.MarkovChains.varianceReal mu f := by
        symm
        change ProbabilityTheory.variance f mu = _
        simpa [mean] using
          (ProbabilityTheory.variance_eq_integral hf.aemeasurable)
      _ = second - mean ^ 2 := by
        simpa [mean, second] using
          (Arlib.MarkovChains.varianceReal_eq_sub hf)
  rw [hcenter]
  nlinarith

/-- Relative second moments and accepted-law bias combine additively in the
centered target moment used by the paired numerator. -/
theorem integral_sub_acceptedMean_sq_le_of_relativeSecondMoment
    {S : Type*} [MeasurableSpace S]
    {mu : Measure S} [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : MemLp f 2 mu)
    {acceptedMean factor bias : ℝ}
    (hmean : 0 < ∫ x, f x ∂mu)
    (hfactor :
      (∫ x, f x ^ 2 ∂mu) / (∫ x, f x ∂mu) ^ 2 ≤ factor)
    (hbias0 : 0 ≤ bias)
    (hbias : |acceptedMean - ∫ x, f x ∂mu| ≤ bias) :
    (∫ x, (f x - acceptedMean) ^ 2 ∂mu) ≤
      (factor - 1) * (∫ x, f x ∂mu) ^ 2 + bias ^ 2 := by
  let mean := ∫ x, f x ∂mu
  let second := ∫ x, f x ^ 2 ∂mu
  have hmeanSq : 0 < mean ^ 2 := sq_pos_of_pos hmean
  have hsecond : second ≤ factor * mean ^ 2 := by
    rw [div_le_iff₀ hmeanSq] at hfactor
    simpa [mean, second] using hfactor
  have hcenter : (∫ x, (f x - mean) ^ 2 ∂mu) = second - mean ^ 2 := by
    calc
      (∫ x, (f x - mean) ^ 2 ∂mu) =
          Arlib.MarkovChains.varianceReal mu f := by
        symm
        change ProbabilityTheory.variance f mu = _
        simpa [mean] using
          (ProbabilityTheory.variance_eq_integral hf.aemeasurable)
      _ = second - mean ^ 2 := by
        simpa [mean, second] using
          (Arlib.MarkovChains.varianceReal_eq_sub hf)
  have hcenterLe : (∫ x, (f x - mean) ^ 2 ∂mu) ≤
      (factor - 1) * mean ^ 2 := by
    rw [hcenter]
    nlinarith
  have hbiasSq : (mean - acceptedMean) ^ 2 ≤ bias ^ 2 := by
    have habs : |mean - acceptedMean| ≤ bias := by
      simpa [abs_sub_comm] using hbias
    have hprod := mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hbias0 (abs_nonneg (mean - acceptedMean)))
    nlinarith [sq_abs (mean - acceptedMean)]
  rw [integral_sub_sq_eq_integral_sub_mean_sq_add hf acceptedMean]
  change (∫ x, (f x - mean) ^ 2 ∂mu) +
      (mean - acceptedMean) ^ 2 ≤ _
  exact add_le_add hcenterLe hbiasSq

/-- The stationary accepted mean differs from the exact target mean by the
explicit square-root KLS defect, with the target second moment as scale. -/
theorem accuracyStationaryAcceptedMean_bias_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) :
    |accuracyStationaryAcceptedMean q I sigma2 weight -
        ∫ x, weight x
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))| ≤
      accuracyAcceptedBiasScale q *
        (1 + 65 * ∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) := by
  simpa [accuracyStationaryAcceptedMean] using
    stationary_accuracyAcceptedTarget_integral_bias_le
      q I hsigma2 hweight hweight0 hmem

/-- Centered homogeneous accepted-mean bias.  If the exact target variance
is at most `R²`, then the KLS accepted mean moves by at most the tiny core
accuracy scale times `R`.  Applying this with the cooling-ratio variance is
what preserves the accelerated schedule's telescoping `factor - 1` charge. -/
theorem accuracyStationaryAcceptedMean_bias_le_centered_secondMoment
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {R : ℝ} (hR : 0 < R)
    (hcentered :
      (∫ x, (weight x - ∫ y, weight y
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) ≤ R ^ 2) :
    |accuracyStationaryAcceptedMean q I sigma2 weight -
        ∫ x, weight x
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))| ≤
      67 * accuracyAcceptedBiasScale q * R := by
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let accepted := accuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let mean := ∫ x, weight x ∂nu
  let centered : AmbientSpace q.n → ℝ := fun x => weight x - mean
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  let _ : IsProbabilityMeasure accepted :=
    accuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_stationary q I hsigma2
  have hcenterMeas : Measurable centered := hweight.sub measurable_const
  have hcenterMem : MemLp centered 2 nu := by
    exact hmem.sub (memLp_const mean)
  have hwarm : Arlib.IsWarm 64 accepted nu := by
    simpa [accepted, nu, pi] using
      stationary_accuracyAcceptedTarget_isWarm q I hsigma2
  have hle : accepted ≤ (64 : ENNReal) • nu :=
    (Arlib.MarkovChains.isWarm_iff_le_smul _ _).1 hwarm
  have hweightAccepted : MemLp weight 2 accepted :=
    (hmem.smul_measure (by norm_num : (64 : ENNReal) ≠ ⊤)).mono_measure hle
  have htransfer :=
    stationary_accuracyAcceptedTarget_integral_bias_le_sqrt_secondMoment
      q I hsigma2 hcenterMeas hcenterMem hR
      (by simpa [centered, mean, nu] using hcentered)
  have htargetIntegral : (∫ x, centered x ∂nu) = 0 := by
    rw [show centered = fun x => weight x - mean by rfl,
      integral_sub (hmem.integrable (by norm_num)) (integrable_const mean)]
    simp [mean, nu]
  have hacceptedIntegral : (∫ x, centered x ∂accepted) =
      accuracyStationaryAcceptedMean q I sigma2 weight - mean := by
    rw [show centered = fun x => weight x - mean by rfl,
      integral_sub (hweightAccepted.integrable (by norm_num))
        (integrable_const mean)]
    simp [accuracyStationaryAcceptedMean, accepted, pi]
  change |(∫ x, centered x ∂accepted) - (∫ x, centered x ∂nu)| ≤
    67 * accuracyAcceptedBiasScale q * R at htransfer
  rw [hacceptedIntegral, htargetIntegral, sub_zero] at htransfer
  simpa [mean, nu] using htransfer

/-- The paired numerator variance inherits the same centered target scale.
Both the intrinsic target variance and the accepted-law displacement are now
proportional to `R²`; there is no phase-count-sized additive defect. -/
theorem varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_centeredSecondMoment
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {R : ℝ} (hR : 0 < R)
    (hcentered :
      (∫ x, (weight x - ∫ y, weight y
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) ≤ R ^ 2) :
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (fun x => accuracyImportanceWeight q I sigma2
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) x) ≤
      4 * (R ^ 2 +
        (67 * accuracyAcceptedBiasScale q * R) ^ 2) := by
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let mean := ∫ x, weight x ∂nu
  let acceptedMean := accuracyStationaryAcceptedMean q I sigma2 weight
  let bias := 67 * accuracyAcceptedBiasScale q * R
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hbias0 : 0 ≤ bias := by
    dsimp [bias]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (accuracyAcceptedBiasScale_pos q).le) hR.le
  have hbias : |acceptedMean - mean| ≤ bias := by
    simpa [acceptedMean, mean, bias, nu] using
      accuracyStationaryAcceptedMean_bias_le_centered_secondMoment
        q I hsigma2 hweight.measurable hmem hR hcentered
  have hbiasSq : (mean - acceptedMean) ^ 2 ≤ bias ^ 2 := by
    have habs : |mean - acceptedMean| ≤ bias := by
      simpa [abs_sub_comm] using hbias
    have hprod := mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hbias0 (abs_nonneg (mean - acceptedMean)))
    nlinarith [sq_abs (mean - acceptedMean)]
  have htarget := integral_sub_sq_eq_integral_sub_mean_sq_add
    (mu := nu) hmem acceptedMean
  have hsource := varianceReal_accuracyImportanceWeight_sub_acceptedMean_le
    q I hsigma2 hweight hmem
  calc
    _ ≤ 4 * ∫ y, (weight y - acceptedMean) ^ 2 ∂nu := by
      simpa [acceptedMean, nu] using hsource
    _ = 4 * ((∫ y, (weight y - mean) ^ 2 ∂nu) +
        (mean - acceptedMean) ^ 2) := by
      rw [htarget]
    _ ≤ 4 * (R ^ 2 + bias ^ 2) := by
      gcongr
    _ = _ := by rfl

/-- Sharp relative-moment specialization of the centered paired variance
bound.  Its entire right-hand side is proportional to `factor - 1`, including
the executable KLS bias. -/
theorem varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_relativeSecondMoment_sharp
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {factor : ℝ} (hfactorOne : 1 < factor)
    (hmean : 0 < ∫ x, weight x
      ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (hrelative :
      (∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) /
        (∫ x, weight x
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) ^ 2 ≤ factor) :
    let mean := ∫ x, weight x
      ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
    let R := Real.sqrt (factor - 1) * mean
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (fun x => accuracyImportanceWeight q I sigma2
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) x) ≤
      4 * (R ^ 2 + (67 * accuracyAcceptedBiasScale q * R) ^ 2) := by
  dsimp only
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let mean := ∫ x, weight x ∂nu
  let R := Real.sqrt (factor - 1) * mean
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hR : 0 < R := by
    dsimp [R, mean]
    exact mul_pos (Real.sqrt_pos.2 (sub_pos.mpr hfactorOne))
      (by simpa [nu] using hmean)
  have hcentered : (∫ x, (weight x - mean) ^ 2 ∂nu) ≤ R ^ 2 := by
    have hvar := integral_sub_mean_sq_le_of_relativeSecondMoment
      (mu := nu) hmem (by simpa [nu] using hmean)
      (by simpa [nu] using hrelative)
    have hsqrt : (Real.sqrt (factor - 1)) ^ 2 = factor - 1 :=
      Real.sq_sqrt (sub_nonneg.mpr hfactorOne.le)
    simpa [R, mean, hsqrt, mul_pow] using hvar
  simpa [R, mean, nu] using
    varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_centeredSecondMoment
      q I hsigma2 hweight hmem hR hcentered

/-- Relative-moment specialization of the centered accepted-mean bias. -/
theorem accuracyStationaryAcceptedMean_bias_le_of_relativeSecondMoment_sharp
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {factor : ℝ} (hfactorOne : 1 < factor)
    (hmean : 0 < ∫ x, weight x
      ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (hrelative :
      (∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) /
        (∫ x, weight x
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) ^ 2 ≤ factor) :
    let mean := ∫ x, weight x
      ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
    |accuracyStationaryAcceptedMean q I sigma2 weight - mean| ≤
      67 * accuracyAcceptedBiasScale q *
        (Real.sqrt (factor - 1) * mean) := by
  dsimp only
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let mean := ∫ x, weight x ∂nu
  let R := Real.sqrt (factor - 1) * mean
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hR : 0 < R := by
    exact mul_pos (Real.sqrt_pos.2 (sub_pos.mpr hfactorOne))
      (by simpa [mean, nu] using hmean)
  have hcentered : (∫ x, (weight x - mean) ^ 2 ∂nu) ≤ R ^ 2 := by
    have hvar := integral_sub_mean_sq_le_of_relativeSecondMoment
      (mu := nu) hmem (by simpa [nu] using hmean)
      (by simpa [nu] using hrelative)
    have hsqrt : (Real.sqrt (factor - 1)) ^ 2 = factor - 1 :=
      Real.sq_sqrt (sub_nonneg.mpr hfactorOne.le)
    simpa [R, mean, hsqrt, mul_pow] using hvar
  simpa [R, mean, nu] using
    accuracyStationaryAcceptedMean_bias_le_centered_secondMoment
      q I hsigma2 hweight hmem hR hcentered

/-- Final sharp local variance package: target relative second moment plus
the proved KLS bias controls the centered paired numerator at speedy
stationarity. -/
theorem varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_relativeSecondMoment
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (hmem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {factor : ℝ}
    (hmean : 0 < ∫ x, weight x
      ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (hrelative :
      (∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) /
        (∫ x, weight x
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) ^ 2 ≤ factor) :
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (fun x => accuracyImportanceWeight q I sigma2
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I sigma2 weight) x) ≤
      4 * ((factor - 1) *
          (∫ x, weight x
            ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
              Measure (AmbientSpace q.n))) ^ 2 +
        (accuracyAcceptedBiasScale q *
          (1 + 65 * ∫ x, weight x ^ 2
            ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
              Measure (AmbientSpace q.n)))) ^ 2) := by
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let acceptedMean := accuracyStationaryAcceptedMean q I sigma2 weight
  let bias := accuracyAcceptedBiasScale q *
    (1 + 65 * ∫ x, weight x ^ 2 ∂nu)
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have hbias0 : 0 ≤ bias := by
    dsimp [bias]
    exact mul_nonneg (accuracyAcceptedBiasScale_pos q).le <|
      add_nonneg zero_le_one <| mul_nonneg (by norm_num) <|
        integral_nonneg fun x => sq_nonneg (weight x)
  have hbias : |acceptedMean - ∫ x, weight x ∂nu| ≤ bias := by
    simpa [acceptedMean, bias, nu] using
      accuracyStationaryAcceptedMean_bias_le q I hsigma2
        hweight.measurable hweight0 hmem
  have htarget :=
    integral_sub_acceptedMean_sq_le_of_relativeSecondMoment
      (mu := nu) hmem (acceptedMean := acceptedMean)
      (factor := factor) (bias := bias)
      (by simpa [nu] using hmean)
      (by simpa [nu] using hrelative) hbias0 hbias
  have hsource :=
    varianceReal_accuracyImportanceWeight_sub_acceptedMean_le
      q I hsigma2 hweight hmem
  calc
    _ ≤ 4 * ∫ y, (weight y - acceptedMean) ^ 2 ∂nu := by
      simpa [acceptedMean, nu] using hsource
    _ ≤ 4 * ((factor - 1) * (∫ x, weight x ∂nu) ^ 2 + bias ^ 2) := by
      gcongr
    _ = _ := by rfl

/-- Deterministic self-normalized ratio reduction: a bad ratio with a
nonzero denominator forces either a bad centered numerator or a bad
denominator. -/
theorem paired_ratio_bad_implies_centered_or_denominator
    {k p r eta numerator denominator : ℝ}
    (hk : 0 < k) (hp : 0 < p) (heta : 0 < eta)
    (hden : denominator ≠ 0)
    (hbad : eta ≤ |numerator / denominator - r|) :
    k * p * eta / 2 ≤ |numerator - r * denominator| ∨
      k * p / 2 ≤ |denominator - k * p| := by
  by_contra h
  push_neg at h
  have hdenBounds := (abs_lt.mp h.2)
  have hdenPos : 0 < denominator := by nlinarith
  have hcenter : |numerator - r * denominator| < eta * denominator := by
    have hscale : k * p * eta / 2 < eta * denominator := by
      nlinarith
    exact h.1.trans hscale
  have hratio : |numerator / denominator - r| < eta := by
    have hid : numerator / denominator - r =
        (numerator - r * denominator) / denominator := by
      field_simp [hden]
    rw [hid, abs_div, abs_of_pos hdenPos]
    exact (div_lt_iff₀ hdenPos).2 <| by
      simpa [mul_comm] using hcenter
  exact (not_lt_of_ge hbad) hratio

/-- Spectral Chebyshev cost appearing in one linear projection of a paired
collector. -/
noncomputable def accuracyPairLinearSpectralCost
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (samples : ℕ)
    (a b m threshold : ℝ) : ℝ :=
  (samples : ℝ) *
    (3 * ((Arlib.MarkovChains.spectralGap
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2))
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))⁻¹ *
      Arlib.MarkovChains.varianceReal
        (Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (fun x => accuracyImportanceWeight q I sigma2
          (fun y => a * weight y + b) x - m))) / threshold ^ 2

/-- Successful self-normalized paired ratios obey the union of the centered
numerator and denominator spectral bounds. -/
theorem bind_accuracyImportancePairProgram_success_ratio_deviation_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (hweightMem : MemLp weight 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (proposalCap samples : ℕ) (hsamples : 0 < samples)
    {mu : Measure (AmbientSpace q.n)} {M : ENNReal}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    {eta : ℝ} (heta : 0 < eta) :
    let p := accuracyStationaryAcceptanceMean q I sigma2
    let r := accuracyStationaryAcceptedMean q I sigma2 weight
    let law := mu.bind fun current =>
      (cappedAccuracyProperCollectPairs q sigma2 weight
        (proposalCap + samples) 1 samples current).runEstimate oracle.query
    law (optionSomeEvent {output | output.1.2 ≠ 0 ∧
        eta ≤ |output.1.1 / output.1.2 - r|}) ≤
      M * ENNReal.ofReal
        (accuracyPairLinearSpectralCost q I sigma2 weight samples
          1 (-r) 0 ((samples : ℝ) * p * eta / 2)) +
      M * ENNReal.ofReal
        (accuracyPairLinearSpectralCost q I sigma2 weight samples
          0 1 p ((samples : ℝ) * p / 2)) := by
  dsimp only
  let p := accuracyStationaryAcceptanceMean q I sigma2
  let r := accuracyStationaryAcceptedMean q I sigma2 weight
  let pairLaw : AmbientSpace q.n →
      Measure (Option ((ℝ × ℝ) × AmbientSpace q.n)) := fun current =>
    (cappedAccuracyProperCollectPairs q sigma2 weight
      (proposalCap + samples) 1 samples current).runEstimate oracle.query
  let Ebad : Set (Option ((ℝ × ℝ) × AmbientSpace q.n)) :=
    optionSomeEvent {output | output.1.2 ≠ 0 ∧
      eta ≤ |output.1.1 / output.1.2 - r|}
  let Enum : Set (Option ((ℝ × ℝ) × AmbientSpace q.n)) :=
    optionSomeEvent {output | (samples : ℝ) * p * eta / 2 ≤
      |output.1.1 - r * output.1.2|}
  let Eden : Set (Option ((ℝ × ℝ) × AmbientSpace q.n)) :=
    optionSomeEvent {output | (samples : ℝ) * p / 2 ≤
      |output.1.2 - (samples : ℝ) * p|}
  have hsampleR : (0 : ℝ) < samples := by exact_mod_cast hsamples
  have hp : 0 < p := by
    simpa [p] using accuracyStationaryAcceptanceMean_pos q I hsigma2
  have hsubset : Ebad ⊆ Enum ∪ Eden := by
    intro output houtput
    cases output with
    | none => exact False.elim houtput
    | some output =>
        rcases houtput with ⟨hden, hbad⟩
        have hor := paired_ratio_bad_implies_centered_or_denominator
          hsampleR hp heta hden hbad
        exact hor.elim (fun h => Or.inl h) (fun h => Or.inr h)
  have hEnum : MeasurableSet Enum := by
    exact measurableSet_optionSomeEvent <|
      measurableSet_le measurable_const (by fun_prop)
  have hEden : MeasurableSet Eden := by
    exact measurableSet_optionSomeEvent <|
      measurableSet_le measurable_const (by fun_prop)
  have hcenterWeight :
      (fun y => (1 : ℝ) * weight y + -r) =
        fun y => weight y - r := by
    funext y
    ring
  have hnumMean :
      ∫ x, (accuracyImportanceWeight q I sigma2
          (fun y => (1 : ℝ) * weight y + -r) x - 0)
        ∂Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2 = 0 := by
    rw [hcenterWeight]
    simpa only [sub_zero, r] using
      integral_accuracyImportanceWeight_sub_acceptedMean_eq_zero
        q I hsigma2 hweight.measurable hweightMem
  have hnumMem : MemLp (fun x =>
      accuracyImportanceWeight q I sigma2
        (fun y => (1 : ℝ) * weight y + -r) x - 0) 2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
    rw [hcenterWeight]
    simpa only [sub_zero, r] using
      accuracyImportanceWeight_sub_acceptedMean_memLp
        q I hsigma2 hweight
  obtain ⟨Bnum, hBnum, hnumBound⟩ :=
    exists_accuracyImportanceWeight_abs_sub_le q I hsigma2
      (hweight.sub continuous_const) (0 : ℝ)
  have hsubWeight :
      (weight - fun _ => r) = (fun y => weight y - r) := by
    funext y
    rfl
  have hnumBound' : ∀ x,
      |accuracyImportanceWeight q I sigma2
        (fun y => (1 : ℝ) * weight y + -r) x - 0| ≤ Bnum := by
    intro x
    rw [hcenterWeight]
    rw [← hsubWeight]
    simpa only [sub_zero, r] using hnumBound x
  have hdenMean :
      ∫ x, (accuracyImportanceWeight q I sigma2
          (fun y => (0 : ℝ) * weight y + 1) x - p)
        ∂Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2 = 0 := by
    simpa [accuracyImportanceWeight, p] using
      integral_accuracyAcceptanceWeight_sub_stationaryMean_eq_zero
        q I hsigma2
  have hdenMem : MemLp (fun x =>
      accuracyImportanceWeight q I sigma2
        (fun y => (0 : ℝ) * weight y + 1) x - p) 2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
    simpa [accuracyImportanceWeight, p] using
      accuracyAcceptanceWeight_sub_stationaryMean_memLp q I hsigma2
  have hdenBound : ∀ x,
      |accuracyImportanceWeight q I sigma2
        (fun y => (0 : ℝ) * weight y + 1) x - p| ≤ 1 := by
    intro x
    simpa [accuracyImportanceWeight, p] using
      accuracyAcceptanceWeight_sub_stationaryMean_abs_le_one q I hsigma2 x
  have hcnum : 0 < (samples : ℝ) * p * eta / 2 := by positivity
  have hcden : 0 < (samples : ℝ) * p / 2 := by positivity
  have hnum :=
    bind_accuracyImportancePairProgram_success_linear_deviation_le_of_isWarm
      q I oracle hsigma2 hweight.measurable 1 (-r) proposalCap samples
      hwarm 0 hnumMean hnumMem hBnum hnumBound' hcnum
  have hden :=
    bind_accuracyImportancePairProgram_success_linear_deviation_le_of_isWarm
      q I oracle hsigma2 hweight.measurable 0 1 proposalCap samples
      hwarm p hdenMean hdenMem (by norm_num : (0 : ℝ) ≤ 1) hdenBound hcden
  change (mu.bind pairLaw) Ebad ≤ _
  calc
    (mu.bind pairLaw) Ebad ≤ (mu.bind pairLaw) (Enum ∪ Eden) :=
      measure_mono hsubset
    _ ≤ (mu.bind pairLaw) Enum + (mu.bind pairLaw) Eden :=
      measure_union_le Enum Eden
    _ ≤ M * ENNReal.ofReal
          (accuracyPairLinearSpectralCost q I sigma2 weight samples
            1 (-r) 0 ((samples : ℝ) * p * eta / 2)) +
        M * ENNReal.ofReal
          (accuracyPairLinearSpectralCost q I sigma2 weight samples
            0 1 p ((samples : ℝ) * p / 2)) := by
      exact add_le_add (by simpa [pairLaw, Enum, accuracyPairLinearSpectralCost,
          sub_eq_add_neg]
        using hnum) (by simpa [pairLaw, Eden, accuracyPairLinearSpectralCost]
        using hden)

/-- The globally capped paired collector has exactly the same failure event
as any scalar projection, hence inherits the proved proper-step proposal
cutoff bound. -/
theorem half_mul_natCast_mul_bind_accuracyImportancePairProgram_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (proposalCap samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal) *
        (mu.bind fun current =>
          (cappedAccuracyProperCollectPairs q sigma2 weight
            (proposalCap + samples) 1 samples current).runEstimate
              oracle.query) {none} ≤
      (samples : ENNReal) * M := by
  let pairLaw : AmbientSpace q.n →
      Measure (Option ((ℝ × ℝ) × AmbientSpace q.n)) := fun current =>
    (cappedAccuracyProperCollectPairs q sigma2 weight
      (proposalCap + samples) 1 samples current).runEstimate oracle.query
  let scalarLaw : AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun current =>
    (cappedAccuracyProperCollectWeights q sigma2
      (fun y => (0 : ℝ) * weight y + 0)
      (proposalCap + samples) 1 samples current).runEstimate oracle.query
  let project := accuracyPairLinearOutput (n := q.n) 0 0
  have hpairMeas : Measurable pairLaw := by
    exact (cappedAccuracyProperCollectPairs_measurable_and_strong
      q I oracle hsigma2 hweight (proposalCap + samples) 1 samples).1
  have hproject : Measurable project :=
    measurable_accuracyPairLinearOutput 0 0
  have hmap : (mu.bind pairLaw).map project = mu.bind scalarLaw := by
    rw [map_bind_eq_bind_map_of_measurable mu hpairMeas hproject]
    apply Measure.bind_congr_right
    filter_upwards with current
    exact runEstimate_cappedAccuracyProperCollectPairs_map_linear
      q I oracle hsigma2 hweight (proposalCap + samples) 1 samples current 0 0
  have hpre : project ⁻¹' ({none} : Set (Option (ℝ × AmbientSpace q.n))) =
      ({none} : Set (Option ((ℝ × ℝ) × AmbientSpace q.n))) := by
    ext output
    cases output <;> simp [project, accuracyPairLinearOutput]
  have hfailure : (mu.bind pairLaw) {none} =
      (mu.bind scalarLaw) {none} := by
    rw [← hmap, Measure.map_apply hproject measurableSet_option_none]
    rw [hpre]
  rw [show (fun current =>
      (cappedAccuracyProperCollectPairs q sigma2 weight
        (proposalCap + samples) 1 samples current).runEstimate oracle.query) =
      pairLaw by rfl, hfailure]
  simpa [scalarLaw] using
    (half_mul_natCast_mul_bind_accuracyImportanceProgram_none_le
      q I oracle hsigma2 (weight := fun _ => (0 : ℝ)) measurable_const
      hwarm proposalCap 1 samples)

end ArlibCommunity.Algorithms.CV18
