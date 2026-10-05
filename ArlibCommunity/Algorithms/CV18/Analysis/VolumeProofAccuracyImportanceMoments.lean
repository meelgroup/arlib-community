/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyWarmStart

/-! # Sharp moment transfer for the CV18 importance correction

The acceptance indicator in the executable KLS correction has constant
variance.  Estimating numerator and denominator independently would therefore
lose the accelerated `1 / n` phase variance.  The self-normalized estimator
instead centers the numerator by the *same* acceptance observable.  Its
second moment is controlled by the accepted submeasure, and that submeasure
is dominated by a universal constant times the desired Gaussian law.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise
open Arlib MarkovChains

/-- The unnormalised speedy stationary measure on an accuracy core is
dominated by the ordinary Gaussian measure on the full truncated body. -/
theorem accuracyPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 ≤
      truncatedGaussianMeasure q I sigma2 := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [ellGaussianMeasure, withDensity_apply _ hA,
    truncatedGaussianMeasure, withDensity_apply _ hA]
  rw [Measure.restrict_restrict hA, Measure.restrict_restrict hA]
  have hsub : A ∩ accuracyPhaseTruncatedBody q I sigma2 ⊆
      A ∩ truncatedBody q I := fun _ hx => ⟨hx.1, hx.2.1⟩
  calc
    (∫⁻ x in A ∩ accuracyPhaseTruncatedBody q I sigma2,
        ell (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) x * gaussianWeight sigma2 x) ≤
      ∫⁻ x in A ∩ accuracyPhaseTruncatedBody q I sigma2,
        gaussianWeight sigma2 x := by
      apply lintegral_mono
      intro x
      simpa using mul_le_mul'
        (ell_le_one (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) x) le_rfl
    _ ≤ ∫⁻ x in A ∩ truncatedBody q I,
        gaussianWeight sigma2 x :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ = ∫⁻ x in A ∩ truncatedBody q I,
        ENNReal.ofReal (gaussianDensity sigma2 x) := by
      apply lintegral_congr
      intro x
      simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]

/-- The full Gaussian normalizer is at most four times the speedy-core
normalizer: one factor two is radial truncation and one is average local
conductance. -/
theorem accuracyPhase_gaussianMass_le_four_ellGaussianMass
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedGaussianMeasure q I sigma2 Set.univ ≤
      4 * ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 Set.univ := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let full : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight sigma2 x
  let core : ENNReal := ∫⁻ x in K, gaussianWeight sigma2 x
  let speedy : ENNReal := ellGaussianMeasure K delta sigma2 Set.univ
  have hfull : truncatedGaussianMeasure q I sigma2 Set.univ = full := by
    rw [truncatedGaussianMeasure_apply_univ q I hsigma2]
    exact (lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
      (truncatedBody_measurable q I) hsigma2).symm
  have hfullCore : full ≤ 2 * core := by
    rw [show full = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) sigma2) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hsigma2]
    rw [show core = ENNReal.ofReal (gaussianIntegral K sigma2) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (by dsimp [K]; exact accuracyPhaseTruncatedBody_measurable q I sigma2)
        hsigma2]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [K] using
        accuracyPhase_full_gaussianIntegral_le_two_core q I hsigma2)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * core ≤ speedy := by
    simpa [K, delta, core, speedy] using
      half_mul_gaussianWeight_le_accuracyPhaseEllGaussian q I hsigma2
  have hcore : core ≤ 2 * speedy := by
    calc
      core = 2 * (ENNReal.ofReal (1 / 2 : ℝ) * core) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 * speedy := mul_le_mul' le_rfl hhalf
  rw [hfull]
  calc
    full ≤ 2 * core := hfullCore
    _ ≤ 2 * (2 * speedy) := mul_le_mul' le_rfl hcore
    _ = 4 * speedy := by ring

/-- The speedy stationary law is universally `4`-warm for the exact
truncated Gaussian target at the same variance. -/
theorem accuracyPhase_speedyStationary_isWarm_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm 4
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  let mu := ellGaussianMeasure
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let nu := truncatedGaussianMeasure q I sigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmu0 : mu Set.univ ≠ 0 := by
    dsimp [mu]
    exact ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmutop : mu Set.univ ≠ ⊤ := by
    dsimp [mu]
    exact ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      (figureOneProposalRadius q sigma2) hsigma2
  have hnu0 : nu Set.univ ≠ 0 := by
    intro hzero
    have hmeasure : nu = 0 := Measure.measure_univ_eq_zero.mp hzero
    exact truncatedGaussianMeasure_ne_zero q I hsigma2 (by simpa [nu] using hmeasure)
  have hnutop : nu Set.univ ≠ ⊤ := by
    let _ := truncatedGaussianMeasure_isFinite q I hsigma2
    exact measure_ne_top nu Set.univ
  have hdom : mu ≤ (1 : ENNReal) • nu := by
    simpa [mu, nu] using
      accuracyPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
        q I sigma2
  have hmass : nu Set.univ ≤ (4 : ENNReal) * mu Set.univ := by
    simpa [mu, nu] using
      accuracyPhase_gaussianMass_le_four_ellGaussianMass q I hsigma2
  have hw := isWarm_normalize_of_le_smul hmu0 hmutop hnu0 hnutop hdom hmass
  simpa [mu, nu, ellGaussianProb,
    truncatedGaussianProbability_toMeasure q I hsigma2,
    truncatedGaussianMeasure_apply_univ q I hsigma2] using hw

/-- Applying the KLS acceptance density to an exact phase Gaussian and
scaling the accepted point outward produces a submeasure of that same phase
Gaussian.  The missing mass is precisely the homothety Jacobian and the part
of the target outside the accuracy core. -/
theorem truncatedGaussianProbability_acceptance_map_le_self
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I sigma2 hsigma2
    (nu.withDensity
      (accuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x) ≤ nu := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let c := accuracyScaleFactor q
  let core := c • K
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal := gaussianScaleAcceptance sigma2 c
  let gaussian : Measure (AmbientSpace q.n) :=
    (volume : Measure (AmbientSpace q.n)).withDensity (gaussianWeight sigma2)
  let proposalGaussian : Measure (AmbientSpace q.n) :=
    (volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight (sigma2 / c ^ 2))
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hc1 : c ≤ 1 := by simpa [c] using accuracyScaleFactor_le_one q
  have hK : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hcore : MeasurableSet core := by
    dsimp [core]
    exact measurableSet_smul_set_cv18 hK hc0.ne'
  have hscale : Measurable scale := by dsimp [scale]; fun_prop
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    refine ⟨unitBall_subset_truncatedBody q I
      (Metric.mem_closedBall_self zero_le_one), ?_⟩
    exact Metric.mem_closedBall_self (accuracyPhaseRadius_pos q hsigma2).le
  have hcoreK : core ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (accuracyPhaseTruncatedBody_convex q I sigma2).smul_mem_of_zero_mem
      hzero hx ⟨hc0.le, hc1⟩
  have hKfull : K ⊆ truncatedBody q I := fun _ hx => hx.1
  have hcoreFull : core ⊆ truncatedBody q I := hcoreK.trans hKfull
  have hgaussianCore0 : gaussian core ≠ 0 := by
    have hvol0 : volume core ≠ 0 := by
      dsimp [core]
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact mul_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 q.n))
        (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
    exact withDensity_gaussianWeight_ne_zero sigma2 hvol0
  have hgaussianCoreTop : gaussian core ≠ ⊤ := by
    have hvolTop : volume core ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
        (measure_mono hcoreK)
    exact withDensity_gaussianWeight_ne_top hsigma2 hcore hvolTop
  have hnuCore0 : nu core ≠ 0 := by
    rw [truncatedGaussianProbability_apply q I hsigma2 hcore]
    rw [Set.inter_eq_left.2 hcoreFull]
    have hfull0 : ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) sigma2) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr
        (gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2)
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top) (by
      rw [show (fun x : AmbientSpace q.n =>
          ENNReal.ofReal (gaussianDensity sigma2 x)) = gaussianWeight sigma2 by
        funext x
        simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]]
      simpa [gaussian, withDensity_apply _ hcore] using hgaussianCore0)
  have hnuCoreTop : nu core ≠ ⊤ := measure_ne_top nu core
  have hraw : truncatedGaussianMeasure q I sigma2 =
      gaussian.restrict (truncatedBody q I) := by
    unfold truncatedGaussianMeasure
    change (volume.restrict (truncatedBody q I)).withDensity
        (fun x => ENNReal.ofReal (gaussianDensity sigma2 x)) = _
    rw [show (fun x : AmbientSpace q.n =>
        ENNReal.ofReal (gaussianDensity sigma2 x)) = gaussianWeight sigma2 by
      funext x
      simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]]
    dsimp [gaussian]
    exact (restrict_withDensity (f := gaussianWeight sigma2)
      (truncatedBody_measurable q I)).symm
  have hnuEq : nu =
      (ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ •
          gaussian.restrict (truncatedBody q I) := by
    rw [show nu =
        (truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n)) by rfl,
      truncatedGaussianProbability_toMeasure q I hsigma2, hraw]
  have hcondNu : Arlib.condOn nu core = Arlib.condOn gaussian core := by
    rw [hnuEq]
    calc
      Arlib.condOn
          ((ENNReal.ofReal
            (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ •
              gaussian.restrict (truncatedBody q I)) core =
          Arlib.condOn (gaussian.restrict (truncatedBody q I)) core :=
        condOn_smul_cv18 _ hcore
          (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
          (ENNReal.inv_ne_top.mpr <|
            ENNReal.ofReal_ne_zero_iff.mpr
              (gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2))
      _ = Arlib.condOn gaussian core :=
        condOn_restrict_eq_condOn_of_subset_cv18 gaussian hcore hcoreFull
  have hmapCond : (Arlib.condOn nu core).map scale =
      Arlib.condOn proposalGaussian K := by
    rw [hcondNu]
    simpa [scale, core, gaussian, proposalGaussian] using
      map_condOn_gaussian_smul_cv18 hK hc0 (variance := sigma2)
  have hrestrict : nu.restrict core = nu core • Arlib.condOn nu core := by
    rw [Arlib.condOn_def, smul_smul,
      ENNReal.mul_inv_cancel hnuCore0 hnuCoreTop, one_smul]
  have hsource := map_withDensity_accuracyRejectionAcceptance
    q I sigma2 nu
  change (nu.withDensity
      (accuracyGaussianRejectionAcceptance q I sigma2)).map scale ≤ nu
  rw [hsource, hrestrict, Measure.map_smul, withDensity_smul_measure,
    hmapCond]
  have hproposalDensity :
      (Arlib.condOn proposalGaussian K).withDensity g =
        (proposalGaussian K)⁻¹ • gaussian.restrict K := by
    simpa [proposalGaussian, gaussian, g, c] using
      condOn_gaussian_withDensity_scaleAcceptance_cv18 hK sigma2 c
  rw [hproposalDensity]
  rw [smul_smul]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, Measure.restrict_apply hA,
    truncatedGaussianProbability_apply q I hsigma2 hA]
  have hAK : A ∩ K ⊆ A ∩ truncatedBody q I :=
    fun _ hx => ⟨hx.1, hKfull hx.2⟩
  have hgaussianAK : gaussian (A ∩ K) =
      ∫⁻ x in A ∩ K, gaussianWeight sigma2 x := by
    rw [show gaussian =
        (volume : Measure (AmbientSpace q.n)).withDensity
          (gaussianWeight sigma2) by rfl,
      withDensity_apply _ (hA.inter hK)]
  rw [hgaussianAK]
  have hweightEq : (fun x : AmbientSpace q.n =>
      ENNReal.ofReal (gaussianDensity sigma2 x)) = gaussianWeight sigma2 := by
    funext x
    simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]
  rw [hweightEq]
  have hcoreMass : nu core ≤
      (ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
        proposalGaussian K := by
    rw [truncatedGaussianProbability_apply q I hsigma2 hcore,
      Set.inter_eq_left.2 hcoreFull, hweightEq]
    apply mul_le_mul' le_rfl
    rw [show proposalGaussian K =
        ∫⁻ x in K, gaussianWeight (sigma2 / c ^ 2) x by
      dsimp [proposalGaussian]
      rw [withDensity_apply _ hK]]
    rw [show core = c • K by rfl,
      lintegral_gaussianWeight_smul_set_cv18 hK hc0 sigma2]
    exact mul_le_of_le_one_left bot_le <|
      ENNReal.ofReal_le_one.mpr <| by
        exact pow_le_one₀ hc0.le hc1
  calc
    (nu core * (proposalGaussian K)⁻¹) *
          (∫⁻ x in A ∩ K, gaussianWeight sigma2 x) ≤
        (((ENNReal.ofReal
          (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
            proposalGaussian K) * (proposalGaussian K)⁻¹) *
          (∫⁻ x in A ∩ K, gaussianWeight sigma2 x) := by
      gcongr
    _ = (ENNReal.ofReal
          (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
          (∫⁻ x in A ∩ K, gaussianWeight sigma2 x) := by
      have hp0 : proposalGaussian K ≠ 0 := by
        dsimp [proposalGaussian]
        exact withDensity_gaussianWeight_ne_zero (sigma2 / c ^ 2)
          (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      have hpTop : proposalGaussian K ≠ ⊤ := by
        dsimp [proposalGaussian]
        exact withDensity_gaussianWeight_ne_top (by positivity) hK
          (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      calc
        (ENNReal.ofReal
              (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
              proposalGaussian K * (proposalGaussian K)⁻¹ *
              (∫⁻ x in A ∩ K, gaussianWeight sigma2 x) =
            (ENNReal.ofReal
              (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
              (proposalGaussian K * (proposalGaussian K)⁻¹) *
              (∫⁻ x in A ∩ K, gaussianWeight sigma2 x) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hp0 hpTop, mul_one]
    _ ≤ (ENNReal.ofReal
          (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
          (∫⁻ x in A ∩ truncatedBody q I,
            gaussianWeight sigma2 x) := by
      exact mul_le_mul' le_rfl <|
        lintegral_mono' (Measure.restrict_mono hAK le_rfl) le_rfl

/-- Before normalization, the stationary accepted target submeasure is at
most four times the exact Gaussian target. -/
theorem stationary_accuracyAcceptedSubmeasure_le_four_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let pi := ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I sigma2 hsigma2
    (pi.withDensity
      (accuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x) ≤
          (4 : ENNReal) • nu := by
  dsimp only
  let pi := ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let accept := accuracyGaussianRejectionAcceptance q I sigma2
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  have hpi : pi ≤ (4 : ENNReal) • nu := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa [pi, nu, Measure.smul_apply, smul_eq_mul] using
      (accuracyPhase_speedyStationary_isWarm_target q I hsigma2 A hA)
  have hdensity : pi.withDensity accept ≤
      (4 : ENNReal) • nu.withDensity accept := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [withDensity_apply _ hA, Measure.smul_apply,
      withDensity_apply _ hA, smul_eq_mul]
    calc
      (∫⁻ x in A, accept x ∂pi) ≤
          ∫⁻ x in A, accept x ∂((4 : ENNReal) • nu) := by
        exact lintegral_mono'
          (Measure.restrict_mono le_rfl hpi) le_rfl
      _ = 4 * ∫⁻ x in A, accept x ∂nu := by
        rw [setLIntegral_smul_measure, smul_eq_mul]
  have hmap := Measure.map_mono hdensity (by
    change Measurable scale
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id)
  rw [Measure.map_smul] at hmap
  have hself := truncatedGaussianProbability_acceptance_map_le_self
    q I hsigma2
  change (pi.withDensity accept).map scale ≤ 4 • nu
  exact hmap.trans <| by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul' le_rfl (Measure.le_iff.mp hself A hA)

/-- The normalized stationary accepted law is universally `64`-warm for the
exact Gaussian target.  This is the quantitative replacement for using TV
distance when transferring unbounded ratio second moments. -/
theorem stationary_accuracyAcceptedTarget_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm 64
      (accuracyGaussianAcceptedTargetLaw q I sigma2
        (ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2))
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  let pi := ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let accepted :=
    (pi.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmassTop : ellGaussianMeasure
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      (figureOneProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  have hacceptedLower : ENNReal.ofReal (7 / 64 : ℝ) ≤ accepted Set.univ := by
    have h := accuracyPhase_stationary_acceptance_ge q I hsigma2
    change ENNReal.ofReal (7 / 64 : ℝ) ≤ accepted Set.univ
    dsimp [accepted]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ]
    simpa [pi] using h
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 64 : ℝ)).trans_le
      hacceptedLower
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      calc
        accepted Set.univ =
            (pi.withDensity
              (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := by
          dsimp [accepted]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
            Set.preimage_univ]
        _ ≤ pi Set.univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
          calc
            (∫⁻ x, accuracyGaussianRejectionAcceptance q I sigma2 x ∂pi) ≤
                ∫⁻ _x, (1 : ENNReal) ∂pi := by
              exact lintegral_mono <|
                accuracyGaussianRejectionAcceptance_le_one q I hsigma2
            _ = pi Set.univ := lintegral_one
  have hnu0 : nu Set.univ ≠ 0 := by simp [nu]
  have hnuTop : nu Set.univ ≠ ⊤ := by simp [nu]
  have hdom : accepted ≤ (4 : ENNReal) • nu := by
    simpa [accepted, pi, nu] using
      stationary_accuracyAcceptedSubmeasure_le_four_target q I hsigma2
  have hmass : nu Set.univ ≤ (16 : ENNReal) * accepted Set.univ := by
    rw [show nu Set.univ = 1 by simp [nu]]
    calc
      1 = 16 * ENNReal.ofReal (1 / 16 : ℝ) := by
        rw [show (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
      _ ≤ 16 * ENNReal.ofReal (7 / 64 : ℝ) := by
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by norm_num))
      _ ≤ 16 * accepted Set.univ := mul_le_mul' le_rfl hacceptedLower
  have hw := isWarm_normalize_of_le_smul
    haccepted0 hacceptedTop hnu0 hnuTop hdom hmass
  change IsWarm 64 (Arlib.condOn accepted Set.univ) nu
  rw [Arlib.condOn_def, Measure.restrict_univ]
  convert hw using 1 <;> norm_num

/-- Warmness transfers every square-integrable real second moment.  This
small adapter is useful below because the KLS observable is unbounded on the
ambient space even though its accepted law is dominated by the target. -/
theorem integral_sq_le_of_isWarm_cv18
    {S : Type*} [MeasurableSpace S]
    {M : ENNReal} (hMtop : M ≠ ⊤) {mu nu : Measure S}
    (hwarm : IsWarm M mu nu) {f : S → ℝ} (hf : MemLp f 2 nu) :
    (∫ x, f x ^ 2 ∂mu) ≤ M.toReal * ∫ x, f x ^ 2 ∂nu := by
  have hle : mu ≤ M • nu := (isWarm_iff_le_smul _ _).1 hwarm
  calc
    (∫ x, f x ^ 2 ∂mu) ≤ ∫ x, f x ^ 2 ∂(M • nu) := by
      exact integral_mono_measure hle
        (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
        (hf.integrable_sq.smul_measure hMtop)
    _ = M.toReal * ∫ x, f x ^ 2 ∂nu := by
      rw [integral_smul_measure]
      rfl

/-- The square of a centered Rao--Blackwell observation at speedy
stationarity is bounded by four times the corresponding exact-target second
moment.  Crucially, the same acceptance weight multiplies the centered
observable before squaring; this is the cancellation lost by independent
numerator and denominator trajectories. -/
theorem integral_stationary_accuracyImportance_centered_sq_le_four_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (r : ℝ)
    (hsource : MemLp
      (accuracyImportanceWeight q I sigma2 (fun y => weight y - r)) 2
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (htarget : MemLp (fun y => weight y - r) 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) :
    (∫ x, accuracyImportanceWeight q I sigma2
          (fun y => weight y - r) x ^ 2
        ∂ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2) ≤
      4 * ∫ y, (weight y - r) ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n)) := by
  let pi := ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let accept := accuracyGaussianRejectionAcceptance q I sigma2
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let u : AmbientSpace q.n → ℝ := fun y => weight y - r
  let accepted := (pi.withDensity accept).map scale
  have haccept : Measurable accept :=
    measurable_accuracyGaussianRejectionAcceptance q I sigma2
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hu : Measurable u := by
    exact hweight.sub measurable_const
  have hdom : accepted ≤ (4 : ENNReal) • nu := by
    simpa [accepted, pi, nu, accept, scale] using
      stationary_accuracyAcceptedSubmeasure_le_four_target q I hsigma2
  have hu2Large : Integrable (fun y => u y ^ 2) ((4 : ENNReal) • nu) := by
    have hu2 : Integrable (fun y => u y ^ 2) nu := by
      simpa [u, nu] using htarget.integrable_sq
    exact hu2.smul_measure (by norm_num)
  have hu2Accepted : Integrable (fun y => u y ^ 2) accepted :=
    hu2Large.mono_measure hdom
  have hu2Density : Integrable (fun x => u (scale x) ^ 2)
      (pi.withDensity accept) := by
    apply (integrable_map_measure hu2Accepted.aestronglyMeasurable
      hscale.aemeasurable).mp
    simpa [accepted] using hu2Accepted
  have hweighted : Integrable
      (fun x => (accept x).toReal * u (scale x) ^ 2) pi := by
    have hfinite : ∀ᵐ x ∂pi, accept x < ⊤ :=
      Filter.Eventually.of_forall fun x => lt_of_le_of_lt
        (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)
        ENNReal.one_lt_top
    have h := (integrable_withDensity_iff haccept hfinite).mp hu2Density
    simpa [mul_comm] using h
  have hpoint : ∀ x,
      accuracyImportanceWeight q I sigma2 u x ^ 2 ≤
        (accept x).toReal * u (scale x) ^ 2 := by
    intro x
    have ha0 : 0 ≤ (accept x).toReal := ENNReal.toReal_nonneg
    have ha1 : (accept x).toReal ≤ 1 := by
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)
    change ((accept x).toReal * u (scale x)) ^ 2 ≤
      (accept x).toReal * u (scale x) ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith)
      (sq_nonneg (u (scale x)))
  have hleft :
      (∫ x, accuracyImportanceWeight q I sigma2 u x ^ 2 ∂pi) ≤
        ∫ x, (accept x).toReal * u (scale x) ^ 2 ∂pi := by
    apply integral_mono_ae hsource.integrable_sq hweighted
    exact Filter.Eventually.of_forall hpoint
  have hidentity :
      (∫ x, (accept x).toReal * u (scale x) ^ 2 ∂pi) =
        ∫ y, u y ^ 2 ∂accepted := by
    dsimp only [accepted]
    rw [integral_map hscale.aemeasurable
      ((hu.pow_const 2).aestronglyMeasurable)]
    rw [integral_withDensity_eq_integral_toReal_smul haccept
      (Filter.Eventually.of_forall fun x => lt_of_le_of_lt
        (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)
        ENNReal.one_lt_top)]
    simp only [smul_eq_mul]
  have hright : (∫ y, u y ^ 2 ∂accepted) ≤
      ∫ y, u y ^ 2 ∂((4 : ENNReal) • nu) := by
    exact integral_mono_measure hdom
      (Filter.Eventually.of_forall fun y => sq_nonneg (u y)) hu2Large
  calc
    (∫ x, accuracyImportanceWeight q I sigma2
          (fun y => weight y - r) x ^ 2 ∂pi) =
        ∫ x, accuracyImportanceWeight q I sigma2 u x ^ 2 ∂pi := by rfl
    _ ≤ ∫ x, (accept x).toReal * u (scale x) ^ 2 ∂pi := hleft
    _ = ∫ y, u y ^ 2 ∂accepted := hidentity
    _ ≤ ∫ y, u y ^ 2 ∂((4 : ENNReal) • nu) := hright
    _ = 4 * ∫ y, (weight y - r) ^ 2 ∂nu := by
      rw [integral_smul_measure]
      norm_num [u]
    _ = 4 * ∫ y, (weight y - r) ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n)) := by rfl

end ArlibCommunity.Algorithms.CV18
