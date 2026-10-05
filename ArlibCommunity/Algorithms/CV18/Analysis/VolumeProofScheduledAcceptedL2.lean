/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedSupport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyTVL2

/-!
# L2 domination for the schedule-targeted accepted law

The schedule-targeted KLS core uses a different radius from the older
accuracy core.  This module supplies the corresponding warm domination
needed to transfer unbounded Gaussian-ratio moments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

/-- The unnormalised speedy measure on the scheduled core is dominated by
the ordinary Gaussian measure on the full truncated body. -/
theorem scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    ellGaussianMeasure
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 ≤
      truncatedGaussianMeasure q I sigma2 := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [ellGaussianMeasure, withDensity_apply _ hA,
    truncatedGaussianMeasure, withDensity_apply _ hA]
  rw [Measure.restrict_restrict hA, Measure.restrict_restrict hA]
  have hsub : A ∩ figureOneScheduledPhaseBody q I sigma2 ⊆
      A ∩ truncatedBody q I := fun _ hx => ⟨hx.1, hx.2.1⟩
  calc
    (∫⁻ x in A ∩ figureOneScheduledPhaseBody q I sigma2,
        ell (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) x *
          gaussianWeight sigma2 x) ≤
      ∫⁻ x in A ∩ figureOneScheduledPhaseBody q I sigma2,
        gaussianWeight sigma2 x := by
      apply lintegral_mono
      intro x
      simpa using mul_le_mul'
        (ell_le_one (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) x) le_rfl
    _ ≤ ∫⁻ x in A ∩ truncatedBody q I,
        gaussianWeight sigma2 x :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ = ∫⁻ x in A ∩ truncatedBody q I,
        ENNReal.ofReal (gaussianDensity sigma2 x) := by
      apply lintegral_congr
      intro x
      simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]

/-- The full truncated Gaussian normalizer is at most four times the
scheduled speedy-core normalizer. -/
theorem scheduledPhase_gaussianMass_le_four_ellGaussianMass
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedGaussianMeasure q I sigma2 Set.univ ≤
      4 * ellGaussianMeasure
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
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
        (by dsimp [K]; exact figureOneScheduledPhaseBody_measurable q I sigma2)
        hsigma2]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [K] using
        scheduledPhase_full_gaussianIntegral_le_two_core q I hsigma2)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * core ≤ speedy := by
    simpa [K, delta, core, speedy] using
      half_mul_gaussianWeight_le_scheduledPhaseEllGaussian q I hsigma2
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

/-- The schedule-targeted speedy stationary law is universally `4`-warm
for the exact truncated Gaussian at the same variance. -/
theorem scheduledPhase_speedyStationary_isWarm_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm 4
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  let mu := ellGaussianMeasure
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  let nu := truncatedGaussianMeasure q I sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmu0 : mu Set.univ ≠ 0 := by
    dsimp [mu]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmutop : mu Set.univ ≠ ⊤ := by
    dsimp [mu]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) hsigma2
  have hnu0 : nu Set.univ ≠ 0 := by
    intro hzero
    have hmeasure : nu = 0 := Measure.measure_univ_eq_zero.mp hzero
    exact truncatedGaussianMeasure_ne_zero q I hsigma2
      (by simpa [nu] using hmeasure)
  have hnutop : nu Set.univ ≠ ⊤ := by
    let _ := truncatedGaussianMeasure_isFinite q I hsigma2
    exact measure_ne_top nu Set.univ
  have hdom : mu ≤ (1 : ENNReal) • nu := by
    simpa [mu, nu] using
      scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
        q I sigma2
  have hmass : nu Set.univ ≤ (4 : ENNReal) * mu Set.univ := by
    simpa [mu, nu] using
      scheduledPhase_gaussianMass_le_four_ellGaussianMass q I hsigma2
  have hw := isWarm_normalize_of_le_smul hmu0 hmutop hnu0 hnutop hdom hmass
  simpa [mu, nu, ellGaussianProb,
    truncatedGaussianProbability_toMeasure q I hsigma2,
    truncatedGaussianMeasure_apply_univ q I hsigma2] using hw

/-- Applying the schedule-targeted KLS acceptance density to the exact
Gaussian and expanding the accepted point produces a submeasure of the same
exact Gaussian. -/
theorem truncatedGaussianProbability_scheduledAcceptance_map_le_self
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I sigma2 hsigma2
    (nu.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x) ≤ nu := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
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
  have hK : MeasurableSet K :=
    figureOneScheduledPhaseBody_measurable q I sigma2
  have hcore : MeasurableSet core := by
    dsimp [core]
    exact measurableSet_smul_set_cv18 hK hc0.ne'
  have hscale : Measurable scale := by dsimp [scale]; fun_prop
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    refine ⟨unitBall_subset_truncatedBody q I
      (Metric.mem_closedBall_self zero_le_one), ?_⟩
    exact Metric.mem_closedBall_self
      (figureOneScheduledPhaseRadius_pos q hsigma2).le
  have hcoreK : core ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (figureOneScheduledPhaseBody_convex q I sigma2).smul_mem_of_zero_mem
      hzero hx ⟨hc0.le, hc1⟩
  have hKfull : K ⊆ truncatedBody q I := fun _ hx => hx.1
  have hcoreFull : core ⊆ truncatedBody q I := hcoreK.trans hKfull
  have hgaussianCore0 : gaussian core ≠ 0 := by
    have hvol0 : volume core ≠ 0 := by
      dsimp [core]
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact mul_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 q.n))
        (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
    exact withDensity_gaussianWeight_ne_zero sigma2 hvol0
  have hgaussianCoreTop : gaussian core ≠ ⊤ := by
    have hvolTop : volume core ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
        (measure_mono hcoreK)
    exact withDensity_gaussianWeight_ne_top hsigma2 hcore hvolTop
  have hnuCore0 : nu core ≠ 0 := by
    rw [truncatedGaussianProbability_apply q I hsigma2 hcore]
    rw [Set.inter_eq_left.2 hcoreFull]
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
  have hsource := map_withDensity_scheduledAccuracyRejectionAcceptance
    q I sigma2 nu
  change (nu.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map scale ≤ nu
  rw [hsource, hrestrict, Measure.map_smul, withDensity_smul_measure,
    hmapCond]
  have hproposalDensity :
      (Arlib.condOn proposalGaussian K).withDensity g =
        (proposalGaussian K)⁻¹ • gaussian.restrict K := by
    simpa [proposalGaussian, gaussian, g, c] using
      condOn_gaussian_withDensity_scaleAcceptance_cv18 hK sigma2 c
  rw [hproposalDensity, smul_smul]
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
      ENNReal.ofReal_le_one.mpr <| pow_le_one₀ hc0.le hc1
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
          (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      have hpTop : proposalGaussian K ≠ ⊤ := by
        dsimp [proposalGaussian]
        exact withDensity_gaussianWeight_ne_top (by positivity) hK
          (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
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

/-- Before normalization, the schedule-targeted accepted submeasure is at
most four times the exact Gaussian target. -/
theorem stationary_scheduledAcceptedSubmeasure_le_four_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I sigma2 hsigma2
    (pi.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x) ≤
          (4 : ENNReal) • nu := by
  dsimp only
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let accept := scheduledAccuracyGaussianRejectionAcceptance q I sigma2
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  have hpi : pi ≤ (4 : ENNReal) • nu := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa [pi, nu, Measure.smul_apply, smul_eq_mul] using
      (scheduledPhase_speedyStationary_isWarm_target q I hsigma2 A hA)
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
  have hself := truncatedGaussianProbability_scheduledAcceptance_map_le_self
    q I hsigma2
  change (pi.withDensity accept).map scale ≤ 4 • nu
  exact hmap.trans <| by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul' le_rfl (Measure.le_iff.mp hself A hA)

/-- The normalized schedule-targeted accepted law is universally `32`-warm
for the exact Gaussian.  This is the missing L2 bridge for unbounded cooling
ratios. -/
theorem stationary_scheduledAcceptedTarget_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm 32
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
        (ellGaussianProb
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2))
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let accepted :=
    (pi.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x)
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmassTop : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  have hacceptedLower : ENNReal.ofReal (1 / 8 : ℝ) ≤
      accepted Set.univ := by
    have h := scheduledAccuracyPhase_stationary_acceptance_ge_one_eighth
      q I hsigma2
    change ENNReal.ofReal (1 / 8 : ℝ) ≤ accepted Set.univ
    dsimp [accepted]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ]
    simpa [pi] using h
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (1 / 8 : ℝ)).trans_le hacceptedLower
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <| by
      calc
        accepted Set.univ =
            (pi.withDensity
              (scheduledAccuracyGaussianRejectionAcceptance q I sigma2))
                Set.univ := by
          dsimp [accepted]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
            Set.preimage_univ]
        _ ≤ pi Set.univ := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
          calc
            (∫⁻ x, scheduledAccuracyGaussianRejectionAcceptance q I sigma2 x
                ∂pi) ≤ ∫⁻ _x, (1 : ENNReal) ∂pi := by
              exact lintegral_mono <|
                scheduledAccuracyGaussianRejectionAcceptance_le_one
                  q I hsigma2
            _ = pi Set.univ := lintegral_one
  have hnu0 : nu Set.univ ≠ 0 := by simp [nu]
  have hnuTop : nu Set.univ ≠ ⊤ := by simp [nu]
  have hdom : accepted ≤ (4 : ENNReal) • nu := by
    simpa [accepted, pi, nu] using
      stationary_scheduledAcceptedSubmeasure_le_four_target q I hsigma2
  have hmass : nu Set.univ ≤ (8 : ENNReal) * accepted Set.univ := by
    rw [show nu Set.univ = 1 by simp [nu]]
    calc
      1 = 8 * ENNReal.ofReal (1 / 8 : ℝ) := by
        rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num
      _ ≤ 8 * accepted Set.univ := mul_le_mul' le_rfl hacceptedLower
  have hw := isWarm_normalize_of_le_smul
    haccepted0 hacceptedTop hnu0 hnuTop hdom hmass
  rw [scheduledBalancedAccuracyGaussianAcceptedTargetLaw_eq]
  change IsWarm 32 (Arlib.condOn accepted Set.univ) nu
  rw [Arlib.condOn_def, Measure.restrict_univ]
  convert hw using 1 <;> norm_num

#print axioms scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
#print axioms scheduledPhase_gaussianMass_le_four_ellGaussianMass
#print axioms scheduledPhase_speedyStationary_isWarm_target
#print axioms truncatedGaussianProbability_scheduledAcceptance_map_le_self
#print axioms stationary_scheduledAcceptedSubmeasure_le_four_target
#print axioms stationary_scheduledAcceptedTarget_isWarm

end ArlibCommunity.Algorithms.CV18
