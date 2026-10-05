/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialSpeedyWarmStart

/-! # Body-independent warm starts for independent CV18 phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal
open Arlib Arlib.MarkovChains

/-- The known Gaussian law conditioned on the centered inball of an accuracy
phase.  It depends only on public parameters, never on the unknown body. -/
noncomputable def freshPhaseStartMeasure (q : VolumeParams) (sigma2 : ℝ) :
    Measure (AmbientSpace q.n) :=
  Arlib.uniformOn
    ((volume : Measure (AmbientSpace q.n)).withDensity (gaussianWeight sigma2))
    (Metric.closedBall 0 (accuracyPhaseInradius q sigma2))

/-- A body-independent ENNReal warmness coefficient for the fresh phase
start.  The first factor pays for the local-conductance floor on the inball;
the second is the reciprocal Gaussian mass of that inball. -/
noncomputable def freshPhaseWarmCoefficient
    (q : VolumeParams) (sigma2 : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ q.n) *
    (((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight sigma2)) Set.univ /
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight sigma2))
        (Metric.closedBall 0 (accuracyPhaseInradius q sigma2)))

theorem freshPhaseGaussianBall_mass_ne_zero
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight sigma2))
      (Metric.closedBall 0 (accuracyPhaseInradius q sigma2)) ≠ 0 := by
  apply withDensity_gaussianWeight_ne_zero
  exact (Metric.measure_closedBall_pos volume (0 : AmbientSpace q.n)
    (accuracyPhaseInradius_pos q hsigma2)).ne'

theorem freshPhaseGaussianBall_mass_ne_top
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight sigma2))
      (Metric.closedBall 0 (accuracyPhaseInradius q sigma2)) ≠ ⊤ := by
  exact withDensity_gaussianWeight_ne_top hsigma2 measurableSet_closedBall
    (isCompact_closedBall (0 : AmbientSpace q.n)
      (accuracyPhaseInradius q sigma2)).measure_lt_top.ne

theorem freshPhaseStartMeasure_isProbabilityMeasure
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsProbabilityMeasure (freshPhaseStartMeasure q sigma2) := by
  unfold freshPhaseStartMeasure
  exact Arlib.isProbabilityMeasure_uniformOn _
    (freshPhaseGaussianBall_mass_ne_zero q hsigma2)
    (freshPhaseGaussianBall_mass_ne_top q hsigma2)

/-- The unnormalised known inball Gaussian is `2^n`-dominated by the
unnormalised speedy stationary measure of every compatible accuracy body. -/
theorem freshPhaseGaussian_restrict_le_speedy
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let G : Measure (AmbientSpace q.n) :=
      (volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight sigma2)
    let B := Metric.closedBall (0 : AmbientSpace q.n)
      (accuracyPhaseInradius q sigma2)
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    G.restrict B ≤ ENNReal.ofReal ((2 : ℝ) ^ q.n) •
      ellGaussianMeasure K delta sigma2 := by
  dsimp only
  let G : Measure (AmbientSpace q.n) :=
    (volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight sigma2)
  let B := Metric.closedBall (0 : AmbientSpace q.n)
    (accuracyPhaseInradius q sigma2)
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ q.n)
  have hBK : B ⊆ K := by
    intro x hx
    have hnorm : ‖x‖ ≤ accuracyPhaseInradius q sigma2 := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
    refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
    · rw [unitBall, Metric.mem_closedBall, dist_zero_right]
      exact hnorm.trans (min_le_left _ _)
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hnorm.trans (min_le_right _ _)
  have hfloor : ∀ x ∈ B,
      ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) ≤ ell K delta x := by
    intro x hx
    exact ofReal_halfPow_le_ell_of_closedBall_subset
      (accuracyPhaseInradius_pos q hsigma2)
      (figureOneProposalRadius_pos q hsigma2)
      (figureOneProposalRadius_le_accuracyPhaseInradius q hsigma2)
      hBK hx
  have hCtheta : C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) = 1 := by
    dsimp [C]
    rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q.n),
      ← ENNReal.ofReal_one]
    congr 1
    rw [← mul_pow]
    norm_num
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA]
  change G (A ∩ B) ≤ _
  rw [show G (A ∩ B) = ∫⁻ x in A ∩ B, gaussianWeight sigma2 x by
    dsimp [G]
    rw [withDensity_apply _ (hA.inter measurableSet_closedBall)] ]
  rw [Measure.smul_apply, smul_eq_mul]
  rw [ellGaussianMeasure, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  have hmeasEll : Measurable fun x : AmbientSpace q.n =>
      ell K delta x * gaussianWeight sigma2 x :=
    measurable_ell_mul_gaussianWeight
      (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
  rw [← lintegral_const_mul _ hmeasEll]
  calc
    (∫⁻ x in A ∩ B, gaussianWeight sigma2 x) ≤
        ∫⁻ x in A ∩ B, C *
          (ell K delta x * gaussianWeight sigma2 x) := by
      apply setLIntegral_mono'
      · exact hA.inter measurableSet_closedBall
      · intro x hx
        calc
          gaussianWeight sigma2 x = 1 * gaussianWeight sigma2 x :=
            (one_mul _).symm
          _ = (C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n)) *
              gaussianWeight sigma2 x := by rw [hCtheta]
          _ ≤ C * (ell K delta x * gaussianWeight sigma2 x) := by
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (mul_le_mul' (hfloor x hx.2) le_rfl)
    _ ≤ ∫⁻ x in A ∩ K, C *
        (ell K delta x * gaussianWeight sigma2 x) :=
      lintegral_mono_set (fun x hx => ⟨hx.1, hBK hx.2⟩)

/-- A fresh public Gaussian-inball draw is warm for the phase's speedy
stationary law, uniformly over every admissible unknown body. -/
theorem freshPhaseStartMeasure_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm (freshPhaseWarmCoefficient q sigma2)
      (freshPhaseStartMeasure q sigma2)
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) := by
  let G : Measure (AmbientSpace q.n) :=
    (volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight sigma2)
  let B := Metric.closedBall (0 : AmbientSpace q.n)
    (accuracyPhaseInradius q sigma2)
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let mu := G.restrict B
  let nu := ellGaussianMeasure K delta sigma2
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ q.n)
  let D : ℝ≥0∞ := G Set.univ / G B
  have hGB0 : G B ≠ 0 := by
    exact freshPhaseGaussianBall_mass_ne_zero q hsigma2
  have hGBtop : G B ≠ ⊤ := by
    exact freshPhaseGaussianBall_mass_ne_top q hsigma2
  have hmu0 : mu Set.univ ≠ 0 := by
    simpa [mu, Measure.restrict_apply_univ] using hGB0
  have hmutop : mu Set.univ ≠ ⊤ := by
    simpa [mu, Measure.restrict_apply_univ] using hGBtop
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hnu0 : nu Set.univ ≠ 0 := by
    exact ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hnutop : nu Set.univ ≠ ⊤ := by
    exact ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  have hdom : mu ≤ C • nu := by
    simpa [mu, nu, C, G, B, K, delta] using
      freshPhaseGaussian_restrict_le_speedy q I hsigma2
  have hnuG : nu Set.univ ≤ G Set.univ := by
    calc
      nu Set.univ ≤ ∫⁻ x in K, gaussianWeight sigma2 x :=
        ellGaussianMeasure_univ_le_gaussianMass delta sigma2
      _ ≤ ∫⁻ x, gaussianWeight sigma2 x ∂volume := by
        exact setLIntegral_le_lintegral _ _
      _ = G Set.univ := by
        dsimp [G]
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hmass : nu Set.univ ≤ D * mu Set.univ := by
    calc
      nu Set.univ ≤ G Set.univ := hnuG
      _ = (G Set.univ / G B) * G B := by
        exact (ENNReal.div_mul_cancel hGB0 hGBtop).symm
      _ = D * mu Set.univ := by simp [D, mu, Measure.restrict_apply_univ]
  have hw := isWarm_normalize_of_le_smul hmu0 hmutop hnu0 hnutop hdom hmass
  have hmuMass : mu Set.univ = G B := by
    simp [mu]
  rw [hmuMass] at hw
  simpa only [freshPhaseStartMeasure, freshPhaseWarmCoefficient,
    Arlib.uniformOn_def, ellGaussianProb,
    G, B, K, delta, mu, nu, C, D] using hw

end ArlibCommunity.Algorithms.CV18
