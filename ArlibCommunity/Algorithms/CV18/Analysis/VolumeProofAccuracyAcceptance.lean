/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyRejectionSemantics

/-! # Constant success probability of the executable CV18 KLS correction -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open Arlib MarkovChains

/-- A TV perturbation of a proposal whose rejection acceptance is at least
one half still accepts with probability at least one quarter. -/
theorem TVLe.withDensity_mass_ge_quarter_cv18
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ))
    {accept : S → ENNReal} (haccept : Measurable accept)
    (haccept_one : ∀ x, accept x ≤ 1)
    (hnu : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (nu.withDensity accept) Set.univ) :
    ENNReal.ofReal (1 / 4 : ℝ) ≤
      (mu.withDensity accept) Set.univ := by
  have hweighted := TVLe.withDensity_le_one_cv18 h haccept haccept_one
  have hquarterAdd : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by
        gcongr
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num
  have hadd : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
      (mu.withDensity accept) Set.univ + epsilon :=
    hquarterAdd.trans (hnu.trans (hweighted.right MeasurableSet.univ))
  exact ENNReal.le_of_add_le_add_right
    (ne_top_of_le_ne_top (by norm_num) hepsilon) hadd

/-- At speedy stationarity, conditioning on the homothetic core and scaling
back gives the ideal enlarged-variance Gaussian proposal up to the concrete
KLS core-defect error. -/
theorem accuracyPhase_stationaryCoreMap_tv_proposal
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let c := accuracyScaleFactor q
    let pi := ellGaussianProb K delta sigma2
    let proposal := Arlib.condOn
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K
    Arlib.TVLe
      ((Arlib.condOn pi (c • K)).map (fun x => c⁻¹ • x))
      proposal (4 * ENNReal.ofReal (accuracyCoreError q)) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let c := accuracyScaleFactor q
  let pi := ellGaussianProb K delta sigma2
  let proposal := Arlib.condOn
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight (sigma2 / c ^ 2))) K
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hc1 : c < 1 := by
    dsimp [c, accuracyScaleFactor]
    have : 0 < 1 / (2 * (q.n : ℝ)) := by positivity
    linarith
  have hKmeas : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hKconv : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKcompact : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ := accuracyPhaseTruncatedBody_volume_ne_top q I sigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hKmeas hKconv hKcompact.isBounded hK0
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  by_cases hsmall : accuracyPhaseRadius q sigma2 ≤ 1
  · have hcoreEq := condOn_ellGaussianProb_smul_eq_gaussian_radius_cv18
      hKmeas hKconv (accuracyPhaseInradius_pos q hsigma2)
      (ball_accuracyPhaseInradius_subset q I sigma2) hc0 hc1 hdelta
      (by
        calc
          delta ≤ accuracyPhaseInradius q sigma2 / (2 * (q.n : ℝ)) :=
            figureOneProposalRadius_le_accuracyPhaseCoreStep q hsigma2 hsmall
          _ = (1 - c) * accuracyPhaseInradius q sigma2 := by
            dsimp [c, accuracyScaleFactor]
            ring)
      hmass0 hmasstop
    have hmap := congrArg
      (fun mu : Measure (AmbientSpace q.n) => mu.map (fun x => c⁻¹ • x)) hcoreEq
    rw [map_condOn_gaussian_smul_cv18 hKmeas hc0] at hmap
    have heq : (Arlib.condOn pi (c • K)).map (fun x => c⁻¹ • x) =
        proposal := by simpa [pi, proposal] using hmap
    rw [heq]
    exact (Arlib.TVLe.refl proposal).mono bot_le
  · have hlarge : 1 ≤ accuracyPhaseRadius q sigma2 := le_of_not_ge hsmall
    have hunit : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
      intro x hx
      refine ⟨unitBall_subset_truncatedBody q I (by simpa [unitBall] using hx), ?_⟩
      have hx1 : ‖x‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      simpa [Metric.mem_closedBall, dist_zero_right] using hx1.trans hlarge
    have hcoreM : MeasurableSet (c • K) :=
      ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcompact.isClosed).measurableSet
    have hsub : c • K ⊆ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hKconv.smul_mem_of_zero_mem
        (hunit (Metric.mem_closedBall_self zero_le_one)) hx ⟨hc0.le, hc1.le⟩
    have hcoreVol0 : volume (c • K) ≠ 0 := by
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 q.n)) hK0
    have hcoreVoltop : volume (c • K) ≠ ⊤ := by
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
    have hgaussCore0 :
        (((volume : Measure (AmbientSpace q.n)).withDensity
          (gaussianWeight sigma2)).restrict K) (c • K) ≠ 0 := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact withDensity_gaussianWeight_ne_zero _ hcoreVol0
    have hgaussCoretop :
        (((volume : Measure (AmbientSpace q.n)).withDensity
          (gaussianWeight sigma2)).restrict K) (c • K) ≠ ⊤ := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact withDensity_gaussianWeight_ne_top hsigma2 hcoreM hcoreVoltop
    have hpaper := standardCore_defect_and_speedyMass_cv18
      hn hKconv hKcompact.isClosed hKtop hunit hdelta
      (Real.sqrt_pos.2 hsigma2) (accuracyCoreError_pos q)
      (accuracyCoreError_le_one_div_sixteen q)
      (figureOneProposalRadius_le_accuracyCoreErrorStep q hsigma2)
      (by
        convert hgaussCore0 using 1 <;>
          simp [c, accuracyScaleFactor, div_eq_mul_inv, mul_comm,
            Real.sq_sqrt hsigma2.le])
      (by
        convert hgaussCoretop using 1 <;>
          simp [c, accuracyScaleFactor, div_eq_mul_inv, mul_comm,
            Real.sq_sqrt hsigma2.le])
      (by simpa [Real.sq_sqrt hsigma2.le] using hmass0)
      (by simpa [Real.sq_sqrt hsigma2.le] using hmasstop)
    have hcompare := TVLe.condOn_ellGaussianProb_gaussian_of_coreDefect_cv18
      hKmeas hcoreM delta sigma2 hmass0 hmasstop hgaussCore0 hgaussCoretop
      ENNReal.ofReal_ne_top
      (ENNReal.ofReal_le_ofReal
        ((accuracyCoreError_le_one_div_sixteen q).trans (by norm_num)))
      (by simpa [c, accuracyScaleFactor, Real.sq_sqrt hsigma2.le] using hpaper.1)
    have hgaussRestrict :
        Arlib.condOn
            (((volume : Measure (AmbientSpace q.n)).withDensity
              (gaussianWeight sigma2)).restrict K) (c • K) =
          Arlib.condOn
            ((volume : Measure (AmbientSpace q.n)).withDensity
              (gaussianWeight sigma2)) (c • K) :=
      condOn_restrict_eq_condOn_of_subset_cv18 _ hcoreM hsub
    rw [hgaussRestrict] at hcompare
    have hmap := hcompare.map ((continuous_const_smul c⁻¹).measurable)
    have htarget := map_condOn_gaussian_smul_cv18 hKmeas hc0
      (variance := sigma2)
    rw [htarget] at hmap
    simpa [pi, proposal] using hmap

/-- At speedy stationarity, one executable KLS rejection attempt succeeds
with probability at least `7/64`. -/
theorem accuracyPhase_stationary_acceptance_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 64 : ℝ) ≤
      (pi.withDensity
        (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let c := accuracyScaleFactor q
  let pi := ellGaussianProb K delta sigma2
  let core := c • K
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal := gaussianScaleAcceptance sigma2 c
  let source := (Arlib.condOn pi core).map scale
  let proposal := Arlib.condOn
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight (sigma2 / c ^ 2))) K
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hKmeas : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hKconv : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKcompact : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ := accuracyPhaseTruncatedBody_volume_ne_top q I sigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hKmeas hKconv hKcompact.isBounded hK0
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hcoreMass : ENNReal.ofReal (7 / 16 : ℝ) ≤ pi core := by
    simpa [pi, core, K, delta, c] using
      accuracyPhase_speedy_core_mass q I hsigma2
  have hcore0 : pi core ≠ 0 :=
    ne_of_gt ((by norm_num : 0 < ENNReal.ofReal (7 / 16 : ℝ)).trans_le hcoreMass)
  have hcoretop : pi core ≠ ⊤ := measure_ne_top pi core
  let _ : IsProbabilityMeasure (Arlib.condOn pi core) :=
    Arlib.isProbabilityMeasure_condOn pi hcore0 hcoretop
  let _ : IsProbabilityMeasure source :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hscaled : 0 < sigma2 / c ^ 2 := by positivity
  have hprop0 :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K ≠ 0 :=
    withDensity_gaussianWeight_ne_zero _ hK0
  have hproptop :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K ≠ ⊤ :=
    withDensity_gaussianWeight_ne_top hscaled hKmeas hKtop
  let _ : IsProbabilityMeasure proposal :=
    Arlib.isProbabilityMeasure_condOn _ hprop0 hproptop
  have hsourceTv : Arlib.TVLe source proposal
      (4 * ENNReal.ofReal (accuracyCoreError q)) := by
    simpa [source, proposal, pi, core, scale, K, delta, c] using
      accuracyPhase_stationaryCoreMap_tv_proposal q I hsigma2
  have herr : 4 * ENNReal.ofReal (accuracyCoreError q) ≤
      ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by
      nlinarith [accuracyCoreError_le_one_div_sixty_four q])
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (proposal.withDensity g) Set.univ := by
    dsimp [proposal, g, c]
    exact half_le_condOn_gaussian_scaleAcceptance_mass_standardCore_cv18
      hn hKmeas hKconv
      (by
        refine ⟨unitBall_subset_truncatedBody q I
          (Metric.mem_closedBall_self zero_le_one), ?_⟩
        simpa [Metric.mem_closedBall] using
          (accuracyPhaseRadius_pos q hsigma2).le)
      (by simpa [c, accuracyScaleFactor] using hprop0)
      (by simpa [c, accuracyScaleFactor] using hproptop)
  have hg : Measurable g := by
    dsimp [g]
    exact measurable_gaussianScaleAcceptance sigma2 c
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    dsimp [g]
    exact gaussianScaleAcceptance_le_one hsigma2 hc0
      (accuracyScaleFactor_le_one q) x
  have hsourceAccept : ENNReal.ofReal (1 / 4 : ℝ) ≤
      (source.withDensity g) Set.univ :=
    TVLe.withDensity_mass_ge_quarter_cv18 hsourceTv herr hg hg1 hhalf
  have hrestrict : pi.restrict core = pi core • Arlib.condOn pi core := by
    rw [Arlib.condOn_def, smul_smul,
      ENNReal.mul_inv_cancel hcore0 hcoretop, one_smul]
  have hsourceScale :
      ((pi.restrict core).map scale).withDensity g =
        pi core • (source.withDensity g) := by
    rw [hrestrict, Measure.map_smul, withDensity_smul_measure]
  have hmeasure := map_withDensity_accuracyRejectionAcceptance q I sigma2 pi
  have htotal := congrArg (fun mu : Measure (AmbientSpace q.n) => mu Set.univ) hmeasure
  have hscale : Measurable scale := by fun_prop
  rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ,
    hsourceScale, Measure.smul_apply, smul_eq_mul] at htotal
  calc
    ENNReal.ofReal (7 / 64 : ℝ) =
        ENNReal.ofReal (7 / 16 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7 / 16)]
      norm_num
    _ ≤ pi core * (source.withDensity g) Set.univ :=
      mul_le_mul hcoreMass hsourceAccept bot_le bot_le
    _ = (pi.withDensity
        (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := htotal.symm

/-- After a Figure-1 mixing block, a single executable KLS rejection attempt
succeeds with probability at least `1/16`. -/
theorem accuracyPhase_mixed_acceptance_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := lazy (speedyMetropolisGaussian K delta sigma2)
    let mu := iterate P mu0 t
    ENNReal.ofReal (1 / 16 : ℝ) ≤
      (mu.withDensity
        (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := lazy (speedyMetropolisGaussian K delta sigma2)
  let pi := ellGaussianProb K delta sigma2
  let mu := iterate P mu0 t
  have hmixPhase := mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht
  have hmix : Arlib.TVLe mu pi (ENNReal.ofReal mixError) := by
    simpa [MixesWithin, mu, pi, P, K, delta] using hmixPhase
  have hstationary : ENNReal.ofReal (7 / 64 : ℝ) ≤
      (pi.withDensity
        (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := by
    simpa [pi, K, delta] using accuracyPhase_stationary_acceptance_ge q I hsigma2
  have hweighted := TVLe.withDensity_le_one_cv18 hmix
    (measurable_accuracyGaussianRejectionAcceptance q I sigma2)
    (accuracyGaussianRejectionAcceptance_le_one q I hsigma2)
  have hadd : ENNReal.ofReal (1 / 16 : ℝ) + ENNReal.ofReal mixError ≤
      ENNReal.ofReal (7 / 64 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (1 / 16 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) := by
        gcongr
      _ ≤ ENNReal.ofReal (7 / 64 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 16)
          (by norm_num : (0 : ℝ) ≤ 1 / 64)]
        norm_num
  have hadd' : ENNReal.ofReal (1 / 16 : ℝ) + ENNReal.ofReal mixError ≤
      (mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ +
        ENNReal.ofReal mixError :=
    hadd.trans (hstationary.trans (hweighted.right MeasurableSet.univ))
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hadd'

end ArlibCommunity.Algorithms.CV18
