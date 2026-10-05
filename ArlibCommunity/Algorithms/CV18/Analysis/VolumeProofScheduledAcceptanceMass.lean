/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledParameters

/-! # Uniform scheduled balanced branch masses -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

noncomputable def scheduledBalancedAcceptedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity (scheduledBalancedAccuracyGaussianAcceptance q I sigma2)

noncomputable def scheduledBalancedRejectedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity
    (fun x => 1 - scheduledBalancedAccuracyGaussianAcceptance q I sigma2 x)

/-- Before the second rejection, conditioning on the scheduled homothetic
core and scaling gives the enlarged-variance Gaussian proposal up to the
scheduled core defect. -/
theorem figureOneScheduled_stationaryCoreMap_tv_proposal
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let c := accuracyScaleFactor q
    let pi := ellGaussianProb K delta sigma2
    let proposal := Arlib.condOn
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K
    Arlib.TVLe
      ((Arlib.condOn pi (c • K)).map (fun x => c⁻¹ • x))
      proposal (4 * ENNReal.ofReal (figureOneScheduledCoreError q)) := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let c := accuracyScaleFactor q
  let pi := ellGaussianProb K delta sigma2
  let proposal := Arlib.condOn
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight (sigma2 / c ^ 2))) K
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hc1 : c < 1 := by
    dsimp [c, accuracyScaleFactor]
    have : 0 < 1 / (2 * (q.n : ℝ)) := by positivity
    linarith
  have hKmeas : MeasurableSet K :=
    figureOneScheduledPhaseBody_measurable q I sigma2
  have hKconv : Convex ℝ K := figureOneScheduledPhaseBody_convex q I sigma2
  have hKcompact : IsCompact K := figureOneScheduledPhaseBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 :=
    figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ :=
    figureOneScheduledPhaseBody_volume_ne_top q I sigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hKmeas hKconv hKcompact.isBounded hK0
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  by_cases hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1
  · have hcoreEq := condOn_ellGaussianProb_smul_eq_gaussian_radius_cv18
      hKmeas hKconv (figureOneScheduledPhaseInradius_pos q hsigma2)
      (ball_scheduledPhaseInradius_subset q I sigma2) hc0 hc1 hdelta
      (by
        calc
          delta ≤ figureOneScheduledPhaseInradius q sigma2 /
              (2 * (q.n : ℝ)) :=
            figureOneScheduledProposalRadius_le_inradiusStep q hsigma2 hsmall
          _ = (1 - c) * figureOneScheduledPhaseInradius q sigma2 := by
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
  · have hlarge : 1 ≤ figureOneScheduledPhaseRadius q sigma2 :=
      le_of_not_ge hsmall
    have hunit : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
      intro x hx
      refine ⟨unitBall_subset_truncatedBody q I (by
        simpa [unitBall] using hx), hx.trans hlarge⟩
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
      (Real.sqrt_pos.2 hsigma2) (figureOneScheduledCoreError_pos q)
      (figureOneScheduledCoreError_le_one_div_sixteen q)
      (figureOneScheduledProposalRadius_le_coreStep q hsigma2)
      (by convert hgaussCore0 using 1 <;>
        simp [c, accuracyScaleFactor, div_eq_mul_inv, mul_comm,
          Real.sq_sqrt hsigma2.le])
      (by convert hgaussCoretop using 1 <;>
        simp [c, accuracyScaleFactor, div_eq_mul_inv, mul_comm,
          Real.sq_sqrt hsigma2.le])
      (by simpa [Real.sq_sqrt hsigma2.le] using hmass0)
      (by simpa [Real.sq_sqrt hsigma2.le] using hmasstop)
    have hcompare := TVLe.condOn_ellGaussianProb_gaussian_of_coreDefect_cv18
      hKmeas hcoreM delta sigma2 hmass0 hmasstop hgaussCore0 hgaussCoretop
      ENNReal.ofReal_ne_top
      (ENNReal.ofReal_le_ofReal
        ((figureOneScheduledCoreError_le_one_div_sixteen q).trans (by norm_num)))
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

end ArlibCommunity.Algorithms.CV18
