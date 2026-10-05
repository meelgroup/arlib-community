/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyProperProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialTail

/-! # Concrete KLS error parameters for every CV18 accuracy phase -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal Pointwise

/-- A concrete error for the KLS homothetic-core argument.  Its exponential
decay leaves ample room in Figure 1's proposal-radius constant. -/
noncomputable def accuracyCoreError (q : VolumeParams) : ℝ :=
  Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ)

theorem accuracyCoreError_pos (q : VolumeParams) :
    0 < accuracyCoreError q := by
  unfold accuracyCoreError
  apply div_pos (Real.exp_pos _)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)

theorem accuracyCoreError_le_one_div_sixteen (q : VolumeParams) :
    accuracyCoreError q ≤ 1 / 16 := by
  have hn : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) :=
    le_max_left _ _
  have hexp : Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) ≤
      Real.exp (-6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold accuracyCoreError
  calc
    Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ) ≤
        Real.exp (-6) / 1 := by
      calc
        _ ≤ Real.exp (-6) / (q.n : ℝ) :=
          div_le_div_of_nonneg_right hexp (by positivity)
        _ ≤ Real.exp (-6) / 1 := by
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hn
    _ ≤ 1 / 64 := by simpa using exp_neg_six_le_one_div_64
    _ ≤ 1 / 16 := by norm_num

theorem accuracyCoreError_le_one_div_sixty_four (q : VolumeParams) :
    accuracyCoreError q ≤ 1 / 64 := by
  have hn : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) :=
    le_max_left _ _
  have hexp : Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) ≤
      Real.exp (-6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold accuracyCoreError
  calc
    Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ) ≤
        Real.exp (-6) / 1 := by
      calc
        _ ≤ Real.exp (-6) / (q.n : ℝ) :=
          div_le_div_of_nonneg_right hexp (by positivity)
        _ ≤ Real.exp (-6) / 1 := by
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hn
    _ ≤ 1 / 64 := by simpa using exp_neg_six_le_one_div_64

theorem log_n_div_accuracyCoreError_le (q : VolumeParams) :
    Real.log ((q.n : ℝ) / accuracyCoreError q) ≤
      130 * protectedLog ((q.n : ℝ) / q.eps) := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have heps0 : 0 < q.eps := q.heps.1
  have hnle : (q.n : ℝ) ≤ (q.n : ℝ) / q.eps := by
    rw [le_div_iff₀ heps0]
    have hnnonneg : (0 : ℝ) ≤ q.n := hn0.le
    nlinarith [q.heps.2.le]
  have hlogn : Real.log (q.n : ℝ) ≤ L := by
    calc
      Real.log (q.n : ℝ) ≤ Real.log ((q.n : ℝ) / q.eps) :=
        Real.strictMonoOn_log.monotoneOn hn0 (div_pos hn0 heps0) hnle
      _ ≤ L := le_max_right _ _
  have hexp0 : Real.exp (-128 * L) ≠ 0 := (Real.exp_pos _).ne'
  have hnne : (q.n : ℝ) ≠ 0 := hn0.ne'
  change Real.log ((q.n : ℝ) /
      (Real.exp (-128 * L) / (q.n : ℝ))) ≤ 130 * L
  have heq : (q.n : ℝ) / (Real.exp (-128 * L) / (q.n : ℝ)) =
      ((q.n : ℝ) * (q.n : ℝ)) / Real.exp (-128 * L) := by
    field_simp
  rw [heq, Real.log_div (mul_ne_zero hnne hnne) hexp0,
    Real.log_mul hnne hnne, Real.log_exp]
  nlinarith

/-- Figure 1's actual proposal radius satisfies the KLS large-core condition
at the concrete error above; no phase-local analytic premise remains. -/
theorem figureOneProposalRadius_le_accuracyCoreErrorStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))) := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  let b : ℝ := Real.sqrt ((q.n : ℝ) * L)
  let d : ℝ := Real.sqrt
    ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hcore16 := accuracyCoreError_le_one_div_sixteen q
  have hratio : 1 < (q.n : ℝ) / accuracyCoreError q := by
    rw [lt_div_iff₀ (accuracyCoreError_pos q)]
    have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    nlinarith
  have hlog0 : 0 < Real.log ((q.n : ℝ) / accuracyCoreError q) :=
    Real.log_pos hratio
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hlog := log_n_div_accuracyCoreError_le q
  change Real.log ((q.n : ℝ) / accuracyCoreError q) ≤ 130 * L at hlog
  have hsq : d ^ 2 ≤ (16 * b) ^ 2 := by
    have hbSq : b ^ 2 = (q.n : ℝ) * L := by
      dsimp [b]
      rw [Real.sq_sqrt]
      positivity
    have hdSq : d ^ 2 = (q.n : ℝ) *
        Real.log ((q.n : ℝ) / accuracyCoreError q) := by
      dsimp [d]
      rw [Real.sq_sqrt]
      positivity
    rw [hdSq, mul_pow, hbSq]
    norm_num
    have := mul_le_mul_of_nonneg_left hlog hn0.le
    nlinarith
  have hdb : d ≤ 16 * b := by
    nlinarith [Real.sqrt_nonneg
      ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))]
  unfold figureOneProposalRadius
  change min (Real.sqrt sigma2) 1 / (4096 * b) ≤ 1 / (8 * d)
  calc
    min (Real.sqrt sigma2) 1 / (4096 * b) ≤ 1 / (4096 * b) := by
      gcongr
      exact min_le_right _ _
    _ ≤ 1 / (8 * d) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith

/-- Uniform constant mass of the homothetic KLS core under every accuracy
phase's speedy stationary law. -/
theorem accuracyPhase_speedy_core_mass
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ENNReal.ofReal (7 / 16 : ℝ) ≤
      Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
        (accuracyScaleFactor q • accuracyPhaseTruncatedBody q I sigma2) := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let c := accuracyScaleFactor q
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hKmeas : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hKconv : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKcompact : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ := accuracyPhaseTruncatedBody_volume_ne_top q I sigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero hKmeas hKconv
      hKcompact.isBounded hK0 hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  by_cases hsmall : accuracyPhaseRadius q sigma2 ≤ 1
  · have hhalf :=
      Arlib.MarkovChains.half_le_ellGaussianProb_standardCore_radius_cv18
        hn hKmeas hKconv (accuracyPhaseInradius_pos q hsigma2)
        (ball_accuracyPhaseInradius_subset q I sigma2) hdelta
        (figureOneProposalRadius_le_accuracyPhaseCoreStep q hsigma2 hsmall)
        hsigma2 hmass0 hmasstop
    exact (by norm_num : ENNReal.ofReal (7 / 16 : ℝ) ≤
      ENNReal.ofReal (1 / 2 : ℝ)).trans (by simpa [K, delta, c,
        accuracyScaleFactor] using hhalf)
  · have hlarge : 1 ≤ accuracyPhaseRadius q sigma2 := le_of_not_ge hsmall
    have hunit : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
      intro x hx
      refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
      · simpa [unitBall] using hx
      · rw [Metric.mem_closedBall, dist_zero_right]
        have hx1 : ‖x‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx
        exact hx1.trans hlarge
    have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
    have hc1 : c < 1 := by
      dsimp [c, accuracyScaleFactor]
      have : 0 < 1 / (2 * (q.n : ℝ)) := by positivity
      linarith
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
          (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K) (c • K) ≠ 0 := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _ hcoreVol0
    have hgaussCoretop :
        (((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K) (c • K) ≠ ⊤ := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_top hsigma2
        hcoreM hcoreVoltop
    have hpaper := Arlib.MarkovChains.standardCore_defect_and_speedyMass_cv18
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
    simpa [K, delta, c, accuracyScaleFactor, Real.sq_sqrt hsigma2.le] using hpaper.2

/-- After the advertised mixing block, the homothetic core has nonzero mass.
This discharges the normalization guard of the executable rejection sampler. -/
theorem accuracyPhase_iterate_core_ne_zero
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    (Arlib.MarkovChains.iterate
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)) mu0 t)
      (accuracyScaleFactor q • accuracyPhaseTruncatedBody q I sigma2) ≠ 0 := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hmixPhase := mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht
  have hmix : Arlib.TVLe mu pi (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, mu, pi, P, K, delta] using hmixPhase
  have hcoreM : MeasurableSet
      (accuracyScaleFactor q • accuracyPhaseTruncatedBody q I sigma2) :=
    ((isClosedMap_smul_of_ne_zero (accuracyScaleFactor_pos q).ne')
      (accuracyPhaseTruncatedBody q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isClosed).measurableSet
  have hmass := accuracyPhase_speedy_core_mass q I hsigma2
  intro hzero
  have hupper := hmix.right hcoreM
  change pi (accuracyScaleFactor q • K) ≤
      mu (accuracyScaleFactor q • K) + ENNReal.ofReal mixError at hupper
  rw [hzero, zero_add] at hupper
  have herr : ENNReal.ofReal mixError ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
    ENNReal.ofReal_le_ofReal hmixError64
  have : ENNReal.ofReal (7 / 16 : ℝ) ≤
      ENNReal.ofReal (1 / 64 : ℝ) := hmass.trans (hupper.trans herr)
  norm_num at this

set_option maxHeartbeats 800000 in
/-- The complete KLS phase sampler with all geometric and core-error choices
discharged.  This combines the small- and large-radius branches and leaves
only the ordinary warm-start and walk-length inputs. -/
theorem accuracyPhaseSampleToGaussian_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError +
        32 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  by_cases hsmall : accuracyPhaseRadius q sigma2 ≤ 1
  · have h := accuracyPhaseSampleToGaussian_smallRadius_cv18 q I hsigma2
      hsmall hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht
    apply h.mono
    gcongr
    exact le_self_add
  · have hlarge : 1 ≤ accuracyPhaseRadius q sigma2 := le_of_not_ge hsmall
    have hcore0 := accuracyCoreError_pos q
    have hcore16 := accuracyCoreError_le_one_div_sixteen q
    have hcombinedReal :
        8 * mixError + 4 * accuracyCoreError q ≤ (1 : ℝ) / 4 := by
      nlinarith [accuracyCoreError_le_one_div_sixty_four q]
    have hcombined :
        8 * ENNReal.ofReal mixError +
          4 * ENNReal.ofReal (accuracyCoreError q) ≤
            ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 8 * mixError)
          (by positivity : 0 ≤ 4 * accuracyCoreError q)]
      exact ENNReal.ofReal_le_ofReal hcombinedReal
    exact accuracyPhaseSampleToGaussian_largeRadius_cv18 q I hsigma2
      hlarge hcore0 hcore16
      (figureOneProposalRadius_le_accuracyCoreErrorStep q hsigma2)
      hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht hcombined

end ArlibCommunity.Algorithms.CV18
