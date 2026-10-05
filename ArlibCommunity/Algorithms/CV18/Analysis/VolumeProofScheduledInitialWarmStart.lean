/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetainedWarm

/-! # Initial warm start for the schedule-targeted speedy body

The schedule-targeted radial cutoff is at least the former accuracy cutoff,
while its proposal radius is smaller.  Thus the same centered-inball argument
used at the first CV18 cooling phase gives a warm good part for the actual
scheduled speedy stationary law.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

theorem figureOnePerSampleMixingError_le_eps
    (q : VolumeParams) : figureOnePerSampleMixingError q ≤ q.eps := by
  have ha : (1 : ℝ) ≤ figureOneDependentAlpha q :=
    figureOneDependentAlpha_one_le q
  have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hden1 : 1 ≤
      4096 * figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ) := by
    have ha4 : 1 ≤ figureOneDependentAlpha q ^ 4 := one_le_pow₀ ha
    nlinarith
  have hden2 : 1 ≤
      3 * (figureOneDependentMaxSampleCount q : ℝ) *
        (figureOneDependentPhaseCount q : ℝ) := by
    nlinarith
  have he2 : q.eps ^ 2 ≤ q.eps := by
    nlinarith [q.heps.1, q.heps.2]
  unfold figureOnePerSampleMixingError figureOneDependentEpsilon
  calc
    q.eps ^ 2 /
          (4096 * figureOneDependentAlpha q ^ 4 *
            (figureOneDependentPhaseCount q : ℝ)) /
        (3 * (figureOneDependentMaxSampleCount q : ℝ) *
          (figureOneDependentPhaseCount q : ℝ))
        ≤ q.eps ^ 2 /
          (4096 * figureOneDependentAlpha q ^ 4 *
            (figureOneDependentPhaseCount q : ℝ)) :=
      div_le_self (div_nonneg (sq_nonneg q.eps) (by positivity)) hden2
    _ ≤ q.eps ^ 2 := div_le_self (sq_nonneg q.eps) hden1
    _ ≤ q.eps := he2

theorem protectedLog_dimension_eps_le_scheduledAccuracyLog
    (q : VolumeParams) :
    protectedLog ((q.n : ℝ) / q.eps) ≤
      figureOneScheduledAccuracyLog q := by
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hcore : figureOneScheduledCoreError q ≤ q.eps := by
    unfold figureOneScheduledCoreError
    calc
      figureOnePerSampleMixingError q / 768 ≤
          figureOnePerSampleMixingError q := by
        apply div_le_self (figureOnePerSampleMixingError_pos q).le
        norm_num
      _ ≤ q.eps := figureOnePerSampleMixingError_le_eps q
  have hratio : (q.n : ℝ) / q.eps ≤
      (q.n : ℝ) / figureOneScheduledCoreError q := by
    exact div_le_div_of_nonneg_left hn.le
      (figureOneScheduledCoreError_pos q) hcore
  have hlog : protectedLog ((q.n : ℝ) / q.eps) ≤
      protectedLog ((q.n : ℝ) / figureOneScheduledCoreError q) := by
    unfold protectedLog
    exact max_le_max le_rfl (Real.log_le_log
      (by positivity [q.heps.1]) hratio)
  exact hlog.trans (le_max_left _ _)

theorem accuracyPhaseRadius_le_scheduledPhaseRadius
    (q : VolumeParams) (sigma2 : ℝ) :
    accuracyPhaseRadius q sigma2 ≤
      figureOneScheduledPhaseRadius q sigma2 := by
  unfold accuracyPhaseRadius figureOneScheduledPhaseRadius
  have hn : (0 : ℝ) ≤ q.n := Nat.cast_nonneg q.n
  have hlog := protectedLog_dimension_eps_le_scheduledAccuracyLog q
  gcongr

theorem accuracyPhaseInradius_le_scheduledPhaseInradius
    (q : VolumeParams) (sigma2 : ℝ) :
    accuracyPhaseInradius q sigma2 ≤
      figureOneScheduledPhaseInradius q sigma2 := by
  unfold accuracyPhaseInradius figureOneScheduledPhaseInradius
  exact min_le_min le_rfl (accuracyPhaseRadius_le_scheduledPhaseRadius q sigma2)

theorem figureOneScheduledProposalRadius_le_scheduledPhaseInradius
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneScheduledProposalRadius q sigma2 ≤
      figureOneScheduledPhaseInradius q sigma2 := by
  by_cases hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1
  · have hstep := figureOneScheduledProposalRadius_le_inradiusStep
      q hsigma2 hsmall
    have hn : (1 : ℝ) ≤ 2 * q.n := by
      have hn' : (1 : ℝ) ≤ q.n := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
      nlinarith
    exact hstep.trans (div_le_self
      (figureOneScheduledPhaseInradius_pos q hsigma2).le hn)
  · have hrho : figureOneScheduledPhaseInradius q sigma2 = 1 := by
      unfold figureOneScheduledPhaseInradius
      rw [min_eq_left]
      exact le_of_not_ge hsmall
    rw [hrho]
    unfold figureOneScheduledProposalRadius
    have hb : 1 ≤ 4096 * Real.sqrt
        ((q.n : ℝ) * figureOneScheduledAccuracyLog q) := by
      have hn : (1 : ℝ) ≤ q.n := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
      have hL : 1 ≤ figureOneScheduledAccuracyLog q :=
        figureOneScheduledAccuracyLog_one_le q
      have hsqrt : 1 ≤ Real.sqrt
          ((q.n : ℝ) * figureOneScheduledAccuracyLog q) := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_le_sqrt
        nlinarith
      nlinarith
    exact (div_le_self (by positivity : 0 ≤ min (Real.sqrt sigma2) 1) hb).trans
      (min_le_right _ _)

/-- The initial truncated Gaussian loses at most one half of its mass when
restricted to the centered inball of the actual scheduled phase body. -/
theorem initialTruncatedGaussian_scheduledInball_compl_le_half
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
      (Metric.closedBall 0
        (figureOneScheduledPhaseInradius q (initialVariance q)))ᶜ ≤ 1 / 2 := by
  refine (measure_mono ?_).trans
    (initialTruncatedGaussian_accuracyInball_compl_le_half q I)
  exact compl_subset_compl.mpr fun x hx => by
    rw [Metric.mem_closedBall] at hx ⊢
    exact hx.trans (accuracyPhaseInradius_le_scheduledPhaseInradius
      q (initialVariance q))

theorem initialTruncatedGaussian_scheduledInball_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
      (Metric.closedBall 0
        (figureOneScheduledPhaseInradius q (initialVariance q)))ᶜ ≤
      ENNReal.ofReal (q.eps / 32) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16) := by
  refine (measure_mono ?_).trans
    (initialTruncatedGaussian_accuracyInball_compl_le q I)
  exact compl_subset_compl.mpr fun x hx => by
    rw [Metric.mem_closedBall] at hx ⊢
    exact hx.trans (accuracyPhaseInradius_le_scheduledPhaseInradius
      q (initialVariance q))

/-- The initial truncated Gaussian restricted to the scheduled centered
inball is pointwise dominated by the first scheduled speedy stationary law. -/
theorem initialTruncatedGaussian_scheduledInball_dom_speedy
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let good : Set (AmbientSpace q.n) :=
      Metric.closedBall 0
        (figureOneScheduledPhaseInradius q (initialVariance q))
    let pi : Measure (AmbientSpace q.n) :=
      ellGaussianProb
        (figureOneScheduledPhaseBody q I (initialVariance q))
        (figureOneScheduledProposalRadius q (initialVariance q))
        (initialVariance q)
    ∀ A, MeasurableSet A →
      sigma (A ∩ good) ≤ ENNReal.ofReal ((2 : ℝ) ^ q.n) * pi A := by
  dsimp only
  intro A hA
  let s := initialVariance q
  let K := figureOneScheduledPhaseBody q I s
  let good := Metric.closedBall (0 : AmbientSpace q.n)
    (figureOneScheduledPhaseInradius q s)
  let delta := figureOneScheduledProposalRadius q s
  let F : ENNReal := ENNReal.ofReal (gaussianIntegral (truncatedBody q I) s)
  let z : ENNReal := ellGaussianMeasure K delta s Set.univ
  let N : ENNReal := ∫⁻ x in A ∩ good, gaussianWeight s x
  let E : ENNReal := ellGaussianMeasure K delta s A
  let C : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ q.n)
  have hs : 0 < s := initialVariance_pos q
  have hgoodK : good ⊆ K := by
    intro x hx
    have hnorm : ‖x‖ ≤ figureOneScheduledPhaseInradius q s := by
      simpa [good, Metric.mem_closedBall, dist_zero_right] using hx
    exact ⟨unitBall_subset_truncatedBody q I (by
      rw [unitBall, Metric.mem_closedBall, dist_zero_right]
      exact hnorm.trans (min_le_left _ _)), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnorm.trans (min_le_right _ _)⟩
  have hzF : z ≤ F := by
    calc
      z ≤ ∫⁻ x in K, gaussianWeight s x :=
        ellGaussianMeasure_univ_le_gaussianMass delta s
      _ ≤ ∫⁻ x in truncatedBody q I, gaussianWeight s x :=
        lintegral_mono_set (fun _ hx => hx.1)
      _ = F := by
        dsimp [F]
        exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
          (truncatedBody_measurable q I) hs
  have hfloor : ∀ x ∈ good,
      ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) ≤ ell K delta x := by
    intro x hx
    exact ofReal_halfPow_le_ell_of_closedBall_subset
      (figureOneScheduledPhaseInradius_pos q hs)
      (figureOneScheduledProposalRadius_pos q hs)
      (figureOneScheduledProposalRadius_le_scheduledPhaseInradius q hs)
      (fun y hy => by
        have hnorm : ‖y‖ ≤ figureOneScheduledPhaseInradius q s := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hy
        exact ⟨unitBall_subset_truncatedBody q I (by
          rw [unitBall, Metric.mem_closedBall, dist_zero_right]
          exact hnorm.trans (min_le_left _ _)), by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hnorm.trans (min_le_right _ _)⟩) hx
  have hCtheta : C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) = 1 := by
    dsimp [C]
    rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q.n)]
    rw [← ENNReal.ofReal_one]
    congr 1
    rw [← mul_pow]
    norm_num
  have hNE : N ≤ C * E := by
    dsimp [N, E]
    rw [ellGaussianMeasure, withDensity_apply _ hA,
      Measure.restrict_restrict hA]
    have hmeasEll : Measurable fun x : AmbientSpace q.n =>
        ell K delta x * gaussianWeight s x :=
      measurable_ell_mul_gaussianWeight
        (by dsimp [K]; exact figureOneScheduledPhaseBody_measurable q I s)
        delta s
    rw [← lintegral_const_mul _ hmeasEll]
    calc
      (∫⁻ x in A ∩ good, gaussianWeight s x) ≤
          ∫⁻ x in A ∩ good, C * (ell K delta x * gaussianWeight s x) := by
        apply setLIntegral_mono'
        · exact hA.inter measurableSet_closedBall
        · intro x hx
          calc
            gaussianWeight s x = 1 * gaussianWeight s x := (one_mul _).symm
            _ = (C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n)) *
                gaussianWeight s x := by rw [hCtheta]
            _ ≤ C * (ell K delta x * gaussianWeight s x) := by
              rw [mul_assoc]
              exact mul_le_mul' le_rfl
                (mul_le_mul' (hfloor x hx.2) le_rfl)
      _ ≤ ∫⁻ x in A ∩ K,
          C * (ell K delta x * gaussianWeight s x) := by
        exact lintegral_mono_set (fun x hx => ⟨hx.1, hgoodK hx.2⟩)
  rw [truncatedGaussianProbability_apply q I hs
    (hA.inter measurableSet_closedBall)]
  have hweightEq : (fun x : AmbientSpace q.n =>
      ENNReal.ofReal (gaussianDensity s x)) = gaussianWeight s := by
    funext x
    simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]
  rw [show (A ∩ good) ∩ truncatedBody q I = A ∩ good by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, (hgoodK hx.2).1⟩]
  simp_rw [hweightEq]
  change F⁻¹ * N ≤ C * (z⁻¹ * E)
  calc
    F⁻¹ * N ≤ F⁻¹ * (C * E) := mul_le_mul' le_rfl hNE
    _ = C * (F⁻¹ * E) := by ac_rfl
    _ ≤ C * (z⁻¹ * E) := by
      exact mul_le_mul' le_rfl (mul_le_mul' (ENNReal.inv_le_inv.2 hzF) le_rfl)

/-- Conditioning away the initial scheduled-inball tail gives a probability
law warm for the first scheduled speedy phase. -/
theorem initialScheduledSpeedy_restrictOff_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let bad : Set (AmbientSpace q.n) :=
      (Metric.closedBall 0
        (figureOneScheduledPhaseInradius q (initialVariance q)))ᶜ
    IsWarm (ENNReal.ofReal (initialSpeedyWarmConstant q))
      (restrictOff sigma bad)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (initialVariance q))
        (figureOneScheduledProposalRadius q (initialVariance q))
        (initialVariance q)) := by
  dsimp only
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
  let good : Set (AmbientSpace q.n) :=
    Metric.closedBall 0
      (figureOneScheduledPhaseInradius q (initialVariance q))
  let bad : Set (AmbientSpace q.n) := goodᶜ
  let pi : Measure (AmbientSpace q.n) :=
    ellGaussianProb
      (figureOneScheduledPhaseBody q I (initialVariance q))
      (figureOneScheduledProposalRadius q (initialVariance q))
      (initialVariance q)
  have hbad : sigma bad ≤ 1 / 2 := by
    simpa [sigma, bad, good] using
      initialTruncatedGaussian_scheduledInball_compl_le_half q I
  have hdom : ∀ A : Set (AmbientSpace q.n), MeasurableSet A →
      sigma (A \ bad) ≤ ENNReal.ofReal ((2 : ℝ) ^ q.n) * pi A := by
    intro A hA
    have h := initialTruncatedGaussian_scheduledInball_dom_speedy q I A hA
    simpa [sigma, pi, bad, good, Set.diff_compl] using h
  have hw := isWarm_restrictOff (sigma := sigma) (pi := pi)
    (measurableSet_closedBall.compl) hbad hdom
  simpa [initialSpeedyWarmConstant, sigma, pi, bad, good,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using hw

/-- Exact exceptional-mass coupling for the first scheduled phase. -/
theorem initialScheduledSpeedy_restrictOff_tvLe
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let bad : Set (AmbientSpace q.n) :=
      (Metric.closedBall 0
        (figureOneScheduledPhaseInradius q (initialVariance q)))ᶜ
    TVLe (restrictOff sigma bad) sigma
      (ENNReal.ofReal (q.eps / 32) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  exact (tvLe_restrictOff measurableSet_closedBall.compl
    (initialTruncatedGaussian_scheduledInball_compl_le_half q I)).symm.mono
      (initialTruncatedGaussian_scheduledInball_compl_le q I)

/-! ## Constant-warm scaled start used by the executable

The actual first collector contracts its initial draw by `accuracyScaleFactor`.
The KLS accepted target is already close to the truncated Gaussian; after the
same contraction it supplies an `8`-warm good law.  This is the polynomial
warm start needed by both mixing and expected-cost bounds.
-/

private theorem initialContractedAcceptedTarget_isProbabilityMeasure_aux
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma2 := initialVariance q
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    IsProbabilityMeasure
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map contract) := by
  dsimp only
  let sigma2 := initialVariance q
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hsigma2 : 0 < sigma2 := initialVariance_pos q
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    have hsharp := scheduledBalancedAcceptedStateMeasure_mass_ge_one_sixteenth
      q I hsigma2
    exact (by norm_num : ENNReal.ofReal (7 / 128 : ℝ) ≤
      ENNReal.ofReal (1 / 16 : ℝ)).trans (by
        simpa [K, delta, pi] using hsharp)
  let _ : IsProbabilityMeasure
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi) :=
    scheduledBalancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi haccepted
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem initialScaledScheduled_leUpTo_contractedAcceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma2 := initialVariance q
    let sigma := (truncatedGaussianProbability q I sigma2
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (scheduledBalancedAccuracyGaussianAcceptedTargetLaw
      q I sigma2 pi).map contract
    MeasureLeUpTo (sigma.map contract) good
      (scheduledBalancedStationaryTargetError q) := by
  dsimp only
  have htv := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I (initialVariance_pos q)
  let _ : IsProbabilityMeasure
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I
        (initialVariance q)
        (ellGaussianProb
          (figureOneScheduledPhaseBody q I (initialVariance q))
          (figureOneScheduledProposalRadius q (initialVariance q))
          (initialVariance q))).map
            (fun x => accuracyScaleFactor q • x)) :=
    initialContractedAcceptedTarget_isProbabilityMeasure_aux q I
  exact MeasureLeUpTo.of_tvLe
    ((htv.map (by fun_prop : Measurable fun x : AmbientSpace q.n =>
      accuracyScaleFactor q • x)).symm)

theorem initialContractedAcceptedTarget_isWarm_eight
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma2 := initialVariance q
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    IsWarm 8
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map contract) pi := by
  dsimp only
  exact map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
    q I (initialVariance_pos q)

theorem initialContractedAcceptedTarget_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma2 := initialVariance q
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    IsProbabilityMeasure
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map contract) := by
  exact initialContractedAcceptedTarget_isProbabilityMeasure_aux q I

/-- Exact good/bad decomposition of the scaled initial law.  The good part is
a probability measure, is `8`-warm for phase zero, and the bad mass is only
the already-budgeted stationary-target correction. -/
theorem exists_initialScaledScheduled_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma2 := initialVariance q
    let sigma := (truncatedGaussianProbability q I sigma2
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (scheduledBalancedAccuracyGaussianAcceptedTargetLaw
      q I sigma2 pi).map contract
    ∃ bad : Measure (AmbientSpace q.n),
      IsProbabilityMeasure good ∧
      (sigma.map contract ≤ good + bad) ∧
      IsWarm 8 good pi ∧
      bad Set.univ ≤ scheduledBalancedStationaryTargetError q := by
  dsimp only
  have hmlu := initialScaledScheduled_leUpTo_contractedAcceptedTarget q I
  obtain ⟨bad, hle, hbad⟩ := hmlu
  exact ⟨bad,
    initialContractedAcceptedTarget_isProbabilityMeasure q I,
    hle, initialContractedAcceptedTarget_isWarm_eight q I, hbad⟩

#print axioms initialScheduledSpeedy_restrictOff_isWarm
#print axioms initialScheduledSpeedy_restrictOff_tvLe
#print axioms exists_initialScaledScheduled_good_bad

end ArlibCommunity.Algorithms.CV18
