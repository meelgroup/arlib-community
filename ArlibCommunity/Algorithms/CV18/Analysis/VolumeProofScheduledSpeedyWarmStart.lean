/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperExpectedCost

/-! # Warm starts for successive scheduled speedy phases

This is the scheduled-body analogue of `VolumeProofSpeedyWarmStart`.  The
accuracy logarithm is independent of the phase variance, so the original
adjacent-radius argument carries over verbatim.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

theorem figureOneScheduledPhaseRadius_mono (q : VolumeParams) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    figureOneScheduledPhaseRadius q s ≤ figureOneScheduledPhaseRadius q t := by
  unfold figureOneScheduledPhaseRadius
  gcongr

theorem figureOneScheduledPhaseBody_mono
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    figureOneScheduledPhaseBody q I s ⊆ figureOneScheduledPhaseBody q I t := by
  intro x hx
  exact ⟨hx.1, Metric.closedBall_subset_closedBall
    (figureOneScheduledPhaseRadius_mono q hs hst) hx.2⟩

theorem figureOneScheduledProposalRadius_mono
    (q : VolumeParams) {s t : ℝ} (hst : s ≤ t) :
    figureOneScheduledProposalRadius q s ≤
      figureOneScheduledProposalRadius q t := by
  unfold figureOneScheduledProposalRadius
  apply div_le_div_of_nonneg_right
  · exact min_le_min (Real.sqrt_le_sqrt hst) le_rfl
  · positivity

theorem figureOneScheduledProposalRadius_succ_le_fixedFactor_mul
    (q : VolumeParams) (k : ℕ) :
    figureOneScheduledProposalRadius q (scheduleValue q (k + 1)) ≤
      Real.sqrt (1 + 1 / (q.n : ℝ)) *
        figureOneScheduledProposalRadius q (scheduleValue q k) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  let D : ℝ :=
    4096 * Real.sqrt ((q.n : ℝ) * figureOneScheduledAccuracyLog q)
  have hD : 0 < D := by
    dsimp [D]
    positivity [figureOneScheduledAccuracyLog_one_le q]
  unfold figureOneScheduledProposalRadius
  change min (Real.sqrt t) 1 / D ≤
    Real.sqrt (1 + 1 / (q.n : ℝ)) * (min (Real.sqrt s) 1 / D)
  apply (div_le_iff₀ hD).2
  rw [mul_assoc, div_mul_cancel₀ _ hD.ne']
  by_cases hsone : 1 ≤ s
  · have htone : 1 ≤ t := hsone.trans hst
    rw [min_eq_right (Real.one_le_sqrt.mpr hsone),
      min_eq_right (Real.one_le_sqrt.mpr htone)]
    simpa using Real.one_le_sqrt.mpr
      (show (1 : ℝ) ≤ 1 + 1 / (q.n : ℝ) by positivity)
  · have hslt : s < 1 := lt_of_not_ge hsone
    have htbound : t ≤ s * (1 + 1 / (q.n : ℝ)) := by
      rw [show t = nextVariance q s by
        simpa [s, t] using scheduleValue_succ q k]
      unfold nextVariance coolingRate
      rw [if_pos hslt.le]
      exact min_le_right _ _
    have hsqrt_s_le : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hslt.le
    rw [min_eq_left hsqrt_s_le]
    calc
      min (Real.sqrt t) 1 ≤ Real.sqrt t := min_le_left _ _
      _ ≤ Real.sqrt (s * (1 + 1 / (q.n : ℝ))) := Real.sqrt_le_sqrt htbound
      _ = Real.sqrt s * Real.sqrt (1 + 1 / (q.n : ℝ)) := by
        rw [Real.sqrt_mul hs.le]
      _ = Real.sqrt (1 + 1 / (q.n : ℝ)) * Real.sqrt s := mul_comm _ _

theorem figureOneScheduledProposalRadius_succ_ratio_pow_le_expHalf
    (q : VolumeParams) (k : ℕ) :
    (figureOneScheduledProposalRadius q (scheduleValue q (k + 1)) /
        figureOneScheduledProposalRadius q (scheduleValue q k)) ^ q.n ≤
      Real.exp (1 / 2) := by
  have hratio :
      figureOneScheduledProposalRadius q (scheduleValue q (k + 1)) /
          figureOneScheduledProposalRadius q (scheduleValue q k) ≤
        Real.sqrt (1 + 1 / (q.n : ℝ)) := by
    exact (div_le_iff₀
      (figureOneScheduledProposalRadius_pos q (scheduleValue_pos q k))).2
      (by simpa [mul_comm] using
        figureOneScheduledProposalRadius_succ_le_fixedFactor_mul q k)
  have hratio0 : 0 ≤
      figureOneScheduledProposalRadius q (scheduleValue q (k + 1)) /
        figureOneScheduledProposalRadius q (scheduleValue q k) :=
    div_nonneg
      (figureOneScheduledProposalRadius_pos q (scheduleValue_pos q (k + 1))).le
      (figureOneScheduledProposalRadius_pos q (scheduleValue_pos q k)).le
  exact (pow_le_pow_left₀ hratio0 hratio q.n).trans
    (fixedRate_sqrt_factor_le q.n
      (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok))

theorem scheduledPhase_ell_adjacent_le_expHalf
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (x : AmbientSpace q.n) :
    ell (figureOneScheduledPhaseBody q I (scheduleValue q k))
        (figureOneScheduledProposalRadius q (scheduleValue q k)) x ≤
      ENNReal.ofReal (Real.exp (1 / 2)) *
        ell (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
          (figureOneScheduledProposalRadius q (scheduleValue q (k + 1))) x := by
  have hs := scheduleValue_pos q k
  have ht := scheduleValue_pos q (k + 1)
  have hst := scheduleValue_mono q (Nat.le_add_right k 1)
  refine (ell_le_radiusRatioPow_of_subset
    (figureOneScheduledProposalRadius_pos q hs)
    (figureOneScheduledProposalRadius_pos q ht)
    (figureOneScheduledPhaseBody_mono q I hs.le hst)
    (figureOneScheduledProposalRadius_mono q hst) x).trans ?_
  exact mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (figureOneScheduledProposalRadius_succ_ratio_pow_le_expHalf q k)) le_rfl

theorem scheduledPhase_ellGaussianMeasure_adjacent_le_expHalf
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    ellGaussianMeasure
        (figureOneScheduledPhaseBody q I (scheduleValue q k))
        (figureOneScheduledProposalRadius q (scheduleValue q k))
        (scheduleValue q k) ≤
      ENNReal.ofReal (Real.exp (1 / 2)) •
        ellGaussianMeasure
          (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
          (figureOneScheduledProposalRadius q (scheduleValue q (k + 1)))
          (scheduleValue q (k + 1)) := by
  have hs := scheduleValue_pos q k
  have hst := scheduleValue_mono q (Nat.le_add_right k 1)
  apply ellGaussianMeasure_le_smul_of_subset
    (figureOneScheduledPhaseBody_measurable q I (scheduleValue q k))
    (figureOneScheduledPhaseBody_measurable q I (scheduleValue q (k + 1)))
    (figureOneScheduledPhaseBody_mono q I hs.le hst)
  intro x hx
  calc
    ell (figureOneScheduledPhaseBody q I (scheduleValue q k))
          (figureOneScheduledProposalRadius q (scheduleValue q k)) x *
        gaussianWeight (scheduleValue q k) x ≤
      (ENNReal.ofReal (Real.exp (1 / 2)) *
        ell (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
          (figureOneScheduledProposalRadius q (scheduleValue q (k + 1))) x) *
        gaussianWeight (scheduleValue q k) x := by
      exact mul_le_mul' (scheduledPhase_ell_adjacent_le_expHalf q I k x) le_rfl
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) *
        (ell (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
          (figureOneScheduledProposalRadius q (scheduleValue q (k + 1))) x *
          gaussianWeight (scheduleValue q (k + 1)) x) := by
      rw [mul_assoc]
      apply mul_le_mul' le_rfl
      exact mul_le_mul' le_rfl
        (gaussianWeight_mono_variance_cv18 hs hst x)

theorem scheduledPhase_full_gaussianIntegral_le_two_core
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    gaussianIntegral (truncatedBody q I) sigma2 ≤
      2 * gaussianIntegral (figureOneScheduledPhaseBody q I sigma2) sigma2 := by
  let K : Set (AmbientSpace q.n) := truncatedBody q I
  let B : Set (AmbientSpace q.n) :=
    Metric.closedBall 0 (figureOneScheduledPhaseRadius q sigma2)
  let full : ℝ := gaussianIntegral K sigma2
  let core : ℝ := gaussianIntegral (K ∩ B) sigma2
  let tail : ℝ := ∫ x in K \ B, gaussianDensity sigma2 x
  let nu : ℝ := figureOneScheduledRadialError q
  have hf := integrable_gaussianDensity (n := q.n) hsigma2
  have hdecomp : core + tail = full := by
    dsimp [core, tail, full]
    rw [gaussianIntegral_eq_setIntegral (truncatedBody_measurable q I),
      gaussianIntegral_eq_setIntegral
        ((truncatedBody_measurable q I).inter measurableSet_closedBall)]
    exact integral_inter_add_sdiff measurableSet_closedBall hf.integrableOn
  have htail : tail ≤ nu * full := by
    simpa [tail, nu, full, K, B] using
      figureOneScheduled_gaussianIntegral_tail_le q I hsigma2
  have hnu : nu ≤ 1 / 2 := by
    dsimp [nu]
    unfold figureOneScheduledRadialError
    nlinarith [figureOnePerSampleMixingError_le_one q]
  have hfull0 : 0 ≤ full := by
    dsimp [full]
    rw [gaussianIntegral_eq_setIntegral (truncatedBody_measurable q I)]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  dsimp [core, K, B] at *
  unfold figureOneScheduledPhaseBody
  nlinarith

theorem scheduledPhase_ellGaussianMass_adjacent_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    ellGaussianMeasure
        (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
        (figureOneScheduledProposalRadius q (scheduleValue q (k + 1)))
        (scheduleValue q (k + 1)) Set.univ ≤
      (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) *
        ellGaussianMeasure
          (figureOneScheduledPhaseBody q I (scheduleValue q k))
          (figureOneScheduledProposalRadius q (scheduleValue q k))
          (scheduleValue q k) Set.univ := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let Ks := figureOneScheduledPhaseBody q I s
  let Kt := figureOneScheduledPhaseBody q I t
  let ds := figureOneScheduledProposalRadius q s
  let dt := figureOneScheduledProposalRadius q t
  let Gs : ENNReal := ∫⁻ x in Ks, gaussianWeight s x
  let Gt : ENNReal := ∫⁻ x in Kt, gaussianWeight t x
  let Fs : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight s x
  let Ft : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight t x
  let zs : ENNReal := ellGaussianMeasure Ks ds s Set.univ
  let zt : ENNReal := ellGaussianMeasure Kt dt t Set.univ
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hGtFt : Gt ≤ Ft := by
    dsimp [Gt, Ft, Kt]
    exact lintegral_mono_set fun _ hx => hx.1
  have hFtFs : Ft ≤ ENNReal.ofReal (Real.exp (1 / 2)) * Fs := by
    rw [show Ft = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) t) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) ht]
    rw [show Fs = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hs]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [s, t] using gaussianIntegral_adjacent_le_expHalf q I k)
  have hFsGs : Fs ≤ ENNReal.ofReal 2 * Gs := by
    rw [show Fs = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hs]
    rw [show Gs = ENNReal.ofReal (gaussianIntegral Ks s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (by dsimp [Ks]; exact figureOneScheduledPhaseBody_measurable q I s) hs]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [s, Ks] using scheduledPhase_full_gaussianIntegral_le_two_core q I hs)
  have hztGt : zt ≤ Gt := by
    dsimp [zt, Gt]
    exact ellGaussianMeasure_univ_le_gaussianMass dt t
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * Gs ≤ zs := by
    simpa [s, Ks, ds, Gs, zs] using
      half_mul_gaussianWeight_le_scheduledPhaseEllGaussian q I hs
  have hGsZs : Gs ≤ ENNReal.ofReal 2 * zs := by
    calc
      Gs = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2 : ℝ) * Gs) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal 2 * zs := mul_le_mul' le_rfl hhalf
  change zt ≤ (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) * zs
  calc
    zt ≤ Gt := hztGt
    _ ≤ Ft := hGtFt
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * Fs := hFtFs
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * (ENNReal.ofReal 2 * Gs) :=
      mul_le_mul' le_rfl hFsGs
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) *
        (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * zs)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hGsZs)
    _ = (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) * zs := by
      have hfour : ENNReal.ofReal 2 * ENNReal.ofReal 2 = ENNReal.ofReal 4 := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [← hfour]
      ac_rfl

/-- Consecutive scheduled speedy stationary laws satisfy the same universal
warm-start bound as the original fixed-accuracy phase bodies. -/
theorem scheduledPhase_speedyStationary_adjacent_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    IsWarm (ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q k))
        (figureOneScheduledProposalRadius q (scheduleValue q k))
        (scheduleValue q k))
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q (k + 1)))
        (figureOneScheduledProposalRadius q (scheduleValue q (k + 1)))
        (scheduleValue q (k + 1))) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let Ks := figureOneScheduledPhaseBody q I s
  let Kt := figureOneScheduledPhaseBody q I t
  let ds := figureOneScheduledProposalRadius q s
  let dt := figureOneScheduledProposalRadius q t
  let mus := ellGaussianMeasure Ks ds s
  let muNext := ellGaussianMeasure Kt dt t
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hds : 0 < ds := figureOneScheduledProposalRadius_pos q hs
  have hdt : 0 < dt := figureOneScheduledProposalRadius_pos q ht
  have hmus0 : mus Set.univ ≠ 0 := by
    dsimp [mus]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I s)
      (figureOneScheduledPhaseBody_convex q I s)
      (figureOneScheduledPhaseBody_isCompact q I s).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hs) hds s
  have hmut0 : muNext Set.univ ≠ 0 := by
    dsimp [muNext]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I t)
      (figureOneScheduledPhaseBody_convex q I t)
      (figureOneScheduledPhaseBody_isCompact q I t).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I ht) hdt t
  have hmusto : mus Set.univ ≠ ⊤ := by
    dsimp [mus]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I s) ds hs
  have hmutto : muNext Set.univ ≠ ⊤ := by
    dsimp [muNext]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I t) dt ht
  have hdom : mus ≤ ENNReal.ofReal (Real.exp (1 / 2)) • muNext := by
    simpa [mus, muNext, Ks, Kt, ds, dt, s, t] using
      scheduledPhase_ellGaussianMeasure_adjacent_le_expHalf q I k
  have hmass : muNext Set.univ ≤
      (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) *
        mus Set.univ := by
    simpa [mus, muNext, Ks, Kt, ds, dt, s, t] using
      scheduledPhase_ellGaussianMass_adjacent_le q I k
  have hw := isWarm_normalize_of_le_smul
    hmus0 hmusto hmut0 hmutto hdom hmass
  change IsWarm (ENNReal.ofReal (speedyAdjacentWarmConstant q))
    ((mus Set.univ)⁻¹ • mus) ((muNext Set.univ)⁻¹ • muNext)
  convert hw using 1
  unfold speedyAdjacentWarmConstant
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

#print axioms scheduledPhase_ellGaussianMeasure_adjacent_le_expHalf
#print axioms scheduledPhase_ellGaussianMass_adjacent_le
#print axioms scheduledPhase_speedyStationary_adjacent_isWarm

end ArlibCommunity.Algorithms.CV18
