/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.External.Kr25.Arlib.Convexity.ProductLocalization
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.BrascampLieb1D
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.Variance
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.IndicatorVariance

/-!
# Gaussian variance for an arbitrary one-dimensional log-concave profile

This is the analytic interface between the arbitrary profile returned by
`Arlib.exists_logConcave_profile_product_lt` and the moment argument in Gaussian cooling.
Unlike the exponential-needle integration-by-parts lemma in `GaussianCooling.Variance`, it makes
no differentiability or continuity assumption on the profile.
-/

open MeasureTheory Set intervalIntegral

namespace Arlib.GaussianCooling

/-- The unnormalized variance of `D(t) exp (-t² x/(2σ²))` on a bounded interval is at most
`σ²/x` times the square of its mass.

This is `Arlib.brascampLieb_oneDim` with Gaussian scale `σ/√x`, followed by the elementary
fact that the mean minimizes the second moment.  In particular, `D` need only be nonnegative and
log-concave on the interval; endpoint discontinuities cause no problem. -/
theorem logConcaveProfile_gaussian_variance
    {σ x a b : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hab : a ≤ b) {D : ℝ → ℝ}
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) :
    (∫ t in a..b, t ^ 2 * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))) *
          (∫ t in a..b, D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))) -
        (∫ t in a..b, t * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))) ) ^ 2
      ≤ (σ ^ 2 / x) *
        (∫ t in a..b, D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))) ^ 2 := by
  let τ : ℝ := σ / Real.sqrt x
  have hτ : 0 < τ := div_pos hσ (Real.sqrt_pos.2 hx)
  have hτsq : τ ^ 2 = σ ^ 2 / x := by
    dsimp only [τ]
    rw [div_pow, Real.sq_sqrt hx.le]
  let W : ℝ → ℝ := fun t ↦ D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))
  have hexp : ∀ t : ℝ,
      Real.exp (-(t - 0) ^ 2 / (2 * τ ^ 2)) =
        Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)) := by
    intro t
    congr 1
    rw [hτsq]
    field_simp [ne_of_gt hx, ne_of_gt hσ]
    ring
  have hWint : IntervalIntegrable W volume a b := by
    apply hDint.mul_continuousOn
    exact (by fun_prop : Continuous (fun t : ℝ ↦
      Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))).continuousOn
  have hBLint : IntervalIntegrable
      (fun t ↦ D t * Real.exp (-(t - 0) ^ 2 / (2 * τ ^ 2))) volume a b := by
    simpa only [hexp] using hWint
  obtain ⟨c, _hc, hBL⟩ :=
    Arlib.brascampLieb_oneDim hτ hab hD0 hDlc hBLint
  simp_rw [hexp] at hBL
  rw [hτsq] at hBL
  change (∫ t in a..b, (t - c) ^ 2 * W t) ≤
      (σ ^ 2 / x) * ∫ t in a..b, W t at hBL
  have hW0 : ∀ t ∈ Icc a b, 0 ≤ W t := by
    intro t ht
    exact mul_nonneg (hD0 t ht) (Real.exp_nonneg _)
  have hmass0 : 0 ≤ ∫ t in a..b, W t :=
    intervalIntegral.integral_nonneg hab hW0
  have hM0 : IntervalIntegrable W volume a b := hWint
  have hM1 : IntervalIntegrable (fun t ↦ t * W t) volume a b :=
    hWint.continuousOn_mul continuousOn_id
  have hM2 : IntervalIntegrable (fun t ↦ t ^ 2 * W t) volume a b :=
    hWint.continuousOn_mul (continuous_pow 2).continuousOn
  have hcenter :
      (∫ t in a..b, (t - c) ^ 2 * W t) =
        (∫ t in a..b, t ^ 2 * W t) -
          2 * c * (∫ t in a..b, t * W t) + c ^ 2 * (∫ t in a..b, W t) := by
    calc
      (∫ t in a..b, (t - c) ^ 2 * W t) =
          ∫ t in a..b, (t ^ 2 * W t - (2 * c) * (t * W t)) + c ^ 2 * W t := by
            apply intervalIntegral.integral_congr
            intro t _
            ring
      _ = (∫ t in a..b, t ^ 2 * W t) -
          2 * c * (∫ t in a..b, t * W t) + c ^ 2 * (∫ t in a..b, W t) := by
            rw [intervalIntegral.integral_add
              (hM2.sub (hM1.const_mul (2 * c))) (hM0.const_mul (c ^ 2)),
              intervalIntegral.integral_sub hM2 (hM1.const_mul (2 * c)),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hmul := mul_le_mul_of_nonneg_left hBL hmass0
  rw [hcenter] at hmul
  change
    (∫ t in a..b, t ^ 2 * W t) * (∫ t in a..b, W t) -
        (∫ t in a..b, t * W t) ^ 2 ≤
      (σ ^ 2 / x) * (∫ t in a..b, W t) ^ 2
  nlinarith [sq_nonneg ((∫ t in a..b, t * W t) - c * (∫ t in a..b, W t))]

/-! ## Profile moments and differentiation -/

/-- The `k`th moment of an arbitrary profile times the centered Gaussian at inverse-scale `x`. -/
noncomputable def profileJ (D : ℝ → ℝ) (σ a b : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in a..b, t ^ k * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))

variable {D : ℝ → ℝ} {σ a b R : ℝ}

lemma profileJ_intervalIntegrable (hDint : IntervalIntegrable D volume a b)
    (_hσ : σ ≠ 0) (k : ℕ) (x : ℝ) :
    IntervalIntegrable
      (fun t ↦ t ^ k * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))) volume a b := by
  have hc : Continuous (fun t : ℝ ↦ t ^ k * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))) := by
    fun_prop
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    hDint.mul_continuousOn hc.continuousOn

/-- Differentiation of arbitrary-profile Gaussian moments in the inverse-scale parameter. -/
theorem hasDerivAt_profileJ (_hab : a ≤ b) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : σ ≠ 0) (k : ℕ) (x₀ : ℝ) :
    HasDerivAt (profileJ D σ a b k)
      (-(1 / (2 * σ ^ 2)) * profileJ D σ a b (k + 2) x₀) x₀ := by
  have hσpos : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  let F : ℝ → ℝ → ℝ := fun x t ↦
    t ^ k * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))
  let F' : ℝ → ℝ → ℝ := fun x t ↦
    -(1 / (2 * σ ^ 2)) *
      (t ^ (k + 2) * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))))
  let bound : ℝ → ℝ := fun t ↦
    |D t| * ((1 / (2 * σ ^ 2)) *
      (|t| ^ (k + 2) * Real.exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2))))
  have hbound_cont : Continuous (fun t : ℝ ↦
      (1 / (2 * σ ^ 2)) *
        (|t| ^ (k + 2) * Real.exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2)))) := by
    fun_prop
  have hbound_int : IntervalIntegrable bound volume a b := by
    rw [show bound = fun t ↦ |D t| * ((1 / (2 * σ ^ 2)) *
        (|t| ^ (k + 2) * Real.exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2)))) by rfl]
    exact hDint.norm.mul_continuousOn hbound_cont.continuousOn
  have hFaes : ∀ x, AEStronglyMeasurable (F x) := by
    intro x
    exact ((continuous_pow k).aestronglyMeasurable.mul
      (hDaes.mul (by fun_prop : Continuous (fun t : ℝ ↦
        Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))).aestronglyMeasurable))
  have hF'aes : AEStronglyMeasurable (F' x₀) := by
    exact (continuous_const.aestronglyMeasurable.mul
      ((continuous_pow (k + 2)).aestronglyMeasurable.mul
        (hDaes.mul (by fun_prop : Continuous (fun t : ℝ ↦
          Real.exp (-(t ^ 2 * x₀) / (2 * σ ^ 2)))).aestronglyMeasurable)))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := a) (b := b) (F := F) (F' := F') (x₀ := x₀) (bound := bound)
    (μ := volume) (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x ↦ (hFaes x).mono_measure Measure.restrict_le_self)
    (profileJ_intervalIntegrable hDint hσ k x₀)
    (hF'aes.mono_measure Measure.restrict_le_self) ?_ hbound_int
    (Filter.Eventually.of_forall fun t _ x _ ↦ ?_)
  · change HasDerivAt (profileJ D σ a b k) _ x₀
    refine key.2.congr_deriv ?_
    rw [profileJ, intervalIntegral.integral_const_mul]
  · refine Filter.Eventually.of_forall fun t _ x hx ↦ ?_
    have hxb : |x| ≤ |x₀| + 1 := by
      have hd : |x - x₀| < 1 := by simpa [Real.dist_eq] using hx
      calc |x| = |x₀ + (x - x₀)| := by rw [add_sub_cancel]
        _ ≤ |x₀| + |x - x₀| := abs_add_le _ _
        _ ≤ |x₀| + 1 := by linarith
    have he : Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)) ≤
        Real.exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have : -(t ^ 2 * x) ≤ t ^ 2 * (|x₀| + 1) := by
        calc
          -(t ^ 2 * x) ≤ |t ^ 2 * x| := neg_le_abs _
          _ = t ^ 2 * |x| := by rw [abs_mul, abs_pow, sq_abs]
          _ ≤ t ^ 2 * (|x₀| + 1) := mul_le_mul_of_nonneg_left hxb (sq_nonneg t)
      exact (div_le_div_iff₀ hσpos hσpos).2 (by nlinarith)
    rw [Real.norm_eq_abs]
    dsimp only [F', bound]
    calc
      |-(1 / (2 * σ ^ 2)) *
          (t ^ (k + 2) * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))))| =
          |D t| * ((1 / (2 * σ ^ 2)) *
            (|t| ^ (k + 2) * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))) := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (Real.exp_nonneg _),
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * σ ^ 2))]
        ring
      _ ≤ |D t| * ((1 / (2 * σ ^ 2)) *
            (|t| ^ (k + 2) * Real.exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2)))) := by
        gcongr
  · dsimp only [F, F']
    have hlin : HasDerivAt (fun y : ℝ ↦ -(t ^ 2 * y)) (-(t ^ 2)) x := by
      simpa [neg_mul] using (hasDerivAt_id x).const_mul (-(t ^ 2))
    have he := (hlin.div_const (2 * σ ^ 2)).exp
    have hout := he.const_mul (t ^ k * D t)
    have hout' : HasDerivAt
        (fun y : ℝ ↦ t ^ k * (D t * Real.exp (-(t ^ 2 * y) / (2 * σ ^ 2))))
        (t ^ k * D t *
          (Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)) * (-(t ^ 2) / (2 * σ ^ 2)))) x := by
      simpa only [mul_assoc] using hout
    refine hout'.congr_deriv ?_
    rw [pow_add]
    field_simp

lemma profileJ_eq_setIntegral (hab : a ≤ b) (k : ℕ) (x : ℝ) :
    profileJ D σ a b k x =
      ∫ t, t ^ k * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))
        ∂(volume.restrict (Ioc a b)) := by
  rw [profileJ, intervalIntegral.integral_of_le hab]

/-- The bounded-support fourth-moment comparison, for an arbitrary profile. -/
theorem profileJ_sq_var_le (hab : a ≤ b) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b) (hσ : σ ≠ 0)
    (hR : ∀ t ∈ Ioc a b, |t| ≤ R) (x : ℝ) :
    profileJ D σ a b 4 x * profileJ D σ a b 0 x - (profileJ D σ a b 2 x) ^ 2 ≤
      4 * R ^ 2 *
        (profileJ D σ a b 2 x * profileJ D σ a b 0 x -
          (profileJ D σ a b 1 x) ^ 2) := by
  let W : ℝ → ℝ := fun t ↦ indicator (Icc a b) D t *
    Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))
  have hW0 : ∀ t, 0 ≤ W t := fun t ↦
    mul_nonneg (indicator_nonneg hD0 t) (Real.exp_nonneg _)
  have haeR : ∀ᵐ t ∂(volume.restrict (Ioc a b)), |t| ≤ R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hR t ht
  have hint : ∀ k : ℕ, Integrable (fun t ↦ t ^ k * W t)
      (volume.restrict (Ioc a b)) := by
    intro k
    have hi := profileJ_intervalIntegrable hDint hσ k x
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hi
    exact (hi.mono_set Ioc_subset_Icc_self).congr_fun
      (fun t ht ↦ by simp [W, indicator_of_mem (Ioc_subset_Icc_self ht)]) measurableSet_Ioc
  have key := sq_var_le (μ := volume.restrict (Ioc a b)) (M := R) (w := W)
    hW0 haeR hint
  have hk : ∀ k : ℕ, (∫ t, t ^ k * W t ∂(volume.restrict (Ioc a b))) =
      profileJ D σ a b k x := by
    intro k
    rw [profileJ_eq_setIntegral hab]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp [W, indicator_of_mem (Ioc_subset_Icc_self ht)]
  have h0 : (∫ t, W t ∂(volume.restrict (Ioc a b))) = profileJ D σ a b 0 x := by
    simpa using hk 0
  have h1 : (∫ t, t * W t ∂(volume.restrict (Ioc a b))) = profileJ D σ a b 1 x := by
    simpa using hk 1
  rw [h0, h1, hk 2, hk 4] at key
  exact key

/-- Brascamp–Lieb in the moment notation used by the generic cooling replay. -/
theorem profileJ_var_le (x : ℝ) (hσ : 0 < σ) (hx : 0 < x) (hab : a ≤ b)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) :
    profileJ D σ a b 2 x * profileJ D σ a b 0 x - (profileJ D σ a b 1 x) ^ 2 ≤
      (σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2 := by
  simpa only [profileJ, pow_zero, one_mul, pow_one] using
    logConcaveProfile_gaussian_variance hσ hx hab hD0 hDlc hDint

/-- The normalized second moment of an arbitrary-profile Gaussian weight. -/
noncomputable def profileV (D : ℝ → ℝ) (σ a b : ℝ) (x : ℝ) : ℝ :=
  profileJ D σ a b 2 x / profileJ D σ a b 0 x

theorem hasDerivAt_profileV (hab : a ≤ b) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : σ ≠ 0)
    (hJpos : ∀ x, 0 < profileJ D σ a b 0 x) (x : ℝ) :
    HasDerivAt (profileV D σ a b)
      ((1 / (2 * σ ^ 2)) *
        ((profileJ D σ a b 2 x) ^ 2 -
          profileJ D σ a b 0 x * profileJ D σ a b 4 x) /
            (profileJ D σ a b 0 x) ^ 2) x := by
  have h0 := hasDerivAt_profileJ hab hDint hDaes hσ 0 x
  have h2 := hasDerivAt_profileJ hab hDint hDaes hσ 2 x
  norm_num at h0 h2
  have hne := (hJpos x).ne'
  have hq := h2.div h0 hne
  refine hq.congr_deriv ?_
  have hσ2 : (2 : ℝ) * σ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Generic counterpart of paper Lemma 5.6. -/
theorem profileV_deriv_ge (hab : a ≤ b) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDlc : LogConcaveOn (Icc a b) D) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : 0 < σ)
    (hJpos : ∀ x, 0 < profileJ D σ a b 0 x)
    (hR : ∀ t ∈ Ioc a b, |t| ≤ R) {x : ℝ} (hx : 0 < x) :
    -(2 * R ^ 2 / x) ≤ deriv (profileV D σ a b) x := by
  have hd := hasDerivAt_profileV hab hDint hDaes hσ.ne' hJpos x
  rw [hd.deriv]
  have h1 := profileJ_sq_var_le hab hD0 hDint hσ.ne' hR x
  have h2 := profileJ_var_le x hσ hx hab hD0 hDlc hDint
  have h3 : profileJ D σ a b 4 x * profileJ D σ a b 0 x -
      (profileJ D σ a b 2 x) ^ 2 ≤
        4 * R ^ 2 * ((σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  rw [le_div_iff₀ (sq_pos_of_pos (hJpos x))]
  have h3' : profileJ D σ a b 4 x * profileJ D σ a b 0 x -
      (profileJ D σ a b 2 x) ^ 2 ≤
        (4 * R ^ 2 * σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2 := by
    calc
      _ ≤ 4 * R ^ 2 * ((σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2) := h3
      _ = _ := by field_simp
  have hstep : -(4 * R ^ 2 * σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2 ≤
      (profileJ D σ a b 2 x) ^ 2 -
        profileJ D σ a b 0 x * profileJ D σ a b 4 x := by nlinarith [h3']
  calc
    -(2 * R ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2 =
        1 / (2 * σ ^ 2) *
          (-(4 * R ^ 2 * σ ^ 2 / x) * (profileJ D σ a b 0 x) ^ 2) := by
            field_simp
            ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)

/-! ## The generic profile ratio -/

noncomputable def profileH (D : ℝ → ℝ) (σ a b : ℝ) (α : ℝ) : ℝ :=
  profileJ D σ a b 0 (1 + α) * profileJ D σ a b 0 (1 - α) /
    (profileJ D σ a b 0 1) ^ 2

lemma profileH_pos (hJpos : ∀ x, 0 < profileJ D σ a b 0 x) (α : ℝ) :
    0 < profileH D σ a b α :=
  div_pos (mul_pos (hJpos _) (hJpos _)) (pow_pos (hJpos _) 2)

lemma profileH_zero (hJpos : ∀ x, 0 < profileJ D σ a b 0 x) :
    profileH D σ a b 0 = 1 := by
  have h := (hJpos 1).ne'
  rw [profileH]
  norm_num
  rw [← pow_two]
  exact div_self (pow_ne_zero 2 h)

theorem hasDerivAt_profileH (hab : a ≤ b) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : σ ≠ 0)
    (hJpos : ∀ x, 0 < profileJ D σ a b 0 x) (α : ℝ) :
    HasDerivAt (profileH D σ a b)
      (1 / (2 * σ ^ 2) * profileH D σ a b α *
        (profileV D σ a b (1 - α) - profileV D σ a b (1 + α))) α := by
  have hA : HasDerivAt (fun z : ℝ ↦ profileJ D σ a b 0 (1 + z))
      (-(1 / (2 * σ ^ 2)) * profileJ D σ a b 2 (1 + α)) α := by
    have h := (hasDerivAt_profileJ hab hDint hDaes hσ 0 (1 + α)).comp α
      ((hasDerivAt_id α).const_add 1)
    norm_num at h ⊢
    exact h
  have hB : HasDerivAt (fun z : ℝ ↦ profileJ D σ a b 0 (1 - z))
      (1 / (2 * σ ^ 2) * profileJ D σ a b 2 (1 - α)) α := by
    have h := (hasDerivAt_profileJ hab hDint hDaes hσ 0 (1 - α)).comp α
      ((hasDerivAt_id α).const_sub 1)
    norm_num at h ⊢
    refine h.congr_deriv ?_
    ring
  have hp := (hA.mul hB).div_const ((profileJ D σ a b 0 1) ^ 2)
  refine hp.congr_deriv ?_
  have h1 := (hJpos (1 + α)).ne'
  have h2 := (hJpos (1 - α)).ne'
  have h3 := (hJpos 1).ne'
  simp only [profileH, profileV]
  field_simp
  ring

lemma monotoneOn_profileV_add_log (hab : a ≤ b)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) (hDaes : AEStronglyMeasurable D)
    (hσ : 0 < σ) (hJpos : ∀ x, 0 < profileJ D σ a b 0 x)
    (hR : ∀ t ∈ Ioc a b, |t| ≤ R) :
    MonotoneOn (fun x ↦ profileV D σ a b x + 2 * R ^ 2 * Real.log x)
      (Icc (1 / 2 : ℝ) (3 / 2)) := by
  have hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt
      (fun x ↦ profileV D σ a b x + 2 * R ^ 2 * Real.log x)
      (deriv (profileV D σ a b) x + 2 * R ^ 2 / x) x := by
    intro x hx
    have h1 := hasDerivAt_profileV hab hDint hDaes hσ.ne' hJpos x
    have h2 := (Real.hasDerivAt_log hx).const_mul (2 * R ^ 2)
    have h3 := h1.add h2
    rw [h1.deriv]
    refine h3.congr_deriv ?_
    field_simp
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact ((hd x hx0).differentiableAt).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact ((hd x hx0).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hd x hx0.ne').deriv]
    have hv := profileV_deriv_ge hab hD0 hDlc hDint hDaes hσ hJpos hR hx0
    linarith

theorem profileV_diff_le (hab : a ≤ b) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDlc : LogConcaveOn (Icc a b) D) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : 0 < σ)
    (hJpos : ∀ x, 0 < profileJ D σ a b 0 x)
    (hR : ∀ t ∈ Ioc a b, |t| ≤ R) {alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2) :
    profileV D σ a b (1 - alpha) - profileV D σ a b (1 + alpha) ≤
      8 * R ^ 2 * alpha := by
  have hm := monotoneOn_profileV_add_log hab hD0 hDlc hDint hDaes hσ hJpos hR
  have hmem1 : (1 - alpha) ∈ Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hmem2 : (1 + alpha) ∈ Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hle := hm hmem1 hmem2 (by linarith)
  have hlog : Real.log (1 + alpha) - Real.log (1 - alpha) =
      Real.log ((1 + alpha) / (1 - alpha)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hb := log_ratio_le halpha0 halpha
  have hmul : 2 * R ^ 2 * (Real.log (1 + alpha) - Real.log (1 - alpha)) ≤
      2 * R ^ 2 * (4 * alpha) := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  linarith

/-- The arbitrary-log-concave-profile version of paper Lemma 5.7. -/
theorem profileH_le_exp (hab : a ≤ b) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDlc : LogConcaveOn (Icc a b) D) (hDint : IntervalIntegrable D volume a b)
    (hDaes : AEStronglyMeasurable D) (hσ : 0 < σ)
    (hJpos : ∀ x, 0 < profileJ D σ a b 0 x)
    (hR : ∀ t ∈ Ioc a b, |t| ≤ R) {alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2) :
    profileH D σ a b alpha ≤ Real.exp (2 * R ^ 2 * alpha ^ 2 / σ ^ 2) := by
  let phi : ℝ → ℝ := fun z ↦ Real.log (profileH D σ a b z) -
    2 * R ^ 2 * z ^ 2 / σ ^ 2
  have hdphi : ∀ z, HasDerivAt phi
      (deriv (profileH D σ a b) z / profileH D σ a b z -
        4 * R ^ 2 * z / σ ^ 2) z := by
    intro z
    have h1 := hasDerivAt_profileH hab hDint hDaes hσ.ne' hJpos z
    have hl := h1.log (profileH_pos hJpos z).ne'
    have hq : HasDerivAt (fun z : ℝ ↦ 2 * R ^ 2 * z ^ 2 / σ ^ 2)
        (4 * R ^ 2 * z / σ ^ 2) z := by
      refine (((hasDerivAt_pow 2 z).const_mul (2 * R ^ 2)).div_const (σ ^ 2)).congr_deriv ?_
      ring
    have hs := hl.sub hq
    rw [h1.deriv]
    exact hs
  have hanti : AntitoneOn phi (Icc (0 : ℝ) (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun z _ ↦ ((hdphi z).differentiableAt).continuousAt.continuousWithinAt)
      (fun z _ ↦ ((hdphi z).differentiableAt).differentiableWithinAt) ?_
    intro z hz
    rw [interior_Icc] at hz
    rw [(hdphi z).deriv]
    have hv := profileV_diff_le hab hD0 hDlc hDint hDaes hσ hJpos hR hz.1.le hz.2.le
    have hh := hasDerivAt_profileH hab hDint hDaes hσ.ne' hJpos z
    have hp := profileH_pos hJpos z
    have hc : 0 < 1 / (2 * σ ^ 2) * profileH D σ a b z := by positivity
    have hder : deriv (profileH D σ a b) z ≤
        4 * R ^ 2 * z * profileH D σ a b z / σ ^ 2 := by
      rw [hh.deriv]
      calc
        1 / (2 * σ ^ 2) * profileH D σ a b z *
            (profileV D σ a b (1 - z) - profileV D σ a b (1 + z)) ≤
            1 / (2 * σ ^ 2) * profileH D σ a b z * (8 * R ^ 2 * z) :=
          mul_le_mul_of_nonneg_left hv hc.le
        _ = _ := by field_simp; ring
    have hdiv : deriv (profileH D σ a b) z / profileH D σ a b z ≤
        4 * R ^ 2 * z / σ ^ 2 := by
      rw [div_le_iff₀ hp]
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hder
    linarith
  have hphi0 : phi 0 = 0 := by
    simp [phi, profileH_zero hJpos]
  have hle : phi alpha ≤ 0 := by
    have h := hanti (left_mem_Icc.mpr (by norm_num)) ⟨halpha0, halpha⟩ halpha0
    rwa [hphi0] at h
  have hlog : Real.log (profileH D σ a b alpha) ≤
      2 * R ^ 2 * alpha ^ 2 / σ ^ 2 := by
    dsimp only [phi] at hle
    linarith
  exact (Real.log_le_iff_le_exp (profileH_pos hJpos alpha)).mp hlog

/-- Positivity of one zeroth Gaussian moment is equivalent to positivity of all of them: the
Gaussian factor never changes the support. -/
theorem profileJ_zero_pos_all (hD0 : ∀ t, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b) (hσ : σ ≠ 0) {x₀ : ℝ}
    (hpos : 0 < profileJ D σ a b 0 x₀) : ∀ x, 0 < profileJ D σ a b 0 x := by
  intro x
  have hi0 := profileJ_intervalIntegrable hDint hσ 0 x₀
  have hix := profileJ_intervalIntegrable hDint hσ 0 x
  have hn0 : ∀ᵐ t ∂volume,
      0 ≤ t ^ 0 * (D t * Real.exp (-(t ^ 2 * x₀) / (2 * σ ^ 2))) :=
    Filter.Eventually.of_forall fun t ↦ mul_nonneg (by positivity)
      (mul_nonneg (hD0 t) (Real.exp_nonneg _))
  have hnx : ∀ᵐ t ∂volume,
      0 ≤ t ^ 0 * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2))) :=
    Filter.Eventually.of_forall fun t ↦ mul_nonneg (by positivity)
      (mul_nonneg (hD0 t) (Real.exp_nonneg _))
  have hsupp : Function.support
      (fun t ↦ t ^ 0 * (D t * Real.exp (-(t ^ 2 * x₀) / (2 * σ ^ 2)))) =
      Function.support
      (fun t ↦ t ^ 0 * (D t * Real.exp (-(t ^ 2 * x) / (2 * σ ^ 2)))) := by
    ext t
    simp only [Function.mem_support, pow_zero, one_mul, ne_eq, mul_eq_zero,
      Real.exp_ne_zero, or_false]
  have hchar0 := (intervalIntegral.integral_pos_iff_support_of_nonneg_ae hn0 hi0).mp hpos
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae hnx hix).mpr
  rwa [← hsupp]

/-! ## Affine pushforward of a localization needle -/

/-- A Gaussian integral against an arbitrary localization profile and parameterization. -/
noncomputable def profileNeedleJ {n : ℕ} (D : ℝ → ℝ)
    (p e : EuclSpace n) (a b σ x : ℝ) : ℝ :=
  ∫ t in a..b, D t * Real.exp (-(‖needleMap p e t‖ ^ 2 * x) / (2 * σ ^ 2))

/-- **Affine pushforward package.**  A nondegenerate arbitrary parameterization is converted to
the unit-speed parameter `u = ⟨p,w⟩ + ‖e‖t`.  The pushed profile is the zero extension of
`D ((u-⟨p,w⟩)/‖e‖)`, hence remains globally measurable and log-concave.  All Gaussian
integrals acquire the same positive Jacobian and the expected orthogonal-offset factor. -/
theorem exists_normalized_logConcave_profile {n : ℕ} {p e : EuclSpace n} (he : e ≠ 0)
    {a b : ℝ} (hab : a ≤ b) {D : ℝ → ℝ}
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) :
    ∃ (q w : EuclSpace n) (A B : ℝ) (E : ℝ → ℝ) (c L : ℝ),
      0 < L ∧ inner ℝ q w = 0 ∧ ‖w‖ = 1 ∧ A ≤ B ∧
      (∀ u ∈ Icc A B, (u - c) / L ∈ Icc a b) ∧
      (∀ u ∈ Icc A B, needleMap q w u = needleMap p e ((u - c) / L)) ∧
      (∀ u, 0 ≤ E u) ∧ IsLogConcave E ∧ IntervalIntegrable E volume A B ∧
      (∀ (σ x : ℝ), σ ≠ 0 →
        profileNeedleJ D p e a b σ x =
          L⁻¹ * Real.exp (-(‖q‖ ^ 2 * x) / (2 * σ ^ 2)) * profileJ E σ A B 0 x) := by
  let L : ℝ := ‖e‖
  have hL : 0 < L := norm_pos_iff.mpr he
  let w : EuclSpace n := L⁻¹ • e
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_cancel₀ hL.ne']
  let c : ℝ := inner ℝ p w
  let q : EuclSpace n := p - c • w
  have hqw : inner ℝ q w = 0 := by
    dsimp only [q]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw]
    simp [c]
  have hew : e = L • w := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  let A := c + L * a
  let B := c + L * b
  have hAB : A ≤ B := by dsimp only [A, B]; nlinarith
  let Dc : ℝ → ℝ := indicator (Icc a b) D
  have hDclc : IsLogConcave Dc := Arlib.isLogConcave_indicator_of_logConcaveOn hDlc hD0
  have hDc0 : ∀ t, 0 ≤ Dc t := fun t ↦ indicator_nonneg hD0 t
  let E : ℝ → ℝ := fun u ↦ Dc (L⁻¹ * u + (-(L⁻¹ * c)))
  have hElc : IsLogConcave E := by
    exact hDclc.comp_smul_add L⁻¹ (-(L⁻¹ * c))
  have hE0 : ∀ u, 0 ≤ E u := fun u ↦ hDc0 _
  have hEeq : ∀ u ∈ Icc A B, E u = D ((u - c) / L) := by
    intro u hu
    have ht : (u - c) / L ∈ Icc a b := by
      dsimp only [A, B] at hu
      constructor
      · rw [le_div_iff₀ hL]
        nlinarith [hu.1]
      · rw [div_le_iff₀ hL]
        nlinarith [hu.2]
    have heqarg : L⁻¹ * u + (-(L⁻¹ * c)) = (u - c) / L := by
      field_simp
      ring
    dsimp only [E, Dc]
    rw [heqarg, indicator_of_mem ht]
  have hEint : IntervalIntegrable E volume A B := by
    have hscale := hDint.comp_mul_left (c := L⁻¹)
    have hshift := hscale.comp_sub_right c
    have hshift' : IntervalIntegrable (fun u ↦ D (L⁻¹ * (u - c))) volume A B := by
      convert hshift using 1 <;> simp only [A, B] <;> field_simp <;> ring
    apply hshift'.congr
    intro u hu
    have hu' : u ∈ Icc A B := by
      rw [uIoc_of_le hAB] at hu
      exact Ioc_subset_Icc_self hu
    rw [hEeq u hu']
    field_simp
  refine ⟨q, w, A, B, E, c, L, hL, hqw, hw, hAB, ?_, ?_, hE0, hElc, hEint, ?_⟩
  · intro u hu
    dsimp only [A, B] at hu
    constructor
    · rw [le_div_iff₀ hL]
      nlinarith [hu.1]
    · rw [div_le_iff₀ hL]
      nlinarith [hu.2]
  · intro u hu
    rw [needleMap_apply, needleMap_apply]
    dsimp only [q, w]
    field_simp
    module
  · intro sigma x hsigma
    have hgeom : ∀ t, needleMap p e t = needleMap q w (c + L * t) := by
      intro t
      rw [needleMap_apply, needleMap_apply, hew]
      dsimp only [q]
      module
    have hnorm : ∀ u, ‖needleMap q w u‖ ^ 2 = ‖q‖ ^ 2 + u ^ 2 :=
      fun u ↦ norm_add_smul_sq hqw hw u
    let F : ℝ → ℝ := fun u ↦
      E u * Real.exp (-(‖needleMap q w u‖ ^ 2 * x) / (2 * sigma ^ 2))
    have hcomp : ∀ t ∈ Icc a b,
        D t * Real.exp (-(‖needleMap p e t‖ ^ 2 * x) / (2 * sigma ^ 2)) =
          F (L * t + c) := by
      intro t ht
      have hu : L * t + c ∈ Icc A B := by
        dsimp only [A, B]
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hL.le,
          mul_le_mul_of_nonneg_left ht.2 hL.le]
      dsimp only [F]
      rw [hEeq _ hu]
      have htarg : ((L * t + c - c) / L) = t := by field_simp; ring
      rw [htarg, add_comm (L * t) c, ← hgeom t]
    rw [profileNeedleJ]
    have hchange : (∫ t in a..b,
        D t * Real.exp (-(‖needleMap p e t‖ ^ 2 * x) / (2 * sigma ^ 2))) =
        ∫ t in a..b, F (L * t + c) :=
      intervalIntegral.integral_congr fun t ht ↦ hcomp t (by simpa [uIcc_of_le hab] using ht)
    rw [hchange, intervalIntegral.integral_comp_mul_add (f := F) hL.ne' c]
    simp only [A, B, smul_eq_mul]
    have hfactor : (∫ u in c + L * a..c + L * b, F u) =
        Real.exp (-(‖q‖ ^ 2 * x) / (2 * sigma ^ 2)) *
          profileJ E sigma (c + L * a) (c + L * b) 0 x := by
      rw [profileJ, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [F]
      rw [hnorm]
      have hsplit : -((‖q‖ ^ 2 + u ^ 2) * x) / (2 * sigma ^ 2) =
          -(‖q‖ ^ 2 * x) / (2 * sigma ^ 2) + -(u ^ 2 * x) / (2 * sigma ^ 2) := by
        field_simp
        ring
      rw [hsplit, Real.exp_add]
      simp
      ring
    rw [show L * a + c = c + L * a by ring, show L * b + c = c + L * b by ring, hfactor]
    ring

/-- Every nondegenerate arbitrary-profile needle obeys the Gaussian cooling product bound. -/
theorem profileNeedle_product_le_of_ne_zero {n : ℕ} {p e : EuclSpace n} (he : e ≠ 0)
    {a b : ℝ} {D : ℝ → ℝ} {sigma alpha R : ℝ} (hab : a ≤ b)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) (hsigma : 0 < sigma)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2)
    (hR : ∀ t ∈ Icc a b, ‖needleMap p e t‖ ≤ R)
    (hpos : 0 < profileNeedleJ D p e a b sigma (1 + alpha)) :
    profileNeedleJ D p e a b sigma (1 + alpha) *
        profileNeedleJ D p e a b sigma (1 - alpha) ≤
      Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
        (profileNeedleJ D p e a b sigma 1) ^ 2 := by
  obtain ⟨q, w, A, B, E, c, L, hL, hqw, hw, hAB, hmem, hmap, hE0, hElc, hEint,
    hfactor⟩ := exists_normalized_logConcave_profile he hab hD0 hDlc hDint
  have hR' : ∀ u ∈ Ioc A B, |u| ≤ R := by
    intro u hu
    have hucc : u ∈ Icc A B := Ioc_subset_Icc_self hu
    have hr := hR ((u - c) / L) (hmem u hucc)
    rw [← hmap u hucc] at hr
    have hsquares : |u| ^ 2 ≤ ‖needleMap q w u‖ ^ 2 := by
      rw [needleMap_apply]
      rw [norm_add_smul_sq hqw hw u, sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg ‖q‖)
    exact ((sq_le_sq₀ (abs_nonneg u) (norm_nonneg _)).mp hsquares).trans hr
  have hfplus := hfactor sigma (1 + alpha) hsigma.ne'
  have hfminus := hfactor sigma (1 - alpha) hsigma.ne'
  have hfone := hfactor sigma 1 hsigma.ne'
  have hJsome : 0 < profileJ E sigma A B 0 (1 + alpha) := by
    rw [hfplus] at hpos
    rcases (mul_pos_iff.mp hpos) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (by positivity :
          0 ≤ L⁻¹ * Real.exp (- (‖q‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)))) h.1)
  have hJpos : ∀ x, 0 < profileJ E sigma A B 0 x :=
    profileJ_zero_pos_all hE0 hEint hsigma.ne' hJsome
  have hEa : AEStronglyMeasurable E :=
    (Arlib.measurable_of_isLogConcave hElc hE0).aestronglyMeasurable
  have hH := profileH_le_exp hAB (fun t _ ↦ hE0 t)
    (hElc.logConcaveOn (convex_Icc A B)) hEint hEa
    hsigma hJpos hR' halpha0 halpha
  have hJbound : profileJ E sigma A B 0 (1 + alpha) *
      profileJ E sigma A B 0 (1 - alpha) ≤
        Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
          (profileJ E sigma A B 0 1) ^ 2 := by
    rw [profileH, div_le_iff₀ (sq_pos_of_pos (hJpos 1))] at hH
    exact hH
  have hoff :
      Real.exp (- (‖q‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
          Real.exp (- (‖q‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) =
        (Real.exp (- (‖q‖ ^ 2 * 1) / (2 * sigma ^ 2))) ^ 2 := by
    let z : ℝ := -(‖q‖ ^ 2 * 1) / (2 * sigma ^ 2)
    calc
      _ = Real.exp
          (- (‖q‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2) +
            - (‖q‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) := (Real.exp_add _ _).symm
      _ = Real.exp (z + z) := by
        congr 1
        dsimp only [z]
        field_simp
        ring
      _ = Real.exp z * Real.exp z := Real.exp_add _ _
      _ = _ := by rw [pow_two]
  rw [hfplus, hfminus, hfone]
  calc
    (L⁻¹ * Real.exp (- (‖q‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
          profileJ E sigma A B 0 (1 + alpha)) *
        (L⁻¹ * Real.exp (- (‖q‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) *
          profileJ E sigma A B 0 (1 - alpha)) =
      (L⁻¹) ^ 2 * (Real.exp (- (‖q‖ ^ 2 * 1) / (2 * sigma ^ 2))) ^ 2 *
        (profileJ E sigma A B 0 (1 + alpha) * profileJ E sigma A B 0 (1 - alpha)) := by
          calc
            _ = (L⁻¹) ^ 2 *
                (Real.exp (- (‖q‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
                  Real.exp (- (‖q‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2))) *
                (profileJ E sigma A B 0 (1 + alpha) *
                  profileJ E sigma A B 0 (1 - alpha)) := by ring
            _ = _ := by rw [hoff]
    _ ≤ (L⁻¹) ^ 2 * (Real.exp (- (‖q‖ ^ 2 * 1) / (2 * sigma ^ 2))) ^ 2 *
        (Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
          (profileJ E sigma A B 0 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hJbound (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
        (L⁻¹ * Real.exp (- (‖q‖ ^ 2 * 1) / (2 * sigma ^ 2)) *
          profileJ E sigma A B 0 1) ^ 2 := by ring

/-- The same product bound, including the constant (`e = 0`) needle. -/
theorem profileNeedle_product_le {n : ℕ} {p e : EuclSpace n}
    {a b : ℝ} {D : ℝ → ℝ} {sigma alpha R : ℝ} (hab : a ≤ b)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDlc : LogConcaveOn (Icc a b) D)
    (hDint : IntervalIntegrable D volume a b) (hsigma : 0 < sigma)
    (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2)
    (hR : ∀ t ∈ Icc a b, ‖needleMap p e t‖ ≤ R)
    (hpos : 0 < profileNeedleJ D p e a b sigma (1 + alpha)) :
    profileNeedleJ D p e a b sigma (1 + alpha) *
        profileNeedleJ D p e a b sigma (1 - alpha) ≤
      Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
        (profileNeedleJ D p e a b sigma 1) ^ 2 := by
  by_cases he : e = 0
  · subst e
    have hconst : ∀ x : ℝ, profileNeedleJ D p 0 a b sigma x =
        Real.exp (- (‖p‖ ^ 2 * x) / (2 * sigma ^ 2)) * ∫ t in a..b, D t := by
      intro x
      rw [profileNeedleJ, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [needleMap_apply, smul_zero, add_zero]
      ring
    rw [hconst, hconst, hconst]
    have hoff :
        Real.exp (- (‖p‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
            Real.exp (- (‖p‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) =
          (Real.exp (- (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2))) ^ 2 := by
      calc
        _ = Real.exp
            (- (‖p‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2) +
              - (‖p‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) := (Real.exp_add _ _).symm
        _ = Real.exp
            (- (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2) +
              - (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2)) := by
                congr 1
                field_simp
                ring
        _ = Real.exp (- (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2)) *
            Real.exp (- (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2)) := Real.exp_add _ _
        _ = _ := (pow_two _).symm
    have hC : 1 ≤ Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) := by
      rw [Real.one_le_exp_iff]
      positivity
    rw [show (Real.exp (- (‖p‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
        (∫ t in a..b, D t)) *
        (Real.exp (- (‖p‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2)) *
          (∫ t in a..b, D t)) =
        (Real.exp (- (‖p‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2)) *
          Real.exp (- (‖p‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2))) *
          (∫ t in a..b, D t) ^ 2 by ring, hoff]
    have hc' := mul_le_mul_of_nonneg_right hC
      (mul_nonneg
        (sq_nonneg (Real.exp (- (‖p‖ ^ 2 * 1) / (2 * sigma ^ 2))))
        (sq_nonneg (∫ t in a..b, D t)))
    simpa only [one_mul, mul_pow] using hc'
  · exact profileNeedle_product_le_of_ne_zero he hab hD0 hDlc hDint hsigma
      halpha0 halpha hR hpos

lemma setIntegral_profileNeedle_eq {n : ℕ} {p e : EuclSpace n} {a b : ℝ}
    (hab : a ≤ b) {D : ℝ → ℝ} {sigma x : ℝ} :
    (∫ t in Icc a b,
        Real.exp (-(‖needleMap p e t‖ ^ 2 * x) / (2 * sigma ^ 2)) * D t) =
      profileNeedleJ D p e a b sigma x := by
  rw [profileNeedleJ, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  ring

/-- **Unconditional compact-body Gaussian product bound.**  This discharges the localization
input for an indicator of a compact convex body in dimension at least two. -/
theorem compactConvex_gaussian_product_le {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {sigma alpha R : ℝ}
    (hsigma : 0 < sigma) (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2)
    (hKR : K ⊆ Metric.closedBall 0 R) :
    (∫ x in K, Real.exp (-(‖x‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2))) *
        (∫ x in K, Real.exp (-(‖x‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2))) ≤
      Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
        (∫ x in K, Real.exp (-(‖x‖ ^ 2 * 1) / (2 * sigma ^ 2))) ^ 2 := by
  let C : ℝ := Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2)
  let fplus : EuclSpace n → ℝ := fun x ↦
    Real.exp (-(‖x‖ ^ 2 * (1 + alpha)) / (2 * sigma ^ 2))
  let fminus : EuclSpace n → ℝ := fun x ↦
    Real.exp (-(‖x‖ ^ 2 * (1 - alpha)) / (2 * sigma ^ 2))
  let fzero : EuclSpace n → ℝ := fun x ↦
    Real.exp (-(‖x‖ ^ 2 * 1) / (2 * sigma ^ 2))
  have hcplus : Continuous fplus := by dsimp only [fplus]; fun_prop
  have hcminus : Continuous fminus := by dsimp only [fminus]; fun_prop
  have hczero : Continuous fzero := by dsimp only [fzero]; fun_prop
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hpos : ∀ f : EuclSpace n → ℝ, Continuous f → (∀ x, 0 < f x) →
      0 < ∫ x in K, f x := by
    intro f hfc hfp
    have hint : IntegrableOn f K := hfc.continuousOn.integrableOn_compact hKcomp
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem hKcl.measurableSet fun x _ ↦ (hfp x).le) hint).mpr
    have hsupp : Function.support f = Set.univ := by
      ext x
      simp [Function.mem_support, (hfp x).ne']
    simpa [hsupp] using hvol
  have hpminus : 0 < ∫ x in K, fminus x := hpos fminus hcminus fun x ↦ Real.exp_pos _
  have hpzero : 0 < ∫ x in K, fzero x := hpos fzero hczero fun x ↦ Real.exp_pos _
  by_contra hnot
  have hfail : C * (∫ x in K, fzero x) * (∫ x in K, fzero x) <
      (∫ x in K, fplus x) * (∫ x in K, fminus x) := by
    simpa only [C, fplus, fminus, fzero, pow_two, mul_assoc] using lt_of_not_ge hnot
  have hfail' : (∫ x in K, C * fzero x) * (∫ x in K, fzero x) <
      (∫ x in K, fplus x) * (∫ x in K, fminus x) := by
    rw [MeasureTheory.integral_const_mul]
    exact hfail
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hlocal⟩ :=
    Arlib.exists_logConcave_profile_product_lt
      (f₁ := fplus) (f₂ := fminus) (f₃ := fun x ↦ C * fzero x) (f₄ := fzero)
      hn hKc hKcl hKb
      hcplus hcminus ((continuous_const.mul hczero)) hczero
      (fun x ↦ (Real.exp_pos _).le)
      (fun x ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (fun x ↦ (Real.exp_pos _).le) hpminus
      (by rw [MeasureTheory.integral_const_mul]; exact mul_pos (Real.exp_pos _) hpzero) hfail'
  have hlocal' : C * (profileNeedleJ D p e a b sigma 1) ^ 2 <
      profileNeedleJ D p e a b sigma (1 + alpha) *
        profileNeedleJ D p e a b sigma (1 - alpha) := by
    change (∫ t in Icc a b, (C * fzero (needleMap p e t)) * D t) *
        (∫ t in Icc a b, fzero (needleMap p e t) * D t) <
      (∫ t in Icc a b, fplus (needleMap p e t) * D t) *
        (∫ t in Icc a b, fminus (needleMap p e t) * D t) at hlocal
    have hCint : (∫ t in Icc a b, (C * fzero (needleMap p e t)) * D t) =
        C * profileNeedleJ D p e a b sigma 1 := by
      calc
        _ = C * (∫ t in Icc a b, fzero (needleMap p e t) * D t) := by
          rw [← MeasureTheory.integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Icc
          intro t _
          ring
        _ = _ := by
          dsimp only [fzero]
          rw [setIntegral_profileNeedle_eq hab]
    rw [hCint] at hlocal
    dsimp only [fplus, fminus, fzero] at hlocal
    rw [setIntegral_profileNeedle_eq hab, setIntegral_profileNeedle_eq hab,
      setIntegral_profileNeedle_eq hab] at hlocal
    simpa [pow_two, mul_assoc] using hlocal
  have hplus0 : 0 ≤ profileNeedleJ D p e a b sigma (1 + alpha) := by
    rw [← setIntegral_profileNeedle_eq hab]
    exact setIntegral_nonneg measurableSet_Icc fun t ht ↦
      mul_nonneg (Real.exp_nonneg _) (hD0 t ht)
  have hminus0 : 0 ≤ profileNeedleJ D p e a b sigma (1 - alpha) := by
    rw [← setIntegral_profileNeedle_eq hab]
    exact setIntegral_nonneg measurableSet_Icc fun t ht ↦
      mul_nonneg (Real.exp_nonneg _) (hD0 t ht)
  have hplus : 0 < profileNeedleJ D p e a b sigma (1 + alpha) := by
    have hprod : 0 < profileNeedleJ D p e a b sigma (1 + alpha) *
        profileNeedleJ D p e a b sigma (1 - alpha) := by
      have hC0 : 0 ≤ C * (profileNeedleJ D p e a b sigma 1) ^ 2 :=
        mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
      linarith
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · linarith
  have hradius : ∀ t ∈ Icc a b, ‖needleMap p e t‖ ≤ R := by
    intro t ht
    have hm := hKR (hseg t ht)
    simpa [Metric.mem_closedBall, dist_zero_right] using hm
  have hbound := profileNeedle_product_le hab hD0 hDlc hDint hsigma
    halpha0 halpha hradius hplus
  exact (not_lt_of_ge hbound) hlocal'

lemma G_indicator_div_eq_setIntegral {n : ℕ} {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) {sigma x : ℝ} (hsigma : sigma ≠ 0) (hx : x ≠ 0) :
    G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / x) =
      ∫ y in K, Real.exp (- (‖y‖ ^ 2 * x) / (2 * sigma ^ 2)) := by
  rw [G]
  have hfun : (fun y ↦ gW (indicator K (1 : EuclSpace n → ℝ))
      (sigma ^ 2 / x) y) =
      indicator K (fun y ↦ Real.exp (- (‖y‖ ^ 2 * x) / (2 * sigma ^ 2))) := by
    funext y
    by_cases hy : y ∈ K
    · rw [gW, indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, one_mul]
      congr 1
      field_simp
    · rw [gW, indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  rw [hfun, MeasureTheory.integral_indicator hKm]

/-- The compact-body product theorem in the exact `G` form consumed by the variance identity. -/
theorem compactConvex_G_product_le {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {sigma alpha R : ℝ}
    (hsigma : 0 < sigma) (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2)
    (hKR : K ⊆ Metric.closedBall 0 R) :
    G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) *
        G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 - alpha)) ≤
      Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) *
        (G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2)) ^ 2 := by
  have hp : (1 : ℝ) + alpha ≠ 0 := by linarith
  have hm : (1 : ℝ) - alpha ≠ 0 := by linarith
  have hone : (1 : ℝ) ≠ 0 := one_ne_zero
  have hGone := G_indicator_div_eq_setIntegral (K := K) hKcl.measurableSet
    (sigma := sigma) (x := 1) hsigma.ne' hone
  simp only [div_one, mul_one] at hGone
  rw [G_indicator_div_eq_setIntegral hKcl.measurableSet hsigma.ne' hp,
    G_indicator_div_eq_setIntegral hKcl.measurableSet hsigma.ne' hm, hGone]
  simpa only [mul_one] using
    compactConvex_gaussian_product_le hn hKc hKcl hKb hvol hsigma
      halpha0 halpha hKR

/-- Indicator-body version of `lc_variance_bound`, with localization discharged. -/
theorem compactConvex_lc_variance_bound {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {sigma alpha R : ℝ}
    (hsigma : 0 < sigma) (halpha0 : 0 ≤ alpha) (halpha : alpha ≤ 1 / 2)
    (hKR : K ⊆ Metric.closedBall 0 R)
    (hGa : G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) ≠ 0)
    (hGb : G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) ≠ 0) :
    (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
          gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x) ^ 2
        * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
          G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) /
      (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
          gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x)
        * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
          G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) ^ 2 ≤
      Real.exp (2 * R ^ 2 * alpha ^ 2 / sigma ^ 2) := by
  have hp : (1 : ℝ) + alpha ≠ 0 := by linarith
  have hm : (1 : ℝ) - alpha ≠ 0 := by linarith
  rw [variance_ratio hsigma.ne' hp hm hGa hGb]
  rw [div_le_iff₀ (by positivity : 0 <
    (G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2)) ^ 2)]
  exact compactConvex_G_product_le hn hKc hKcl hKb hvol hsigma halpha0 halpha hKR

/-- **Unconditional compact-body form of paper Claim 5.11.**  At the accelerated rate
`alpha = sigma²/(2 C² n)`, localization and the two normalizer side conditions are both
discharged by convexity, boundedness, and positive volume of `K`. -/
theorem compactConvex_fast_var_bound {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclSpace n)} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K) {sigma C alpha : ℝ}
    (hsigma : 0 < sigma) (hC : 0 < C)
    (halpha : alpha = sigma ^ 2 / (2 * C ^ 2 * n)) (halpha2 : alpha ≤ 1 / 2)
    (hKR : K ⊆ Metric.closedBall 0 (C * √n)) :
    (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
          gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x) ^ 2
        * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
          G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) /
      (∫ x, (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) x /
          gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x)
        * (gW (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)) x /
          G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2 / (1 + alpha)))) ^ 2 ≤
      1 + sigma ^ 2 / (C ^ 2 * n) := by
  have hnNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have halpha0 : 0 ≤ alpha := by rw [halpha]; positivity
  have hGa : G (indicator K (1 : EuclSpace n → ℝ))
      (sigma ^ 2 / (1 + alpha)) ≠ 0 :=
    G_indicator_ne_zero hKcl.measurableSet hvol (by positivity)
  have hGb : G (indicator K (1 : EuclSpace n → ℝ)) (sigma ^ 2) ≠ 0 :=
    G_indicator_ne_zero hKcl.measurableSet hvol (by positivity)
  exact (compactConvex_lc_variance_bound hn hKc hKcl hKb hvol hsigma halpha0
    halpha2 hKR hGa hGb).trans (fast_var_bound hsigma hC hnpos halpha halpha2)

#print axioms logConcaveProfile_gaussian_variance
#print axioms hasDerivAt_profileJ
#print axioms profileH_le_exp
#print axioms exists_normalized_logConcave_profile
#print axioms profileNeedle_product_le
#print axioms compactConvex_gaussian_product_le
#print axioms compactConvex_G_product_le
#print axioms compactConvex_lc_variance_bound
#print axioms compactConvex_fast_var_bound

end Arlib.GaussianCooling
