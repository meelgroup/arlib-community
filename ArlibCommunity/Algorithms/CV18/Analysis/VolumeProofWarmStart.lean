/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSchedule

open MeasureTheory
open scoped Pointwise

namespace ArlibCommunity.Algorithms.CV18

/-! # Warm starts between adjacent restricted Gaussians

This file proves the normalization bounds behind the warm-start assertion in
Figure 1.  The fixed-rate part uses a change of variables and convexity; the
accelerated part uses the truncation radius directly.
-/

/-- Pointwise warmness of the normalized restricted Gaussian at variance `s`
with respect to the one at variance `t`. -/
def RestrictedGaussianWarm {n : ℕ} (K : Set (AmbientSpace n))
    (s t M : ℝ) : Prop :=
  ∀ x ∈ K, gaussianDensity s x / gaussianIntegral K s ≤
    M * (gaussianDensity t x / gaussianIntegral K t)

/-- Measure-level warmness: `mu` is dominated by `M` times `nu`. -/
def MeasureWarm {E : Type*} [MeasurableSpace E]
    (M : ℝ) (mu nu : Measure E) : Prop :=
  mu ≤ ENNReal.ofReal M • nu

theorem gaussianDensity_scale {n : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : AmbientSpace n) :
    gaussianDensity t (Real.sqrt (t / s) • x) = gaussianDensity s x := by
  unfold gaussianDensity
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  have hdiv : 0 ≤ t / s := div_nonneg ht.le hs.le
  rw [Real.sq_sqrt hdiv]
  field_simp [hs.ne', ht.ne']

/-- Scaling a convex set containing zero bounds the growth of its Gaussian
partition function. -/
theorem gaussianIntegral_scaling_le {n : ℕ} (K : Set (AmbientSpace n))
    (hK : MeasurableSet K) (hconvex : Convex ℝ K)
    (hzero : (0 : AmbientSpace n) ∈ K) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    gaussianIntegral K t ≤
      Real.sqrt (t / s) ^ n * gaussianIntegral K s := by
  have ht : 0 < t := hs.trans_le hst
  let r : ℝ := Real.sqrt (t / s)
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos ht hs)
  have hr1 : 1 ≤ r := by
    change 1 ≤ Real.sqrt (t / s)
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    exact (le_div_iff₀ hs).2 (by simpa using hst)
  have hsubset : K ⊆ r • K := by
    intro x hx
    exact hconvex.mem_smul_of_zero_mem hzero hx hr1
  rw [gaussianIntegral_eq_setIntegral hK,
    gaussianIntegral_eq_setIntegral hK]
  have hmono : (∫ x in K, gaussianDensity t x) ≤
      ∫ x in r • K, gaussianDensity t x := by
    apply setIntegral_mono_set
    · exact (integrable_gaussianDensity ht).integrableOn
    · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall hsubset
  have hchange := Measure.setIntegral_comp_smul_of_pos volume
    (gaussianDensity t) K hr
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hchange
  have hdensity : (∫ x in K, gaussianDensity t (r • x)) =
      ∫ x in K, gaussianDensity s x := by
    apply setIntegral_congr_fun hK
    intro x _
    exact gaussianDensity_scale hs ht x
  rw [hdensity] at hchange
  have hrpow : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [smul_eq_mul] at hchange
  field_simp [hrpow] at hchange
  change (∫ x in K, gaussianDensity t x) ≤
    r ^ n * ∫ x in K, gaussianDensity s x
  calc
    (∫ x in K, gaussianDensity t x) ≤
        ∫ x in r • K, gaussianDensity t x := hmono
    _ = r ^ n * ∫ x in K, gaussianDensity s x := by
      simpa [mul_comm] using hchange.symm

theorem fixedRate_sqrt_factor_le (n : ℕ) (hn : 0 < n) :
    Real.sqrt (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / 2) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase : 0 ≤ 1 + 1 / (n : ℝ) := by positivity
  have hsquare : (Real.sqrt (1 + 1 / (n : ℝ)) ^ n) ^ 2 =
      (1 + ((n : ℝ))⁻¹) ^ n := by
    rw [← pow_mul, show n * 2 = 2 * n by omega, pow_mul,
      Real.sq_sqrt hbase]
    simp [one_div]
  have hexpsquare : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hsquare, hexpsquare]
  exact Real.one_add_inv_pow_le_exp

theorem gaussianDensity_mono_variance {n : ℕ} {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (x : AmbientSpace n) :
    gaussianDensity s x ≤ gaussianDensity t x := by
  rw [gaussianDensity_eq, gaussianDensity_eq]
  apply Real.exp_le_exp.mpr
  have hrecip : 1 / (2 * t) ≤ 1 / (2 * s) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hrecip (sq_nonneg ‖x‖)
  calc
    -‖x‖ ^ 2 / (2 * s) = -(‖x‖ ^ 2 * (1 / (2 * s))) := by ring
    _ ≤ -(‖x‖ ^ 2 * (1 / (2 * t))) := neg_le_neg hmul
    _ = -‖x‖ ^ 2 / (2 * t) := by ring

theorem gaussianIntegral_mono_variance {n : ℕ} (K : Set (AmbientSpace n))
    (hK : MeasurableSet K) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    gaussianIntegral K s ≤ gaussianIntegral K t := by
  rw [gaussianIntegral_eq_setIntegral hK, gaussianIntegral_eq_setIntegral hK]
  apply integral_mono_ae
  · exact (integrable_gaussianDensity hs).integrableOn
  · exact (integrable_gaussianDensity (hs.trans_le hst)).integrableOn
  · exact Filter.Eventually.of_forall (gaussianDensity_mono_variance hs hst)

theorem restrictedGaussianWarm_of_partition_growth {n : ℕ}
    (K : Set (AmbientSpace n)) {s t M : ℝ}
    (hZs : 0 < gaussianIntegral K s) (hZt : 0 < gaussianIntegral K t)
    (hden : ∀ x : AmbientSpace n, gaussianDensity s x ≤ gaussianDensity t x)
    (hgrowth : gaussianIntegral K t ≤ M * gaussianIntegral K s) :
    RestrictedGaussianWarm K s t M := by
  intro x _hx
  have hd := hden x
  have hnonneg : 0 ≤ gaussianDensity t x := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hgrowth hnonneg
  change gaussianDensity s x / gaussianIntegral K s ≤
    M * (gaussianDensity t x / gaussianIntegral K t)
  apply le_trans (div_le_div_of_nonneg_right hd hZs.le)
  field_simp [hZs.ne', hZt.ne']
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The density-ratio formulation of restricted-Gaussian warmness implies the
usual domination statement between the normalized probability measures. -/
theorem restrictedGaussianWarm_to_measureWarm
    (q : VolumeParams) (I : VolumeInput q.n) {s t M : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hM : 0 ≤ M)
    (hwarm : RestrictedGaussianWarm (truncatedBody q I) s t M) :
    MeasureWarm M
      (truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))
      (truncatedGaussianProbability q I t ht : Measure (AmbientSpace q.n)) := by
  unfold MeasureWarm
  rw [Measure.le_iff]
  intro S hS
  rw [truncatedGaussianProbability_apply q I hs hS,
    Measure.smul_apply, smul_eq_mul,
    truncatedGaussianProbability_apply q I ht hS]
  let Zs := gaussianIntegral (truncatedBody q I) s
  let Zt := gaussianIntegral (truncatedBody q I) t
  have hZs : 0 < Zs := by
    simpa [Zs] using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have hZt : 0 < Zt := by
    simpa [Zt] using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  have hmeas_s : Measurable fun x : AmbientSpace q.n =>
      ENNReal.ofReal (gaussianDensity s x) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianDensity
    fun_prop
  have hmeas_t : Measurable fun x : AmbientSpace q.n =>
      ENNReal.ofReal (gaussianDensity t x) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianDensity
    fun_prop
  rw [← lintegral_const_mul _ hmeas_s, ← lintegral_const_mul _ hmeas_t]
  have hmeas_norm_t : Measurable fun x : AmbientSpace q.n =>
      (ENNReal.ofReal (gaussianIntegral (truncatedBody q I) t))⁻¹ *
        ENNReal.ofReal (gaussianDensity t x) := measurable_const.mul hmeas_t
  rw [← lintegral_const_mul _ hmeas_norm_t]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem
      (hS.inter (truncatedBody_measurable q I))] with x hx
  have hw := hwarm x hx.2
  rw [← ENNReal.ofReal_inv_of_pos hZs, ← ENNReal.ofReal_inv_of_pos hZt]
  change ENNReal.ofReal Zs⁻¹ * ENNReal.ofReal (gaussianDensity s x) ≤
    ENNReal.ofReal M *
      (ENNReal.ofReal Zt⁻¹ * ENNReal.ofReal (gaussianDensity t x))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Zs⁻¹),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Zt⁻¹),
    ← ENNReal.ofReal_mul hM]
  apply ENNReal.ofReal_le_ofReal
  simpa [div_eq_inv_mul, mul_assoc] using hw

/-- Every fixed-rate phase, including a terminally clamped one, is
`exp(1/2)`-warm. -/
theorem truncatedGaussian_fixedRate_warm
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t)
    (hstep : t ≤ s * (1 + 1 / (q.n : ℝ))) :
    RestrictedGaussianWarm (truncatedBody q I) s t (Real.exp (1 / 2)) := by
  have hn : 0 < q.n := lt_of_lt_of_le (by omega) q.dim_ok
  have hscale := gaussianIntegral_scaling_le (truncatedBody q I)
    (truncatedBody_measurable q I) (truncatedVolumeInput q I).body.convex
    (unitBall_subset_truncatedBody q I (by simp [unitBall])) hs hst
  have hratio : t / s ≤ 1 + 1 / (q.n : ℝ) :=
    (div_le_iff₀ hs).2 (by simpa [mul_comm] using hstep)
  have hsqrt : Real.sqrt (t / s) ≤
      Real.sqrt (1 + 1 / (q.n : ℝ)) := Real.sqrt_le_sqrt hratio
  have hpows : Real.sqrt (t / s) ^ q.n ≤
      Real.sqrt (1 + 1 / (q.n : ℝ)) ^ q.n :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt q.n
  have hfactor := fixedRate_sqrt_factor_le q.n hn
  have hZs : 0 < gaussianIntegral (truncatedBody q I) s := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have ht : 0 < t := hs.trans_le hst
  have hZt : 0 < gaussianIntegral (truncatedBody q I) t := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  apply restrictedGaussianWarm_of_partition_growth _ hZs hZt
    (gaussianDensity_mono_variance hs hst)
  calc
    gaussianIntegral (truncatedBody q I) t ≤
        Real.sqrt (t / s) ^ q.n * gaussianIntegral (truncatedBody q I) s := hscale
    _ ≤ Real.sqrt (1 + 1 / (q.n : ℝ)) ^ q.n *
        gaussianIntegral (truncatedBody q I) s := by gcongr
    _ ≤ Real.exp (1 / 2) * gaussianIntegral (truncatedBody q I) s := by gcongr

/-- On a set of squared radius at most `T`, an accelerated variance step grows
the unnormalized density by at most `exp(1/4)`. -/
theorem gaussianDensity_accelerated_le {n : ℕ} {s t T : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hT : 0 < T)
    (hdelta : t - s ≤ s * t / (2 * T))
    (x : AmbientSpace n) (hx : ‖x‖ ^ 2 ≤ T) :
    gaussianDensity t x ≤ Real.exp (1 / 4) * gaussianDensity s x := by
  rw [gaussianDensity_eq, gaussianDensity_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hexp : -‖x‖ ^ 2 / (2 * t) ≤ 1 / 4 + -‖x‖ ^ 2 / (2 * s) := by
    have hcoef : 0 ≤ s * t / (2 * T) := by positivity
    have hmul1 := mul_le_mul_of_nonneg_left hdelta (sq_nonneg ‖x‖)
    have hmul2 := mul_le_mul_of_nonneg_right hx hcoef
    have hmid : ‖x‖ ^ 2 * (s * t / (2 * T)) ≤ s * t / 2 := by
      calc
        ‖x‖ ^ 2 * (s * t / (2 * T)) ≤
            T * (s * t / (2 * T)) := hmul2
        _ = s * t / 2 := by field_simp [hT.ne']
    have hdiff : ‖x‖ ^ 2 * (t - s) ≤ s * t / 2 := hmul1.trans hmid
    have hrearrange :
        -‖x‖ ^ 2 / (2 * t) - (-‖x‖ ^ 2 / (2 * s)) =
          ‖x‖ ^ 2 * (t - s) / (2 * s * t) := by
      field_simp [hs.ne', ht.ne']
      ring
    have hquot : ‖x‖ ^ 2 * (t - s) / (2 * s * t) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * s * t)]
      nlinarith
    apply (sub_le_iff_le_add).mp
    rw [hrearrange]
    exact hquot
  simpa using hexp

theorem gaussianIntegral_accelerated_le {n : ℕ} (K : Set (AmbientSpace n))
    (hK : MeasurableSet K) {s t T : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hT : 0 < T)
    (hdelta : t - s ≤ s * t / (2 * T))
    (hbounded : ∀ x ∈ K, ‖x‖ ^ 2 ≤ T) :
    gaussianIntegral K t ≤ Real.exp (1 / 4) * gaussianIntegral K s := by
  rw [gaussianIntegral_eq_setIntegral hK, gaussianIntegral_eq_setIntegral hK,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono_ae
  · exact (integrable_gaussianDensity ht).integrableOn
  · exact (integrable_gaussianDensity hs).integrableOn.const_mul _
  · filter_upwards [ae_restrict_mem hK] with x hx
    exact gaussianDensity_accelerated_le hs ht hT hdelta x (hbounded x hx)

/-- Every accelerated phase on the truncated body is `exp(1/2)`-warm (the
partition-function argument actually gives the stronger `exp(1/4)`). -/
theorem truncatedGaussian_accelerated_warm
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t)
    (hdelta : t - s ≤ s * t / (2 * terminalVariance q)) :
    RestrictedGaussianWarm (truncatedBody q I) s t (Real.exp (1 / 2)) := by
  have ht : 0 < t := hs.trans_le hst
  have hT := terminalVariance_pos' q
  have hgrowth := gaussianIntegral_accelerated_le (truncatedBody q I)
    (truncatedBody_measurable q I) hs ht hT hdelta
    (fun x hx => norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx)
  have hZs : 0 < gaussianIntegral (truncatedBody q I) s := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have hZt : 0 < gaussianIntegral (truncatedBody q I) t := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  apply restrictedGaussianWarm_of_partition_growth _ hZs hZt
    (gaussianDensity_mono_variance hs hst)
  calc
    gaussianIntegral (truncatedBody q I) t ≤
        Real.exp (1 / 4) * gaussianIntegral (truncatedBody q I) s := hgrowth
    _ ≤ Real.exp (1 / 2) * gaussianIntegral (truncatedBody q I) s := by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) hZs.le

/-- Consecutive values of the executable Figure-1 schedule satisfy the warm
start bound used by the mixing analysis. -/
theorem scheduleValue_adjacent_warm (q : VolumeParams) (I : VolumeInput q.n)
    (k : ℕ) :
    RestrictedGaussianWarm (truncatedBody q I)
      (scheduleValue q k) (scheduleValue q (k + 1)) (Real.exp (1 / 2)) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht : 0 < t := hs.trans_le hst
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  by_cases hsone : s ≤ 1
  · apply truncatedGaussian_fixedRate_warm q I hs hst
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans_eq ?_
    rw [coolingRate, if_pos hsone]
  · apply truncatedGaussian_accelerated_warm q I hs hst
    have hraw : t ≤ s * (1 + s / (2 * terminalVariance q)) := by
      rw [ht_next]
      unfold nextVariance
      refine (min_le_right _ _).trans_eq ?_
      rw [coolingRate, if_neg hsone]
    have hT := terminalVariance_pos' q
    have hfirst : t - s ≤ s ^ 2 / (2 * terminalVariance q) := by
      calc
        t - s ≤ s * (1 + s / (2 * terminalVariance q)) - s := by linarith
        _ = s ^ 2 / (2 * terminalVariance q) := by ring
    have hsquare : s ^ 2 ≤ s * t := by nlinarith
    exact hfirst.trans (div_le_div_of_nonneg_right hsquare (by positivity))

theorem scheduleValue_adjacent_measureWarm
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    MeasureWarm (Real.exp (1 / 2))
      (truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
      (truncatedGaussianProbability q I (scheduleValue q (k + 1))
        (scheduleValue_pos q (k + 1)) : Measure (AmbientSpace q.n)) := by
  exact restrictedGaussianWarm_to_measureWarm q I
    (scheduleValue_pos q k) (scheduleValue_pos q (k + 1)) (by positivity)
    (scheduleValue_adjacent_warm q I k)

end ArlibCommunity.Algorithms.CV18
