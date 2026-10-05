/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofThirdMomentLogConcavity
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianDeathArithmetic
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofWarmStart

/-!
# Third moments for accelerated CV18 phases

On the terminally truncated body an accelerated variance update changes the
pointwise importance weight by at most `exp (1 / 4)`.  This gives a uniform
`L³` estimate which is stronger than the fixed-phase constant used by the
equation-(6) assembly.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The density-growth estimate is equivalently a pointwise bound on the
Gaussian ratio weight. -/
theorem gaussianRatioWeight_le_exp_quarter_of_accelerated
    {n : ℕ} {s t T : ℝ} (hs : 0 < s) (ht : 0 < t) (hT : 0 < T)
    (hdelta : t - s ≤ s * t / (2 * T))
    (x : AmbientSpace n) (hx : ‖x‖ ^ 2 ≤ T) :
    gaussianRatioWeight s t x ≤ Real.exp (1 / 4) := by
  have hdensity := gaussianDensity_accelerated_le hs ht hT hdelta x hx
  rw [gaussianDensity_eq, gaussianDensity_eq] at hdensity
  unfold gaussianRatioWeight
  rw [div_le_iff₀ (Real.exp_pos _)]
  simpa [mul_comm] using hdensity

/-- Increasing the variance makes every Gaussian ratio weight at least one. -/
theorem one_le_gaussianRatioWeight_of_le
    {n : ℕ} {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (x : AmbientSpace n) :
    1 ≤ gaussianRatioWeight s t x := by
  have hdensity := gaussianDensity_mono_variance hs hst x
  rw [gaussianDensity_eq, gaussianDensity_eq] at hdensity
  unfold gaussianRatioWeight
  rw [one_le_div (Real.exp_pos _)]
  exact hdensity

/-- Every accelerated scheduled Gaussian ratio has relative third moment at
most `(129/64)^3`.  The deliberately shared constant lets fixed and
accelerated phases use the same equation-(6) arithmetic. -/
theorem scheduleValue_accelerated_thirdMoment_le_rational_mean_cube
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : ¬ scheduleValue q k ≤ 1) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    (∫ x, weight x ^ 3 ∂nu) ≤
      ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
  dsimp only
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q k)
  let weight := gaussianRatioWeight (n := q.n) s t
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht : 0 < t := hs.trans_le hst
  have hT : 0 < terminalVariance q := terminalVariance_pos' q
  let _ : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hraw : t ≤ s * (1 + s / (2 * terminalVariance q)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans_eq ?_
    rw [coolingRate, if_neg]
    simpa [s] using hsone
  have hdelta : t - s ≤ s * t / (2 * terminalVariance q) := by
    have hfirst : t - s ≤ s ^ 2 / (2 * terminalVariance q) := by
      calc
        t - s ≤ s * (1 + s / (2 * terminalVariance q)) - s := by
          linarith
        _ = s ^ 2 / (2 * terminalVariance q) := by ring
    have hsquare : s ^ 2 ≤ s * t := by nlinarith
    exact hfirst.trans (div_le_div_of_nonneg_right hsquare (by positivity))
  have hweightMeas : Measurable weight := measurable_gaussianRatioWeight s t
  have hweightMem : MemLp weight 3 nu := by
    simpa [weight, nu, s, t] using
      gaussianRatioWeight_memLp q I hs ht 3
  have hcubeInt : Integrable (fun x => weight x ^ 3) nu := by
    have h := hweightMem.integrable_norm_pow'
    apply h.congr
    filter_upwards with x
    have hpositive : 0 < weight x := by
      dsimp [weight, gaussianRatioWeight]
      positivity
    simp only [Real.norm_eq_abs, abs_of_pos hpositive]
  have hupper : ∀ᵐ x ∂nu, weight x ≤ Real.exp (1 / 4) := by
    filter_upwards [truncatedGaussianProbability_ae_mem q I hs] with x hx
    exact gaussianRatioWeight_le_exp_quarter_of_accelerated hs ht hT hdelta x
      (norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx)
  have hlower : ∀ x, 1 ≤ weight x := by
    intro x
    exact one_le_gaussianRatioWeight_of_le hs hst x
  have hmean : 1 ≤ ∫ x, weight x ∂nu := by
    have honeInt : Integrable (fun _x : AmbientSpace q.n => (1 : ℝ)) nu :=
      integrable_const 1
    calc
      1 = ∫ _x, (1 : ℝ) ∂nu := by simp
      _ ≤ ∫ x, weight x ∂nu := by
        apply integral_mono_ae honeInt (hweightMem.integrable (by norm_num))
        exact Filter.Eventually.of_forall hlower
  have hexp53 : Real.exp (1 / 2) ≤ (5 / 3 : ℝ) := by
    convert Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) using 1 <;> norm_num
  have hexp : Real.exp (1 / 4) ≤ (129 / 64 : ℝ) := by
    calc
      Real.exp (1 / 4) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 5 / 3 := hexp53
      _ ≤ 129 / 64 := by norm_num
  have hpoint : ∀ᵐ x ∂nu,
      weight x ^ 3 ≤ (Real.exp (1 / 4)) ^ 3 := by
    filter_upwards [hupper] with x hx
    exact pow_le_pow_left₀ (zero_le_one.trans (hlower x)) hx 3
  have hconstCube :
      Integrable (fun _x : AmbientSpace q.n => (Real.exp (1 / 4)) ^ 3) nu :=
    integrable_const _
  calc
    (∫ x, weight x ^ 3 ∂nu) ≤
        ∫ _x, (Real.exp (1 / 4)) ^ 3 ∂nu := by
      apply integral_mono_ae hcubeInt hconstCube hpoint
    _ = (Real.exp (1 / 4)) ^ 3 := by simp
    _ ≤ ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity) ?_ 3
      calc
        Real.exp (1 / 4) ≤ 129 / 64 := hexp
        _ ≤ (129 / 64 : ℝ) * ∫ x, weight x ∂nu := by
          nlinarith

#print axioms gaussianRatioWeight_le_exp_quarter_of_accelerated
#print axioms one_le_gaussianRatioWeight_of_le
#print axioms scheduleValue_accelerated_thirdMoment_le_rational_mean_cube

end ArlibCommunity.Algorithms.CV18
