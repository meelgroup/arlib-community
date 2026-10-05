/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofIdealProduct
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.LogConcaveProfileVariance

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Unconditional accelerated-phase moment bound

This module adapts the compact-convex localization theorem vendored under
`ArlibCommunity.External.Kr25` to the variance convention and clipped cooling
schedule used by the CV18 executable model.
-/

/-- The localization product theorem, specialized to one accelerated CV18
transition.  The next variance may be clipped at the terminal variance; only
the upper bound by the unclipped update is needed. -/
theorem gaussianRatioWeight_accelerated_relativeSecondMoment_le_localized
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hsT : s ≤ terminalVariance q)
    (hraw : t ≤ s * (1 + s / (2 * terminalVariance q))) :
    ((∫ x, gaussianRatioWeight s t x ^ 2
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight s t x
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) ^ 2) ≤
      1 + s / terminalVariance q := by
  let K : Set (AmbientSpace q.n) := truncatedBody q I
  let T : ℝ := terminalVariance q
  let alpha : ℝ := (t - s) / s
  let u : ℝ := s * t / (2 * s - t)
  have hT : 0 < T := by simpa [T] using terminalVariance_pos' q
  have ht : 0 < t := hs.trans_le hst
  have halpha0 : 0 ≤ alpha := by dsimp [alpha]; positivity
  have hratio : s / (2 * T) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * T)]
    nlinarith
  have halpha : alpha ≤ 1 / 2 := by
    have hdelta : t - s ≤ s ^ 2 / (2 * T) := by
      calc
        t - s ≤ s * (1 + s / (2 * T)) - s := by linarith
        _ = s ^ 2 / (2 * T) := by ring
    dsimp [alpha]
    rw [div_le_iff₀ hs]
    nlinarith
  have htwo : t < 2 * s := by
    have : t ≤ 3 * s / 2 := by
      calc
        t ≤ s * (1 + s / (2 * T)) := hraw
        _ ≤ 3 * s / 2 := by nlinarith
    nlinarith
  have hden : 0 < 2 * s - t := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hKc : Convex ℝ K := by
    simpa [K] using (truncatedVolumeInput q I).body.convex
  have hKcl : IsClosed K := by
    simpa [K] using (truncatedVolumeInput q I).body.isCompact.isClosed
  have hKb : Bornology.IsBounded K := by
    simpa [K] using (truncatedVolumeInput q I).body.isCompact.isBounded
  have hvol : 0 < volume K := by
    have hunit : 0 < volume (unitBall q.n) :=
      Metric.measure_closedBall_pos volume (0 : AmbientSpace q.n) zero_lt_one
    exact hunit.trans_le (measure_mono (unitBall_subset_truncatedBody q I))
  have hKR : K ⊆ Metric.closedBall 0 (Real.sqrt T) := by
    intro x hx
    exact hx.2
  have hsqrtT : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hsqrtt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hproduct :=
    Arlib.GaussianCooling.compactConvex_gaussian_product_le
      (le_trans (by norm_num : 2 ≤ 3) q.dim_ok) hKc hKcl hKb
      hvol (sigma := Real.sqrt t) (alpha := alpha) (R := Real.sqrt T)
      (Real.sqrt_pos.2 ht) halpha0 halpha hKR
  have hplus :
      (∫ x in K,
          Real.exp (-(‖x‖ ^ 2 * (1 + alpha)) / (2 * (Real.sqrt t) ^ 2))) =
        gaussianIntegral K s := by
    rw [gaussianIntegral_eq_setIntegral hKcl.measurableSet]
    apply setIntegral_congr_fun hKcl.measurableSet
    intro x _
    rw [gaussianDensity_eq]
    apply congrArg Real.exp
    dsimp [alpha]
    rw [hsqrtt]
    field_simp [hs.ne', ht.ne']
    ring
  have hminus :
      (∫ x in K,
          Real.exp (-(‖x‖ ^ 2 * (1 - alpha)) / (2 * (Real.sqrt t) ^ 2))) =
        gaussianIntegral K u := by
    rw [gaussianIntegral_eq_setIntegral hKcl.measurableSet]
    apply setIntegral_congr_fun hKcl.measurableSet
    intro x _
    rw [gaussianDensity_eq]
    apply congrArg Real.exp
    dsimp [alpha, u]
    rw [hsqrtt]
    field_simp [hs.ne', ht.ne', hden.ne']
    ring
  have hzero :
      (∫ x in K,
          Real.exp (-(‖x‖ ^ 2 * 1) / (2 * (Real.sqrt t) ^ 2))) =
        gaussianIntegral K t := by
    rw [gaussianIntegral_eq_setIntegral hKcl.measurableSet]
    apply setIntegral_congr_fun hKcl.measurableSet
    intro x _
    rw [gaussianDensity_eq, hsqrtt]
    apply congrArg Real.exp
    ring
  rw [hplus, hminus, hzero, hsqrtT, hsqrtt] at hproduct
  have hZs : 0 < gaussianIntegral K s := by
    simpa [K] using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have hZt : 0 < gaussianIntegral K t := by
    simpa [K] using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  rw [gaussianRatioWeight_secondMoment_eq q I hs ht,
    gaussianRatioWeight_mean_eq q I hs]
  change (gaussianIntegral K u / gaussianIntegral K s) /
      (gaussianIntegral K t / gaussianIntegral K s) ^ 2 ≤ _
  have hquotient :
      (gaussianIntegral K u / gaussianIntegral K s) /
          (gaussianIntegral K t / gaussianIntegral K s) ^ 2 =
        gaussianIntegral K u * gaussianIntegral K s /
          gaussianIntegral K t ^ 2 := by
    field_simp [hZs.ne', hZt.ne']
  rw [hquotient]
  let exponent : ℝ := 2 * T * alpha ^ 2 / t
  have hproduct' :
      gaussianIntegral K u * gaussianIntegral K s ≤
        Real.exp exponent * gaussianIntegral K t ^ 2 := by
    simpa [exponent, mul_comm, mul_left_comm, mul_assoc] using hproduct
  have hexponent0 : 0 ≤ exponent := by dsimp [exponent]; positivity
  have halpha_le : alpha ≤ s / (2 * T) := by
    have hdelta : t - s ≤ s ^ 2 / (2 * T) := by
      calc
        t - s ≤ s * (1 + s / (2 * T)) - s := by linarith
        _ = s ^ 2 / (2 * T) := by ring
    dsimp [alpha]
    rw [div_le_iff₀ hs]
    nlinarith
  have hexponent_le : exponent ≤ s / (2 * T) := by
    have hratio0 : 0 ≤ s / (2 * T) := by positivity
    have halpha_sq : alpha ^ 2 ≤ (s / (2 * T)) ^ 2 :=
      (sq_le_sq₀ halpha0 hratio0).2 halpha_le
    have hbound1 : 2 * T * alpha ^ 2 ≤ s ^ 2 / (2 * T) := by
      calc
        2 * T * alpha ^ 2 ≤ 2 * T * (s / (2 * T)) ^ 2 := by gcongr
        _ = s ^ 2 / (2 * T) := by field_simp [hT.ne']
    have hsquare : s ^ 2 ≤ s * t := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hst hs.le
    have hbound2 : s ^ 2 / (2 * T) ≤ s * t / (2 * T) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    dsimp [exponent]
    rw [div_le_iff₀ ht]
    calc
      2 * T * alpha ^ 2 ≤ s ^ 2 / (2 * T) := hbound1
      _ ≤ s * t / (2 * T) := hbound2
      _ = s / (2 * T) * t := by ring
  have hexponent_lt_two : exponent < 2 :=
    lt_of_le_of_lt (hexponent_le.trans hratio) (by norm_num)
  have hexp : Real.exp exponent ≤ 1 + s / T := by
    calc
      Real.exp exponent ≤ (2 + exponent) / (2 - exponent) :=
        Real.exp_le_two_add_div_two_sub hexponent0 hexponent_lt_two
      _ ≤ 1 + 2 * exponent := by
        rw [div_le_iff₀ (by linarith : 0 < 2 - exponent)]
        nlinarith [mul_nonneg hexponent0 (sub_nonneg.mpr (by linarith : exponent ≤ 1))]
      _ ≤ 1 + 2 * (s / (2 * T)) := by gcongr
      _ = 1 + s / T := by field_simp [hT.ne']
  calc
    gaussianIntegral K u * gaussianIntegral K s / gaussianIntegral K t ^ 2 ≤
        (Real.exp exponent * gaussianIntegral K t ^ 2) /
          gaussianIntegral K t ^ 2 := by gcongr
    _ = Real.exp exponent := by field_simp [hZt.ne']
    _ ≤ 1 + s / T := hexp
    _ = 1 + s / terminalVariance q := by rfl

/-- The sharp accelerated-moment condition required by the ideal-product
analysis is unconditional for the executable clipped schedule. -/
theorem figureOneSharpAcceleratedMoments
    (q : VolumeParams) (I : VolumeInput q.n) :
    FigureOneSharpAcceleratedMoments q I := by
  intro k
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have hsT : s ≤ terminalVariance q := scheduleValue_le_terminal q k
  have hsone : 1 < s := by simpa [s] using lt_of_not_ge k.property
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hraw : t ≤ s * (1 + s / (2 * terminalVariance q)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans_eq ?_
    rw [coolingRate, if_neg]
    simpa [s] using not_le_of_gt hsone
  exact gaussianRatioWeight_accelerated_relativeSecondMoment_le_localized
    q I hs hst hsT hraw

#print axioms figureOneSharpAcceleratedMoments

end ArlibCommunity.Algorithms.CV18
