/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialTail

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The product of exact adjacent partition-function ratios along a cooling list. -/
noncomputable def adjacentRatioProduct {α : Type*} (Z : α → ℝ) : List α → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => Z b / Z a * adjacentRatioProduct Z (b :: rest)
termination_by values => values.length

theorem adjacentRatioProduct_telescopes {α : Type*} (Z : α → ℝ) :
    ∀ (a : α) (rest : List α),
      (∀ x ∈ a :: rest, Z x ≠ 0) →
        Z a * adjacentRatioProduct Z (a :: rest) =
          Z ((a :: rest).getLast (by simp)) := by
  intro a rest
  induction rest generalizing a with
  | nil => simp [adjacentRatioProduct]
  | cons b rest ih =>
      intro hnonzero
      rw [adjacentRatioProduct]
      have ha : Z a ≠ 0 := hnonzero a (by simp)
      have htail : ∀ x ∈ b :: rest, Z x ≠ 0 := by
        intro x hx
        exact hnonzero x (by simp [hx])
      rw [show Z a * (Z b / Z a * adjacentRatioProduct Z (b :: rest)) =
          Z b * adjacentRatioProduct Z (b :: rest) by field_simp]
      exact ih b htail

theorem gaussianIntegral_pos (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  rw [gaussianIntegral_eq_setIntegral hK]
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (integrable_gaussianDensity (n := q.n) hsigma2).integrableOn).2
  have hunit : 0 < volume (unitBall q.n) := by
    exact Metric.measure_closedBall_pos volume (0 : AmbientSpace q.n) zero_lt_one
  have hbody : 0 < volume (I.body : Set (AmbientSpace q.n)) :=
    hunit.trans_le (measure_mono I.unitBall_subset)
  simpa [Function.support, gaussianDensity, hK] using hbody

theorem euclideanVolume_pos (q : VolumeParams) (I : VolumeInput q.n) :
    0 < euclideanVolume I := by
  unfold euclideanVolume
  apply ENNReal.toReal_pos
  · exact (lt_of_lt_of_le
      (Metric.measure_closedBall_pos volume (0 : AmbientSpace q.n) zero_lt_one)
      (measure_mono I.unitBall_subset)).ne'
  · exact I.body.isCompact.measure_lt_top.ne

/-- Exact Gaussian ratios telescope from the first to the last variance. -/
theorem coolingGaussianRatios_telescopes
    (q : VolumeParams) (I : VolumeInput q.n) (a : ℝ) (rest : List ℝ)
    (hpositive : ∀ sigma2 ∈ a :: rest, 0 < sigma2) :
    gaussianIntegral (I.body : Set (AmbientSpace q.n)) a *
        adjacentRatioProduct
          (fun sigma2 => gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2)
          (a :: rest) =
      gaussianIntegral (I.body : Set (AmbientSpace q.n))
        ((a :: rest).getLast (by simp)) := by
  apply adjacentRatioProduct_telescopes
  intro sigma2 hsigma2
  exact (gaussianIntegral_pos q I (hpositive sigma2 hsigma2)).ne'

/-- The last exact Gaussian-to-uniform ratio cancels the terminal partition function. -/
theorem gaussianToUniformRatio_cancels
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 *
        (euclideanVolume I /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2) =
      euclideanVolume I := by
  field_simp [(gaussianIntegral_pos q I hsigma2).ne']

/-- With exact phase ratios, Figure 1 differs from true volume only by the
replacement of the restricted starting integral by its known full-space value. -/
theorem exactCoolingBridge
    (q : VolumeParams) (I : VolumeInput q.n) (S : VolumeCoolingSchedule q) :
    initialGaussianIntegral q *
          adjacentRatioProduct
            (fun sigma2 => gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2)
            S.variances *
          (euclideanVolume I /
            gaussianIntegral (I.body : Set (AmbientSpace q.n)) (terminalVariance q)) =
      (initialGaussianIntegral q /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) (initialVariance q)) *
        euclideanVolume I := by
  obtain ⟨a, rest, hvars⟩ := List.exists_cons_of_ne_nil S.nonempty
  have hstart : a = initialVariance q := by
    have hs := S.start
    rw [hvars] at hs
    simpa using hs
  have hfinish : (a :: rest).getLast (by simp) = terminalVariance q := by
    have hf := S.finish
    rw [hvars] at hf
    rw [List.getLast?_eq_some_getLast (by simp)] at hf
    exact Option.some.inj hf
  have hpositive : ∀ sigma2 ∈ a :: rest, 0 < sigma2 := by
    intro sigma2 hsigma2
    exact S.positive sigma2 (hvars ▸ hsigma2)
  have htele := coolingGaussianRatios_telescopes q I a rest hpositive
  have hfinish' : (initialVariance q :: rest).getLast (by simp) = terminalVariance q := by
    simpa [hstart] using hfinish
  rw [hstart, hfinish'] at htele
  rw [hvars, hstart]
  have hinitial := (gaussianIntegral_pos q I (initialVariance_pos q)).ne'
  have hterminalVariance : 0 < terminalVariance q := by
    unfold terminalVariance
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hterminal := (gaussianIntegral_pos q I hterminalVariance).ne'
  field_simp [hinitial, hterminal]
  linear_combination initialGaussianIntegral q * euclideanVolume I * htele

/-- Multiplying a relative approximation to a positive normalizer by an exact
nonnegative target-to-normalizer ratio preserves the same relative error. -/
theorem relativeApprox_div_mul {eps z estimate target : ℝ}
    (hz : 0 < z) (htarget : 0 ≤ target)
    (happrox : RelativeApprox eps z estimate) :
    RelativeApprox eps target ((estimate / z) * target) := by
  unfold RelativeApprox Arlib.relErr at happrox ⊢
  constructor
  · calc
      (1 - eps) * target = (((1 - eps) * z) / z) * target := by
        field_simp
      _ ≤ (estimate / z) * target := by
        exact mul_le_mul_of_nonneg_right
          ((div_le_div_iff_of_pos_right hz).2 happrox.1) htarget
  · calc
      (estimate / z) * target ≤ (((1 + eps) * z) / z) * target := by
        exact mul_le_mul_of_nonneg_right
          ((div_le_div_iff_of_pos_right hz).2 happrox.2) htarget
      _ = (1 + eps) * target := by
        field_simp

/-- The exact-ratio version of Figure 1 inherits precisely the initial-tail
relative error and no additional deterministic error. -/
theorem exactCoolingBridge_relativeApprox
    (q : VolumeParams) (I : VolumeInput q.n) (S : VolumeCoolingSchedule q)
    (hinitial : RelativeApprox (q.eps / 32)
      (gaussianIntegral (I.body : Set (AmbientSpace q.n)) (initialVariance q))
      (initialGaussianIntegral q)) :
    RelativeApprox (q.eps / 32) (euclideanVolume I)
      (initialGaussianIntegral q *
          adjacentRatioProduct
            (fun sigma2 => gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2)
            S.variances *
          (euclideanVolume I /
            gaussianIntegral (I.body : Set (AmbientSpace q.n)) (terminalVariance q))) := by
  rw [exactCoolingBridge q I S]
  exact relativeApprox_div_mul
    (gaussianIntegral_pos q I (initialVariance_pos q))
    (euclideanVolume_pos q I).le hinitial

/-- Importance reweighting by one Gaussian phase has exactly the adjacent
partition-function integral. This is the deterministic expectation identity
behind every ratio estimator in Figure 1. -/
theorem gaussianRatio_weightedIntegral
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (_hsigma2 : 0 < sigma2) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x *
          gaussianDensity sigma2 x) =
      gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  rw [gaussianIntegral_eq_setIntegral hK]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hK] with x hx
  simp only [gaussianRatioSample, unnormGaussian, Set.indicator_of_mem hx]
  rw [gaussianDensity_eq, gaussianDensity_eq]
  field_simp [(Real.exp_pos _).ne']

/-- Squaring an adjacent Gaussian importance weight produces another Gaussian
integral at the harmonic effective variance `sigma2*tau2/(2*sigma2-tau2)`.
This is the exact algebraic identity used by both CV18 ratio-moment regimes. -/
theorem gaussianRatio_secondMomentIntegral
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x ^ 2 *
          gaussianDensity sigma2 x) =
      gaussianIntegral (I.body : Set (AmbientSpace q.n))
        (sigma2 * tau2 / (2 * sigma2 - tau2)) := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  rw [gaussianIntegral_eq_setIntegral hK]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hK] with x hx
  simp only [gaussianRatioSample, unnormGaussian, Set.indicator_of_mem hx]
  rw [gaussianDensity_eq, gaussianDensity_eq]
  rw [div_pow]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.exp_sub, ← Real.exp_add]
  congr 1
  field_simp [(Real.exp_pos _).ne', hsigma2.ne', htau2.ne']
  ring

/-- Cubing an adjacent Gaussian importance weight produces the Gaussian
integral at effective variance `sigma2*tau2/(3*sigma2-2*tau2)`.

For the fixed-rate schedule this variance remains positive even in dimension
three, unlike the fourth-moment effective variance.  This is the exact moment
identity needed by the `L³` treatment of the low-dimensional phase. -/
theorem gaussianRatio_thirdMomentIntegral
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x ^ 3 *
          gaussianDensity sigma2 x) =
      gaussianIntegral (I.body : Set (AmbientSpace q.n))
        (sigma2 * tau2 / (3 * sigma2 - 2 * tau2)) := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  rw [gaussianIntegral_eq_setIntegral hK]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hK] with x hx
  simp only [gaussianRatioSample, unnormGaussian, Set.indicator_of_mem hx]
  rw [gaussianDensity_eq, gaussianDensity_eq]
  rw [div_pow]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.exp_sub, ← Real.exp_add]
  congr 1
  field_simp [(Real.exp_pos _).ne', hsigma2.ne', htau2.ne']
  ring

/-- The normalized first moment of an exact Gaussian ratio is the ratio of its
two partition functions. -/
theorem gaussianRatio_mean_eq
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x *
          gaussianDensity sigma2 x) /
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 =
      gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 /
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 := by
  rw [gaussianRatio_weightedIntegral q I hsigma2]

/-- The relative second moment of an exact phase ratio is the three-partition-
function quotient used in the paper's fixed and accelerated variance bounds. -/
theorem gaussianRatio_relativeSecondMoment_eq
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    ((∫ x in (I.body : Set (AmbientSpace q.n)),
          gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x ^ 2 *
            gaussianDensity sigma2 x) /
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2) /
        (gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2) ^ 2 =
      gaussianIntegral (I.body : Set (AmbientSpace q.n))
          (sigma2 * tau2 / (2 * sigma2 - tau2)) *
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 ^ 2 := by
  rw [gaussianRatio_secondMomentIntegral q I hsigma2 htau2]
  have hs := (gaussianIntegral_pos q I hsigma2).ne'
  have ht := (gaussianIntegral_pos q I htau2).ne'
  field_simp [hs, ht]

/-- The normalized relative third moment of an exact phase ratio is the
corresponding three-partition-function quotient. -/
theorem gaussianRatio_relativeThirdMoment_eq
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    ((∫ x in (I.body : Set (AmbientSpace q.n)),
          gaussianRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 tau2 x ^ 3 *
            gaussianDensity sigma2 x) /
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2) /
        (gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2) ^ 3 =
      gaussianIntegral (I.body : Set (AmbientSpace q.n))
          (sigma2 * tau2 / (3 * sigma2 - 2 * tau2)) *
        gaussianIntegral (I.body : Set (AmbientSpace q.n)) sigma2 ^ 2 /
          gaussianIntegral (I.body : Set (AmbientSpace q.n)) tau2 ^ 3 := by
  rw [gaussianRatio_thirdMomentIntegral q I hsigma2 htau2]
  have hs := (gaussianIntegral_pos q I hsigma2).ne'
  have ht := (gaussianIntegral_pos q I htau2).ne'
  field_simp [hs, ht]

/-- Reweighting the terminal Gaussian by the reciprocal density has exactly
Lebesgue volume as its weighted integral. -/
theorem uniformRatio_weightedIntegral
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (_hsigma2 : 0 < sigma2) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        uniformRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 x *
          gaussianDensity sigma2 x) = euclideanVolume I := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  calc
    (∫ x in (I.body : Set (AmbientSpace q.n)),
        uniformRatioSample (I.body : Set (AmbientSpace q.n)) sigma2 x *
          gaussianDensity sigma2 x) =
        ∫ _x in (I.body : Set (AmbientSpace q.n)), (1 : ℝ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem hK] with x hx
      simp only [uniformRatioSample, Set.indicator_of_mem hx]
      rw [gaussianDensity_eq, ← Real.exp_add]
      rw [show ‖x‖ ^ 2 / (2 * sigma2) + -‖x‖ ^ 2 / (2 * sigma2) = 0 by ring]
      exact Real.exp_zero
    _ = euclideanVolume I := by
      rw [MeasureTheory.setIntegral_one_eq_measureReal]
      rfl

end ArlibCommunity.Algorithms.CV18
