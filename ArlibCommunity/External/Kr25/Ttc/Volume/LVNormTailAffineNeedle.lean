/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailLocalizationBridge
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.SharpIsoperimetry

/-!
# Affine-coordinate moment transport for the LV tail needle

The closest-point parameter removes the affine offset from the localized second moment.  This
is the geometric identity needed to feed `LVNormTailHazard` at scale
`sqrt (M-d^2) / ‖e‖`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

variable {n : ℕ}

noncomputable def needleClosestParam (p e : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -(inner ℝ p e) / ‖e‖ ^ 2

noncomputable def needleOffsetSq (p e : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖needleMap p e (needleClosestParam p e)‖ ^ 2

theorem inner_needleMap_closest_direction {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0) :
    inner ℝ (needleMap p e (needleClosestParam p e)) e = 0 := by
  have he2 : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  rw [needleMap_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  unfold needleClosestParam
  field_simp
  ring

/-- Orthogonal decomposition of squared norm along an arbitrary nondegenerate needle. -/
theorem norm_needleMap_sq_closest {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0) (t : ℝ) :
    ‖needleMap p e t‖ ^ 2 = needleOffsetSq p e +
      ‖e‖ ^ 2 * (t - needleClosestParam p e) ^ 2 := by
  let c := needleClosestParam p e
  let q := needleMap p e c
  have hqe : inner ℝ q e = 0 := inner_needleMap_closest_direction he
  have hmap : needleMap p e t = q + (t - c) • e := by
    rw [needleMap_apply]
    dsimp only [q]
    rw [needleMap_apply]
    module
  rw [hmap, norm_add_sq_real, real_inner_smul_right, hqe, mul_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  dsimp only [needleOffsetSq, q, c]
  ring

theorem needleOffsetSq_nonneg (p e : EuclideanSpace ℝ (Fin n)) :
    0 ≤ needleOffsetSq p e := sq_nonneg _

/-- The localized norm moment splits into the offset mass plus a centered scalar moment. -/
theorem intervalIntegral_norm_needleMap_sq_decomp
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    {a b : ℝ} {D : ℝ → ℝ} (hDint : IntervalIntegrable D volume a b) :
    (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
      needleOffsetSq p e * (∫ t in a..b, D t) +
        ‖e‖ ^ 2 * ∫ t in a..b, (t - needleClosestParam p e) ^ 2 * D t := by
  have hsqint : IntervalIntegrable
      (fun t => (t - needleClosestParam p e) ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  rw [show (fun t => ‖needleMap p e t‖ ^ 2 * D t) =
      (fun t => needleOffsetSq p e * D t +
        ‖e‖ ^ 2 * ((t - needleClosestParam p e) ^ 2 * D t)) by
    funext t
    rw [norm_needleMap_sq_closest he]
    ring]
  rw [intervalIntegral.integral_add (hDint.const_mul _) (hsqint.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The two localized set integrals supply a genuine positive profile mass and an exact
unnormalized norm-moment identity.  Keeping this as an interval-integral statement makes it
directly consumable by the one-dimensional hazard estimates. -/
theorem localizedNeedle_mass_pos_and_normMoment
    {p e : EuclideanSpace ℝ (Fin n)} {a b M c : ℝ} {D : ℝ → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hab : a ≤ b) (hc0 : 0 ≤ c)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b)
    (hqc : Continuous q)
    (hqle : ∀ x, q x ≤
      {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x - c)
    (hmoment : (∫ t in Icc a b, (‖needleMap p e t‖ ^ 2 - M) * D t) = 0)
    (hqpos : 0 < ∫ t in Icc a b, q (needleMap p e t) * D t) :
    0 < ∫ t in a..b, D t ∧
      (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
        M * ∫ t in a..b, D t := by
  have hneedle : Continuous (fun t : ℝ => needleMap p e t) := by
    simp_rw [needleMap_apply]
    fun_prop
  have hqint : IntervalIntegrable (fun t => q (needleMap p e t) * D t) volume a b :=
    hDint.continuousOn_mul (hqc.comp hneedle).continuousOn
  have hqpos' : 0 < ∫ t in a..b, q (needleMap p e t) * D t := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact hqpos
  have hqone : ∀ t ∈ Icc a b, q (needleMap p e t) ≤ 1 := by
    intro t ht
    have h := hqle (needleMap p e t)
    by_cases hx : M < ‖needleMap p e t‖ ^ 2
    · have hxmem : needleMap p e t ∈
          {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2} := hx
      rw [indicator_of_mem hxmem] at h
      linarith
    · have hx' : needleMap p e t ∉
          {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2} := by simpa using hx
      rw [indicator_of_notMem hx'] at h
      linarith
  have hmono : (∫ t in a..b, q (needleMap p e t) * D t) ≤ ∫ t in a..b, D t := by
    refine intervalIntegral.integral_mono_on hab hqint hDint ?_
    intro t ht
    exact mul_le_of_le_one_left (hD0 t ht) (hqone t ht)
  have hmass : 0 < ∫ t in a..b, D t := hqpos'.trans_le hmono
  have hnormint : IntervalIntegrable
      (fun t => ‖needleMap p e t‖ ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hmconst : IntervalIntegrable (fun t => M * D t) volume a b := hDint.const_mul M
  have hmoment' : (∫ t in a..b, (‖needleMap p e t‖ ^ 2 - M) * D t) = 0 := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact hmoment
  have hsplit : (∫ t in a..b, (‖needleMap p e t‖ ^ 2 - M) * D t) =
      (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) -
        M * ∫ t in a..b, D t := by
    rw [show (fun t => (‖needleMap p e t‖ ^ 2 - M) * D t) =
        (fun t => ‖needleMap p e t‖ ^ 2 * D t - M * D t) by
      funext t
      ring]
    rw [intervalIntegral.integral_sub hnormint hmconst,
      intervalIntegral.integral_const_mul]
  exact ⟨hmass, by linarith [hmoment', hsplit]⟩

/-- Exact centered scalar moment after affine orthogonalization. -/
theorem localizedNeedle_centeredMoment
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    {a b M : ℝ} {D : ℝ → ℝ} (hDint : IntervalIntegrable D volume a b)
    (hnorm : (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
      M * ∫ t in a..b, D t) :
    ‖e‖ ^ 2 * ∫ t in a..b, (t - needleClosestParam p e) ^ 2 * D t =
      (M - needleOffsetSq p e) * ∫ t in a..b, D t := by
  rw [intervalIntegral_norm_needleMap_sq_decomp he hDint] at hnorm
  linarith

/-- Closest-point coordinate clamped to the actual needle segment. -/
noncomputable def needleSegmentCenter (a b : ℝ) (p e : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max a (min b (needleClosestParam p e))

theorem needleSegmentCenter_mem {a b : ℝ} (hab : a ≤ b)
    (p e : EuclideanSpace ℝ (Fin n)) :
    needleSegmentCenter a b p e ∈ Icc a b := by
  simp [needleSegmentCenter, hab]

/-- Projecting the orthogonal closest-point coordinate onto the parameter interval can only
decrease its squared distance to every parameter in the interval. -/
theorem sq_sub_needleSegmentCenter_le {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (p e : EuclideanSpace ℝ (Fin n)) :
    (t - needleSegmentCenter a b p e) ^ 2 ≤ (t - needleClosestParam p e) ^ 2 := by
  let c := needleClosestParam p e
  rcases lt_or_ge c a with hca | hac
  · have hmin : min b c = c := min_eq_right (hca.le.trans hab)
    have hmax : max a c = a := max_eq_left hca.le
    simp only [needleSegmentCenter, c, hmin, hmax]
    change (t - a) ^ 2 ≤ (t - c) ^ 2
    have hfac : 0 ≤ (a - c) * (2 * t - a - c) :=
      mul_nonneg (by linarith) (by linarith [ht.1])
    nlinarith
  · rcases le_or_gt c b with hcb | hbc
    · simp [needleSegmentCenter, c, min_eq_right hcb, max_eq_right hac]
    · have hmin : min b c = b := min_eq_left hbc.le
      have hmax : max a b = b := max_eq_right hab
      simp only [needleSegmentCenter, c, hmin, hmax]
      change (t - b) ^ 2 ≤ (t - c) ^ 2
      have hfac : 0 ≤ (c - b) * (c + b - 2 * t) :=
        mul_nonneg (by linarith) (by linarith [ht.2])
      nlinarith

theorem norm_needleMap_segmentCenter_sq_le {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b) :
    ‖needleMap p e (needleSegmentCenter a b p e)‖ ^ 2 ≤ ‖needleMap p e t‖ ^ 2 := by
  rw [norm_needleMap_sq_closest he, norm_needleMap_sq_closest he]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖e‖)
  let c := needleClosestParam p e
  rcases lt_or_ge c a with hca | hac
  · have hmin : min b c = c := min_eq_right (hca.le.trans hab)
    have hmax : max a c = a := max_eq_left hca.le
    simp only [needleSegmentCenter, c, hmin, hmax]
    have hfac : 0 ≤ (t - a) * (t + a - 2 * c) :=
      mul_nonneg (by linarith [ht.1]) (by linarith [ht.1])
    nlinarith
  · rcases le_or_gt c b with hcb | hbc
    · simp only [needleSegmentCenter, c, min_eq_right hcb, max_eq_right hac,
        sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact sq_nonneg _
    · have hmin : min b c = b := min_eq_left hbc.le
      have hmax : max a b = b := max_eq_right hab
      simp only [needleSegmentCenter, c, hmin, hmax]
      have hfac : 0 ≤ (b - t) * (2 * c - b - t) :=
        mul_nonneg (by linarith [ht.2]) (by linarith [ht.2])
      nlinarith

/-- The localized scalar variance is bounded at the ambient moment scale `sqrt M /‖e‖`,
with a center that lies on the segment.  This avoids any positivity issue for `M-d²`. -/
theorem localizedNeedle_variance_le_ambientScale
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    {a b M : ℝ} {D : ℝ → ℝ} (hab : a ≤ b)
    (hM : 0 ≤ M) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b)
    (hnorm : (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
      M * ∫ t in a..b, D t) :
    (∫ t in a..b, (t - needleSegmentCenter a b p e) ^ 2 * D t) ≤
      (Real.sqrt M / ‖e‖) ^ 2 * ∫ t in a..b, D t := by
  have heNorm : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hmass0 : 0 ≤ ∫ t in a..b, D t :=
    intervalIntegral.integral_nonneg hab hD0
  have hcint : IntervalIntegrable
      (fun t => (t - needleClosestParam p e) ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hzint : IntervalIntegrable
      (fun t => (t - needleSegmentCenter a b p e) ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hmono : (∫ t in a..b, (t - needleSegmentCenter a b p e) ^ 2 * D t) ≤
      ∫ t in a..b, (t - needleClosestParam p e) ^ 2 * D t := by
    refine intervalIntegral.integral_mono_on hab hzint hcint ?_
    intro t ht
    exact mul_le_mul_of_nonneg_right (sq_sub_needleSegmentCenter_le hab ht p e) (hD0 t ht)
  have hcenter := localizedNeedle_centeredMoment he hDint hnorm
  have hoff0 := needleOffsetSq_nonneg p e
  have hsqrt : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM
  have hV : (∫ t in a..b, (t - needleClosestParam p e) ^ 2 * D t) ≤
      M / ‖e‖ ^ 2 * ∫ t in a..b, D t := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos heNorm)).2
    nlinarith [mul_nonneg hoff0 hmass0]
  calc
    (∫ t in a..b, (t - needleSegmentCenter a b p e) ^ 2 * D t) ≤
        ∫ t in a..b, (t - needleClosestParam p e) ^ 2 * D t := hmono
    _ ≤ M / ‖e‖ ^ 2 * ∫ t in a..b, D t := hV
    _ = (Real.sqrt M / ‖e‖) ^ 2 * ∫ t in a..b, D t := by
      rw [div_pow, hsqrt]

/-- The clamped closest point has norm at most the root-mean-square radius of a positive
localized profile. -/
theorem norm_needleMap_segmentCenter_le_sqrtMoment
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    {a b M : ℝ} {D : ℝ → ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDint : IntervalIntegrable D volume a b)
    (hmass : 0 < ∫ t in a..b, D t)
    (hnorm : (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
      M * ∫ t in a..b, D t) :
    ‖needleMap p e (needleSegmentCenter a b p e)‖ ≤ Real.sqrt M := by
  have hconstint : IntervalIntegrable
      (fun t => ‖needleMap p e (needleSegmentCenter a b p e)‖ ^ 2 * D t) volume a b :=
    hDint.const_mul _
  have hnormint : IntervalIntegrable
      (fun t => ‖needleMap p e t‖ ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by
      simp_rw [needleMap_apply]
      fun_prop))
  have hmono := intervalIntegral.integral_mono_on hab hconstint hnormint (fun t ht =>
    mul_le_mul_of_nonneg_right (norm_needleMap_segmentCenter_sq_le he hab ht) (hD0 t ht))
  rw [intervalIntegral.integral_const_mul, hnorm] at hmono
  have hsquare : ‖needleMap p e (needleSegmentCenter a b p e)‖ ^ 2 ≤ M := by
    nlinarith
  nlinarith [Real.sq_sqrt hM, norm_nonneg (needleMap p e (needleSegmentCenter a b p e)),
    Real.sqrt_nonneg M]

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.norm_needleMap_sq_closest
#print axioms Ttc.CVAdaptive.intervalIntegral_norm_needleMap_sq_decomp
#print axioms Ttc.CVAdaptive.localizedNeedle_mass_pos_and_normMoment
#print axioms Ttc.CVAdaptive.localizedNeedle_centeredMoment
#print axioms Ttc.CVAdaptive.sq_sub_needleSegmentCenter_le
#print axioms Ttc.CVAdaptive.localizedNeedle_variance_le_ambientScale
#print axioms Ttc.CVAdaptive.norm_needleMap_segmentCenter_le_sqrtMoment
