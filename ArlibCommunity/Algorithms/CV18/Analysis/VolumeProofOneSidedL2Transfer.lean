/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyTVL2

/-!
# One-sided L2 transfer from total variation

For a lower bound on an executable nonnegative mean, no warm domination of
the executable law is needed.  Truncate the observable, use total variation
on the truncation, and charge only the ideal law's upper tail.  This is useful
for killed CV18 samples, whose failure atom has observable value zero.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A TV comparison gives a one-sided mean lower bound using only the
reference law's second moment. -/
theorem Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfmemMu : MemLp f 2 mu) (hfmemNu : MemLp f 2 nu)
    {T : ℝ} (hT : 0 < T) :
    (∫ x, f x ∂nu) -
        (epsilon.toReal * T + (∫ x, f x ^ 2 ∂nu) / T) ≤
      ∫ x, f x ∂mu := by
  let cut : S → ℝ := fun x => min (f x) T
  let g : S → ℝ := fun x => cut x / T
  have hfintMu : Integrable f mu := hfmemMu.integrable (by norm_num)
  have hfintNu : Integrable f nu := hfmemNu.integrable (by norm_num)
  have hcutMeas : Measurable cut := hf.min measurable_const
  have hcut0 : ∀ x, 0 ≤ cut x := fun x => le_min (hf0 x) hT.le
  have hcutT : ∀ x, cut x ≤ T := fun x => min_le_right _ _
  have hcutIntMu : Integrable cut mu := by
    refine Integrable.mono' (integrable_const T)
      hcutMeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hcut0 x)]
    exact hcutT x
  have hcutIntNu : Integrable cut nu := by
    refine Integrable.mono' (integrable_const T)
      hcutMeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hcut0 x)]
    exact hcutT x
  have hgMeas : Measurable g := hcutMeas.div_const T
  have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (hcut0 x) hT.le
  have hg1 : ∀ x, g x ≤ 1 := fun x => (div_le_one hT).2 (hcutT x)
  have hscaled := htv.integral_le hepsilon hgMeas hg0 hg1
  have hcutEqMu : (∫ x, cut x ∂mu) = T * ∫ x, g x ∂mu := by
    rw [show cut = fun x => T * g x by
      funext x
      dsimp [g]
      field_simp [hT.ne']]
    exact integral_const_mul T g
  have hcutEqNu : (∫ x, cut x ∂nu) = T * ∫ x, g x ∂nu := by
    rw [show cut = fun x => T * g x by
      funext x
      dsimp [g]
      field_simp [hT.ne']]
    exact integral_const_mul T g
  have hmiddle : (∫ x, cut x ∂nu) - epsilon.toReal * T ≤
      ∫ x, cut x ∂mu := by
    have hdiff : |(∫ x, cut x ∂mu) - ∫ x, cut x ∂nu| ≤
        epsilon.toReal * T := by
      rw [hcutEqMu, hcutEqNu, ← mul_sub, abs_mul, abs_of_pos hT,
        mul_comm]
      exact mul_le_mul_of_nonneg_right hscaled hT.le
    linarith [neg_abs_le ((∫ x, cut x ∂mu) - ∫ x, cut x ∂nu)]
  have htailPoint : ∀ x, 0 ≤ f x - cut x := fun x =>
    sub_nonneg.mpr (min_le_left _ _)
  have htailSq : ∀ x, f x - cut x ≤ f x ^ 2 / T := by
    intro x
    dsimp [cut]
    by_cases h : f x ≤ T
    · rw [min_eq_left h]
      simpa using div_nonneg (sq_nonneg (f x)) hT.le
    · rw [min_eq_right (le_of_not_ge h), le_div_iff₀ hT]
      nlinarith [sq_nonneg (f x), hf0 x]
  have hsqIntNu : Integrable (fun x => f x ^ 2) nu :=
    hfmemNu.integrable_sq
  have htailIntNu : Integrable (fun x => f x - cut x) nu :=
    hfintNu.sub hcutIntNu
  have htail : (∫ x, f x ∂nu) - ∫ x, cut x ∂nu ≤
      (∫ x, f x ^ 2 ∂nu) / T := by
    rw [← integral_sub hfintNu hcutIntNu]
    calc
      (∫ x, f x - cut x ∂nu) ≤
          ∫ x, f x ^ 2 / T ∂nu := by
        apply integral_mono htailIntNu (hsqIntNu.div_const T)
        exact htailSq
      _ = (∫ x, f x ^ 2 ∂nu) / T := integral_div T _
  have hcutLe : (∫ x, cut x ∂mu) ≤ ∫ x, f x ∂mu := by
    apply integral_mono hcutIntMu hfintMu
    intro x
    exact min_le_left _ _
  linarith

/-- Square-root optimization of the one-sided transfer bound. -/
theorem Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfmemMu : MemLp f 2 mu) (hfmemNu : MemLp f 2 nu)
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hepsEta : epsilon.toReal ≤ eta ^ 2)
    (hsecond : (∫ x, f x ^ 2 ∂nu) ≤ R ^ 2) :
    (∫ x, f x ∂nu) - 2 * eta * R ≤ ∫ x, f x ∂mu := by
  have hbase := Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment
    htv hepsilon hf hf0 hfmemMu hfmemNu (T := R / eta) (div_pos hR heta)
  have hsq0 : 0 ≤ ∫ x, f x ^ 2 ∂nu :=
    integral_nonneg fun x => sq_nonneg (f x)
  have hfirst : epsilon.toReal * (R / eta) ≤ eta * R := by
    rw [show epsilon.toReal * (R / eta) =
      (epsilon.toReal * R) / eta by ring]
    apply (div_le_iff₀ heta).2
    have hmul := mul_le_mul_of_nonneg_right hepsEta hR.le
    nlinarith
  have htail : (∫ x, f x ^ 2 ∂nu) / (R / eta) ≤ eta * R := by
    calc
      (∫ x, f x ^ 2 ∂nu) / (R / eta) ≤ R ^ 2 / (R / eta) :=
        div_le_div_of_nonneg_right hsecond (div_pos hR heta).le
      _ = eta * R := by field_simp [heta.ne', hR.ne']
  linarith

#print axioms Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment
#print axioms Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt

end ArlibCommunity.Algorithms.CV18
