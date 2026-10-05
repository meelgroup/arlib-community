/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableTransfer

/-!
# Bounded-observable transfer with almost-everywhere support

The executable cooling laws are supported on bounded ratio observations, but
the corresponding observable is not bounded on the entire ambient type.  This
module packages the standard clamp argument which turns almost-everywhere
support under both laws into the global bounds required by total-variation
moment transfer.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A measurable real observable which is almost everywhere in `[0, B]` is in
`L²` under a finite measure. -/
theorem memLp_two_of_ae_nonnegative_le
    {S : Type*} [MeasurableSpace S] {mu : Measure S} [IsFiniteMeasure mu]
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hfB : ∀ᵐ x ∂mu, f x ≤ B) :
    MemLp f 2 mu := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [hf0, hfB] with x hx0 hxB
  rw [Real.norm_eq_abs, abs_of_nonneg hx0]
  exact hxB

/-- The small-TV moment lemma remains valid when boundedness is known only
almost everywhere under each of the two probability laws. -/
theorem Arlib.TVLe.positive_mean_and_second_le_four_of_ae
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0mu : ∀ᵐ x ∂mu, 0 ≤ f x) (hfBmu : ∀ᵐ x ∂mu, f x ≤ B)
    (hf0nu : ∀ᵐ x ∂nu, 0 ≤ f x) (hfBnu : ∀ᵐ x ∂nu, f x ≤ B)
    {idealMean : ℝ} (hidealMean : idealMean = ∫ x, f x ∂nu)
    (hidealMeanPos : 0 < idealMean)
    (hidealSecond : (∫ x, f x ^ 2 ∂nu) ≤ 2 * idealMean ^ 2)
    (hmeanError : B * epsilon.toReal ≤ idealMean / 8)
    (hsecondError : B ^ 2 * epsilon.toReal ≤ idealMean ^ 2 / 8) :
    0 < ∫ x, f x ∂mu ∧
      (∫ x, f x ^ 2 ∂mu) ≤ 4 * (∫ x, f x ∂mu) ^ 2 := by
  let g : S → ℝ := fun x => min (max 0 (f x)) B
  have hg : Measurable g := (measurable_const.max hf).min measurable_const
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    exact le_min (le_max_left _ _) hB.le
  have hgB : ∀ x, g x ≤ B := fun x => min_le_right _ _
  have hgeqmu : ∀ᵐ x ∂mu, g x = f x := by
    filter_upwards [hf0mu, hfBmu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  have hgeqnu : ∀ᵐ x ∂nu, g x = f x := by
    filter_upwards [hf0nu, hfBnu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  have hmeanMu : (∫ x, g x ∂mu) = ∫ x, f x ∂mu :=
    integral_congr_ae hgeqmu
  have hmeanNu : (∫ x, g x ∂nu) = ∫ x, f x ∂nu :=
    integral_congr_ae hgeqnu
  have hsecondMu : (∫ x, g x ^ 2 ∂mu) = ∫ x, f x ^ 2 ∂mu :=
    integral_congr_ae (by
      filter_upwards [hgeqmu] with x hx
      rw [hx])
  have hsecondNu : (∫ x, g x ^ 2 ∂nu) = ∫ x, f x ^ 2 ∂nu :=
    integral_congr_ae (by
      filter_upwards [hgeqnu] with x hx
      rw [hx])
  have hresult := Arlib.TVLe.positive_mean_and_second_le_four h hepsilon
    hg hB hg0 hgB (idealMean := idealMean)
    (hidealMean.trans hmeanNu.symm) hidealMeanPos
    (hsecondNu.trans_le hidealSecond) hmeanError hsecondError
  rw [hmeanMu, hsecondMu] at hresult
  exact hresult

/-- At the exact-chance budget used by Figure One, support in
`[0, exp (1/2)]`, ideal mean at least one, and ideal relative second moment at
most two suffice for the executable raw moment bound. -/
theorem Arlib.TVLe.positive_mean_and_second_le_four_of_ae_expHalf
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≤ ENNReal.ofReal (1 / 64 : ℝ))
    {f : S → ℝ} (hf : Measurable f)
    (hf0mu : ∀ᵐ x ∂mu, 0 ≤ f x)
    (hfBmu : ∀ᵐ x ∂mu, f x ≤ Real.exp (1 / 2))
    (hf0nu : ∀ᵐ x ∂nu, 0 ≤ f x)
    (hfBnu : ∀ᵐ x ∂nu, f x ≤ Real.exp (1 / 2))
    {idealMean : ℝ} (hidealMean : idealMean = ∫ x, f x ∂nu)
    (hidealMeanOne : 1 ≤ idealMean)
    (hidealSecond : (∫ x, f x ^ 2 ∂nu) ≤ 2 * idealMean ^ 2) :
    0 < ∫ x, f x ∂mu ∧
      (∫ x, f x ^ 2 ∂mu) ≤ 4 * (∫ x, f x ∂mu) ^ 2 := by
  have hepsilonTop : epsilon ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hepsilon
  have hepsilonReal : epsilon.toReal ≤ 1 / 64 := by
    rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 64)]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hepsilon
  have hexp : Real.exp (1 / 2) ≤ (5 / 3 : ℝ) := by
    convert Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) using 1 <;> norm_num
  have hidealMeanPos : 0 < idealMean := lt_of_lt_of_le zero_lt_one hidealMeanOne
  have hmeanError : Real.exp (1 / 2) * epsilon.toReal ≤ idealMean / 8 := by
    have hepsilon0 : 0 ≤ epsilon.toReal := ENNReal.toReal_nonneg
    have hexp0 := (Real.exp_pos (1 / 2)).le
    nlinarith
  have hsecondError : Real.exp (1 / 2) ^ 2 * epsilon.toReal ≤
      idealMean ^ 2 / 8 := by
    have hepsilon0 : 0 ≤ epsilon.toReal := ENNReal.toReal_nonneg
    have hexp0 := (Real.exp_pos (1 / 2)).le
    have hmeanSq : 1 ≤ idealMean ^ 2 := by nlinarith
    nlinarith [mul_self_le_mul_self hexp0 hexp]
  exact Arlib.TVLe.positive_mean_and_second_le_four_of_ae h hepsilonTop hf
    (Real.exp_pos _) hf0mu hfBmu hf0nu hfBnu hidealMean hidealMeanPos
    hidealSecond hmeanError hsecondError

#print axioms memLp_two_of_ae_nonnegative_le
#print axioms Arlib.TVLe.positive_mean_and_second_le_four_of_ae
#print axioms Arlib.TVLe.positive_mean_and_second_le_four_of_ae_expHalf

end ArlibCommunity.Algorithms.CV18
