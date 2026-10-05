/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Approximate independence for the CV18 product argument

This file formalizes the probability lemmas used in Cousins--Vempala Lemmas
7.12--7.17.  Their dependence coefficient is the strong-mixing coefficient

`sup |P(X in A, Y in B) - P(X in A) P(Y in B)|`,

with the supremum left in the consumer-friendly bounded form below.  This is
strictly weaker than total-variation closeness of the joint law to the product
law, and that distinction matters for the warm-start argument.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Set

variable {Omega S T U V : Type*}
  [MeasurableSpace Omega] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [MeasurableSpace V]

/-- The Cousins--Vempala approximate-independence coefficient in bounded
form.  `ApproxIndepFun epsilon X Y mu` says that every measurable rectangle in
the joint law differs from the product of its marginals by at most `epsilon`.
-/
def ApproxIndepFun (epsilon : ℝ) (X : Omega -> S) (Y : Omega -> T)
    (mu : Measure Omega) : Prop :=
  forall A : Set S, MeasurableSet A -> forall B : Set T, MeasurableSet B ->
    |mu.real (X ⁻¹' A ∩ Y ⁻¹' B) -
      mu.real (X ⁻¹' A) * mu.real (Y ⁻¹' B)| <= epsilon

/-- An approximate-independence estimate remains true after enlarging its
error budget. -/
theorem ApproxIndepFun.mono {epsilon epsilon' : ℝ}
    {X : Omega -> S} {Y : Omega -> T} {mu : Measure Omega}
    (h : ApproxIndepFun epsilon X Y mu) (hle : epsilon <= epsilon') :
    ApproxIndepFun epsilon' X Y mu := by
  intro A hA B hB
  exact (h A hA B hB).trans hle

/-- CV18 Lemma 7.12: measurable postprocessing cannot increase the
approximate-independence coefficient. -/
theorem ApproxIndepFun.comp {epsilon : ℝ} {X : Omega -> S} {Y : Omega -> T}
    {mu : Measure Omega} (h : ApproxIndepFun epsilon X Y mu)
    {f : S -> U} {g : T -> V} (hf : Measurable f) (hg : Measurable g) :
    ApproxIndepFun epsilon (f ∘ X) (g ∘ Y) mu := by
  intro A hA B hB
  simpa [Function.comp_def, preimage_preimage] using
    h (f ⁻¹' A) (hf hA) (g ⁻¹' B) (hg hB)

/-- Approximate independence is symmetric. -/
theorem ApproxIndepFun.symm {epsilon : ℝ} {X : Omega -> S} {Y : Omega -> T}
    {mu : Measure Omega} (h : ApproxIndepFun epsilon X Y mu) :
    ApproxIndepFun epsilon Y X mu := by
  intro B hB A hA
  simpa [inter_comm, mul_comm, abs_sub_comm] using h A hA B hB

/-- As observed after equation (4) of Lovasz--Vempala [24], it suffices to
check approximate independence on left events of probability at least one
half.  The complementary rectangle has the same covariance with opposite
sign. -/
theorem ApproxIndepFun.of_large_left
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {epsilon : ℝ} {X : Omega -> S} {Y : Omega -> T}
    (hX : Measurable X) (hY : Measurable Y)
    (hlarge : forall A : Set S, MeasurableSet A ->
      1 / 2 <= mu.real (X ⁻¹' A) ->
      forall B : Set T, MeasurableSet B ->
        |mu.real (X ⁻¹' A ∩ Y ⁻¹' B) -
          mu.real (X ⁻¹' A) * mu.real (Y ⁻¹' B)| <= epsilon) :
    ApproxIndepFun epsilon X Y mu := by
  intro A hA B hB
  let EA : Set Omega := X ⁻¹' A
  let EB : Set Omega := Y ⁻¹' B
  have hEA : MeasurableSet EA := hX hA
  have hEB : MeasurableSet EB := hY hB
  by_cases hhalf : 1 / 2 <= mu.real EA
  · exact hlarge A hA hhalf B hB
  · have hhalfCompl : 1 / 2 <= mu.real EAᶜ := by
      have hsum := probReal_add_probReal_compl (μ := mu) hEA
      rw [not_le] at hhalf
      linarith
    have hcomp := hlarge Aᶜ hA.compl (by simpa [EA] using hhalfCompl) B hB
    have hpreComp : X ⁻¹' Aᶜ = EAᶜ := by simp [EA]
    have hinterComp : X ⁻¹' Aᶜ ∩ Y ⁻¹' B = EB \ EA := by
      ext omega
      simp [EA, EB, and_comm]
    have hEACompl : mu.real EAᶜ = 1 - mu.real EA := by
      rw [measureReal_compl hEA, probReal_univ]
    have hinter : mu.real (EB \ EA) =
        mu.real EB - mu.real (EA ∩ EB) := by
      have hsub := measureReal_sdiff (μ := mu) (s₁ := EB) (s₂ := EA ∩ EB)
        inter_subset_right (hEA.inter hEB) (measure_ne_top mu EB)
      rw [show EB \ (EA ∩ EB) = EB \ EA by ext omega; simp] at hsub
      exact hsub
    change |mu.real (EAᶜ ∩ EB) - mu.real EAᶜ * mu.real EB| <= epsilon at hcomp
    rw [show EAᶜ ∩ EB = EB \ EA by ext omega; simp [and_comm],
      hEACompl, hinter] at hcomp
    change |mu.real (EA ∩ EB) - mu.real EA * mu.real EB| <= epsilon
    rw [show (mu.real EB - mu.real (EA ∩ EB) -
        (1 - mu.real EA) * mu.real EB) =
          -(mu.real (EA ∩ EB) - mu.real EA * mu.real EB) by ring] at hcomp
    simpa [abs_sub_comm] using hcomp

/-- The real mass of a measurable set under a nonnegative real density is
the corresponding set integral. -/
theorem withDensity_ofReal_real_apply_eq_setIntegral
    (mu : Measure Omega) {Y : Omega -> ℝ} (hY : Measurable Y)
    (hY0 : forall omega, 0 <= Y omega) {A : Set Omega}
    (hA : MeasurableSet A) :
    (mu.withDensity (fun omega => ENNReal.ofReal (Y omega))).real A =
      ∫ omega in A, Y omega ∂mu := by
  rw [measureReal_def, withDensity_apply _ hA]
  rw [← integral_toReal
    (hY.ennreal_ofReal.aemeasurable.restrict)
    (Filter.Eventually.of_forall fun omega => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal (hY0 omega)]

/-- The real-valued tail function is integrable on every bounded interval. -/
theorem integrableOn_measureReal_tail_Ioc
    (mu : Measure Omega) [IsFiniteMeasure mu] (f : Omega -> ℝ) (b : ℝ) :
    IntegrableOn (fun t : ℝ => mu.real {omega | t <= f omega})
      (Ioc (0 : ℝ) b) volume := by
  have hconst : IntegrableOn (fun _ : ℝ => (mu Set.univ).toReal)
      (Ioc (0 : ℝ) b) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  refine Integrable.mono' hconst
    ((Arlib.measurable_measureReal_tail mu f).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_mono (subset_univ _) (measure_ne_top mu Set.univ)

/-- Rectangle approximate independence controls the mass of an `X`-tail
under the measure weighted by a bounded nonnegative `Y`.  This is the inner
layer-cake step in CV18 Lemma 7.13. -/
theorem abs_withDensity_tail_sub_mul_univ_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega -> ℝ} (hX : Measurable X) (hY : Measurable Y)
    {a b epsilon : ℝ} (_ha : 0 <= a) (hb : 0 <= b) (_hepsilon : 0 <= epsilon)
    (_hX0 : forall omega, 0 <= X omega) (_hXa : forall omega, X omega <= a)
    (hY0 : forall omega, 0 <= Y omega) (hYb : forall omega, Y omega <= b)
    (hind : ApproxIndepFun epsilon X Y mu) (s : ℝ) :
    let nu := mu.withDensity (fun omega => ENNReal.ofReal (Y omega))
    |nu.real {omega | s <= X omega} -
        mu.real {omega | s <= X omega} * nu.real Set.univ| <= epsilon * b := by
  dsimp only
  let A : Set Omega := {omega | s <= X omega}
  let nu := mu.withDensity (fun omega => ENNReal.ofReal (Y omega))
  have hA : MeasurableSet A := measurableSet_le measurable_const hX
  have hYint : Integrable Y mu := by
    refine (integrable_const b).mono' hY.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 omega)]
    exact hYb omega
  have hYintA : Integrable Y (mu.restrict A) :=
    hYint.mono_measure Measure.restrict_le_self
  have hYlayerA :
      (∫ omega in A, Y omega ∂mu) =
        ∫ t in Ioc (0 : ℝ) b,
          mu.real (A ∩ {omega | t <= Y omega}) := by
    have h := hYintA.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hY0)
      (Filter.Eventually.of_forall hYb)
    simpa only [measureReal_def,
      Measure.restrict_apply (measurableSet_le measurable_const hY), inter_comm] using h
  have hYlayer :
      (∫ omega, Y omega ∂mu) =
        ∫ t in Ioc (0 : ℝ) b, mu.real {omega | t <= Y omega} :=
    hYint.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hY0)
      (Filter.Eventually.of_forall hYb)
  have hnuA : nu.real A = ∫ omega in A, Y omega ∂mu := by
    simpa [nu] using
      withDensity_ofReal_real_apply_eq_setIntegral mu hY hY0 hA
  have hnuUniv : nu.real Set.univ = ∫ omega, Y omega ∂mu := by
    simpa [nu] using
      withDensity_ofReal_real_apply_eq_setIntegral mu hY hY0 MeasurableSet.univ
  let jointTail : ℝ -> ℝ := fun t =>
    mu.real (A ∩ {omega | t <= Y omega})
  let productTail : ℝ -> ℝ := fun t =>
    mu.real A * mu.real {omega | t <= Y omega}
  have hjointInt : IntegrableOn jointTail (Ioc (0 : ℝ) b) := by
    have hbase := integrableOn_measureReal_tail_Ioc (mu.restrict A) Y b
    simpa only [jointTail, measureReal_def,
      Measure.restrict_apply (measurableSet_le measurable_const hY), inter_comm] using hbase
  have hproductInt : IntegrableOn productTail (Ioc (0 : ℝ) b) := by
    change Integrable
      (fun t => mu.real A * mu.real {omega | t <= Y omega})
      (volume.restrict (Ioc (0 : ℝ) b))
    exact (integrableOn_measureReal_tail_Ioc mu Y b).const_mul (mu.real A)
  have hpoint : forall t,
      |jointTail t - productTail t| <= epsilon := by
    intro t
    simpa [jointTail, productTail, A] using
      hind {x : ℝ | s <= x} (measurableSet_le measurable_const measurable_id)
        {y : ℝ | t <= y} (measurableSet_le measurable_const measurable_id)
  rw [show {omega | s <= X omega} = A by rfl, hnuA, hnuUniv,
    hYlayerA, hYlayer]
  change |(∫ t in Ioc (0 : ℝ) b, jointTail t) -
      mu.real A * (∫ t in Ioc (0 : ℝ) b,
        mu.real {omega | t <= Y omega})| <= epsilon * b
  rw [← integral_const_mul]
  change |(∫ t in Ioc (0 : ℝ) b, jointTail t) -
      (∫ t in Ioc (0 : ℝ) b, productTail t)| <= epsilon * b
  rw [← integral_sub hjointInt hproductInt]
  calc
    |∫ t in Ioc (0 : ℝ) b, jointTail t - productTail t| <=
        ∫ t in Ioc (0 : ℝ) b, |jointTail t - productTail t| :=
      abs_integral_le_integral_abs
    _ <= ∫ _t in Ioc (0 : ℝ) b, epsilon := by
      exact integral_mono (hjointInt.sub hproductInt).abs
        (integrableOn_const (by simp [Real.volume_Ioc])) hpoint
    _ = epsilon * b := by
      rw [setIntegral_const]
      simp [hb, mul_comm]

/-- CV18 Lemma 7.13: if nonnegative random variables bounded by `a` and
`b` are `epsilon`-independent, their covariance has absolute value at most
`epsilon * a * b`. -/
theorem ApproxIndepFun.abs_integral_mul_sub_mul_integral_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega -> ℝ} (hX : Measurable X) (hY : Measurable Y)
    {a b epsilon : ℝ} (ha : 0 <= a) (hb : 0 <= b)
    (hepsilon : 0 <= epsilon)
    (hX0 : forall omega, 0 <= X omega) (hXa : forall omega, X omega <= a)
    (hY0 : forall omega, 0 <= Y omega) (hYb : forall omega, Y omega <= b)
    (hind : ApproxIndepFun epsilon X Y mu) :
    |(∫ omega, X omega * Y omega ∂mu) -
        (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu)| <=
      epsilon * a * b := by
  let nu : Measure Omega :=
    mu.withDensity (fun omega => ENNReal.ofReal (Y omega))
  have hXint : Integrable X mu := by
    refine (integrable_const a).mono' hX.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
    exact hXa omega
  have hYint : Integrable Y mu := by
    refine (integrable_const b).mono' hY.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 omega)]
    exact hYb omega
  letI : IsFiniteMeasure nu := by
    dsimp only [nu]
    exact isFiniteMeasure_withDensity_ofReal hYint.hasFiniteIntegral
  have hXintNu : Integrable X nu := by
    refine (integrable_const a).mono' ?_ ?_
    · exact hX.aestronglyMeasurable
    · filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
      exact hXa omega
  have hweighted :
      (∫ omega, X omega ∂nu) = ∫ omega, X omega * Y omega ∂mu := by
    rw [show nu = mu.withDensity (fun omega => ENNReal.ofReal (Y omega)) by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul hY.ennreal_ofReal
      (Filter.Eventually.of_forall fun omega => ENNReal.ofReal_lt_top) X]
    apply integral_congr_ae
    filter_upwards with omega
    rw [ENNReal.toReal_ofReal (hY0 omega), smul_eq_mul, mul_comm]
  have hnuUniv : nu.real Set.univ = ∫ omega, Y omega ∂mu := by
    simpa [nu] using
      withDensity_ofReal_real_apply_eq_setIntegral mu hY hY0 MeasurableSet.univ
  have hXlayerNu :
      (∫ omega, X omega ∂nu) =
        ∫ s in Ioc (0 : ℝ) a, nu.real {omega | s <= X omega} :=
    hXintNu.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hX0)
      (Filter.Eventually.of_forall hXa)
  have hXlayer :
      (∫ omega, X omega ∂mu) =
        ∫ s in Ioc (0 : ℝ) a, mu.real {omega | s <= X omega} :=
    hXint.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hX0)
      (Filter.Eventually.of_forall hXa)
  let weightedTail : ℝ -> ℝ := fun s => nu.real {omega | s <= X omega}
  let productTail : ℝ -> ℝ := fun s =>
    mu.real {omega | s <= X omega} * nu.real Set.univ
  have hweightedInt : IntegrableOn weightedTail (Ioc (0 : ℝ) a) := by
    simpa only [weightedTail] using integrableOn_measureReal_tail_Ioc nu X a
  have hproductInt : IntegrableOn productTail (Ioc (0 : ℝ) a) := by
    change Integrable
      (fun s => mu.real {omega | s <= X omega} * nu.real Set.univ)
      (volume.restrict (Ioc (0 : ℝ) a))
    exact (integrableOn_measureReal_tail_Ioc mu X a).mul_const (nu.real Set.univ)
  have hpoint : forall s,
      |weightedTail s - productTail s| <= epsilon * b := by
    intro s
    simpa [weightedTail, productTail, nu] using
      abs_withDensity_tail_sub_mul_univ_le mu hX hY ha hb hepsilon
        hX0 hXa hY0 hYb hind s
  rw [← hweighted, ← hnuUniv, hXlayerNu, hXlayer]
  change |(∫ s in Ioc (0 : ℝ) a, weightedTail s) -
      (∫ s in Ioc (0 : ℝ) a,
        mu.real {omega | s <= X omega}) * nu.real Set.univ| <=
    epsilon * a * b
  rw [← integral_mul_const]
  change |(∫ s in Ioc (0 : ℝ) a, weightedTail s) -
      (∫ s in Ioc (0 : ℝ) a, productTail s)| <= epsilon * a * b
  rw [← integral_sub hweightedInt hproductInt]
  calc
    |(∫ s in Ioc (0 : ℝ) a, weightedTail s - productTail s)| <=
        ∫ s in Ioc (0 : ℝ) a, |weightedTail s - productTail s| :=
      abs_integral_le_integral_abs
    _ <= ∫ _s in Ioc (0 : ℝ) a, epsilon * b := by
      exact integral_mono (hweightedInt.sub hproductInt).abs
        (integrableOn_const (by simp [Real.volume_Ioc])) hpoint
    _ = epsilon * a * b := by
      rw [setIntegral_const]
      simp [ha]
      ring

/-- The elementary pointwise inequality behind CV18 Lemma 7.14. -/
theorem sub_sq_div_four_mul_le_min {x a : ℝ} (_hx : 0 <= x) (ha : 0 < a) :
    x - x ^ 2 / (4 * a) <= min x a := by
  have hden : 0 < 4 * a := by positivity
  by_cases hxa : x <= a
  · rw [min_eq_left hxa]
    exact sub_le_self _ (div_nonneg (sq_nonneg x) hden.le)
  · rw [min_eq_right (le_of_not_ge hxa)]
    have : x - a <= x ^ 2 / (4 * a) := by
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg (x - 2 * a)]
    nlinarith [sq_nonneg (x - 2 * a)]

/-- CV18 Lemma 7.14 in integral form.  Truncating a nonnegative random
variable at `a` loses at most its second moment divided by `4a`. -/
theorem integral_min_ge_integral_sub_secondMoment_div_four
    (mu : Measure Omega) [IsFiniteMeasure mu] {X : Omega -> ℝ} {a : ℝ}
    (hX : Integrable X mu) (hX2 : Integrable (fun omega => X omega ^ 2) mu)
    (hX0 : forall omega, 0 <= X omega) (ha : 0 < a) :
    (∫ omega, min (X omega) a ∂mu) >=
      (∫ omega, X omega ∂mu) - (∫ omega, X omega ^ 2 ∂mu) / (4 * a) := by
  have hminStrong : AEStronglyMeasurable (fun omega => min (X omega) a) mu :=
    (hX.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hmin : Integrable (fun omega => min (X omega) a) mu := by
    refine (hX.norm.add (integrable_const |a|)).mono' hminStrong ?_
    filter_upwards with omega
    by_cases hxa : X omega <= a
    · rw [min_eq_left hxa, Real.norm_eq_abs]
      exact le_add_of_nonneg_right (abs_nonneg a)
    · rw [min_eq_right (le_of_not_ge hxa), Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg (X omega))
  have hscaled : Integrable (fun omega => X omega ^ 2 / (4 * a)) mu :=
    hX2.div_const (4 * a)
  have hleft : Integrable (fun omega => X omega - X omega ^ 2 / (4 * a)) mu :=
    hX.sub hscaled
  have hle := integral_mono hleft hmin
    (fun omega => sub_sq_div_four_mul_le_min (hX0 omega) ha)
  rw [integral_sub hX hscaled, integral_div] at hle
  exact hle

#print axioms ApproxIndepFun.abs_integral_mul_sub_mul_integral_le
#print axioms integral_min_ge_integral_sub_secondMoment_div_four

end ArlibCommunity.Algorithms.CV18
