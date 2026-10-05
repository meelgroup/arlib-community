/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer

/-!
# Second moments under killed collector domination

A finite executable collector returns `none` when its local cap or retry
budget is exhausted.  The numerical estimator assigns zero to that branch.
Consequently, domination of the successful payload law is enough to transfer
its second moment: the missing mass at `none` contributes exactly zero.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Extend a real observable on successful payloads by zero on failure. -/
def optionZeroLift {A : Type*} (f : A → ℝ) : Option A → ℝ
  | none => 0
  | some x => f x

theorem measurable_optionZeroLift
    {A : Type*} [MeasurableSpace A] {f : A → ℝ} (hf : Measurable f) :
    Measurable (optionZeroLift f) := by
  convert Measurable.optionElim (0 : ℝ) hf using 1
  funext value
  cases value <;> rfl

/-- A successful-payload measure domination transfers the square of the
zero-filled observable.  This is the exact second-moment analogue of the
optional-law decomposition used by the retry approximation layer. -/
theorem integral_optionZeroLift_sq_le_of_success_dom
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) [IsFiniteMeasure L]
    (nu : Measure A) {f : A → ℝ} (hf : Measurable f)
    (hfmem : MemLp f 2 nu)
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S) :
    (∫ value, optionZeroLift f value ^ 2 ∂L) ≤
      ∫ x, f x ^ 2 ∂nu := by
  let error : Measure (Option A) := L {none} • Measure.dirac none
  let upper : Measure (Option A) := nu.map some + error
  have hle : L ≤ upper := by
    dsimp only [upper, error]
    exact optionMeasure_le_map_some_add_failure L nu hdom
  have hsomeSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) (nu.map some) := by
    apply (integrable_map_measure
      ((measurable_optionZeroLift hf).pow_const 2).aestronglyMeasurable
      measurable_some.aemeasurable).2
    rw [show (fun value : Option A => optionZeroLift f value ^ 2) ∘ some =
        fun x => f x ^ 2 by
      funext x
      rfl]
    exact hfmem.integrable_sq
  have herrorTop : L {none} ≠ ⊤ :=
    measure_ne_top L {none}
  have herrorSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) error := by
    dsimp only [error]
    have hdirac : Integrable (fun value : Option A =>
        optionZeroLift f value ^ 2) (Measure.dirac none) := by
      apply integrable_dirac'
        ((measurable_optionZeroLift hf).pow_const 2).stronglyMeasurable
      simp [optionZeroLift]
    exact hdirac.smul_measure herrorTop
  have hupperSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) upper := by
    dsimp only [upper]
    exact integrable_add_measure.2 ⟨hsomeSq, herrorSq⟩
  calc
    (∫ value, optionZeroLift f value ^ 2 ∂L) ≤
        ∫ value, optionZeroLift f value ^ 2 ∂upper :=
      integral_mono_measure hle
        (Filter.Eventually.of_forall fun value => sq_nonneg _)
        hupperSq
    _ = (∫ value, optionZeroLift f value ^ 2 ∂nu.map some) +
          ∫ value, optionZeroLift f value ^ 2 ∂error := by
      dsimp only [upper]
      exact integral_add_measure hsomeSq herrorSq
    _ = (∫ x, f x ^ 2 ∂nu) + 0 := by
      congr 1
      · rw [integral_map measurable_some.aemeasurable
          ((measurable_optionZeroLift hf).pow_const 2).aestronglyMeasurable]
        rfl
      · dsimp only [error]
        rw [integral_smul_measure]
        rw [integral_dirac'
          (fun value : Option A => optionZeroLift f value ^ 2) none
          ((measurable_optionZeroLift hf).pow_const 2).stronglyMeasurable]
        simp [optionZeroLift]
    _ = ∫ x, f x ^ 2 ∂nu := add_zero _

/-- Sharp second-moment transport under a small scalar-law perturbation.
Unlike the older coarse factor-four adapter, this theorem retains an
arbitrary ideal factor and makes the exact finite-walk slack arithmetic
explicit. -/
theorem Arlib.TVLe.second_le_factor_mul_mean_sq_of_ae
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (htv : Arlib.TVLe mu nu epsilon)
    (hepsilonTop : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0mu : ∀ᵐ x ∂mu, 0 ≤ f x) (hfBmu : ∀ᵐ x ∂mu, f x ≤ B)
    (hf0nu : ∀ᵐ x ∂nu, 0 ≤ f x) (hfBnu : ∀ᵐ x ∂nu, f x ≤ B)
    {idealMean factor slack eta zeta : ℝ}
    (hidealMean : idealMean = ∫ x, f x ∂nu)
    (hidealMeanPos : 0 < idealMean)
    (hidealSecond : (∫ x, f x ^ 2 ∂nu) ≤ factor * idealMean ^ 2)
    (hfactor0 : 0 ≤ factor) (hslack0 : 0 ≤ slack)
    (heta1 : eta < 1)
    (hmeanError : B * epsilon.toReal ≤ eta * idealMean)
    (hsecondError : B ^ 2 * epsilon.toReal ≤ zeta * idealMean ^ 2)
    (hfactorBudget : factor + zeta ≤
      factor * (1 + slack) * (1 - eta) ^ 2) :
    (∫ x, f x ^ 2 ∂mu) ≤
      factor * (1 + slack) * (∫ x, f x ∂mu) ^ 2 := by
  let g : S → ℝ := fun x => min (max 0 (f x)) B
  have hg : Measurable g := (measurable_const.max hf).min measurable_const
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    le_min (le_max_left _ _) hB.le
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
    integral_congr_ae <| by
      filter_upwards [hgeqmu] with x hx
      rw [hx]
  have hsecondNu : (∫ x, g x ^ 2 ∂nu) = ∫ x, f x ^ 2 ∂nu :=
    integral_congr_ae <| by
      filter_upwards [hgeqnu] with x hx
      rw [hx]
  have hmeanAbs := Arlib.TVLe.integral_le_of_nonnegative_le
    htv hepsilonTop hg hB hg0 hgB
  have hsecondAbs := Arlib.TVLe.integral_sq_le_of_nonnegative_le
    htv hepsilonTop hg hB hg0 hgB
  rw [hmeanMu, hmeanNu, ← hidealMean] at hmeanAbs
  rw [hsecondMu, hsecondNu] at hsecondAbs
  have hrawLower : (1 - eta) * idealMean ≤ ∫ x, f x ∂mu := by
    have := (abs_le.mp hmeanAbs).1
    nlinarith
  have hlower0 : 0 ≤ (1 - eta) * idealMean :=
    mul_nonneg (sub_nonneg.mpr heta1.le) hidealMeanPos.le
  have hraw0 : 0 ≤ ∫ x, f x ∂mu := hlower0.trans hrawLower
  have hactualSecond : (∫ x, f x ^ 2 ∂mu) ≤
      (factor + zeta) * idealMean ^ 2 := by
    have hupper := (abs_le.mp hsecondAbs).2
    calc
      (∫ x, f x ^ 2 ∂mu) ≤
          (∫ x, f x ^ 2 ∂nu) + B ^ 2 * epsilon.toReal := by
        linarith
      _ ≤ factor * idealMean ^ 2 + zeta * idealMean ^ 2 :=
        add_le_add hidealSecond hsecondError
      _ = (factor + zeta) * idealMean ^ 2 := by ring
  have hcoeff0 : 0 ≤ factor * (1 + slack) :=
    mul_nonneg hfactor0 (by linarith)
  have hsquare : ((1 - eta) * idealMean) ^ 2 ≤
      (∫ x, f x ∂mu) ^ 2 :=
    (sq_le_sq₀ hlower0 hraw0).2 hrawLower
  calc
    (∫ x, f x ^ 2 ∂mu) ≤
        (factor + zeta) * idealMean ^ 2 := hactualSecond
    _ ≤ (factor * (1 + slack) * (1 - eta) ^ 2) *
          idealMean ^ 2 :=
      mul_le_mul_of_nonneg_right hfactorBudget (sq_nonneg idealMean)
    _ = factor * (1 + slack) * ((1 - eta) * idealMean) ^ 2 := by ring
    _ ≤ factor * (1 + slack) * (∫ x, f x ∂mu) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hcoeff0

#print axioms integral_optionZeroLift_sq_le_of_success_dom
#print axioms Arlib.TVLe.second_le_factor_mul_mean_sq_of_ae

end ArlibCommunity.Algorithms.CV18
