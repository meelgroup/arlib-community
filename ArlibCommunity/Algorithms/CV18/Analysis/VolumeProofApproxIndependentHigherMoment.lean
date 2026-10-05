/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovEmpirical

/-!
# Approximate independence for unbounded nonnegative observables

CV18's rectangle-mixing coefficient controls products directly only after
both observables have been bounded.  This module records the truncation
argument needed for the Gaussian phase weights: fourth moments control the
discarded tails, while `ApproxIndepFun` controls the bounded core.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib.MarkovChains

/-- The squared part discarded by truncation at `a` is bounded by the fourth
power divided by `a²`. -/
theorem sq_sub_min_le_fourth_div_sq {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    (x - min x a) ^ 2 ≤ x ^ 4 / a ^ 2 := by
  by_cases hxa : x ≤ a
  · simp [min_eq_left hxa]
    exact div_nonneg (pow_nonneg hx 4) (sq_nonneg a)
  · rw [min_eq_right (le_of_not_ge hxa)]
    have hax : a ≤ x := le_of_not_ge hxa
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    rw [le_div_iff₀ ha2]
    have ha2x2 : a ^ 2 ≤ x ^ 2 := (sq_le_sq₀ ha.le hx).2 hax
    have hsub0 : 0 ≤ x - a := sub_nonneg.mpr hax
    have hsubx : x - a ≤ x := by linarith
    have hsub2 : (x - a) ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ hsub0 hx).2 hsubx
    calc
      (x - a) ^ 2 * a ^ 2 ≤ x ^ 2 * a ^ 2 :=
        mul_le_mul_of_nonneg_right hsub2 (sq_nonneg a)
      _ ≤ x ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_left ha2x2 (sq_nonneg x)
      _ = x ^ 4 := by ring

set_option maxHeartbeats 1000000 in
/-- One-sided covariance control for nonnegative, possibly unbounded
observables.  The first term is CV18 Lemma 7.13 applied to the truncated
variables.  The other two terms are the Cauchy--Schwarz tail costs, expressed
using fourth moments.

This is the paper-faithful replacement for using exact IID cross terms in
Equation (6) after only approximate independence has been established. -/
theorem ApproxIndepFun.integral_mul_le_mul_integral_add_fourthMoment_tails
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX4 : MemLp X 4 mu) (hY4 : MemLp Y 4 mu)
    {a b epsilon : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hepsilon : 0 ≤ epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hind : ApproxIndepFun epsilon X Y mu) :
    (∫ omega, X omega * Y omega ∂mu) ≤
      (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
        epsilon * a * b +
        Real.sqrt ((∫ omega, X omega ^ 4 ∂mu) / a ^ 2) *
          Real.sqrt (∫ omega, Y omega ^ 2 ∂mu) +
        Real.sqrt (∫ omega, X omega ^ 2 ∂mu) *
          Real.sqrt ((∫ omega, Y omega ^ 4 ∂mu) / b ^ 2) := by
  let XT : Omega → ℝ := fun omega => min (X omega) a
  let YT : Omega → ℝ := fun omega => min (Y omega) b
  let XR : Omega → ℝ := fun omega => X omega - XT omega
  let YR : Omega → ℝ := fun omega => Y omega - YT omega
  have hXT : Measurable XT := hX.min measurable_const
  have hYT : Measurable YT := hY.min measurable_const
  have hXR : Measurable XR := hX.sub hXT
  have hYR : Measurable YR := hY.sub hYT
  have hXT0 : ∀ omega, 0 ≤ XT omega := fun omega =>
    le_min (hX0 omega) ha.le
  have hYT0 : ∀ omega, 0 ≤ YT omega := fun omega =>
    le_min (hY0 omega) hb.le
  have hXTa : ∀ omega, XT omega ≤ a := fun omega => min_le_right _ _
  have hYTb : ∀ omega, YT omega ≤ b := fun omega => min_le_right _ _
  have hXR0 : ∀ omega, 0 ≤ XR omega := fun omega =>
    sub_nonneg.mpr (min_le_left _ _)
  have hYR0 : ∀ omega, 0 ≤ YR omega := fun omega =>
    sub_nonneg.mpr (min_le_left _ _)
  have hX2 : MemLp X 2 mu := hX4.mono_exponent (by norm_num)
  have hY2 : MemLp Y 2 mu := hY4.mono_exponent (by norm_num)
  have hXT2 : MemLp XT 2 mu :=
    MemLp.of_bound hXT.aestronglyMeasurable a <| by
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hXT0 omega)]
      exact hXTa omega
  have hYT2 : MemLp YT 2 mu :=
    MemLp.of_bound hYT.aestronglyMeasurable b <| by
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hYT0 omega)]
      exact hYTb omega
  have hXR2 : MemLp XR 2 mu := hX2.sub hXT2
  have hYR2 : MemLp YR 2 mu := hY2.sub hYT2
  have hindT : ApproxIndepFun epsilon XT YT mu := by
    simpa [XT, YT, Function.comp_def] using
      hind.comp (measurable_id.min measurable_const)
        (measurable_id.min measurable_const)
  have hcoreAbs := hindT.abs_integral_mul_sub_mul_integral_le
    mu hXT hYT ha.le hb.le hepsilon hXT0 hXTa hYT0 hYTb
  have hcore : (∫ omega, XT omega * YT omega ∂mu) ≤
      (∫ omega, XT omega ∂mu) * (∫ omega, YT omega ∂mu) +
        epsilon * a * b := by
    linarith [le_abs_self
      ((∫ omega, XT omega * YT omega ∂mu) -
        (∫ omega, XT omega ∂mu) * (∫ omega, YT omega ∂mu))]
  have hXfourthInt : Integrable (fun omega => X omega ^ 4) mu := by
    have h := hX4.integrable_norm_pow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
  have hYfourthInt : Integrable (fun omega => Y omega ^ 4) mu := by
    have h := hY4.integrable_norm_pow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 omega)]
  have hXRsecond : (∫ omega, XR omega ^ 2 ∂mu) ≤
      (∫ omega, X omega ^ 4 ∂mu) / a ^ 2 := by
    rw [← integral_div]
    apply integral_mono hXR2.integrable_sq (hXfourthInt.div_const _)
    exact fun omega => sq_sub_min_le_fourth_div_sq (hX0 omega) ha
  have hYRsecond : (∫ omega, YR omega ^ 2 ∂mu) ≤
      (∫ omega, Y omega ^ 4 ∂mu) / b ^ 2 := by
    rw [← integral_div]
    apply integral_mono hYR2.integrable_sq (hYfourthInt.div_const _)
    exact fun omega => sq_sub_min_le_fourth_div_sq (hY0 omega) hb
  have hXRcross := integral_mul_le_sqrt_mul_sqrt hXR2 hY2
  have hXcrossYR := integral_mul_le_sqrt_mul_sqrt hX2 hYR2
  have hXRsecond0 : 0 ≤ ∫ omega, XR omega ^ 2 ∂mu :=
    integral_nonneg fun omega => sq_nonneg _
  have hYRsecond0 : 0 ≤ ∫ omega, YR omega ^ 2 ∂mu :=
    integral_nonneg fun omega => sq_nonneg _
  have hXfourthTail0 : 0 ≤ (∫ omega, X omega ^ 4 ∂mu) / a ^ 2 := by
    positivity
  have hYfourthTail0 : 0 ≤ (∫ omega, Y omega ^ 4 ∂mu) / b ^ 2 := by
    positivity
  have hXRroot : Real.sqrt (∫ omega, XR omega ^ 2 ∂mu) ≤
      Real.sqrt ((∫ omega, X omega ^ 4 ∂mu) / a ^ 2) :=
    Real.sqrt_le_sqrt hXRsecond
  have hYRroot : Real.sqrt (∫ omega, YR omega ^ 2 ∂mu) ≤
      Real.sqrt ((∫ omega, Y omega ^ 4 ∂mu) / b ^ 2) :=
    Real.sqrt_le_sqrt hYRsecond
  have htailX : (∫ omega, XR omega * Y omega ∂mu) ≤
      Real.sqrt ((∫ omega, X omega ^ 4 ∂mu) / a ^ 2) *
        Real.sqrt (∫ omega, Y omega ^ 2 ∂mu) :=
    hXRcross.trans <| mul_le_mul_of_nonneg_right hXRroot (Real.sqrt_nonneg _)
  have htailY : (∫ omega, X omega * YR omega ∂mu) ≤
      Real.sqrt (∫ omega, X omega ^ 2 ∂mu) *
        Real.sqrt ((∫ omega, Y omega ^ 4 ∂mu) / b ^ 2) :=
    hXcrossYR.trans <| mul_le_mul_of_nonneg_left hYRroot (Real.sqrt_nonneg _)
  have hXTint : Integrable XT mu := hXT2.integrable one_le_two
  have hYTint : Integrable YT mu := hYT2.integrable one_le_two
  have hXint : Integrable X mu := hX2.integrable one_le_two
  have hYint : Integrable Y mu := hY2.integrable one_le_two
  have hXTmean : (∫ omega, XT omega ∂mu) ≤ ∫ omega, X omega ∂mu :=
    integral_mono hXTint hXint fun omega => min_le_left _ _
  have hYTmean : (∫ omega, YT omega ∂mu) ≤ ∫ omega, Y omega ∂mu :=
    integral_mono hYTint hYint fun omega => min_le_left _ _
  have hXmean0 : 0 ≤ ∫ omega, X omega ∂mu := integral_nonneg hX0
  have hYTmean0 : 0 ≤ ∫ omega, YT omega ∂mu := integral_nonneg hYT0
  have hmeanProd :
      (∫ omega, XT omega ∂mu) * (∫ omega, YT omega ∂mu) ≤
        (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) :=
    mul_le_mul hXTmean hYTmean hYTmean0 hXmean0
  have hpoint : ∀ omega, X omega * Y omega ≤
      XT omega * YT omega + XR omega * Y omega + X omega * YR omega := by
    intro omega
    dsimp only [XT, YT, XR, YR]
    nlinarith [hX0 omega, hY0 omega, min_le_left (X omega) a,
      min_le_left (Y omega) b]
  have hprod : Integrable (fun omega => X omega * Y omega) mu :=
    hX2.integrable_mul hY2
  have hcoreInt : Integrable (fun omega => XT omega * YT omega) mu :=
    hXT2.integrable_mul hYT2
  have hXRcrossInt : Integrable (fun omega => XR omega * Y omega) mu :=
    hXR2.integrable_mul hY2
  have hXcrossYRInt : Integrable (fun omega => X omega * YR omega) mu :=
    hX2.integrable_mul hYR2
  calc
    (∫ omega, X omega * Y omega ∂mu) ≤
        ∫ omega, XT omega * YT omega + XR omega * Y omega +
          X omega * YR omega ∂mu :=
      integral_mono hprod ((hcoreInt.add hXRcrossInt).add hXcrossYRInt) hpoint
    _ = ∫ omega, (XT omega * YT omega + XR omega * Y omega) +
          X omega * YR omega ∂mu := by rfl
    _ = (∫ omega, XT omega * YT omega + XR omega * Y omega ∂mu) +
          ∫ omega, X omega * YR omega ∂mu :=
      integral_add (hcoreInt.add hXRcrossInt) hXcrossYRInt
    _ = (∫ omega, XT omega * YT omega ∂mu) +
          (∫ omega, XR omega * Y omega ∂mu) +
          ∫ omega, X omega * YR omega ∂mu := by
      rw [integral_add hcoreInt hXRcrossInt]
    _ ≤ ((∫ omega, XT omega ∂mu) * (∫ omega, YT omega ∂mu) +
          epsilon * a * b) +
        (Real.sqrt ((∫ omega, X omega ^ 4 ∂mu) / a ^ 2) *
          Real.sqrt (∫ omega, Y omega ^ 2 ∂mu)) +
        Real.sqrt (∫ omega, X omega ^ 2 ∂mu) *
          Real.sqrt ((∫ omega, Y omega ^ 4 ∂mu) / b ^ 2) := by
      gcongr
    _ ≤ _ := by
      nlinarith [hmeanProd]

#print axioms sq_sub_min_le_fourth_div_sq
#print axioms
  ApproxIndepFun.integral_mul_le_mul_integral_add_fourthMoment_tails

end ArlibCommunity.Algorithms.CV18
