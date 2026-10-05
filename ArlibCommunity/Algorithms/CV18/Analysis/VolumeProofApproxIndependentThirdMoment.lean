/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentHigherMoment

/-!
# Third-moment covariance bounds for approximately independent observables

This module develops the `L³` truncation variant needed by the fixed-rate
Gaussian cooling step in dimension three.  Unlike the fourth moment, the
third Gaussian-ratio moment remains uniformly finite at the schedule ratio
`1 + 1 / 3`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The `L^(3/2)` tail estimate used after truncating a nonnegative
`L^3` observable at a positive level. -/
theorem sub_min_rpow_three_halves_le_cube_div_rpow
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    (x - min x a) ^ (3 / 2 : ℝ) ≤ x ^ 3 / a ^ (3 / 2 : ℝ) := by
  by_cases hxa : x ≤ a
  · rw [min_eq_left hxa, sub_self, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    positivity
  · have hax : a ≤ x := le_of_not_ge hxa
    have htail0 : 0 ≤ x - a := sub_nonneg.mpr hax
    have hquad : x - a ≤ x ^ 2 / a := by
      rw [le_div_iff₀ ha]
      nlinarith
    rw [min_eq_right hax]
    calc
      (x - a) ^ (3 / 2 : ℝ) ≤ (x ^ 2 / a) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow htail0 hquad (by norm_num)
      _ = (x ^ 2) ^ (3 / 2 : ℝ) / a ^ (3 / 2 : ℝ) := by
        rw [Real.div_rpow (sq_nonneg x) ha.le]
      _ = x ^ 3 / a ^ (3 / 2 : ℝ) := by
        congr 1
        rw [← Real.rpow_natCast_mul hx 2 (3 / 2 : ℝ)]
        norm_num [Real.rpow_natCast]

/-- The real-power normalization behind the optimized `L³` tail cost. -/
theorem cube_div_mul_rpow_three_halves_rpow_two_thirds
    {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    (A ^ 3 / (A * r) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = A / r := by
  rw [Real.div_rpow (pow_nonneg hA.le 3)
    (Real.rpow_nonneg (mul_nonneg hA.le hr.le) _)]
  rw [← Real.rpow_natCast A 3, ← Real.rpow_mul hA.le]
  rw [← Real.rpow_mul (mul_nonneg hA.le hr.le)]
  norm_num [Real.rpow_natCast]
  field_simp [hA.ne']

/-- Taking the one-third real power reverses cubing on a nonnegative real. -/
theorem cube_rpow_one_third {A : ℝ} (hA : 0 ≤ A) :
    (A ^ 3) ^ (1 / 3 : ℝ) = A := by
  convert Real.pow_rpow_inv_natCast (n := 3) hA (by norm_num) using 1
  norm_num

set_option maxHeartbeats 1000000 in
/-- One-sided covariance control obtained by truncating two nonnegative
`L³` observables.  The two tail terms use Hölder with conjugate exponents
`3 / 2` and `3`.  Choosing comparable normalized truncation levels later
turns the displayed error into an `O(epsilon^(1/3))` covariance bound.

This formulation deliberately keeps the real powers visible: consumers can
specialize it either with exact moment identities or with numerical moment
bounds, without passing through `ENNReal` seminorm arithmetic. -/
theorem ApproxIndepFun.integral_mul_le_mul_integral_add_thirdMoment_tails
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX3 : MemLp X 3 mu) (hY3 : MemLp Y 3 mu)
    {a b epsilon : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hepsilon : 0 ≤ epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hind : ApproxIndepFun epsilon X Y mu) :
    (∫ omega, X omega * Y omega ∂mu) ≤
      (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
        epsilon * a * b +
        ((∫ omega, X omega ^ 3 ∂mu) / a ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
          (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) +
        (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) *
          ((∫ omega, Y omega ^ 3 ∂mu) /
            b ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
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
  have hX32 : MemLp X (ENNReal.ofReal (3 / 2 : ℝ)) mu := by
    apply hX3.mono_exponent
    norm_num
  have hY32 : MemLp Y (ENNReal.ofReal (3 / 2 : ℝ)) mu := by
    apply hY3.mono_exponent
    norm_num
  have hXT32 : MemLp XT (ENNReal.ofReal (3 / 2 : ℝ)) mu :=
    MemLp.of_bound hXT.aestronglyMeasurable a <| by
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hXT0 omega)]
      exact hXTa omega
  have hYT32 : MemLp YT (ENNReal.ofReal (3 / 2 : ℝ)) mu :=
    MemLp.of_bound hYT.aestronglyMeasurable b <| by
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hYT0 omega)]
      exact hYTb omega
  have hXR32 : MemLp XR (ENNReal.ofReal (3 / 2 : ℝ)) mu := hX32.sub hXT32
  have hYR32 : MemLp YR (ENNReal.ofReal (3 / 2 : ℝ)) mu := hY32.sub hYT32
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
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
  have hXcubeInt : Integrable (fun omega => X omega ^ 3) mu := by
    have h := hX3.integrable_norm_pow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
  have hYcubeInt : Integrable (fun omega => Y omega ^ 3) mu := by
    have h := hY3.integrable_norm_pow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 omega)]
  have hXRrpowInt : Integrable (fun omega => XR omega ^ (3 / 2 : ℝ)) mu := by
    have h := hXR32.integrable_norm_rpow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hXR0 omega)]
    norm_num
  have hYRrpowInt : Integrable (fun omega => YR omega ^ (3 / 2 : ℝ)) mu := by
    have h := hYR32.integrable_norm_rpow'
    apply h.congr
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hYR0 omega)]
    norm_num
  have hXRmoment : (∫ omega, XR omega ^ (3 / 2 : ℝ) ∂mu) ≤
      (∫ omega, X omega ^ 3 ∂mu) / a ^ (3 / 2 : ℝ) := by
    rw [← integral_div]
    apply integral_mono hXRrpowInt (hXcubeInt.div_const _)
    exact fun omega =>
      sub_min_rpow_three_halves_le_cube_div_rpow (hX0 omega) ha
  have hYRmoment : (∫ omega, YR omega ^ (3 / 2 : ℝ) ∂mu) ≤
      (∫ omega, Y omega ^ 3 ∂mu) / b ^ (3 / 2 : ℝ) := by
    rw [← integral_div]
    apply integral_mono hYRrpowInt (hYcubeInt.div_const _)
    exact fun omega =>
      sub_min_rpow_three_halves_le_cube_div_rpow (hY0 omega) hb
  have hY3' : MemLp Y (ENNReal.ofReal (3 : ℝ)) mu := by simpa using hY3
  have hX3' : MemLp X (ENNReal.ofReal (3 : ℝ)) mu := by simpa using hX3
  have hXRcross := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hXR0) (Filter.Eventually.of_forall hY0)
    hXR32 hY3'
  have hXcrossYR := integral_mul_le_Lp_mul_Lq_of_nonneg hpq.symm
    (Filter.Eventually.of_forall hX0) (Filter.Eventually.of_forall hYR0)
    hX3' hYR32
  have hXRmoment0 : 0 ≤ ∫ omega, XR omega ^ (3 / 2 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hXR0 omega) _
  have hYRmoment0 : 0 ≤ ∫ omega, YR omega ^ (3 / 2 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hYR0 omega) _
  have hXtailTop0 : 0 ≤
      (∫ omega, X omega ^ 3 ∂mu) / a ^ (3 / 2 : ℝ) := by
    exact div_nonneg (integral_nonneg fun omega => pow_nonneg (hX0 omega) 3)
      (Real.rpow_nonneg ha.le _)
  have hYtailTop0 : 0 ≤
      (∫ omega, Y omega ^ 3 ∂mu) / b ^ (3 / 2 : ℝ) := by
    exact div_nonneg (integral_nonneg fun omega => pow_nonneg (hY0 omega) 3)
      (Real.rpow_nonneg hb.le _)
  have hXRroot := Real.rpow_le_rpow hXRmoment0 hXRmoment (by norm_num :
    (0 : ℝ) ≤ 2 / 3)
  have hYRroot := Real.rpow_le_rpow hYRmoment0 hYRmoment (by norm_num :
    (0 : ℝ) ≤ 2 / 3)
  norm_num at hXRcross hXcrossYR
  have htailX : (∫ omega, XR omega * Y omega ∂mu) ≤
      ((∫ omega, X omega ^ 3 ∂mu) / a ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) := by
    exact hXRcross.trans (mul_le_mul_of_nonneg_right hXRroot
      (Real.rpow_nonneg
        (integral_nonneg fun omega => pow_nonneg (hY0 omega) 3) _))
  have htailY : (∫ omega, X omega * YR omega ∂mu) ≤
      (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) *
        ((∫ omega, Y omega ^ 3 ∂mu) / b ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) := by
    exact hXcrossYR.trans (mul_le_mul_of_nonneg_left hYRroot
      (Real.rpow_nonneg
        (integral_nonneg fun omega => pow_nonneg (hX0 omega) 3) _))
  have hXTint : Integrable XT mu := hXT32.integrable (by norm_num)
  have hYTint : Integrable YT mu := hYT32.integrable (by norm_num)
  have hXint : Integrable X mu := hX3.integrable (by norm_num)
  have hYint : Integrable Y mu := hY3.integrable (by norm_num)
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
  have hprod : Integrable (fun omega => X omega * Y omega) mu :=
    (hX3.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)).integrable_mul
      (hY3.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3))
  have hcoreInt : Integrable (fun omega => XT omega * YT omega) mu := by
    refine (integrable_const (a * b)).mono'
      (hXT.mul hYT).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hXT0 omega) (hYT0 omega))]
    exact mul_le_mul (hXTa omega) (hYTb omega) (hYT0 omega) ha.le
  have hXRcrossInt : Integrable (fun omega => XR omega * Y omega) mu := by
    refine hprod.mono' (hXR.mul hY).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hXR0 omega) (hY0 omega))]
    change XR omega * Y omega ≤ X omega * Y omega
    exact mul_le_mul_of_nonneg_right (sub_le_self _ (hXT0 omega)) (hY0 omega)
  have hXcrossYRInt : Integrable (fun omega => X omega * YR omega) mu := by
    refine hprod.mono' (hX.mul hYR).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX0 omega) (hYR0 omega))]
    change X omega * YR omega ≤ X omega * Y omega
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (hYT0 omega)) (hX0 omega)
  have hpoint : ∀ omega, X omega * Y omega ≤
      XT omega * YT omega + XR omega * Y omega + X omega * YR omega := by
    intro omega
    dsimp only [XT, YT, XR, YR]
    nlinarith [hX0 omega, hY0 omega, min_le_left (X omega) a,
      min_le_left (Y omega) b]
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
        (((∫ omega, X omega ^ 3 ∂mu) / a ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
          (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ)) +
        (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) *
          ((∫ omega, Y omega ^ 3 ∂mu) /
            b ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      gcongr
    _ ≤ _ := by gcongr

/-- Scale-normalized `L³` covariance bound.  If the two third moments are at
most `A³` and `B³`, truncating at `A*r` and `B*r` costs
`epsilon * A * B * r² + 2 * A * B / r`.  Taking
`r = epsilon^(-1/3)` gives the expected `3 * epsilon^(1/3) * A * B` rate. -/
theorem ApproxIndepFun.integral_mul_le_mul_integral_add_thirdMoment_scaled
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX3 : MemLp X 3 mu) (hY3 : MemLp Y 3 mu)
    {A B r epsilon : ℝ} (hA : 0 < A) (hB : 0 < B) (hr : 0 < r)
    (hepsilon : 0 ≤ epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hXcube : (∫ omega, X omega ^ 3 ∂mu) ≤ A ^ 3)
    (hYcube : (∫ omega, Y omega ^ 3 ∂mu) ≤ B ^ 3)
    (hind : ApproxIndepFun epsilon X Y mu) :
    (∫ omega, X omega * Y omega ∂mu) ≤
      (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
        epsilon * A * B * r ^ 2 + 2 * A * B / r := by
  have hraw := hind.integral_mul_le_mul_integral_add_thirdMoment_tails
    mu hX hY hX3 hY3 (mul_pos hA hr) (mul_pos hB hr) hepsilon hX0 hY0
  have hMX0 : 0 ≤ ∫ omega, X omega ^ 3 ∂mu :=
    integral_nonneg fun omega => pow_nonneg (hX0 omega) 3
  have hMY0 : 0 ≤ ∫ omega, Y omega ^ 3 ∂mu :=
    integral_nonneg fun omega => pow_nonneg (hY0 omega) 3
  have hAr0 : 0 ≤ A * r := (mul_pos hA hr).le
  have hBr0 : 0 ≤ B * r := (mul_pos hB hr).le
  have hdenA0 : 0 ≤ (A * r) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hAr0 _
  have hdenB0 : 0 ≤ (B * r) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hBr0 _
  have hfracX :
      (∫ omega, X omega ^ 3 ∂mu) / (A * r) ^ (3 / 2 : ℝ) ≤
        A ^ 3 / (A * r) ^ (3 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hXcube hdenA0
  have hfracY :
      (∫ omega, Y omega ^ 3 ∂mu) / (B * r) ^ (3 / 2 : ℝ) ≤
        B ^ 3 / (B * r) ^ (3 / 2 : ℝ) :=
    div_le_div_of_nonneg_right hYcube hdenB0
  have hfracX0 : 0 ≤
      (∫ omega, X omega ^ 3 ∂mu) / (A * r) ^ (3 / 2 : ℝ) :=
    div_nonneg hMX0 hdenA0
  have hfracY0 : 0 ≤
      (∫ omega, Y omega ^ 3 ∂mu) / (B * r) ^ (3 / 2 : ℝ) :=
    div_nonneg hMY0 hdenB0
  have htailRootX :
      ((∫ omega, X omega ^ 3 ∂mu) / (A * r) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) ≤ A / r := by
    calc
      _ ≤ (A ^ 3 / (A * r) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hfracX0 hfracX (by norm_num)
      _ = A / r := cube_div_mul_rpow_three_halves_rpow_two_thirds hA hr
  have htailRootY :
      ((∫ omega, Y omega ^ 3 ∂mu) / (B * r) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) ≤ B / r := by
    calc
      _ ≤ (B ^ 3 / (B * r) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hfracY0 hfracY (by norm_num)
      _ = B / r := cube_div_mul_rpow_three_halves_rpow_two_thirds hB hr
  have hcubeRootX :
      (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) ≤ A := by
    calc
      _ ≤ (A ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hMX0 hXcube (by norm_num)
      _ = A := cube_rpow_one_third hA.le
  have hcubeRootY :
      (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) ≤ B := by
    calc
      _ ≤ (B ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hMY0 hYcube (by norm_num)
      _ = B := cube_rpow_one_third hB.le
  have htailX :
      ((∫ omega, X omega ^ 3 ∂mu) / (A * r) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) *
        (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) ≤ A * B / r := by
    calc
      _ ≤ (A / r) * B := mul_le_mul htailRootX hcubeRootY
        (Real.rpow_nonneg hMY0 _) (div_nonneg hA.le hr.le)
      _ = A * B / r := by ring
  have htailY :
      (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) *
        ((∫ omega, Y omega ^ 3 ∂mu) / (B * r) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) ≤ A * B / r := by
    calc
      _ ≤ A * (B / r) := mul_le_mul hcubeRootX htailRootY
        (Real.rpow_nonneg hfracY0 _) hA.le
      _ = A * B / r := by ring
  calc
    (∫ omega, X omega * Y omega ∂mu) ≤
        (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
          epsilon * (A * r) * (B * r) +
          ((∫ omega, X omega ^ 3 ∂mu) / (A * r) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) *
            (∫ omega, Y omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) +
          (∫ omega, X omega ^ 3 ∂mu) ^ (1 / 3 : ℝ) *
            ((∫ omega, Y omega ^ 3 ∂mu) / (B * r) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) := hraw
    _ ≤ (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
          epsilon * (A * r) * (B * r) + A * B / r + A * B / r := by
      gcongr
    _ = _ := by ring

/-- Optimized third-moment covariance bound.  This is the `p = q = 3`
Davydov rate, obtained here directly from CV18's rectangle coefficient by
truncation and Hölder rather than importing a separate mixing framework. -/
theorem ApproxIndepFun.integral_mul_le_mul_integral_add_three_cbrt_mul
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX3 : MemLp X 3 mu) (hY3 : MemLp Y 3 mu)
    {A B epsilon : ℝ} (hA : 0 < A) (hB : 0 < B) (hepsilon : 0 < epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hXcube : (∫ omega, X omega ^ 3 ∂mu) ≤ A ^ 3)
    (hYcube : (∫ omega, Y omega ^ 3 ∂mu) ≤ B ^ 3)
    (hind : ApproxIndepFun epsilon X Y mu) :
    (∫ omega, X omega * Y omega ∂mu) ≤
      (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
        3 * epsilon ^ (1 / 3 : ℝ) * A * B := by
  let d : ℝ := epsilon ^ (1 / 3 : ℝ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hepsilonCube : d ^ 3 = epsilon := by
    dsimp [d]
    convert Real.rpow_inv_natCast_pow hepsilon.le (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  have hraw := hind.integral_mul_le_mul_integral_add_thirdMoment_scaled
    mu hX hY hX3 hY3 hA hB (inv_pos.mpr hd) hepsilon.le hX0 hY0
      hXcube hYcube
  calc
    (∫ omega, X omega * Y omega ∂mu) ≤
        (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
          epsilon * A * B * d⁻¹ ^ 2 + 2 * A * B / d⁻¹ := hraw
    _ = (∫ omega, X omega ∂mu) * (∫ omega, Y omega ∂mu) +
          3 * d * A * B := by
      rw [← hepsilonCube]
      field_simp [hd.ne']
      ring
    _ = _ := by rfl

#print axioms sub_min_rpow_three_halves_le_cube_div_rpow
#print axioms
  ApproxIndepFun.integral_mul_le_mul_integral_add_thirdMoment_tails
#print axioms
  ApproxIndepFun.integral_mul_le_mul_integral_add_thirdMoment_scaled
#print axioms
  ApproxIndepFun.integral_mul_le_mul_integral_add_three_cbrt_mul

end ArlibCommunity.Algorithms.CV18
