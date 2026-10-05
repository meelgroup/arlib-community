/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Corollary 4.6 of KLS97 at the sharp order `√n`

This file proves, unconditionally,

`∫_K vol((x + tB) \ K) dx ≤ (10 · t·√n / 2r) · vol(K) · vol(tB)`      (KLS-√n)

for a convex, **closed** body `K` of finite volume containing a ball of radius `r > 0`, and any
`t > 0`.  This is Corollary 4.6 of

> R. Kannan, L. Lovász, M. Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for
> convex bodies*, Random Structures & Algorithms **11** (1997), 1–50,

quoted as **Lemma 3.3** of Lovász–Vempala, *Hit-and-Run from a Corner*, **at the correct order
`√n`**, with an explicit absolute constant `C = 10` in place of the paper's `C = 1`.

`Arlib/Convexity/KLS97.lean` proves the same statement with `√n` replaced by `n`, by an
elementary shrink-and-shift argument; that route is *sharp* (up to a factor `1.21`) and
therefore cannot reach `√n`.  This file takes the different route sketched in that file's
docstring and does reach `√n`.  Both files are kept: `KLS97.lean` needs no closedness
hypothesis and has a much shorter proof; this file has the right order in `n`.

## The route

Write `d(y) = dist(y, K)`.  Four ingredients, none of which needs a surface-area measure, mixed
volumes, or Cauchy's projection formula (none of which Mathlib v4.32 has):

1. **Swap** (`Arlib.lintegral_sdiff_eq_lintegral_inter`).  Both
   `∫_K vol(B(x,t) \ K) dx` and `∫_{Kᶜ} vol(K ∩ B(y,t)) dy` compute the `2n`-measure of
   `{(x,y) : x ∈ K, y ∉ K, dist x y ≤ t}`.  Tonelli.

2. **Cap** (`Arlib.volume_inter_closedBall_le_sqrt`, `Arlib.sqrt_pow_le_exp`).  For `y ∉ K` let
   `ν` be the unit normal of the supporting hyperplane at the metric projection of `y`
   (Hilbert projection theorem: `exists_norm_eq_iInf_of_complete_convex` and
   `norm_eq_iInf_iff_real_inner_le_zero`).  Then
   `K ∩ B(y,t) ⊆ {u : ‖u−y‖ ≤ t, ⟪ν,u−y⟫ ≤ −d(y)} ⊆ B(y − d(y)·ν, √(t² − d(y)²))`,
   so `vol(K ∩ B(y,t)) ≤ (1 − d(y)²/t²)^{n/2} · vol(tB) ≤ e^{2 − 2√n·d(y)/t} · vol(tB)`,
   using `√(1−x) ≤ e^{−x/2}` and then `u²/2 − 2u + 2 = (u−2)²/2 ≥ 0` at `u = √n·d(y)/t`.
   The Gaussian majorant is replaced by the *globally smooth* exponential `e^{2 − λ h}`
   (`λ = 2√n/t`) precisely so that the layer cake below needs only one FTC, not a piecewise one;
   the price is the factor `e² = g̃(0)`.

3. **Layer cake** (`Arlib.layercake_infDist`).  `∫_{Kᶜ} e^{2−λ d(y)} dy =
   ∫_0^∞ λ e^{2−λh} · vol({d ≤ h} \ K) dh`, again by Tonelli, the `h`-marginal being
   `∫_h^∞ λ e^{2−λu} du = e^{2−λh}` (FTC on `(d,∞)`).  Mathlib's `Layercake.lean` has only the
   *increasing*-weight form `∫ f = ∫ μ{f ≥ t}`, which does not apply here (`Kᶜ` has infinite
   measure and the weight is decreasing), so this is proved from `lintegral_lintegral_swap`.

4. **Shell** (`Arlib.volume_infDist_le_le`, `Arlib.volume_shell_le`).  `{d ≤ h}` is contained in
   the image of `K` under the homothety of ratio `1 + h/r` about `z`, so
   `vol({d ≤ h}) ≤ (1+h/r)ⁿ vol K` and hence `vol({d ≤ h} \ K) ≤ ((1+h/r)ⁿ − 1)·vol K`.
   *Subtracting `vol K` is what produces the `√n`*: without it the `h`-integral is `≈ 1` and one
   gets nothing.

The resulting one-dimensional estimate (`Arlib.lintegral_weight_le`) is, in the regime
`4t√n ≤ r`,

`∫_0^∞ λ e^{2−λh}((1+h/r)ⁿ − 1) dh ≤ e²·λ·(n/r)·∫_0^∞ h e^{−7λh/8} dh = e²·(32/49)·t√n/r`,

using `(1+x)ⁿ − 1 ≤ nx·e^{nx}` and `n/r ≤ λ/8`.  Since `e²·32/49 = 4.826… < 5`, and since in the
complementary regime `4t√n > r` the claimed bound already exceeds `1` (and the left side never
exceeds `vol K · vol(tB)`), the constant `C = 10` works.  The sharpest constant this route gives
with the threshold `r/4` is `C = 2·e²·32/49 = 9.652…`; `10` is stated for readability.

## Cross-check against the printed statement

KLS97 print `C = 1`, i.e. `t√n/2r`.  Nothing here contradicts that: the ball attains
`1/√(2π) ≈ 0.399` against the printed `1/2`, and the bound proved here is a factor `≈ π`
*larger* than the ball's true value even asymptotically (the exact asymptotics of this route,
before the crude `e²` and `(1+x)ⁿ−1 ≤ nx e^{nx}` steps, is `√(π/2)·t√n/r = √(2π)·t√n/2r`).  So
`C = 10` is a genuine loss of a constant factor against the paper, not evidence of an error in
it.  The remark recorded in `KLS97.lean` — that KLS97's proof of its Lemma 4.3 is not rigorous
as printed, while its constants do check out — is unaffected: the route here never uses
Lemma 4.3, Corollary 4.4, or Corollary 4.5.

## Consequence downstream

`Arlib.lem33_sqrt` has **exactly** the shape of the `hLem33` hypothesis of
`Arlib.volume_goodSet_ge` and `Arlib.lintegral_stepRadius_ge` in
`Arlib/Convexity/StepLength.lean`, except that `Real.sqrt n` is replaced by `10 * Real.sqrt n`.
Those two theorems are stated with the bare `Real.sqrt n`, so `lem33_sqrt` does not discharge
them verbatim; restating them with `Real.sqrt n` replaced by `10 * Real.sqrt n` (equivalently,
carrying an absolute constant `C` through) turns Lemma 3.4's conclusion from
`∫_K s_α ≥ ((1−α)/√n)·vol K` into `∫_K s_α ≥ ((1−α)/(10√n))·vol K` — the same order in `n`,
which is all the conductance bound needs.  `lintegral_stepRadius_ge` already carries the
`IsClosed K` hypothesis that this file requires.

## Main results

* `Arlib.lintegral_volume_closedBall_sdiff_le_sqrt` — `(KLS-√n)`, general inradius `r`.
* `Arlib.lem33_sqrt` — the specialisation to `r = 1`, in the shape of `hLem33`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

section OneDim

/-- `x·e^{-x} ≤ 1` — the only calculus fact behind the tail estimates below. -/
private lemma mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h1 : x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have h2 : (0:ℝ) < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ h2, one_mul]
  exact h1

/-- `h·e^{−b h} ≤ 1/b` for `b > 0`. -/
private lemma mul_exp_neg_le {b : ℝ} (hb : 0 < b) (h : ℝ) :
    h * Real.exp (-b * h) ≤ 1 / b := by
  have hkey : (b * h) * Real.exp (-(b * h)) ≤ 1 := mul_exp_neg_le_one _
  have he : Real.exp (-b * h) = Real.exp (-(b * h)) := by congr 1; ring
  rw [he, le_div_iff₀ hb]
  calc h * Real.exp (-(b * h)) * b = (b * h) * Real.exp (-(b * h)) := by ring
    _ ≤ 1 := hkey

/-- `∫_{(d,∞)} a·e^{c−a h} dh = e^{c−a d}`, as a lower Lebesgue integral. -/
theorem lintegral_Ioi_exp_neg {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    ∫⁻ h in Set.Ioi d, ENNReal.ofReal (a * Real.exp (c - a * h))
      = ENNReal.ofReal (Real.exp (c - a * d)) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun h : ℝ => -Real.exp (c - a * h)) (a * Real.exp (c - a * x)) x := by
    intro x
    have h1 : HasDerivAt (fun h : ℝ => c - a * h) (-a) x := by
      simpa using ((hasDerivAt_id x).const_mul a).const_sub c
    have h2 := h1.exp.neg
    have h3 : -(Real.exp (c - a * x) * -a) = a * Real.exp (c - a * x) := by ring
    rwa [h3] at h2
  have hrw : (fun h : ℝ => a * Real.exp (c - a * h))
      = fun h : ℝ => (a * Real.exp c) * Real.exp (-a * h) := by
    funext h
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hint : IntegrableOn (fun h : ℝ => a * Real.exp (c - a * h)) (Set.Ioi d) := by
    rw [hrw]
    exact (exp_neg_integrableOn_Ioi d ha).const_mul _
  have htend : Tendsto (fun h : ℝ => -Real.exp (c - a * h)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => a * h) atTop atTop :=
      Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id
    have h2 : Tendsto (fun h : ℝ => c - a * h) atTop atBot := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atBot_add_const_left atTop c (tendsto_neg_atTop_atBot.comp h1)
    simpa using (Real.tendsto_exp_atBot.comp h2).neg
  have hval : ∫ h in Set.Ioi d, a * Real.exp (c - a * h) = Real.exp (c - a * d) := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun h : ℝ => -Real.exp (c - a * h))
      (f' := fun h : ℝ => a * Real.exp (c - a * h))
      (a := d) (m := 0)
      ((hderiv d).continuousAt.continuousWithinAt) (fun x _ => hderiv x) hint htend
    simpa using this
  rw [← hval, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun h => by positivity)]

/-- `∫_{(0,∞)} h·e^{−a h} dh = 1/a²`, as a lower Lebesgue integral. -/
private lemma lintegral_Ioi_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    ∫⁻ h in Set.Ioi (0:ℝ), ENNReal.ofReal (h * Real.exp (-(a * h)))
      = ENNReal.ofReal (1 / a ^ 2) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun h : ℝ => -(h / a + 1 / a ^ 2) * Real.exp (-(a * h)))
        (x * Real.exp (-(a * x))) x := by
    intro x
    have h1 : HasDerivAt (fun h : ℝ => -(h / a + 1 / a ^ 2)) (-(1 / a)) x := by
      have : HasDerivAt (fun h : ℝ => h / a + 1 / a ^ 2) (1 / a) x := by
        simpa using ((hasDerivAt_id x).div_const a).add_const (1 / a ^ 2)
      exact this.neg
    have h2 : HasDerivAt (fun h : ℝ => Real.exp (-(a * h)))
        (Real.exp (-(a * x)) * (-a)) x := by
      have hb : HasDerivAt (fun h : ℝ => -(a * h)) (-a) x := by
        simpa [neg_mul] using (hasDerivAt_id x).const_mul (-a)
      simpa using hb.exp
    have h3 := h1.mul h2
    have ha' : a ≠ 0 := ne_of_gt ha
    have heq : -(1 / a) * Real.exp (-(a * x))
        + -(x / a + 1 / a ^ 2) * (Real.exp (-(a * x)) * -a) = x * Real.exp (-(a * x)) := by
      field_simp
      ring
    rwa [heq] at h3
  have hbound : ∀ h : ℝ, 0 ≤ h → h * Real.exp (-(a * h)) ≤ (2 / a) * Real.exp (-(a / 2) * h) := by
    intro h hh
    have hb := mul_exp_neg_le (b := a / 2) (by positivity) h
    have he : Real.exp (-(a * h)) = Real.exp (-(a / 2) * h) * Real.exp (-(a / 2) * h) := by
      rw [← Real.exp_add]; congr 1; ring
    have hinv : (1:ℝ) / (a / 2) = 2 / a := one_div_div a 2
    rw [hinv] at hb
    calc h * Real.exp (-(a * h))
        = (h * Real.exp (-(a / 2) * h)) * Real.exp (-(a / 2) * h) := by rw [he]; ring
      _ ≤ (2 / a) * Real.exp (-(a / 2) * h) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : IntegrableOn (fun h : ℝ => h * Real.exp (-(a * h))) (Set.Ioi (0:ℝ)) := by
    have hg : IntegrableOn (fun h : ℝ => (2 / a) * Real.exp (-(a / 2) * h)) (Set.Ioi (0:ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul _
    refine Integrable.mono' hg ?_ ?_
    · exact (measurable_id.mul ((measurable_const.mul measurable_id).neg.exp)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      have hh0 : (0:ℝ) ≤ h := le_of_lt hh
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound h hh0
  have htend : Tendsto (fun h : ℝ => -(h / a + 1 / a ^ 2) * Real.exp (-(a * h))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u * Real.exp (-u) + Real.exp (-u)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    have h2 : Tendsto (fun h : ℝ => a * h) atTop atTop :=
      Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id
    have h3 := (h1.comp h2).const_mul (-(1 / a ^ 2))
    simp only [Function.comp] at h3
    rw [mul_zero] at h3
    have ha' : a ≠ 0 := ne_of_gt ha
    refine h3.congr fun h => ?_
    field_simp
  have hval : ∫ h in Set.Ioi (0:ℝ), h * Real.exp (-(a * h)) = 1 / a ^ 2 := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun h : ℝ => -(h / a + 1 / a ^ 2) * Real.exp (-(a * h)))
      (f' := fun h : ℝ => h * Real.exp (-(a * h)))
      (a := 0) (m := 0)
      ((hderiv 0).continuousAt.continuousWithinAt) (fun x _ => hderiv x) hint htend
    simpa using this
  rw [← hval, ← ofReal_integral_eq_lintegral_ofReal hint
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
        exact mul_nonneg (le_of_lt hh) (Real.exp_pos _).le)]

end OneDim

section Cap

open RealInnerProductSpace

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- **Supporting hyperplane at the metric projection.**  If `K` is closed convex and `y ∉ K`,
there is a unit vector `ν` with `⟪ν, x − y⟫ ≤ −d(y,K)` for every `x ∈ K`. -/
private lemma exists_unit_supporting (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKne : K.Nonempty)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∉ K) :
    ∃ ν : EuclideanSpace ℝ (Fin n), ‖ν‖ = 1 ∧
      ∀ x ∈ K, ⟪ν, x - y⟫ ≤ -Metric.infDist y K := by
  obtain ⟨v, hvK, hv⟩ := hKcl.exists_infDist_eq_dist hKne y
  have hne : y - v ≠ 0 := sub_ne_zero.mpr (fun hyv => hy (hyv ▸ hvK))
  set d : ℝ := ‖y - v‖ with hd
  have hd0 : 0 < d := norm_pos_iff.mpr hne
  have hdist : Metric.infDist y K = d := by rw [hv, dist_eq_norm]
  have hiInf : ‖y - v‖ = ⨅ w : K, ‖y - (w : EuclideanSpace ℝ (Fin n))‖ := by
    have hrw : (⨅ w : K, ‖y - (w : EuclideanSpace ℝ (Fin n))‖) = Metric.infDist y K := by
      rw [Metric.infDist_eq_iInf]
      simp only [dist_eq_norm]
    rw [hrw, hdist]
  have hchar := (norm_eq_iInf_iff_real_inner_le_zero hKc hvK).mp hiInf
  refine ⟨d⁻¹ • (y - v), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd0), ← hd]
    field_simp
  · intro x hx
    have h2 : ⟪y - v, x - v⟫ ≤ 0 := hchar x hx
    have h1 : ⟪y - v, x - y⟫ ≤ -d ^ 2 := by
      have h3 : x - y = (x - v) - (y - v) := by abel
      rw [h3, inner_sub_right, real_inner_self_eq_norm_sq, ← hd]
      linarith
    rw [hdist, real_inner_smul_left]
    calc d⁻¹ * ⟪y - v, x - y⟫ ≤ d⁻¹ * (-d ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = -d := by field_simp

/-- The spherical cap cut off a ball of radius `t` by a hyperplane at distance `h` from the
centre lies in a ball of radius `√(t²−h²)`; hence the bound on `vol(K ∩ B(y,t))`. -/
theorem volume_inter_closedBall_le_sqrt (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKne : K.Nonempty) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∉ K) (t : ℝ) :
    volume (K ∩ Metric.closedBall y t)
      ≤ ENNReal.ofReal (Real.sqrt (t ^ 2 - Metric.infDist y K ^ 2) ^ n)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  obtain ⟨ν, hν1, hνK⟩ := exists_unit_supporting hKc hKcl hKne hy
  set h : ℝ := Metric.infDist y K with hhdef
  have hh0 : 0 ≤ h := Metric.infDist_nonneg
  have hsub : K ∩ Metric.closedBall y t
      ⊆ Metric.closedBall (y - h • ν) (Real.sqrt (t ^ 2 - h ^ 2)) := by
    rintro x ⟨hxK, hxB⟩
    have hxy : ‖x - y‖ ≤ t := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hxB; exact hxB
    have hin : ⟪ν, x - y⟫ ≤ -h := hνK x hxK
    have hnorm : ‖x - (y - h • ν)‖ ^ 2 ≤ t ^ 2 - h ^ 2 := by
      have he : x - (y - h • ν) = (x - y) + h • ν := by abel
      rw [he, norm_add_sq_real]
      have e1 : ⟪x - y, h • ν⟫ = h * ⟪ν, x - y⟫ := by
        rw [real_inner_smul_right, real_inner_comm]
      have e2 : ‖h • ν‖ = h := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0, hν1, mul_one]
      rw [e1, e2]
      have hA : ‖x - y‖ ^ 2 ≤ t ^ 2 := by nlinarith [norm_nonneg (x - y)]
      have hB : h * ⟪ν, x - y⟫ ≤ h * (-h) := mul_le_mul_of_nonneg_left hin hh0
      nlinarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact Real.le_sqrt_of_sq_le hnorm
  calc volume (K ∩ Metric.closedBall y t)
      ≤ volume (Metric.closedBall (y - h • ν) (Real.sqrt (t ^ 2 - h ^ 2))) := measure_mono hsub
    _ = _ := by
        rw [MeasureTheory.Measure.addHaar_closedBall volume _ (Real.sqrt_nonneg _),
          finrank_euclideanSpace_fin]

/-- `√(t²−h²)ⁿ ≤ e^{2 − 2√n·h/t}·tⁿ`: the Gaussian majorant of the cap weight. -/
private lemma sqrt_pow_le_exp {n : ℕ} {t h : ℝ} (ht : 0 < t) :
    Real.sqrt (t ^ 2 - h ^ 2) ^ n
      ≤ Real.exp (2 - 2 * Real.sqrt n / t * h) * t ^ n := by
  set s : ℝ := Real.sqrt n with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  -- pointwise Gaussian bound on the radius
  have hstep : Real.sqrt (t ^ 2 - h ^ 2) ≤ t * Real.exp (-(h ^ 2 / (2 * t ^ 2))) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hE : (t * Real.exp (-(h ^ 2 / (2 * t ^ 2)))) ^ 2
        = t ^ 2 * Real.exp (-(h ^ 2 / t ^ 2)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      field_simp
      ring
    rw [hE]
    have hbase : 1 - h ^ 2 / t ^ 2 ≤ Real.exp (-(h ^ 2 / t ^ 2)) := by
      have := Real.add_one_le_exp (-(h ^ 2 / t ^ 2))
      linarith
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hbase ht2.le
    calc t ^ 2 - h ^ 2 = t ^ 2 * (1 - h ^ 2 / t ^ 2) := by field_simp
      _ ≤ t ^ 2 * Real.exp (-(h ^ 2 / t ^ 2)) := this
  -- raise to the `n`-th power
  have hpow : Real.sqrt (t ^ 2 - h ^ 2) ^ n
      ≤ t ^ n * Real.exp (-((n : ℝ) * h ^ 2 / (2 * t ^ 2))) := by
    calc Real.sqrt (t ^ 2 - h ^ 2) ^ n
        ≤ (t * Real.exp (-(h ^ 2 / (2 * t ^ 2)))) ^ n :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep n
      _ = t ^ n * Real.exp (-((n : ℝ) * h ^ 2 / (2 * t ^ 2))) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          ring
  refine hpow.trans ?_
  rw [mul_comm (t ^ n)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  rw [← sub_nonneg]
  have hkey : 2 - 2 * s / t * h - -((n : ℝ) * h ^ 2 / (2 * t ^ 2))
      = (s * h - 2 * t) ^ 2 / (2 * t ^ 2) := by
    rw [← hsn]
    field_simp
    ring
  rw [hkey]
  positivity

/-- The unrelaxed Gaussian spherical-cap factor used by KLS97 Theorem 4.16. -/
theorem sqrt_pow_le_gaussian_exp {n : ℕ} {t h : ℝ} (ht : 0 < t) :
    Real.sqrt (t ^ 2 - h ^ 2) ^ n ≤
      Real.exp (-((n : ℝ) * h ^ 2 / (2 * t ^ 2))) * t ^ n := by
  have hstep : Real.sqrt (t ^ 2 - h ^ 2) ≤
      t * Real.exp (-(h ^ 2 / (2 * t ^ 2))) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hE : (t * Real.exp (-(h ^ 2 / (2 * t ^ 2)))) ^ 2 =
        t ^ 2 * Real.exp (-(h ^ 2 / t ^ 2)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      field_simp
      ring
    rw [hE]
    have hbase : 1 - h ^ 2 / t ^ 2 ≤
        Real.exp (-(h ^ 2 / t ^ 2)) := by
      have h := Real.add_one_le_exp (-(h ^ 2 / t ^ 2))
      linarith
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbase ht2.le
    calc
      t ^ 2 - h ^ 2 = t ^ 2 * (1 - h ^ 2 / t ^ 2) := by field_simp
      _ ≤ t ^ 2 * Real.exp (-(h ^ 2 / t ^ 2)) := hmul
  calc
    Real.sqrt (t ^ 2 - h ^ 2) ^ n ≤
        (t * Real.exp (-(h ^ 2 / (2 * t ^ 2)))) ^ n :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep n
    _ = Real.exp (-((n : ℝ) * h ^ 2 / (2 * t ^ 2))) * t ^ n := by
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [mul_comm]
      congr 1
      ring

end Cap

section Shell

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {z : EuclideanSpace ℝ (Fin n)} {r : ℝ}

/-- **The shell bound.**  If `K` is convex, closed and contains `B(z,r)`, then the `h`-neighbourhood
of `K` has volume at most `(1 + h/r)ⁿ · vol K`.

The witness is the homothety of ratio `1 + h/r` about `z`: a point at distance `≤ h` from `K` is
the image of a convex combination of a point of `K` with a point of `B(z,r) ⊆ K`. -/
private lemma volume_infDist_le_le (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r) {h : ℝ} (hh : 0 < h) :
    volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}
      ≤ ENNReal.ofReal ((1 + h / r) ^ n) * volume K := by
  have hKne : K.Nonempty := ⟨z, hball (Metric.mem_closedBall_self hr.le)⟩
  set c : ℝ := 1 + h / r with hc
  have hc1 : 1 ≤ c := by
    have hhr : (0:ℝ) ≤ h / r := by positivity
    rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hθ1 : c⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hc1
  have hθ0 : 0 < c⁻¹ := by positivity
  have hsub : {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}
      ⊆ AffineMap.homothety z c '' K := by
    intro y hy
    obtain ⟨v, hvK, hv⟩ := hKcl.exists_infDist_eq_dist hKne y
    have hu : ‖y - v‖ ≤ h := by
      rw [← dist_eq_norm, ← hv]; exact hy
    refine ⟨AffineMap.homothety z c⁻¹ y, ?_, ?_⟩
    · have hp : z + (r / h) • (y - v) ∈ K := by
        refine hball ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hn1 : ‖z + (r / h) • (y - v) - z‖ = (r / h) * ‖y - v‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [hn1]
        calc (r / h) * ‖y - v‖ ≤ (r / h) * h :=
              mul_le_mul_of_nonneg_left hu (by positivity)
          _ = r := by field_simp
      have hcomb := hKc hvK hp hθ0.le (by linarith : (0:ℝ) ≤ 1 - c⁻¹) (by ring)
      have hscal : (1 - c⁻¹) • ((r / h) • (y - v)) = c⁻¹ • (y - v) := by
        rw [smul_smul]
        congr 1
        rw [hc]
        field_simp
        ring
      have heq : AffineMap.homothety z c⁻¹ y
          = c⁻¹ • v + (1 - c⁻¹) • (z + (r / h) • (y - v)) := by
        rw [AffineMap.homothety_apply]
        simp only [vsub_eq_sub, vadd_eq_add, smul_add, hscal]
        module
      rw [heq]
      exact hcomb
    · rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc0)
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul, hcc, one_smul]
      abel
  calc volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}
      ≤ volume (AffineMap.homothety z c '' K) := measure_mono hsub
    _ = ENNReal.ofReal ((1 + h / r) ^ n) * volume K := by
        rw [MeasureTheory.Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
          abs_of_nonneg (pow_nonneg hc0.le n)]

/-- The part of the `h`-neighbourhood of `K` outside `K` has volume at most
`((1+h/r)ⁿ − 1)·vol K`.  Subtracting `vol K` is what produces the `√n`. -/
private lemma volume_shell_le (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r) {h : ℝ} (hh : 0 < h) :
    volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} \ K)
      ≤ ENNReal.ofReal ((1 + h / r) ^ n - 1) * volume K := by
  have hKsub : K ⊆ {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} := by
    intro y hyK
    have h0 : Metric.infDist y K ≤ 0 := by
      simpa using Metric.infDist_le_dist_of_mem (x := y) hyK
    simp only [Set.mem_setOf_eq]
    linarith
  have hdiff : volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} \ K)
      = volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} - volume K :=
    measure_sdiff hKsub hKcl.measurableSet.nullMeasurableSet hKfin
  have hA : (1:ℝ) ≤ (1 + h / r) ^ n := by
    refine one_le_pow₀ ?_
    have : 0 ≤ h / r := by positivity
    linarith
  have hrw : ENNReal.ofReal ((1 + h / r) ^ n - 1) + 1 = ENNReal.ofReal ((1 + h / r) ^ n) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one]
    congr 1
    ring
  rw [hdiff, tsub_le_iff_right]
  calc volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}
      ≤ ENNReal.ofReal ((1 + h / r) ^ n) * volume K :=
        volume_infDist_le_le hKc hKcl hball hr hh
    _ = (ENNReal.ofReal ((1 + h / r) ^ n - 1) + 1) * volume K := by rw [hrw]
    _ = ENNReal.ofReal ((1 + h / r) ^ n - 1) * volume K + volume K := by
        rw [add_mul, one_mul]

end Shell

section Swap

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- **Swapping the roles of the inside and the outside point.**  Both sides compute the measure
of `{(x,y) : x ∈ K, y ∉ K, dist x y ≤ t}`. -/
private lemma lintegral_sdiff_eq_lintegral_inter (t : ℝ) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      = ∫⁻ y in Kᶜ, volume (K ∩ Metric.closedBall y t) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | dist p.1 p.2 ≤ t} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x y => S.indicator 1 (x, y) with hf
  have hmeas : Measurable (Function.uncurry f) := by
    rw [hf]
    exact measurable_one.indicator hSm
  have hx : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y in Kᶜ, f x y = volume (Metric.closedBall x t \ K) := by
    intro x
    have hrw : ∀ y, f x y
        = (Metric.closedBall x t).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y := by
      intro y
      simp only [hf, Set.indicator_apply, hS, Set.mem_setOf_eq, Metric.mem_closedBall,
        Pi.one_apply]
      rw [dist_comm y x]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.sdiff_eq]
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ x in K, f x y = volume (K ∩ Metric.closedBall y t) := by
    intro y
    have hrw : ∀ x, f x y
        = (Metric.closedBall y t).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) x := by
      intro x
      simp only [hf, Set.indicator_apply, hS, Set.mem_setOf_eq, Metric.mem_closedBall,
        Pi.one_apply]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
  have hswap := lintegral_lintegral_swap (μ := volume.restrict K)
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Kᶜ) hmeas.aemeasurable
  simp_rw [hx, hy] at hswap
  exact hswap

end Swap

section LayerCake

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- **Layer cake against the decreasing weight `e^{c−a·d(y,K)}`.**

`∫_{Kᶜ} e^{c − a·d(y,K)} dy = ∫_0^∞ a·e^{c−a h} · vol({d(·,K) ≤ h} \ K) dh`.

Both sides compute the measure of `{(y,h) : y ∉ K, h > 0, d(y,K) ≤ h}` weighted by
`a·e^{c−a h}`; the `h`-marginal is the fundamental theorem of calculus
(`Arlib.lintegral_Ioi_exp_neg`). -/
private lemma layercake_infDist {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫⁻ y in Kᶜ, ENNReal.ofReal (Real.exp (c - a * Metric.infDist y K))
      = ∫⁻ h in Set.Ioi (0:ℝ), ENNReal.ofReal (a * Real.exp (c - a * h))
          * volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} \ K) := by
  classical
  have hinfc : Continuous fun y : EuclideanSpace ℝ (Fin n) => Metric.infDist y K :=
    Metric.continuous_infDist_pt K
  set T : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | Metric.infDist p.1 K ≤ p.2} with hT
  have hTm : MeasurableSet T :=
    measurableSet_le (hinfc.measurable.comp measurable_fst) measurable_snd
  set F : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ :=
    fun y h => T.indicator (fun p => ENNReal.ofReal (a * Real.exp (c - a * p.2))) (y, h) with hF
  have hmeas : Measurable (Function.uncurry F) := by
    rw [hF]
    refine Measurable.indicator ?_ hTm
    exact (ENNReal.measurable_ofReal.comp
      (((measurable_const.mul measurable_snd).const_sub c).exp.const_mul a))
  -- the `h`-marginal: FTC for the exponential weight
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ h in Set.Ioi (0:ℝ), F y h
        = ENNReal.ofReal (Real.exp (c - a * Metric.infDist y K)) := by
    intro y
    have hd0 : 0 ≤ Metric.infDist y K := Metric.infDist_nonneg
    have hrw : ∀ h : ℝ, F y h
        = (Set.Ici (Metric.infDist y K)).indicator
            (fun h => ENNReal.ofReal (a * Real.exp (c - a * h))) h := by
      intro h
      simp only [hF, Set.indicator_apply, hT, Set.mem_setOf_eq, Set.mem_Ici]
    simp_rw [hrw]
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hae : ((Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0:ℝ) : Set ℝ))
        =ᵐ[volume] (Set.Ioi (Metric.infDist y K) : Set ℝ) := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null ?_ (measure_singleton (Metric.infDist y K))
        rintro x ⟨⟨hx1, _⟩, hx2⟩
        simp only [Set.mem_Ioi, not_lt] at hx2
        simp only [Set.mem_singleton_iff]
        exact le_antisymm hx2 hx1
      · have hsub : Set.Ioi (Metric.infDist y K)
            ⊆ Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0:ℝ) := by
          intro x hx
          rw [Set.mem_Ioi] at hx
          exact ⟨Set.mem_Ici.mpr hx.le, Set.mem_Ioi.mpr (lt_of_le_of_lt hd0 hx)⟩
        rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
    rw [MeasureTheory.setLIntegral_congr hae]
    exact lintegral_Ioi_exp_neg ha c _
  -- the `y`-marginal: the shell measure
  have hx : ∀ h : ℝ, ∫⁻ y in Kᶜ, F y h
      = ENNReal.ofReal (a * Real.exp (c - a * h))
          * volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} \ K) := by
    intro h
    have hSm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} :=
      measurableSet_le hinfc.measurable measurable_const
    have hrw : ∀ y : EuclideanSpace ℝ (Fin n), F y h
        = ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}).indicator
            (fun _ => ENNReal.ofReal (a * Real.exp (c - a * h))) y := by
      intro y
      simp only [hF, Set.indicator_apply, hT, Set.mem_setOf_eq]
    simp_rw [hrw]
    rw [lintegral_indicator hSm, setLIntegral_const, Measure.restrict_apply hSm, Set.sdiff_eq]
  have hswap := lintegral_lintegral_swap
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Kᶜ)
    (ν := (volume : Measure ℝ).restrict (Set.Ioi 0)) hmeas.aemeasurable
  simp_rw [hy, hx] at hswap
  exact hswap

end LayerCake

section Weight

/-- The pointwise majorant driving the `√n`: in the regime `4t√n ≤ r`,

`λ·e^{2−λh}·((1+h/r)ⁿ − 1) ≤ e²·λ·(n/r)·h·e^{−7λh/8}`,  with `λ = 2√n/t`. -/
private lemma weight_pointwise_le {n : ℕ} {t r h : ℝ} (ht : 0 < t) (hr : 0 < r) (hh : 0 < h)
    (hcase : 4 * t * Real.sqrt n ≤ r) :
    (2 * Real.sqrt n / t) * Real.exp (2 - (2 * Real.sqrt n / t) * h) * ((1 + h / r) ^ n - 1)
      ≤ Real.exp 2 * (2 * Real.sqrt n / t) * ((n : ℝ) / r)
          * (h * Real.exp (-(7 * (2 * Real.sqrt n / t) / 8 * h))) := by
  set s : ℝ := Real.sqrt n with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  set lam : ℝ := 2 * s / t with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set X : ℝ := (n : ℝ) * (h / r) with hX
  have hX0 : 0 ≤ X := by positivity
  have hpow : (1 + h / r) ^ n ≤ Real.exp X := by
    have h1 : (1 : ℝ) + h / r ≤ Real.exp (h / r) := by
      have := Real.add_one_le_exp (h / r); linarith
    calc (1 + h / r) ^ n ≤ (Real.exp (h / r)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp X := by rw [← Real.exp_nat_mul, hX]
  have hexp : Real.exp X - 1 ≤ X * Real.exp X := by
    have h1 := Real.add_one_le_exp (-X)
    have h2 : (0:ℝ) < Real.exp X := Real.exp_pos X
    have h3 : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hXle : X ≤ lam / 8 * h := by
    have hfac : lam / 8 * h - X = s * h * (r - 4 * t * s) / (4 * t * r) := by
      rw [hX, hlam, ← hsn]
      field_simp
      ring
    have hnn : 0 ≤ s * h * (r - 4 * t * s) / (4 * t * r) := by
      refine div_nonneg (mul_nonneg (by positivity) ?_) (by positivity)
      linarith
    linarith
  have hstep : (1 + h / r) ^ n - 1 ≤ X * Real.exp (lam / 8 * h) := by
    have h1 : Real.exp X ≤ Real.exp (lam / 8 * h) := Real.exp_le_exp.mpr hXle
    calc (1 + h / r) ^ n - 1 ≤ Real.exp X - 1 := by linarith
      _ ≤ X * Real.exp X := hexp
      _ ≤ X * Real.exp (lam / 8 * h) := mul_le_mul_of_nonneg_left h1 hX0
  have he : Real.exp (2 - lam * h) * Real.exp (lam / 8 * h)
      = Real.exp 2 * Real.exp (-(7 * lam / 8 * h)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc lam * Real.exp (2 - lam * h) * ((1 + h / r) ^ n - 1)
      ≤ lam * Real.exp (2 - lam * h) * (X * Real.exp (lam / 8 * h)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = lam * ((n : ℝ) / r) * h * (Real.exp (2 - lam * h) * Real.exp (lam / 8 * h)) := by
        rw [hX]; ring
    _ = lam * ((n : ℝ) / r) * h * (Real.exp 2 * Real.exp (-(7 * lam / 8 * h))) := by rw [he]
    _ = Real.exp 2 * lam * ((n : ℝ) / r) * (h * Real.exp (-(7 * lam / 8 * h))) := by ring

/-- **The one-dimensional estimate.**  In the regime `4t√n ≤ r`,

`∫_0^∞ λ·e^{2−λh}·((1+h/r)ⁿ − 1) dh ≤ 5·t·√n/r`,  with `λ = 2√n/t`.

The exact value of the majorant integral is `e²·32·t√n/(49 r)`, and `e²·32/49 < 4.83 < 5`. -/
private lemma lintegral_weight_le {n : ℕ} (hn : n ≠ 0) {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hcase : 4 * t * Real.sqrt n ≤ r) :
    ∫⁻ h in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((2 * Real.sqrt n / t) * Real.exp (2 - (2 * Real.sqrt n / t) * h))
          * ENNReal.ofReal ((1 + h / r) ^ n - 1)
      ≤ ENNReal.ofReal (5 * t * Real.sqrt n / r) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  set s : ℝ := Real.sqrt n with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnpos
  have hsn : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  set lam : ℝ := 2 * s / t with hlam
  have hlam0 : 0 < lam := by positivity
  have hpt : ∀ h ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (lam * Real.exp (2 - lam * h)) * ENNReal.ofReal ((1 + h / r) ^ n - 1)
        ≤ ENNReal.ofReal (Real.exp 2 * lam * ((n : ℝ) / r))
            * ENNReal.ofReal (h * Real.exp (-(7 * lam / 8 * h))) := by
    intro h hh
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (weight_pointwise_le ht hr hh hcase)
  have he2 : Real.exp 2 < 7.4 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [h1]
    nlinarith
  have hnum : Real.exp 2 * lam * ((n : ℝ) / r) * (1 / (7 * lam / 8) ^ 2)
      = Real.exp 2 * 32 * t * s / (49 * r) := by
    rw [hlam, ← hsn]
    field_simp
    ring
  have hfin : Real.exp 2 * 32 * t * s / (49 * r) ≤ 5 * t * s / r := by
    rw [div_le_div_iff₀ (by positivity) hr]
    nlinarith [mul_pos (mul_pos ht hs0) hr]
  calc ∫⁻ h in Set.Ioi (0:ℝ),
        ENNReal.ofReal (lam * Real.exp (2 - lam * h)) * ENNReal.ofReal ((1 + h / r) ^ n - 1)
      ≤ ∫⁻ _h in Set.Ioi (0:ℝ), ENNReal.ofReal (Real.exp 2 * lam * ((n : ℝ) / r))
            * ENNReal.ofReal (_h * Real.exp (-(7 * lam / 8 * _h))) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (Real.exp 2 * lam * ((n : ℝ) / r))
          * ∫⁻ h in Set.Ioi (0:ℝ), ENNReal.ofReal (h * Real.exp (-(7 * lam / 8 * h))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp 2 * lam * ((n : ℝ) / r))
          * ENNReal.ofReal (1 / (7 * lam / 8) ^ 2) := by
        rw [lintegral_Ioi_mul_exp_neg (by positivity)]
    _ = ENNReal.ofReal (Real.exp 2 * lam * ((n : ℝ) / r) * (1 / (7 * lam / 8) ^ 2)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (5 * t * s / r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hnum]
        exact hfin

end Weight

section Main

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {z : EuclideanSpace ℝ (Fin n)} {r : ℝ}

/-- **Corollary 4.6 of Kannan–Lovász–Simonovits 1997, at the sharp order `√n`,
with the explicit absolute constant `C = 10`.** -/
theorem lintegral_volume_closedBall_sdiff_le_sqrt (hn : n ≠ 0) (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤) (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (10 * (t * Real.sqrt n) / (2 * r)) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hKm : MeasurableSet K := hKcl.measurableSet
  have hKne : K.Nonempty := ⟨z, hball (Metric.mem_closedBall_self hr.le)⟩
  have hBfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hconst : (10 : ℝ) * (t * Real.sqrt n) / (2 * r) = 5 * t * Real.sqrt n / r := by
    field_simp
    ring
  rw [hconst]
  rcases le_or_gt (4 * t * Real.sqrt n) r with hcase | hcase
  · -- the substantial case `4t√n ≤ r`
    rw [lintegral_sdiff_eq_lintegral_inter (K := K) t]
    have hcap : ∀ y ∈ Kᶜ, volume (K ∩ Metric.closedBall y t)
        ≤ ENNReal.ofReal (Real.exp (2 - 2 * Real.sqrt n / t * Metric.infDist y K))
            * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
      intro y hy
      have h1 := volume_inter_closedBall_le_sqrt hKc hKcl hKne hy t
      have h2 : Real.sqrt (t ^ 2 - Metric.infDist y K ^ 2) ^ n
          ≤ Real.exp (2 - 2 * Real.sqrt n / t * Metric.infDist y K) * t ^ n :=
        sqrt_pow_le_exp ht
      rw [MeasureTheory.Measure.addHaar_closedBall volume (0 : EuclideanSpace ℝ (Fin n)) ht.le,
        finrank_euclideanSpace_fin]
      refine h1.trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h2) _
    calc ∫⁻ y in Kᶜ, volume (K ∩ Metric.closedBall y t)
        ≤ ∫⁻ y in Kᶜ, ENNReal.ofReal
              (Real.exp (2 - 2 * Real.sqrt n / t * Metric.infDist y K))
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
          setLIntegral_mono' hKm.compl hcap
      _ = (∫⁻ y in Kᶜ, ENNReal.ofReal
              (Real.exp (2 - 2 * Real.sqrt n / t * Metric.infDist y K)))
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
          lintegral_mul_const' _ _ hBfin
      _ = (∫⁻ h in Set.Ioi (0:ℝ),
              ENNReal.ofReal (2 * Real.sqrt n / t * Real.exp (2 - 2 * Real.sqrt n / t * h))
                * volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} \ K))
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
          rw [layercake_infDist (by positivity) 2]
      _ ≤ (∫⁻ h in Set.Ioi (0:ℝ),
              ENNReal.ofReal (2 * Real.sqrt n / t * Real.exp (2 - 2 * Real.sqrt n / t * h))
                * (ENNReal.ofReal ((1 + h / r) ^ n - 1) * volume K))
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
          refine mul_le_mul_left (setLIntegral_mono' measurableSet_Ioi ?_) _
          intro h hh
          exact mul_le_mul_right
            (volume_shell_le hKc hKcl hKfin hball hr (Set.mem_Ioi.mp hh)) _
      _ = ((∫⁻ h in Set.Ioi (0:ℝ),
              ENNReal.ofReal (2 * Real.sqrt n / t * Real.exp (2 - 2 * Real.sqrt n / t * h))
                * ENNReal.ofReal ((1 + h / r) ^ n - 1)) * volume K)
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
          congr 1
          rw [← lintegral_mul_const' _ _ hKfin]
          exact lintegral_congr fun h => (mul_assoc _ _ _).symm
      _ ≤ (ENNReal.ofReal (5 * t * Real.sqrt n / r) * volume K)
                * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
          mul_le_mul_left (mul_le_mul_left (lintegral_weight_le hn ht hr hcase) _) _
  · -- the bound is vacuous: `5t√n/r > 5/4 ≥ 1`
    have h1 : (1:ℝ) ≤ 5 * t * Real.sqrt n / r := by
      rw [le_div_iff₀ hr]
      nlinarith
    have hone : (1:ℝ≥0∞) ≤ ENNReal.ofReal (5 * t * Real.sqrt n / r) :=
      ENNReal.one_le_ofReal.mpr h1
    calc ∫⁻ x in K, volume (Metric.closedBall x t \ K)
        ≤ ∫⁻ _x in K, volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
          refine setLIntegral_mono' hKm ?_
          intro x _
          calc volume (Metric.closedBall x t \ K) ≤ volume (Metric.closedBall x t) :=
                measure_mono Set.sdiff_subset
            _ = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
                rw [MeasureTheory.Measure.addHaar_closedBall volume x ht.le,
                  MeasureTheory.Measure.addHaar_closedBall volume
                    (0 : EuclideanSpace ℝ (Fin n)) ht.le]
      _ = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) * volume K :=
          setLIntegral_const _ _
      _ = 1 * volume K * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
          rw [one_mul, mul_comm]
      _ ≤ ENNReal.ofReal (5 * t * Real.sqrt n / r) * volume K
            * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
          mul_le_mul_left (mul_le_mul_left hone _) _

/-- **The specialisation to inradius `1`**, in exactly the shape of the `hLem33` hypothesis
carried by `Arlib.volume_goodSet_ge` and `Arlib.lintegral_stepRadius_ge` — with `Real.sqrt n`
replaced by `10 * Real.sqrt n`. -/
theorem lem33_sqrt (hn : n ≠ 0) (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : Metric.closedBall z 1 ⊆ K) :
    ∀ t : ℝ, 0 < t → ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
  intro t ht
  have h := lintegral_volume_closedBall_sdiff_le_sqrt hn hKc hKcl hKfin hball one_pos ht
  have heq : (10:ℝ) * (t * Real.sqrt n) / (2 * 1) = t * (10 * Real.sqrt n) / 2 := by ring
  rwa [heq] at h

end Main

end Arlib
