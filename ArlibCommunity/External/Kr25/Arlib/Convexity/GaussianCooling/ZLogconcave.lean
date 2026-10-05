/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.Variance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Localization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `ZLogconcaveHypothesis` is a theorem for convex bodies

`Arlib.Convexity.GaussianCooling.Variance` carries paper Lemma 5.9 of Cousins–Vempala as the
explicit hypothesis

```
ZLogconcaveHypothesis f : ∀ a b, 0 < a → 0 < b → zFun f a * zFun f b ≤ zFun f ((a+b)/2) ^ 2
```

with `zFun f a = a^{n+1} · ∫ f(x) e^{-a‖x‖²/2} dx`, on the grounds that Mathlib has neither
Prékopa–Leindler nor Brunn–Minkowski.  `Arlib.Convexity.PrekopaLeindlerN` and
`Arlib.Convexity.Localization` now do, so the hypothesis can be discharged.  This file
discharges it for the case the algorithm actually uses — `f` a (multiple of the) indicator
of a convex measurable set:

* `Arlib.GaussianCooling.zLogconcaveHypothesis_indicator` — for `f = 1_K`, `K` convex and
  measurable, with no boundedness, roundness or `0 ∈ K` hypothesis;
* `Arlib.GaussianCooling.zLogconcaveHypothesis_indicator_const` — for `f = c · 1_K`, any
  `c : ℝ`;
* `Arlib.GaussianCooling.fixed_var_bound_indicator` and
  `Arlib.GaussianCooling.fixed_var_bound_ratio_indicator` — paper Lemma 5.10 for a convex
  body, now *unconditional*.

## The proof

The claim is **not** log-concavity of `a ↦ ∫ f e^{-a‖x‖²/2}` — that function is log-*convex*
(it is a Laplace transform of a positive measure).  The `a^{n+1}` prefactor is what makes the
product log-concave, and it is visible only after the change of variables `x = y/A`:

  `z(A) = A^{n+1} ∫ f(x) e^{-A‖x‖²/2} dx = ∫ A · f(y/A) · e^{-‖y‖²/(2A)} dy`   (`zFun_eq_integral`)

so `z` is a *marginal* of the function `(A, y) ↦ A · f(y/A) · e^{-‖y‖²/(2A)}` on
`ℝ × ℝⁿ`, and Prékopa's marginal theorem (`Arlib.isLogConcave_marginal_pi`) applies as soon
as that integrand is **jointly** log-concave.  For `f = 1_K` it is
(`isLogConcave_zIntegrand`), because the integrand is the indicator of the cone
`{(A, y) : A > 0, y/A ∈ K}` — convex for convex `K` (`convex_zCone`) — times

* `A`, whose `-log` is the convex `-log A`, handled by weighted AM–GM
  (`geom_mean_le_arith_mean2_weighted`), and
* `e^{-‖y‖²/(2A)}`, whose exponent is the **perspective** of `‖y‖²/2`, jointly convex by the
  two-term Cauchy–Schwarz inequality `(au+bv)²/(aA+bB) ≤ au²/A + bv²/B`
  (`sq_div_add_le`, `sum_sq_perspective_le`).

Log-concavity of `z` at the midpoint, with weights `(1/2, 1/2)`, is exactly
`ZLogconcaveHypothesis` after squaring.

## `ZLogconcaveHypothesis` is FALSE for general log-concave `f`

The predicate as stated in `Variance.lean` quantifies over an arbitrary `f : ℝⁿ → ℝ`, and it
does **not** hold for every log-concave `f`, so it cannot be discharged in that generality.
Counterexample (`n = 1`, `f x = e^{-x}`, which is log-concave, positive, and has `G f s`
finite for every `s > 0`):

  `∫ e^{-x} e^{-A x²/2} dx = √(2π/A) · e^{1/(2A)}`, so `z(A) = √(2π) · A^{3/2} e^{1/(2A)}`
  and `log z(A) = c + (3/2) log A + 1/(2A)`, whose second derivative
  `-3/(2A²) + 1/A³` is **positive** for `A < 2/3`: `log z` is strictly *convex* there.

At `a = 1/10`, `b = 1/5`, `(a+b)/2 = 3/20`:

  `z(a)·z(b) / z((a+b)/2)² = (ab)^{3/2} e^{1/(2a)+1/(2b)} / ((a+b)/2)³ e^{2/(a+b)} ≈ 1.928 > 1`,

i.e. `zFun f a * zFun f b ≤ zFun f ((a+b)/2)^2` fails by a factor `≈ 1.93`.  (Checked
numerically against a direct quadrature of the integral as well as against the closed form.)

The obstruction is structural, not an artefact of this proof: the argument above needs
`(A, y) ↦ f(y/A)` to be jointly log-concave, and a `0`-homogeneous function is convex only
if it is constant on its (convex) domain — so, up to a constant factor, indicators of convex
sets are exactly the `f`'s for which the route works.

**Consequence for the audit.**  `fixed_var_bound` and `fixed_var_bound_ratio` are stated for
an arbitrary `f` with `ZLogconcaveHypothesis f` as a hypothesis, which is sound; but that
hypothesis must not be read as "true for every log-concave `f`".  The theorems below are the
instances that are actually available.

## What this file does *not* do

`LocalizationHypothesis` (`Variance.lean:1095`) is untouched: it quantifies over needles and
concludes a statement about the body, i.e. it *is* the Localization Lemma of
Lovász–Simonovits, which this route says nothing about.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real

variable {n : ℕ}

/-! ## The perspective inequality

Joint convexity of `(A, y) ↦ ‖y‖²/(2A)` on `A > 0`, in coordinates.  Everything reduces to
the two-term Cauchy–Schwarz (Engel form) inequality, one coordinate at a time. -/

/-- **Two-term Cauchy–Schwarz, Engel form.**  `(au+bv)²/(aA+bB) ≤ au²/A + bv²/B`; the gap is
`ab(uB-vA)²/(AB)`. -/
theorem sq_div_add_le {a b A B u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B)
    (hpos : 0 < a * A + b * B) :
    (a * u + b * v) ^ 2 / (a * A + b * B) ≤ a * u ^ 2 / A + b * v ^ 2 / B := by
  rw [div_le_iff₀ hpos]
  have key : (a * u ^ 2 / A + b * v ^ 2 / B) * (a * A + b * B) - (a * u + b * v) ^ 2
      = a * b * (u * B - v * A) ^ 2 / (A * B) := by
    field_simp
    ring
  nlinarith [div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u * B - v * A)))
    (mul_pos hA hB).le]

/-- **The perspective inequality** for the squared Euclidean norm, in coordinates:
`‖ay+bz‖²/(2(aA+bB)) ≤ a‖y‖²/(2A) + b‖z‖²/(2B)`. -/
theorem sum_sq_perspective_le {a b A B : ℝ} (y z : Fin n → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B) (hpos : 0 < a * A + b * B) :
    (∑ i, (a • y + b • z) i ^ 2) / (2 * (a * A + b * B))
      ≤ a * ((∑ i, y i ^ 2) / (2 * A)) + b * ((∑ i, z i ^ 2) / (2 * B)) := by
  have h2 : a * (2 * A) + b * (2 * B) = 2 * (a * A + b * B) := by ring
  have hpos2 : 0 < a * (2 * A) + b * (2 * B) := by rw [h2]; linarith
  have hstep : ∀ i : Fin n, ((a • y + b • z) i) ^ 2 / (2 * (a * A + b * B))
      ≤ a * (y i) ^ 2 / (2 * A) + b * (z i) ^ 2 / (2 * B) := by
    intro i
    have h := sq_div_add_le (a := a) (b := b) (A := 2 * A) (B := 2 * B) (u := y i) (v := z i)
      ha hb (by linarith) (by linarith) hpos2
    rw [h2] at h
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  calc (∑ i, (a • y + b • z) i ^ 2) / (2 * (a * A + b * B))
      = ∑ i, ((a • y + b • z) i) ^ 2 / (2 * (a * A + b * B)) := by rw [Finset.sum_div]
    _ ≤ ∑ i, (a * (y i) ^ 2 / (2 * A) + b * (z i) ^ 2 / (2 * B)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = a * ((∑ i, y i ^ 2) / (2 * A)) + b * ((∑ i, z i ^ 2) / (2 * B)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
          ← Finset.mul_sum, mul_div_assoc, mul_div_assoc]

/-! ## The cone over `K` and the jointly log-concave integrand -/

/-- **The open cone over `K`**, `{(A, y) : A > 0, y/A ∈ K} ⊆ ℝ × ℝⁿ`.  Its convexity is what
turns the `A`-dependence of the body `A·K` into a *joint* convexity statement. -/
def zCone (K : Set (EuclSpace n)) : Set (ℝ × (Fin n → ℝ)) :=
  {p : ℝ × (Fin n → ℝ) | 0 < p.1 ∧ (p.1⁻¹ • (WithLp.toLp 2 p.2 : EuclSpace n)) ∈ K}

/-- The cone over a convex set is convex.  Note that `0 ∈ K` is *not* needed. -/
theorem convex_zCone {K : Set (EuclSpace n)} (hK : Convex ℝ K) : Convex ℝ (zCone K) := by
  rintro ⟨A, y⟩ ⟨hA, hyK⟩ ⟨B, z⟩ ⟨hB, hzK⟩ a b ha hb hab
  have hpos : 0 < a * A + b * B := by
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1, zero_mul, one_mul, zero_add]; exact hB
    · nlinarith [mul_nonneg hb hB.le, mul_pos h hA]
  refine ⟨hpos, ?_⟩
  set C : ℝ := a * A + b * B with hC
  -- the two points of `K` are combined with the weights `aA/C`, `bB/C`
  have hmem := hK hyK hzK (a := a * A / C) (b := b * B / C)
    (by positivity) (by positivity) (by field_simp; exact hC.symm)
  have hkey : (a * A / C) • (A⁻¹ • (WithLp.toLp 2 y : EuclSpace n))
      + (b * B / C) • (B⁻¹ • (WithLp.toLp 2 z : EuclSpace n))
      = C⁻¹ • (WithLp.toLp 2 (a • y + b • z) : EuclSpace n) := by
    rw [smul_smul, smul_smul, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul, smul_add,
      smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp
  show (a • (A, y) + b • (B, z)).1⁻¹ •
    (WithLp.toLp 2 (a • (A, y) + b • (B, z)).2 : EuclSpace n) ∈ K
  have h1 : (a • (A, y) + b • (B, z)).1 = C := rfl
  have h2 : (a • (A, y) + b • (B, z)).2 = a • y + b • z := rfl
  rw [h1, h2, ← hkey]
  exact hmem

/-- **The integrand of `z` after the change of variables `x = y/A`:**
`(A, y) ↦ A · 1_K(y/A) · e^{-‖y‖²/(2A)}`. -/
noncomputable def zIntegrand (K : Set (EuclSpace n)) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  Set.indicator (zCone K) (fun q => q.1 * Real.exp (-(∑ i, q.2 i ^ 2) / (2 * q.1))) p

theorem zIntegrand_nonneg (K : Set (EuclSpace n)) (p : ℝ × (Fin n → ℝ)) :
    0 ≤ zIntegrand K p := by
  by_cases h : p ∈ zCone K
  · simp only [zIntegrand, Set.indicator_of_mem h]
    exact mul_nonneg h.1.le (exp_pos _).le
  · simp only [zIntegrand, Set.indicator_of_notMem h]
    exact le_refl 0

/-- **The crux.**  `(A, y) ↦ A · 1_K(y/A) · e^{-‖y‖²/(2A)}` is jointly log-concave on
`ℝ × ℝⁿ`: the support is the convex cone `zCone K`, the factor `A` is handled by weighted
AM–GM and the Gaussian factor by the perspective inequality. -/
theorem isLogConcave_zIntegrand {K : Set (EuclSpace n)} (hK : Convex ℝ K) :
    IsLogConcave (zIntegrand K) := by
  refine ⟨convex_univ, ?_⟩
  rintro ⟨A, y⟩ - ⟨B, z⟩ - a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have ha0' : a = 0 := ha0.symm
    subst ha0'
    have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have hb0' : b = 0 := hb0.symm
    subst hb0'
    have ha1 : a = 1 := by linarith
    subst ha1
    simp
  by_cases hpC : ((A, y) : ℝ × (Fin n → ℝ)) ∈ zCone K
  · by_cases hqC : ((B, z) : ℝ × (Fin n → ℝ)) ∈ zCone K
    · obtain ⟨hA, hyK⟩ := hpC
      obtain ⟨hB, hzK⟩ := hqC
      have hpC : ((A, y) : ℝ × (Fin n → ℝ)) ∈ zCone K := ⟨hA, hyK⟩
      have hqC : ((B, z) : ℝ × (Fin n → ℝ)) ∈ zCone K := ⟨hB, hzK⟩
      have hmid : (a • ((A, y) : ℝ × (Fin n → ℝ)) + b • (B, z)) ∈ zCone K :=
        convex_zCone hK hpC hqC ha hb hab
      have hpos : 0 < a * A + b * B := by nlinarith
      have e1 : (a • ((A, y) : ℝ × (Fin n → ℝ)) + b • (B, z)).1 = a * A + b * B := rfl
      have e2 : (a • ((A, y) : ℝ × (Fin n → ℝ)) + b • (B, z)).2 = a • y + b • z := rfl
      simp only [zIntegrand, Set.indicator_of_mem hpC, Set.indicator_of_mem hqC,
        Set.indicator_of_mem hmid, e1, e2]
      set t1 : ℝ := -(∑ i, y i ^ 2) / (2 * A) with ht1
      set t2 : ℝ := -(∑ i, z i ^ 2) / (2 * B) with ht2
      set t3 : ℝ := -(∑ i, (a • y + b • z) i ^ 2) / (2 * (a * A + b * B)) with ht3
      have hAM : A ^ a * B ^ b ≤ a * A + b * B :=
        geom_mean_le_arith_mean2_weighted ha hb hA.le hB.le hab
      have hexp : a * t1 + b * t2 ≤ t3 := by
        have hp := sum_sq_perspective_le y z ha hb hA hB hpos
        rw [ht1, ht2, ht3, neg_div, neg_div, neg_div]
        nlinarith [hp]
      have hE : Real.exp (a * t1 + b * t2) ≤ Real.exp t3 := Real.exp_le_exp.mpr hexp
      calc (A * Real.exp t1) ^ a * (B * Real.exp t2) ^ b
          = (A ^ a * B ^ b) * Real.exp (a * t1 + b * t2) := by
            rw [Real.mul_rpow hA.le (exp_pos _).le, Real.mul_rpow hB.le (exp_pos _).le,
              ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, mul_comm t1 a, mul_comm t2 b]
            ring
        _ ≤ (a * A + b * B) * Real.exp t3 :=
            mul_le_mul hAM hE (exp_pos _).le (by positivity)
    · simp only [zIntegrand, Set.indicator_of_notMem hqC]
      rw [Real.zero_rpow hb0.ne', mul_zero]
      exact zIntegrand_nonneg _ _
  · simp only [zIntegrand, Set.indicator_of_notMem hpC]
    rw [Real.zero_rpow ha0.ne', zero_mul]
    exact zIntegrand_nonneg _ _

/-! ## Slices: measurability and integrability

The Bochner form of the marginal theorem needs every slice `y ↦ zIntegrand K (A, y)` to be
measurable and integrable — including the slices at `A ≤ 0`, where it vanishes. -/

theorem zIntegrand_slice_pos {K : Set (EuclSpace n)} {A : ℝ} (hA : 0 < A) :
    (fun t : Fin n → ℝ => zIntegrand K (A, t))
      = Set.indicator {t : Fin n → ℝ | (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K}
          (fun t => A * Real.exp (-(∑ i, t i ^ 2) / (2 * A))) := by
  funext t
  by_cases ht : (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K
  · rw [Set.indicator_of_mem
      (show t ∈ {t : Fin n → ℝ | (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K} from ht)]
    simp only [zIntegrand,
      Set.indicator_of_mem (show ((A, t) : ℝ × (Fin n → ℝ)) ∈ zCone K from ⟨hA, ht⟩)]
  · rw [Set.indicator_of_notMem
      (show t ∉ {t : Fin n → ℝ | (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K} from ht)]
    simp only [zIntegrand,
      Set.indicator_of_notMem (show ((A, t) : ℝ × (Fin n → ℝ)) ∉ zCone K from fun h => ht h.2)]

theorem zIntegrand_slice_nonpos {K : Set (EuclSpace n)} {A : ℝ} (hA : ¬ 0 < A) :
    (fun t : Fin n → ℝ => zIntegrand K (A, t)) = fun _ => 0 := by
  funext t
  simp only [zIntegrand,
    Set.indicator_of_notMem (show ((A, t) : ℝ × (Fin n → ℝ)) ∉ zCone K from fun h => hA h.1)]

theorem measurableSet_zSlice {K : Set (EuclSpace n)} (hK : MeasurableSet K) (A : ℝ) :
    MeasurableSet {t : Fin n → ℝ | (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K} :=
  hK.preimage ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.const_smul A⁻¹)

theorem measurable_zIntegrand_slice {K : Set (EuclSpace n)} (hK : MeasurableSet K) (A : ℝ) :
    Measurable fun t : Fin n → ℝ => zIntegrand K (A, t) := by
  by_cases hA : 0 < A
  · rw [zIntegrand_slice_pos hA]
    exact (measurable_const.mul (by fun_prop)).indicator (measurableSet_zSlice hK A)
  · rw [zIntegrand_slice_nonpos hA]
    exact measurable_const

/-- The `n`-dimensional Gaussian is integrable: it is a product of one-dimensional ones. -/
theorem integrable_gaussian_pi {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / c)) := by
  have h1 : (fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / c))
      = fun t : Fin n → ℝ => ∏ i, Real.exp (-(1 / c) * (t i) ^ 2) := by
    funext t
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    field_simp
  rw [h1, MeasureTheory.volume_pi]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by positivity))

theorem integrable_zIntegrand_slice {K : Set (EuclSpace n)} (hK : MeasurableSet K) (A : ℝ) :
    Integrable fun t : Fin n → ℝ => zIntegrand K (A, t) := by
  by_cases hA : 0 < A
  · rw [zIntegrand_slice_pos hA]
    exact ((integrable_gaussian_pi (c := 2 * A) (by positivity)).const_mul A).indicator
      (measurableSet_zSlice hK A)
  · rw [zIntegrand_slice_nonpos hA]
    exact integrable_zero _ _ _

/-! ## The change of variables -/

/-- **`z` is a marginal.**  For `A > 0`,

  `zFun 1_K A = A^{n+1} ∫ 1_K(x) e^{-A‖x‖²/2} dx = ∫ A · 1_K(y/A) e^{-‖y‖²/(2A)} dy`,

by the substitution `x = y/A` (`MeasureTheory.Measure.integral_comp_smul`, which contributes
the factor `A^{-n}`), transported to `ℝⁿ` in coordinates by
`PiLp.volume_preserving_toLp`. -/
theorem zFun_eq_integral {K : Set (EuclSpace n)} {A : ℝ} (hA : 0 < A) :
    zFun (Set.indicator K (1 : EuclSpace n → ℝ)) A
      = ∫ t : Fin n → ℝ, zIntegrand K (A, t) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  set f : EuclSpace n → ℝ := Set.indicator K (1 : EuclSpace n → ℝ) with hf
  set g : EuclSpace n → ℝ := fun w => f (A⁻¹ • w) * Real.exp (-(‖w‖ ^ 2) / (2 * A)) with hg
  -- the rescaled integrand at `A • x` is the original one
  have hcomp : ∀ x : EuclSpace n, g (A • x) = gW f A⁻¹ x := by
    intro x
    simp only [hg, gW]
    rw [smul_smul, inv_mul_cancel₀ hAne, one_smul]
    congr 1
    have h2 : ‖A • x‖ ^ 2 = A ^ 2 * ‖x‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h2]
    field_simp
  -- the scaling formula for the Haar measure
  have hG : G f A⁻¹ = (A ^ n)⁻¹ * ∫ w, g w := by
    have hsc := Measure.integral_comp_smul (volume : Measure (EuclSpace n)) g A
    rw [finrank_euclideanSpace_fin, smul_eq_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (A ^ n)⁻¹)] at hsc
    simp only [G]
    simp_rw [← hcomp]
    exact hsc
  have hz : zFun f A = A * ∫ w, g w := by
    have hAn : (A : ℝ) ^ n ≠ 0 := pow_ne_zero n hAne
    simp only [zFun, hG]
    rw [← mul_assoc]
    congr 1
    rw [pow_succ]
    field_simp
  -- transfer `EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)`
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin n → ℝ)))
      (volume : Measure (Fin n → ℝ)) (volume : Measure (EuclSpace n)) := by
    rw [MeasurableEquiv.coe_toLp]
    exact PiLp.volume_preserving_toLp (Fin n)
  have htr := hmp.integral_comp' g
  rw [MeasurableEquiv.coe_toLp] at htr
  have hpt : ∀ t : Fin n → ℝ,
      A * g (WithLp.toLp 2 t : EuclSpace n) = zIntegrand K (A, t) := by
    intro t
    have hnorm : ‖(WithLp.toLp 2 t : EuclSpace n)‖ ^ 2 = ∑ i, t i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    by_cases ht : (A⁻¹ • (WithLp.toLp 2 t : EuclSpace n)) ∈ K
    · simp only [hg, hf, Set.indicator_of_mem ht, Pi.one_apply, one_mul, hnorm, zIntegrand,
        Set.indicator_of_mem (show ((A, t) : ℝ × (Fin n → ℝ)) ∈ zCone K from ⟨hA, ht⟩)]
    · simp only [hg, hf, Set.indicator_of_notMem ht, zero_mul, mul_zero, zIntegrand,
        Set.indicator_of_notMem (show ((A, t) : ℝ × (Fin n → ℝ)) ∉ zCone K from fun h => ht h.2)]
  calc zFun f A = A * ∫ w : EuclSpace n, g w := hz
    _ = A * ∫ t : Fin n → ℝ, g (WithLp.toLp 2 t : EuclSpace n) := by rw [htr]
    _ = ∫ t : Fin n → ℝ, A * g (WithLp.toLp 2 t : EuclSpace n) := (integral_const_mul A _).symm
    _ = ∫ t : Fin n → ℝ, zIntegrand K (A, t) := by simp_rw [hpt]

/-! ## `ZLogconcaveHypothesis`, proved -/

/-- Prékopa's marginal theorem applied to `zIntegrand`: `A ↦ ∫ zIntegrand K (A, ·)` — which is
`zFun 1_K` on `A > 0` — is log-concave on `ℝ`. -/
theorem isLogConcave_zMarginal {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) :
    IsLogConcave (fun A : ℝ => ∫ t : Fin n → ℝ, zIntegrand K (A, t)) :=
  Arlib.isLogConcave_marginal_pi
    (G := fun (A : ℝ) (t : Fin n → ℝ) => zIntegrand K (A, t))
    (isLogConcave_zIntegrand hK) (fun _ _ => zIntegrand_nonneg _ _)
    (fun A => measurable_zIntegrand_slice hKm A)
    (fun A => integrable_zIntegrand_slice hKm A)

/-- **Paper Lemma 5.9 for a convex body, as a theorem.**  For every convex measurable
`K ⊆ ℝⁿ`, the hypothesis `ZLogconcaveHypothesis` of `fixed_var_bound` holds for the
indicator of `K`.  No boundedness, roundness or `0 ∈ K` assumption. -/
theorem zLogconcaveHypothesis_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) :
    ZLogconcaveHypothesis (Set.indicator K (1 : EuclSpace n → ℝ)) := by
  intro a b ha hb
  have hm : (0 : ℝ) < (a + b) / 2 := by linarith
  have hZnn : ∀ A : ℝ, 0 ≤ ∫ t : Fin n → ℝ, zIntegrand K (A, t) :=
    fun A => integral_nonneg fun t => zIntegrand_nonneg _ _
  have hsq : ∀ x : ℝ, 0 ≤ x → (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hx]
    norm_num
  have key := (isLogConcave_zMarginal hK hKm).geom_le a b
    (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
  have hmid : ((1 : ℝ) / 2) • a + ((1 : ℝ) / 2) • b = (a + b) / 2 := by
    simp only [smul_eq_mul]; ring
  rw [hmid] at key
  rw [zFun_eq_integral ha, zFun_eq_integral hb, zFun_eq_integral hm]
  set Za : ℝ := ∫ t : Fin n → ℝ, zIntegrand K (a, t) with hZa
  set Zb : ℝ := ∫ t : Fin n → ℝ, zIntegrand K (b, t) with hZb
  set Zm : ℝ := ∫ t : Fin n → ℝ, zIntegrand K ((a + b) / 2, t) with hZm
  have hnn : 0 ≤ Za ^ ((1 : ℝ) / 2) * Zb ^ ((1 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg (hZnn a) _) (Real.rpow_nonneg (hZnn b) _)
  have hsquare := mul_self_le_mul_self hnn key
  calc Za * Zb = (Za ^ ((1 : ℝ) / 2) * Zb ^ ((1 : ℝ) / 2))
        * (Za ^ ((1 : ℝ) / 2) * Zb ^ ((1 : ℝ) / 2)) := by
        rw [show (Za ^ ((1 : ℝ) / 2) * Zb ^ ((1 : ℝ) / 2))
            * (Za ^ ((1 : ℝ) / 2) * Zb ^ ((1 : ℝ) / 2))
          = (Za ^ ((1 : ℝ) / 2)) ^ 2 * (Zb ^ ((1 : ℝ) / 2)) ^ 2 from by ring,
          hsq _ (hZnn a), hsq _ (hZnn b)]
    _ ≤ Zm * Zm := hsquare
    _ = Zm ^ 2 := by ring

/-- `zFun` is linear in `f`. -/
theorem zFun_const_mul (f : EuclSpace n → ℝ) (c A : ℝ) :
    zFun (fun x => c * f x) A = c * zFun f A := by
  simp only [zFun, G, gW]
  rw [show (∫ x : EuclSpace n, c * f x * Real.exp (-(‖x‖ ^ 2) / (2 * A⁻¹)))
      = ∫ x : EuclSpace n, c * (f x * Real.exp (-(‖x‖ ^ 2) / (2 * A⁻¹))) from by
        simp only [mul_assoc], integral_const_mul]
  ring

/-- Both sides of `ZLogconcaveHypothesis` scale by `c²`, so it is invariant under scaling
`f` by any constant. -/
theorem ZLogconcaveHypothesis.const_mul {f : EuclSpace n → ℝ} (hf : ZLogconcaveHypothesis f)
    (c : ℝ) : ZLogconcaveHypothesis (fun x => c * f x) := by
  intro a b ha hb
  rw [zFun_const_mul, zFun_const_mul, zFun_const_mul]
  have h := hf a b ha hb
  calc c * zFun f a * (c * zFun f b) = c ^ 2 * (zFun f a * zFun f b) := by ring
    _ ≤ c ^ 2 * (zFun f ((a + b) / 2)) ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = (c * zFun f ((a + b) / 2)) ^ 2 := by ring

/-- **Paper Lemma 5.9 for `f = c · 1_K`.** -/
theorem zLogconcaveHypothesis_indicator_const {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (c : ℝ) :
    ZLogconcaveHypothesis (Set.indicator K (fun _ => c)) := by
  have h := (zLogconcaveHypothesis_indicator hK hKm).const_mul c
  have he : (fun x => c * Set.indicator K (1 : EuclSpace n → ℝ) x)
      = Set.indicator K (fun _ => c) := by
    funext x
    by_cases hx : x ∈ K <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rwa [he] at h

/-- **Non-vacuity witness with content.**  The theorem applies to a genuine body: a
Euclidean ball of any centre and radius. -/
theorem zLogconcaveHypothesis_closedBall (c : EuclSpace n) (r : ℝ) :
    ZLogconcaveHypothesis (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ)) :=
  zLogconcaveHypothesis_indicator (convex_closedBall c r)
    Metric.isClosed_closedBall.measurableSet

/-! ## The fixed-rate variance bound, now unconditional for a convex body -/

/-- **Paper Lemma 5.10 for a convex body, with no assumed input.**  `fixed_var_bound` with
its `ZLogconcaveHypothesis` discharged. -/
theorem fixed_var_bound_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ)))
        * G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 - 1 / (n : ℝ)))
      ≤ (1 + 2 / (n : ℝ)) * (G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2)) ^ 2 :=
  fixed_var_bound (zLogconcaveHypothesis_indicator hK hKm) hσ hn

/-- **Paper Lemma 5.10 in estimator form for a convex body**, with no assumed input:
`E(Y²)/E(Y)² ≤ 1 + 2/n` under the fixed cooling rate `σᵢ₊₁² = σᵢ²(1 + 1/n)`. -/
theorem fixed_var_bound_ratio_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n)
    (hGa : G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) ≠ 0)
    (hGb : G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) ≠ 0) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ)))))
      / (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
            / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
          * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
            / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2
      ≤ 1 + 2 / (n : ℝ) :=
  fixed_var_bound_ratio (zLogconcaveHypothesis_indicator hK hKm) hσ hn hGa hGb

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms sq_div_add_le
#print axioms sum_sq_perspective_le
#print axioms convex_zCone
#print axioms isLogConcave_zIntegrand
#print axioms measurable_zIntegrand_slice
#print axioms integrable_gaussian_pi
#print axioms integrable_zIntegrand_slice
#print axioms zFun_eq_integral
#print axioms isLogConcave_zMarginal
#print axioms zLogconcaveHypothesis_indicator
#print axioms zFun_const_mul
#print axioms ZLogconcaveHypothesis.const_mul
#print axioms zLogconcaveHypothesis_indicator_const
#print axioms zLogconcaveHypothesis_closedBall
#print axioms fixed_var_bound_indicator
#print axioms fixed_var_bound_ratio_indicator

end Arlib.GaussianCooling
