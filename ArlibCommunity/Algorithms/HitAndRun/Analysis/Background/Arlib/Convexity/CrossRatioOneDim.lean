/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatio
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogConcave

/-!
# The one-dimensional cross-ratio inequality for log-concave functions

This file proves Lemma 5.9 of Lovász–Vempala, *The geometry of logconcave functions and
sampling algorithms*: writing `g (x, y) = ∫ x..y, g` for a nonnegative log-concave
`g : ℝ → ℝ`, and for `a < b < c < d` the Euclidean cross-ratio

`(a : c : b : d)   = (d - a) * (c - b) / ((b - a) * (d - c))`

and its `g`-weighted version

`(a : c : b : d)_g = g (a, d) * g (b, c) / (g (a, b) * g (c, d))`,

one has `(a : c : b : d) ≤ (a : c : b : d)_g`.

## Direction of the inequality

The relation glyph in the displayed statement of Lemma 5.9 is `CMSY10` code `0xB8`, whose
name in the encoding vector of the embedded Type 1 font is `greaterequal`; the same font
carries `lessequal` at `0xB7`, so the two are distinguishable and the reading is not a
guess. Independently: the inequality is an *equality* for constant `g` (both sides equal
`(d-a)(c-b)/((b-a)(d-c))`), and for `g t = eᵗ` with `(a,b,c,d) = (0,1,2,3)` the weighted
side is `≈ 4.086` against `3` for the Euclidean side, so the weighted side is the larger
one. Both readings agree: the inequality is `≥` as stated above.

## Main statements

* `Arlib.crossRatio_mul_le_crossRatio_integral` — the division-free form, valid for merely
  nonnegative `g` (no positivity, so `g` may be compactly supported and the denominators
  may vanish).
* `Arlib.crossRatio_le_crossRatio_integral` — the quotient form of Lemma 5.9, under
  `0 < g`.
* `Arlib.integral_mul_integral_le_of_isLogConcave` — the equivalent "overlapping means beat
  separated means" form `M (a,c) * M (b,d) ≥ M (a,b) * M (c,d)`, where `M` is the mean value
  of `g` over an interval. This is the shape the proof actually establishes.
* `Arlib.crossRatioDist_Icc` — the bridge to `Arlib/Convexity/CrossRatio.lean`: on a segment
  of `ℝ`, the `n`-dimensional chord quantity `Arlib.crossRatioDist (Icc a d) b c` evaluates
  to exactly `(d-a)(c-b)/((b-a)(d-c))`, so the two notions of Euclidean cross-ratio agree.
* `Arlib.crossRatioDist_le_crossRatio_integral` — Lemma 5.9 restated through that bridge.

Note that `Arlib.uniformOn_dyerFrieze_dim_one` is a *different* one-dimensional statement
(the Euclidean-metric Dyer–Frieze isoperimetric inequality); nothing here supersedes it and
it is not used.

## Proof outline

Write `A = ∫ a..b, g`, `B = ∫ b..c, g`, `C = ∫ c..d, g` and `α = b - a`, `β = c - b`,
`γ = d - c`. The claim unfolds to the purely algebraic
`β * (α + β + γ) * A * C ≤ α * γ * B * (A + B + C)`.

1. `expAvg u = ∫ s in 0..1, cosh (u * s)` is positive and monotone in `|u|`
   (`Arlib.expAvg_pos`, `Arlib.expAvg_le_expAvg`), and every exponential has
   `∫ x..y, σ * exp (l * t) = (y - x) * σ * exp (l * (x + y) / 2) * expAvg (l * (y - x) / 2)`
   (`Arlib.integral_const_mul_exp`). Since the `exp` prefactors match on the two sides, the
   claim for an exponential reduces to `expAvg` monotonicity
   (`Arlib.exp_crossRatio_key`). This is the "reduce to `g t = eᵗ`" step of Lovász–Vempala,
   made unconditional: no extremality argument is needed, because step 3 below only ever
   *compares* `g` to an exponential.
2. Log-concavity places `g` above the exponential `h` through `(b, g b)` and `(c, g c)` on
   `[b, c]` and below it outside (`Arlib.le_expLine_of_le`, `Arlib.expLine_le_of_mem`,
   `Arlib.le_expLine_of_ge`). Integrating: `A ≤ A'`, `C ≤ C'`, `B' ≤ B`.
3. The target is affine in `A` and in `C` separately and increasing in `B`, so it follows
   from the exponential case by a two-way case split (`Arlib.crossRatio_algebra`). No
   extremal/variational principle is used.

The degenerate branch (`A = 0` or `C = 0`) is trivial, and away from it log-concavity
forces `0 < g b` and `0 < g c`, which is what makes the exponential `h` exist.
-/

namespace Arlib

open MeasureTheory Set intervalIntegral

/-! ### The normalised exponential average `expAvg` -/

/-- `expAvg u = ∫ s in 0..1, cosh (u * s)`. For `u ≠ 0` this is `sinh u / u`, and
`expAvg 0 = 1`; the integral form makes the value at `0` come out right on the nose and
makes monotonicity in `|u|` a pointwise statement about `cosh`. -/
noncomputable def expAvg (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.cosh (u * s)

lemma continuous_cosh_mul (u : ℝ) : Continuous fun s : ℝ => Real.cosh (u * s) :=
  Real.continuous_cosh.comp (continuous_const.mul continuous_id)

lemma intervalIntegrable_cosh_mul (u a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.cosh (u * s)) volume a b :=
  (continuous_cosh_mul u).intervalIntegrable a b

lemma one_le_expAvg (u : ℝ) : 1 ≤ expAvg u := by
  have h : (∫ _s in (0 : ℝ)..1, (1 : ℝ)) ≤ ∫ s in (0 : ℝ)..1, Real.cosh (u * s) :=
    intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (intervalIntegrable_cosh_mul u 0 1) (fun x _ => Real.one_le_cosh _)
  simpa [expAvg] using h

lemma expAvg_pos (u : ℝ) : 0 < expAvg u := lt_of_lt_of_le zero_lt_one (one_le_expAvg u)

lemma expAvg_zero : expAvg 0 = 1 := by simp [expAvg]

/-- `expAvg` is monotone in the absolute value of its argument. -/
lemma expAvg_le_expAvg {u v : ℝ} (h : |u| ≤ |v|) : expAvg u ≤ expAvg v := by
  refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_cosh_mul u 0 1)
    (intervalIntegrable_cosh_mul v 0 1) ?_
  intro x hx
  refine Real.cosh_le_cosh.2 ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg x)

/-- For `u ≠ 0`, `expAvg u = sinh u / u`. -/
lemma expAvg_eq_sinh_div (u : ℝ) (hu : u ≠ 0) : expAvg u = Real.sinh u / u := by
  have h : (∫ s in (0 : ℝ)..1, Real.cosh (u * s))
      = u⁻¹ • ∫ s in (u * 0)..(u * 1), Real.cosh s :=
    intervalIntegral.integral_comp_mul_left (fun s => Real.cosh s) hu
  rw [expAvg, h]
  have h2 : (∫ s in (u * 0)..(u * 1), Real.cosh s) = Real.sinh u := by
    have hftc := intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := u)
      Real.sinh Real.deriv_sinh (fun x _ => Real.differentiable_sinh x)
      Real.continuous_cosh.continuousOn
    simpa using hftc
  rw [h2, smul_eq_mul, inv_mul_eq_div]

/-- Every exponential integrates to a length times a midpoint value times `expAvg`.  This
is the identity `∫ x..y, e^{l t} = (y - x) · e^{l (x+y)/2} · sinh(l (y-x)/2)/(l (y-x)/2)`,
written so that it is also correct at `l = 0` and at `x = y`. -/
lemma integral_const_mul_exp (σ l x y : ℝ) :
    (∫ t in x..y, σ * Real.exp (l * t))
      = (y - x) * σ * Real.exp (l * (x + y) / 2) * expAvg (l * (y - x) / 2) := by
  rcases eq_or_ne (l * (y - x) / 2) 0 with hz | hz
  · -- degenerate: either `l = 0` or `x = y`; both sides are elementary
    rw [hz, expAvg_zero]
    rcases mul_eq_zero.1 (by linarith [hz] : l * (y - x) = 0) with hl | hyx
    · subst hl; simp
    · have : y = x := by linarith
      subst this; simp
  · have hl : l ≠ 0 := by
      intro h; apply hz; rw [h]; ring
    have key : (∫ t in x..y, σ * Real.exp (l * t))
        = σ * (Real.exp (l * y) - Real.exp (l * x)) / l := by
      rw [intervalIntegral.integral_const_mul]
      have h : (∫ t in x..y, Real.exp (l * t)) = l⁻¹ • ∫ t in (l * x)..(l * y), Real.exp t :=
        intervalIntegral.integral_comp_mul_left (fun t => Real.exp t) hl
      rw [h, integral_exp, smul_eq_mul]
      field_simp
    have hexp : Real.exp (l * (x + y) / 2) * Real.exp (l * (y - x) / 2) = Real.exp (l * y) := by
      rw [← Real.exp_add]; ring_nf
    have hexp' : Real.exp (l * (x + y) / 2) * Real.exp (-(l * (y - x) / 2)) = Real.exp (l * x) := by
      rw [← Real.exp_add]; ring_nf
    have hy : y - x ≠ 0 := by
      intro h; apply hz; rw [h]; ring
    rw [key, expAvg_eq_sinh_div _ hz, Real.sinh_eq, ← hexp, ← hexp']
    have hE : Real.exp (l * (x + y) / 2) ≠ 0 := Real.exp_ne_zero _
    field_simp

/-! ### The cross-ratio inequality for a genuine exponential -/

/-- For an exponential `t ↦ σ * exp (l * t)` the "overlapping beats separated" inequality
holds. The `exp` prefactors on the two sides are literally equal, so all that survives is
`expAvg (l * (b-a)/2) ≤ expAvg (l * (c-a)/2)` and `expAvg (l * (d-c)/2) ≤ expAvg (l*(d-b)/2)`,
which is monotonicity of `expAvg` in `|·|`. This is Lovász–Vempala's "we may assume
`g t = eᵗ`" step, used here only as a *comparison* target, never as an extremal claim. -/
lemma exp_crossRatio_key {σ l a b c d : ℝ} (hσ : 0 < σ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (c - a) * (d - b) *
        ((∫ t in a..b, σ * Real.exp (l * t)) * (∫ t in c..d, σ * Real.exp (l * t)))
      ≤ (b - a) * (d - c) *
          ((∫ t in a..c, σ * Real.exp (l * t)) * (∫ t in b..d, σ * Real.exp (l * t))) := by
  have hca : (0 : ℝ) < c - a := by linarith
  have hdb : (0 : ℝ) < d - b := by linarith
  have hba : (0 : ℝ) < b - a := by linarith
  have hdc : (0 : ℝ) < d - c := by linarith
  have hF1 : expAvg (l * (b - a) / 2) ≤ expAvg (l * (c - a) / 2) := by
    refine expAvg_le_expAvg ?_
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hba, abs_of_pos hca]
    have : |l| * (b - a) ≤ |l| * (c - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg l)
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hF2 : expAvg (l * (d - c) / 2) ≤ expAvg (l * (d - b) / 2) := by
    refine expAvg_le_expAvg ?_
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hdc, abs_of_pos hdb]
    have : |l| * (d - c) ≤ |l| * (d - b) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg l)
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hE : Real.exp (l * (a + b) / 2) * Real.exp (l * (c + d) / 2)
      = Real.exp (l * (a + c) / 2) * Real.exp (l * (b + d) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [integral_const_mul_exp, integral_const_mul_exp, integral_const_mul_exp,
    integral_const_mul_exp]
  set E1 := Real.exp (l * (a + b) / 2) with hE1
  set E2 := Real.exp (l * (c + d) / 2) with hE2
  set E3 := Real.exp (l * (a + c) / 2) with hE3
  set E4 := Real.exp (l * (b + d) / 2) with hE4
  set F1 := expAvg (l * (b - a) / 2) with hFF1
  set F2 := expAvg (l * (d - c) / 2) with hFF2
  set F3 := expAvg (l * (c - a) / 2) with hFF3
  set F4 := expAvg (l * (d - b) / 2) with hFF4
  have hM : 0 < (c - a) * (d - b) * (b - a) * (d - c) * σ * σ * (E1 * E2) := by
    have : 0 < E1 * E2 := mul_pos (by rw [hE1]; exact Real.exp_pos _)
      (by rw [hE2]; exact Real.exp_pos _)
    positivity
  have e1 : (c - a) * (d - b) *
        (((b - a) * σ * E1 * F1) * ((d - c) * σ * E2 * F2))
      = ((c - a) * (d - b) * (b - a) * (d - c) * σ * σ * (E1 * E2)) * (F1 * F2) := by ring
  have e2 : (b - a) * (d - c) *
        (((c - a) * σ * E3 * F3) * ((d - b) * σ * E4 * F4))
      = ((c - a) * (d - b) * (b - a) * (d - c) * σ * σ * (E1 * E2)) * (F3 * F4) := by
    rw [hE]; ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ hM.le
  exact mul_le_mul hF1 hF2 (expAvg_pos _).le (le_trans (expAvg_pos _).le hF1)

/-! ### The algebraic core -/

/-- The target `β (α+β+γ) A C ≤ α γ B (A+B+C)` is affine in `A` and in `C` separately and
increasing in `B`. Hence it follows from the same inequality for a comparison triple
`(A', B', C')` that dominates `A` and `C` and is dominated by `B` — no extremal principle
required, just a two-way case split on the signs of the two affine coefficients. -/
lemma crossRatio_algebra {α β γ A B C A' B' C' : ℝ}
    (hα : 0 < α) (_hβ : 0 < β) (hγ : 0 < γ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAA : A ≤ A') (hCC : C ≤ C') (hBB : B' ≤ B) (hB'0 : 0 ≤ B')
    (hexp : β * (α + β + γ) * (A' * C') ≤ α * γ * (B' * (A' + B' + C'))) :
    β * (α + β + γ) * (A * C) ≤ α * γ * (B * (A + B + C)) := by
  have hA' : 0 ≤ A' := hA.trans hAA
  have hC' : 0 ≤ C' := hC.trans hCC
  rcases le_or_gt (β * (α + β + γ) * C) (α * γ * B) with h1 | h1
  · -- the coefficient of `A` is nonnegative: bound `A * (β (α+β+γ) C)` by `A * (α γ B)`
    nlinarith [mul_nonneg hA (sub_nonneg.2 h1),
      mul_nonneg (mul_pos hα hγ).le (mul_nonneg hB (add_nonneg hB hC))]
  · -- the coefficient of `A` is negative: replace `A` by the larger `A'`
    have step1 : α * γ * (B * (A' + B + C)) - β * (α + β + γ) * (A' * C)
        ≤ α * γ * (B * (A + B + C)) - β * (α + β + γ) * (A * C) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hAA) (sub_nonneg.2 h1.le)]
    rcases le_or_gt (β * (α + β + γ) * A') (α * γ * B) with h2 | h2
    · -- the coefficient of `C` is nonnegative at `A = A'`, so drop `C` to `0`
      have t1 : β * (α + β + γ) * (A' * C) ≤ α * γ * B * C := by
        nlinarith [mul_nonneg hC (sub_nonneg.2 h2)]
      have t2 : (0 : ℝ) ≤ α * γ * (B * (A' + B)) :=
        mul_nonneg (mul_pos hα hγ).le (mul_nonneg hB (add_nonneg hA' hB))
      nlinarith [t1, t2, step1]
    · have step2 : α * γ * (B * (A' + B + C')) - β * (α + β + γ) * (A' * C')
          ≤ α * γ * (B * (A' + B + C)) - β * (α + β + γ) * (A' * C) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hCC) (sub_nonneg.2 h2.le)]
      have step3 : α * γ * (B' * (A' + B' + C')) ≤ α * γ * (B * (A' + B + C')) := by
        have hmul : B' * (A' + B' + C') ≤ B * (A' + B + C') := by
          nlinarith [mul_nonneg hB'0 (sub_nonneg.2 hBB)]
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
      linarith

/-! ### Comparing a log-concave function to the exponential through two of its values -/

/-- An exponential satisfies the defining log-concavity inequality with equality. -/
lemma expLine_geom {σ : ℝ} (hσ : 0 < σ) (l x y s : ℝ) :
    (σ * Real.exp (l * x)) ^ (1 - s) * (σ * Real.exp (l * y)) ^ s
      = σ * Real.exp (l * ((1 - s) * x + s * y)) := by
  rw [Real.mul_rpow hσ.le (Real.exp_pos _).le, Real.mul_rpow hσ.le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul,
    show σ ^ (1 - s) * Real.exp (l * x * (1 - s)) * (σ ^ s * Real.exp (l * y * s))
      = σ ^ (1 - s) * σ ^ s * (Real.exp (l * x * (1 - s)) * Real.exp (l * y * s)) from by ring,
    ← Real.rpow_add hσ, ← Real.exp_add,
    show 1 - s + s = (1 : ℝ) from by ring, Real.rpow_one,
    show l * x * (1 - s) + l * y * s = l * ((1 - s) * x + s * y) from by ring]

/-- A log-concave function is positive strictly between two points where it is positive. -/
lemma pos_of_lt_of_lt {g : ℝ → ℝ} (hlc : IsLogConcave g) {x y t : ℝ}
    (hx : 0 < g x) (hy : 0 < g y) (hxt : x < t) (hty : t < y) : 0 < g t := by
  have hyx : (0 : ℝ) < y - x := by linarith
  have hs0 : (0 : ℝ) ≤ (t - x) / (y - x) := div_nonneg (by linarith) hyx.le
  have hts : t = (1 - (t - x) / (y - x)) * x + (t - x) / (y - x) * y := by
    field_simp; ring
  have key := hlc.geom_le x y
    (show (0 : ℝ) ≤ 1 - (t - x) / (y - x) by
      have : (t - x) / (y - x) ≤ 1 := (div_le_one hyx).2 (by linarith)
      linarith) hs0 (by ring)
  rw [smul_eq_mul, smul_eq_mul, ← hts] at key
  have hpos : 0 < g x ^ (1 - (t - x) / (y - x)) * g y ^ ((t - x) / (y - x)) :=
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
  linarith

/-- On `[b, c]`, a log-concave `g` dominates the exponential agreeing with it at `b` and `c`. -/
lemma expLine_le_of_mem {g : ℝ → ℝ} (hlc : IsLogConcave g) {σ l b c : ℝ} (hσ : 0 < σ)
    (hvb : σ * Real.exp (l * b) = g b) (hvc : σ * Real.exp (l * c) = g c) (hbc : b < c)
    {t : ℝ} (ht : t ∈ Set.Icc b c) : σ * Real.exp (l * t) ≤ g t := by
  obtain ⟨ht1, ht2⟩ := ht
  have hcb : (0 : ℝ) < c - b := by linarith
  have hs0 : (0 : ℝ) ≤ (t - b) / (c - b) := div_nonneg (by linarith) hcb.le
  have hs1 : (t - b) / (c - b) ≤ 1 := (div_le_one hcb).2 (by linarith)
  have hts : t = (1 - (t - b) / (c - b)) * b + (t - b) / (c - b) * c := by
    field_simp; ring
  have key := hlc.geom_le b c (show (0 : ℝ) ≤ 1 - (t - b) / (c - b) by linarith) hs0 (by ring)
  rw [smul_eq_mul, smul_eq_mul, ← hts] at key
  calc σ * Real.exp (l * t)
      = (σ * Real.exp (l * b)) ^ (1 - (t - b) / (c - b))
          * (σ * Real.exp (l * c)) ^ ((t - b) / (c - b)) := by
        rw [expLine_geom hσ l b c ((t - b) / (c - b)), ← hts]
    _ = g b ^ (1 - (t - b) / (c - b)) * g c ^ ((t - b) / (c - b)) := by rw [hvb, hvc]
    _ ≤ g t := key

/-- To the left of `b`, `g` lies below the exponential through `(b, g b)` and `(c, g c)`. -/
lemma le_expLine_of_le {g : ℝ → ℝ} (hlc : IsLogConcave g) {σ l b c : ℝ} (hσ : 0 < σ)
    (hvb : σ * Real.exp (l * b) = g b) (hvc : σ * Real.exp (l * c) = g c) (hbc : b < c)
    {t : ℝ} (ht : t ≤ b) : g t ≤ σ * Real.exp (l * t) := by
  rcases eq_or_lt_of_le ht with rfl | htb
  · exact hvb.ge
  · have hct : (0 : ℝ) < c - t := by linarith
    have hs0 : (0 : ℝ) ≤ (b - t) / (c - t) := div_nonneg (by linarith) hct.le
    have hs1 : (b - t) / (c - t) < 1 := (div_lt_one hct).2 (by linarith)
    have hbs : b = (1 - (b - t) / (c - t)) * t + (b - t) / (c - t) * c := by
      field_simp; ring
    have key := hlc.geom_le t c (show (0 : ℝ) ≤ 1 - (b - t) / (c - t) by linarith) hs0 (by ring)
    rw [smul_eq_mul, smul_eq_mul, ← hbs] at key
    have hE : (σ * Real.exp (l * t)) ^ (1 - (b - t) / (c - t))
        * (σ * Real.exp (l * c)) ^ ((b - t) / (c - t)) = g b := by
      rw [expLine_geom hσ l t c ((b - t) / (c - t)), ← hbs, hvb]
    have hposc : 0 < (σ * Real.exp (l * c)) ^ ((b - t) / (c - t)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have key2 : g t ^ (1 - (b - t) / (c - t)) * (σ * Real.exp (l * c)) ^ ((b - t) / (c - t))
        ≤ (σ * Real.exp (l * t)) ^ (1 - (b - t) / (c - t))
          * (σ * Real.exp (l * c)) ^ ((b - t) / (c - t)) := by
      rw [hE, hvc]; exact key
    have key3 : g t ^ (1 - (b - t) / (c - t))
        ≤ (σ * Real.exp (l * t)) ^ (1 - (b - t) / (c - t)) :=
      le_of_mul_le_mul_right key2 hposc
    by_contra hcon
    exact absurd key3 (not_le.2 (Real.rpow_lt_rpow (by positivity) (not_le.1 hcon) (by linarith)))

/-- To the right of `c`, `g` lies below the exponential through `(b, g b)` and `(c, g c)`. -/
lemma le_expLine_of_ge {g : ℝ → ℝ} (hlc : IsLogConcave g) {σ l b c : ℝ} (hσ : 0 < σ)
    (hvb : σ * Real.exp (l * b) = g b) (hvc : σ * Real.exp (l * c) = g c) (hbc : b < c)
    {t : ℝ} (ht : c ≤ t) : g t ≤ σ * Real.exp (l * t) := by
  rcases eq_or_lt_of_le ht with rfl | hct
  · exact hvc.ge
  · have htb : (0 : ℝ) < t - b := by linarith
    have hs0 : (0 : ℝ) < (c - b) / (t - b) := div_pos (by linarith) htb
    have hs1 : (c - b) / (t - b) ≤ 1 := (div_le_one htb).2 (by linarith)
    have hcs : c = (1 - (c - b) / (t - b)) * b + (c - b) / (t - b) * t := by
      field_simp; ring
    have key := hlc.geom_le b t (show (0 : ℝ) ≤ 1 - (c - b) / (t - b) by linarith) hs0.le (by ring)
    rw [smul_eq_mul, smul_eq_mul, ← hcs] at key
    have hE : (σ * Real.exp (l * b)) ^ (1 - (c - b) / (t - b))
        * (σ * Real.exp (l * t)) ^ ((c - b) / (t - b)) = g c := by
      rw [expLine_geom hσ l b t ((c - b) / (t - b)), ← hcs, hvc]
    have hposb : 0 < (σ * Real.exp (l * b)) ^ (1 - (c - b) / (t - b)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have key2 : (σ * Real.exp (l * b)) ^ (1 - (c - b) / (t - b)) * g t ^ ((c - b) / (t - b))
        ≤ (σ * Real.exp (l * b)) ^ (1 - (c - b) / (t - b))
          * (σ * Real.exp (l * t)) ^ ((c - b) / (t - b)) := by
      rw [hE, hvb]; exact key
    have key3 : g t ^ ((c - b) / (t - b)) ≤ (σ * Real.exp (l * t)) ^ ((c - b) / (t - b)) :=
      le_of_mul_le_mul_left key2 hposb
    by_contra hcon
    exact absurd key3 (not_le.2 (Real.rpow_lt_rpow (by positivity) (not_le.1 hcon) hs0))

/-! ### Locating a point where `g` is positive -/

lemma integral_eq_zero_of_eqOn_Ioo {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Ioo a b, g x = 0) : (∫ x in a..b, g x) = 0 := by
  rw [intervalIntegral.integral_of_le hab, ← setIntegral_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
  exact setIntegral_eq_zero_of_forall_eq_zero h

lemma exists_pos_of_integral_ne_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg0 : ∀ x, 0 ≤ g x)
    (h : (∫ x in a..b, g x) ≠ 0) : ∃ x ∈ Set.Ioo a b, 0 < g x := by
  by_contra hcon
  refine h (integral_eq_zero_of_eqOn_Ioo hab fun x hx => le_antisymm ?_ (hg0 x))
  exact not_lt.1 fun hpos => hcon ⟨x, hx, hpos⟩

/-! ### Lovász–Vempala, Lemma 5.9 -/

/-- **The one-dimensional cross-ratio inequality** (Lovász–Vempala, *The geometry of
logconcave functions and sampling algorithms*, Lemma 5.9), in division-free form.

For a nonnegative log-concave `g : ℝ → ℝ` and `a < b < c < d`,
`(d-a)(c-b) · g(a,b) · g(c,d) ≤ (b-a)(d-c) · g(a,d) · g(b,c)`, i.e.
`(a:c:b:d) ≤ (a:c:b:d)_g`.

No positivity of `g` is required: `g` may be compactly supported, in which case the
Euclidean cross-ratio side simply vanishes. Only interval integrability on `[a, d]` is
assumed. -/
theorem crossRatio_mul_le_crossRatio_integral {g : ℝ → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hlc : IsLogConcave g) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hint : IntervalIntegrable g volume a d) :
    (d - a) * (c - b) * ((∫ t in a..b, g t) * (∫ t in c..d, g t))
      ≤ (b - a) * (d - c) * ((∫ t in a..d, g t) * (∫ t in b..c, g t)) := by
  have had : a ≤ d := by linarith
  have hsub : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ d → IntervalIntegrable g volume x y := by
    intro x y hx hxy hy
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hxy, Set.uIcc_of_le had]
    exact Set.Icc_subset_Icc hx hy
  have hIab : IntervalIntegrable g volume a b := hsub le_rfl hab.le (by linarith)
  have hIbc : IntervalIntegrable g volume b c := hsub hab.le hbc.le (by linarith)
  have hIcd : IntervalIntegrable g volume c d := hsub (by linarith) hcd.le le_rfl
  have hIac : IntervalIntegrable g volume a c := hsub le_rfl (by linarith) (by linarith)
  set A := ∫ t in a..b, g t with hAdef
  set B := ∫ t in b..c, g t with hBdef
  set C := ∫ t in c..d, g t with hCdef
  have hABC : A + B + C = ∫ t in a..d, g t := by
    rw [hAdef, hBdef, hCdef, intervalIntegral.integral_add_adjacent_intervals hIab hIbc,
      intervalIntegral.integral_add_adjacent_intervals hIac hIcd]
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hab.le fun u _ => hg0 u
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hbc.le fun u _ => hg0 u
  have hC0 : 0 ≤ C := intervalIntegral.integral_nonneg hcd.le fun u _ => hg0 u
  rw [← hABC]
  -- reduce to the algebraic statement `β (α+β+γ) A C ≤ α γ B (A+B+C)`
  suffices hmain : (c - b) * ((b - a) + (c - b) + (d - c)) * (A * C)
      ≤ (b - a) * (d - c) * (B * (A + B + C)) by
    calc (d - a) * (c - b) * (A * C)
        = (c - b) * ((b - a) + (c - b) + (d - c)) * (A * C) := by ring
      _ ≤ (b - a) * (d - c) * (B * (A + B + C)) := hmain
      _ = (b - a) * (d - c) * ((A + B + C) * B) := by ring
  rcases eq_or_lt_of_le hA0 with hAz | hApos
  · have : A * C = 0 := by rw [← hAz]; ring
    rw [this, mul_zero]
    positivity
  rcases eq_or_lt_of_le hC0 with hCz | hCpos
  · have : A * C = 0 := by rw [← hCz]; ring
    rw [this, mul_zero]
    positivity
  -- both outer integrals are positive, so `g` is positive at `b` and at `c`
  obtain ⟨x₀, hx₀mem, hx₀⟩ := exists_pos_of_integral_ne_zero hab.le hg0 (ne_of_gt hApos)
  obtain ⟨y₀, hy₀mem, hy₀⟩ := exists_pos_of_integral_ne_zero hcd.le hg0 (ne_of_gt hCpos)
  have hgb : 0 < g b := pos_of_lt_of_lt hlc hx₀ hy₀ hx₀mem.2 (by linarith [hy₀mem.1])
  have hgc : 0 < g c := pos_of_lt_of_lt hlc hx₀ hy₀ (by linarith [hx₀mem.2]) hy₀mem.1
  -- the exponential through `(b, g b)` and `(c, g c)`
  set l := (Real.log (g c) - Real.log (g b)) / (c - b) with hldef
  set σ := g b * Real.exp (-(l * b)) with hσdef
  have hσ : 0 < σ := mul_pos hgb (Real.exp_pos _)
  have hvb : σ * Real.exp (l * b) = g b := by
    rw [hσdef, mul_assoc, ← Real.exp_add]; simp
  have hvc : σ * Real.exp (l * c) = g c := by
    rw [hσdef, mul_assoc, ← Real.exp_add,
      show -(l * b) + l * c = l * (c - b) from by ring, hldef,
      div_mul_cancel₀ _ (show c - b ≠ 0 by linarith), Real.exp_sub, Real.exp_log hgc,
      Real.exp_log hgb]
    field_simp
  have hcont : Continuous fun t : ℝ => σ * Real.exp (l * t) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  set A' := ∫ t in a..b, σ * Real.exp (l * t) with hA'def
  set B' := ∫ t in b..c, σ * Real.exp (l * t) with hB'def
  set C' := ∫ t in c..d, σ * Real.exp (l * t) with hC'def
  have hAA : A ≤ A' :=
    intervalIntegral.integral_mono_on hab.le hIab (hcont.intervalIntegrable _ _)
      fun x hx => le_expLine_of_le hlc hσ hvb hvc hbc hx.2
  have hCC : C ≤ C' :=
    intervalIntegral.integral_mono_on hcd.le hIcd (hcont.intervalIntegrable _ _)
      fun x hx => le_expLine_of_ge hlc hσ hvb hvc hbc hx.1
  have hBB : B' ≤ B :=
    intervalIntegral.integral_mono_on hbc.le (hcont.intervalIntegrable _ _) hIbc
      fun x hx => expLine_le_of_mem hlc hσ hvb hvc hbc hx
  have hB'0 : 0 ≤ B' :=
    intervalIntegral.integral_nonneg hbc.le fun u _ => by positivity
  -- the exponential case, converted from the "means" form to the algebraic form
  have hHac : A' + B' = ∫ t in a..c, σ * Real.exp (l * t) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hHbd : B' + C' = ∫ t in b..d, σ * Real.exp (l * t) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hexpM := exp_crossRatio_key (σ := σ) (l := l) hσ hab hbc hcd
  rw [← hHac, ← hHbd] at hexpM
  have hexp : (c - b) * ((b - a) + (c - b) + (d - c)) * (A' * C')
      ≤ (b - a) * (d - c) * (B' * (A' + B' + C')) := by nlinarith [hexpM]
  exact crossRatio_algebra (by linarith : (0 : ℝ) < b - a) (by linarith : (0 : ℝ) < c - b)
    (by linarith : (0 : ℝ) < d - c) hA0 hB0 hC0 hAA hCC hBB hB'0 hexp

/-- The equivalent **"overlapping intervals beat separated intervals"** form. Writing
`M x y = (∫ t in x..y, g t) / (y - x)` for the mean value of `g` on `[x, y]`, this says
`M a b * M c d ≤ M a c * M b d` for `a < b < c < d`: the two *overlapping* intervals
`[a,c]`, `[b,d]` have a larger product of means than the two *disjoint* ones `[a,b]`,
`[c,d]`. It is equivalent to `crossRatio_mul_le_crossRatio_integral` (the two statements
differ by adding `(b-a)(d-c) · g(a,b) · g(c,d)` to both sides), and is the shape the proof
actually runs in. Stated multiplied out, so no positivity is needed. -/
theorem integral_mul_integral_le_of_isLogConcave {g : ℝ → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hlc : IsLogConcave g) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hint : IntervalIntegrable g volume a d) :
    (c - a) * (d - b) * ((∫ t in a..b, g t) * (∫ t in c..d, g t))
      ≤ (b - a) * (d - c) * ((∫ t in a..c, g t) * (∫ t in b..d, g t)) := by
  have had : a ≤ d := by linarith
  have hsub : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ d → IntervalIntegrable g volume x y := by
    intro x y hx hxy hy
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hxy, Set.uIcc_of_le had]
    exact Set.Icc_subset_Icc hx hy
  have hIab : IntervalIntegrable g volume a b := hsub le_rfl hab.le (by linarith)
  have hIbc : IntervalIntegrable g volume b c := hsub hab.le hbc.le (by linarith)
  have hIcd : IntervalIntegrable g volume c d := hsub (by linarith) hcd.le le_rfl
  have hIac : IntervalIntegrable g volume a c := hsub le_rfl (by linarith) (by linarith)
  have hac : (∫ t in a..b, g t) + (∫ t in b..c, g t) = ∫ t in a..c, g t :=
    intervalIntegral.integral_add_adjacent_intervals hIab hIbc
  have hbd : (∫ t in b..c, g t) + (∫ t in c..d, g t) = ∫ t in b..d, g t :=
    intervalIntegral.integral_add_adjacent_intervals hIbc hIcd
  have had' : (∫ t in a..c, g t) + (∫ t in c..d, g t) = ∫ t in a..d, g t :=
    intervalIntegral.integral_add_adjacent_intervals hIac hIcd
  have hmain := crossRatio_mul_le_crossRatio_integral hg0 hlc hab hbc hcd hint
  rw [← hac, ← hbd]
  rw [← had', ← hac] at hmain
  nlinarith [hmain]

/-- **Lovász–Vempala Lemma 5.9**, quotient form: for a positive log-concave `g` and
`a < b < c < d`, the Euclidean cross-ratio `(a:c:b:d)` is at most the `g`-weighted
cross-ratio `(a:c:b:d)_g`. -/
theorem crossRatio_le_crossRatio_integral {g : ℝ → ℝ}
    (hgpos : ∀ x, 0 < g x) (hlc : IsLogConcave g) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hint : IntervalIntegrable g volume a d) :
    (d - a) * (c - b) / ((b - a) * (d - c))
      ≤ ((∫ t in a..d, g t) * (∫ t in b..c, g t))
          / ((∫ t in a..b, g t) * (∫ t in c..d, g t)) := by
  have had : a ≤ d := by linarith
  have hsub : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ d → IntervalIntegrable g volume x y := by
    intro x y hx hxy hy
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hxy, Set.uIcc_of_le had]
    exact Set.Icc_subset_Icc hx hy
  have hApos : 0 < ∫ t in a..b, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hsub le_rfl hab.le (by linarith)) (fun x _ => hgpos x) hab
  have hCpos : 0 < ∫ t in c..d, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hsub (by linarith) hcd.le le_rfl) (fun x _ => hgpos x) hcd
  have hden : (0 : ℝ) < (b - a) * (d - c) := by
    have h1 : (0 : ℝ) < b - a := by linarith
    have h2 : (0 : ℝ) < d - c := by linarith
    positivity
  rw [div_le_div_iff₀ hden (mul_pos hApos hCpos)]
  have hmain := crossRatio_mul_le_crossRatio_integral (fun x => (hgpos x).le) hlc hab hbc hcd hint
  linarith [hmain]

/-! ### Bridge to `Arlib.crossRatioDist`

`Arlib.crossRatioDist K u v` is the *Euclidean* cross-ratio of the chord of `K` through
`u, v`, in an arbitrary normed space. Restricted to a segment in `ℝ` it is literally the
Lovász–Vempala quantity `(a : c : b : d)`: with `K = [a, d]`, `u = b`, `v = c` the chord
endpoints are `a` and `d`, and `crossRatioDist_eq_param` evaluates to
`(d-a)(c-b) / ((b-a)(d-c))`. So the two notions agree, and Lemma 5.9 can be read as a
statement about `crossRatioDist`. -/

lemma chordParam_Icc {a b c d : ℝ} (hbc : b < c) :
    chordParam (Set.Icc a d) b c = Set.Icc ((a - b) / (c - b)) ((d - b) / (c - b)) := by
  have hcb : (0 : ℝ) < c - b := by linarith
  ext t
  rw [mem_chordParam, lineMap_apply', smul_eq_mul]
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [div_le_iff₀ hcb]; linarith, by rw [le_div_iff₀ hcb]; linarith⟩
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hcb] at h1
    rw [le_div_iff₀ hcb] at h2
    exact ⟨by linarith, by linarith⟩

/-- On a segment of `ℝ`, `crossRatioDist` *is* the Lovász–Vempala Euclidean cross-ratio
`(a : c : b : d) = (d-a)(c-b) / ((b-a)(d-c))`. -/
theorem crossRatioDist_Icc {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    crossRatioDist (Set.Icc a d) b c = (d - a) * (c - b) / ((b - a) * (d - c)) := by
  have hcb : (0 : ℝ) < c - b := by linarith
  have hba : (0 : ℝ) < b - a := by linarith
  have hdc : (0 : ℝ) < d - c := by linarith
  have hcb' : c - b ≠ 0 := ne_of_gt hcb
  have hba' : b - a ≠ 0 := ne_of_gt hba
  have hdc' : d - c ≠ 0 := ne_of_gt hdc
  have hle : (a - b) / (c - b) ≤ (d - b) / (c - b) := by
    apply div_le_div_of_nonneg_right (by linarith) hcb.le
  have hlow : chordLow (Set.Icc a d) b c = (a - b) / (c - b) := by
    rw [chordLow, chordParam_Icc (a := a) (d := d) hbc, csInf_Icc hle]
  have hhigh : chordHigh (Set.Icc a d) b c = (d - b) / (c - b) := by
    rw [chordHigh, chordParam_Icc (a := a) (d := d) hbc, csSup_Icc hle]
  rw [crossRatioDist_eq_param (Metric.isBounded_Icc a d) (ne_of_lt hbc)
      ⟨hab.le, by linarith⟩ ⟨by linarith, hcd.le⟩, hlow, hhigh]
  have hnum : (d - b) / (c - b) - (a - b) / (c - b) = (d - a) / (c - b) := by
    field_simp; ring
  have hden1 : -((a - b) / (c - b)) = (b - a) / (c - b) := by
    rw [neg_div', neg_sub]
  have hden2 : (d - b) / (c - b) - 1 = (d - c) / (c - b) := by
    field_simp; ring
  rw [hnum, hden1, hden2]
  field_simp

/-- **Lemma 5.9 in `crossRatioDist` form.** For a positive log-concave `g` on `ℝ` and
`a < b < c < d`, the Euclidean cross-ratio of the chord `[a, d]` at the pair `b, c` is at
most the `g`-weighted cross-ratio. -/
theorem crossRatioDist_le_crossRatio_integral {g : ℝ → ℝ}
    (hgpos : ∀ x, 0 < g x) (hlc : IsLogConcave g) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hint : IntervalIntegrable g volume a d) :
    crossRatioDist (Set.Icc a d) b c
      ≤ ((∫ t in a..d, g t) * (∫ t in b..c, g t))
          / ((∫ t in a..b, g t) * (∫ t in c..d, g t)) := by
  rw [crossRatioDist_Icc hab hbc hcd]
  exact crossRatio_le_crossRatio_integral hgpos hlc hab hbc hcd hint

/-- Non-vacuity: the hypotheses of the main theorem are satisfiable. For a constant `g`
the inequality is an equality (`3 ≤ 3` below), which is also the extremal case. -/
example :
    (3 - 0 : ℝ) * (2 - 1) * ((∫ _t in (0 : ℝ)..1, (1 : ℝ)) * (∫ _t in (2 : ℝ)..3, (1 : ℝ)))
      ≤ (1 - 0 : ℝ) * (3 - 2)
          * ((∫ _t in (0 : ℝ)..3, (1 : ℝ)) * (∫ _t in (1 : ℝ)..2, (1 : ℝ))) :=
  crossRatio_mul_le_crossRatio_integral (fun _ => zero_le_one) (isLogConcave_const zero_le_one)
    (by norm_num) (by norm_num) (by norm_num) intervalIntegrable_const

section AxiomCheck

#print axioms expAvg_le_expAvg
#print axioms integral_const_mul_exp
#print axioms exp_crossRatio_key
#print axioms crossRatio_algebra
#print axioms expLine_geom
#print axioms pos_of_lt_of_lt
#print axioms expLine_le_of_mem
#print axioms le_expLine_of_le
#print axioms le_expLine_of_ge
#print axioms integral_eq_zero_of_eqOn_Ioo
#print axioms exists_pos_of_integral_ne_zero
#print axioms crossRatio_mul_le_crossRatio_integral
#print axioms integral_mul_integral_le_of_isLogConcave
#print axioms crossRatio_le_crossRatio_integral
#print axioms chordParam_Icc
#print axioms crossRatioDist_Icc
#print axioms crossRatioDist_le_crossRatio_integral

end AxiomCheck

end Arlib
