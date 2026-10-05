/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoIndicator
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisOverlapSqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `(1d-2)` at `√(2/π) > ln 2`, and the consumer's `hiso` discharged

Cousins–Vempala's inequality `(1d-2)` (`1409.6011/vol3_journal.tex:501`) is the one-dimensional
ingredient their `thm:iso` reduces to.  They state it at the constant
`\iso = ln 2 ≈ 0.6931` (`vol3_journal.tex:65`).  This repository proved it at
`1/(2√3) ≈ 0.2887` (`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`,
`Arlib/Convexity/ConcaveProfileIso.lean:631`), a factor `2.4` short — and that shortfall was the
**only** thing between the repository and an unconditional `thm:iso` for the density the
Metropolis-filtered Gaussian ball walk uses, because the separation threshold in `thm:iso` is
`d / c` for the `(1d-2)` constant `c`, and the consumer writes `d / log 2`.

This file proves `(1d-2)` at

  `c = √(2/π) ≈ 0.7979 > ln 2 ≈ 0.6931`,

and runs the whole downstream stack at `ln 2`, closing the gap.

## Main results

* `Arlib.gaussian_domination_of_logConcave` — **the crux.**  For `h = F·γ_σ` with `F`
  log-concave, at *every* `x`, either `h t ≤ h x · e^{−(t−x)²/(2σ²)}` for all `t ≥ x`, or the
  same for all `t ≤ x`.
* `Arlib.needle_tail_mass_le` — hence `min(∫_α^x h, ∫_x^β h) ≤ σ√(π/2) · h x`.
* `Arlib.oneDim_isoperimetry_of_tailMass` — a tail-mass bound of that shape gives `(1d-2)` with
  coefficient `1/C`.
* `Arlib.oneDim_isoperimetry_gaussianFactor_sharp` — **`(1d-2)` at `√(2/π)/σ`**, with exactly
  the hypotheses of `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`.
* `Arlib.oneDim_isoperimetry_gaussianFactor_logTwo` — the same weakened to `ln 2`
  (`Arlib.log_two_le_sqrt_two_div_pi`), which is the shape
  `Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim` consumes at `c₂ = log 2`.
* `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`,
  `Arlib.gaussianIndicator_isoperimetry_measurable_logTwo` — `thm:iso` with the metric branch at
  `d / log 2`.
* `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` — the `hiso` binder of
  `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
  (`Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean:284–295`) **character for
  character**, proved.
* `Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex` — **the payoff.**  That
  conductance bound with `hiso` discharged; the only added hypothesis is
  `hRσ : √3·R ≤ 2σ√n`.
* `Arlib.uniform_saturates_hensley` — the diagnosis: where `1/(2√3)` was lost.
* `Arlib.exists_gaussian_tails_gt` — the ceiling: `σ√(π/2)` in the crux is optimal.
* `Arlib.oneDim_isoperimetry_gaussianFactor_sharp_witness`,
  `Arlib.gaussianIndicator_isoperimetry_measurable_logTwo_witness` — non-vacuity.

## The idea

Write `h(t) = F(t)·exp(−(t−t₀)²/(2σ²))` with `F ≥ 0` log-concave.  Fix `x` and *tilt* by the
Gaussian re-centred at `x`:

  `D(t) = h(t)·exp((t−x)²/(2σ²)) = F(t)·exp(affine in t)`,

because `−(t−t₀)² + (t−x)² = 2t(t₀−x) + (x²−t₀²)` is affine.  So `D` is log-concave — this is
exactly the statement that `h` is `σ^{-2}`-**strongly** log-concave — and a log-concave function
cannot exceed its value at `x` on both sides of `x`.  On the side where it does not,

  `∫ h ≤ h(x)·∫ e^{−(t−x)²/(2σ²)} dt ≤ h(x)·σ√(π/2)`,

the half-line mass of the Gaussian.  Then `∫_α^u h · ∫_v^β h ≤ min·max ≤ σ√(π/2)·h(x)·∫_α^β h`
for every `x ∈ [u,v]`, and integrating over `[u,v]` is `(1d-2)` at `1/(σ√(π/2)) = √(2/π)/σ`.

## Why this beats the paper's own constant (`CLAUDE.md` §5)

Cousins–Vempala prove `(1d-2)` in two steps (`vol3_journal.tex:504–506`): Brascamp–Lieb gives
"the variance of `h·l^{n−1}` is at most `1`", and then Lemma `lem:1d-iso` — Theorem 5.1 of
Kannan–Lovász–Simonovits 1995, quoted at `ln 2`, whose derivation the paper carries only inside
an `\iffalse` block (`vol3_journal.tex:444–465`) — is applied to the isotropic rescaling.

**That reduction discards the Gaussian.**  After it, the only thing remembered about the needle
density is "log-concave, variance `≤ σ²`", and the extremal densities for *that* class are the
uniform and the exponential.  The class actually at hand is much smaller: `log-concave × γ_σ`,
i.e. curvature `≥ 1/σ²`, for which the Gaussian tilt above is available.  Keeping it gives
`√(2/π)` by a three-line argument that uses **no** Brascamp–Lieb, **no** Hensley bound and **no**
variance hypothesis at all.

This is not an error in the paper: `ln 2` is a true (weaker) constant on their route, given
KLS95 Theorem 5.1.  It is a route in the paper that is both harder and weaker than necessary for
the class it is applied to.

## Where the old `1/(2√3)` was lost

`Arlib.uniform_saturates_hensley` machine-checks that the uniform weight `w ≡ 1` on `[0,1]`
satisfies the second-moment hypothesis of `Arlib.oneDim_isoperimetry_variance` **with equality**
at `s = 1/(2√3)` and has `sup w = Z/(2√3 s)` **exactly**.  So Hensley's bound
(`Arlib.cube_le_sq_mul_moment`) is tight there and no constant above `1/(2√3)` can be obtained
by bounding `sup w`: the whole factor `2√3·ln 2 ≈ 2.4` is lost in the *other* step, the
pointwise Cheeger inequality `Arlib.cheeger_mul_le`, which replaces `F(x)(1−F(x))` by its bound
through `sup w` and wastes a factor of up to `4` precisely where Hensley is tight (for that
uniform weight the true coefficient is `4 = 2/(√3 s)`).

## What is and is not claimed about optimality

`Arlib.exists_gaussian_tails_gt` shows the constant `σ√(π/2)` in `Arlib.needle_tail_mass_le` is
attained in the limit by the Gaussian itself, so `√(2/π)` is exactly the ceiling **of this
argument**.  It is not the best possible constant in `(1d-2)`: for `h = γ_σ` the true
coefficient is `4·γ(0)·σ = √(8/π) ≈ 1.596/σ`, twice what is proved here, the loss being the
step `∫_α^u h·∫_v^β h ≤ min·max` (with `max ≤ ∫_α^β h` in place of the sharper
`F(x)(1−F(x)) ≤ 1/4`).  Nothing downstream benefits from closing that gap: the payoff is a
cliff at `ln 2`, and `√(2/π)` clears it.

## What is assumed

**Nothing.**  There is no `def`, `structure`, `class` or `axiom` in this file; every declaration
is a `theorem`, and none takes `thm:iso`, `(1d-2)`, a localization binder or any part of one as
a hypothesis.  See the axiom audit at the end.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*,
§3 (`1409.6011/vol3_journal.tex:404–508`).
-/

namespace Arlib

open MeasureTheory Set Filter Metric
open Arlib.MarkovChains
open scoped ENNReal Topology

/-! ### Unimodality of a log-concave function about a point -/

/-- **A log-concave function cannot exceed its value at `x` on both sides of `x`.**

If `D t₁ > D x` and `D t₂ > D x` with `t₁ < x < t₂` then, `x` being a convex combination of
`t₁` and `t₂`, the geometric-mean inequality gives `D x ≥ D t₁ ^ a · D t₂ ^ b > D x`.  No
continuity, no differentiability, no strict positivity: this is quasi-concavity, which
`LogConcaveOn` contains outright. -/
theorem logConcaveOn_forall_le_or_forall_le {α β : ℝ} {D : ℝ → ℝ}
    (hD : LogConcaveOn (Set.Icc α β) D) {x : ℝ} (hx : x ∈ Set.Icc α β) (hDx : 0 ≤ D x) :
    (∀ t ∈ Set.Icc x β, D t ≤ D x) ∨ (∀ t ∈ Set.Icc α x, D t ≤ D x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨t₂, ht₂, h2⟩, ⟨t₁, ht₁, h1⟩⟩ := hcon
  have hne₁ : t₁ ≠ x := by rintro rfl; exact absurd h1 (lt_irrefl _)
  have hne₂ : t₂ ≠ x := by rintro rfl; exact absurd h2 (lt_irrefl _)
  have hx1 : t₁ < x := lt_of_le_of_ne ht₁.2 hne₁
  have hx2 : x < t₂ := lt_of_le_of_ne ht₂.1 (Ne.symm hne₂)
  have hd : 0 < t₂ - t₁ := by linarith
  set a : ℝ := (t₂ - x) / (t₂ - t₁) with hadef
  set b : ℝ := (x - t₁) / (t₂ - t₁) with hbdef
  have ha : 0 < a := div_pos (by linarith) hd
  have hb : 0 < b := div_pos (by linarith) hd
  have hab : a + b = 1 := by rw [hadef, hbdef]; field_simp; ring
  have hcomb : a • t₁ + b • t₂ = x := by
    simp only [smul_eq_mul, hadef, hbdef]
    field_simp
    ring
  have hm₁ : t₁ ∈ Set.Icc α β := ⟨ht₁.1, ht₁.2.trans hx.2⟩
  have hm₂ : t₂ ∈ Set.Icc α β := ⟨hx.1.trans ht₂.1, ht₂.2⟩
  have key := hD.geom_le hm₁ hm₂ ha.le hb.le hab
  rw [hcomb] at key
  have h1pos : 0 < D t₁ := lt_of_le_of_lt hDx h1
  have h2pos : 0 < D t₂ := lt_of_le_of_lt hDx h2
  rcases hDx.lt_or_eq with hpos | hzero
  · have e1 : D x ^ a < D t₁ ^ a := Real.rpow_lt_rpow hDx h1 ha
    have e2 : D x ^ b < D t₂ ^ b := Real.rpow_lt_rpow hDx h2 hb
    have esplit : D x ^ a * D x ^ b = D x := by
      rw [← Real.rpow_add hpos, hab, Real.rpow_one]
    have := mul_lt_mul'' e1 e2 (Real.rpow_nonneg hDx a) (Real.rpow_nonneg hDx b)
    linarith [key, esplit]
  · have hprod : 0 < D t₁ ^ a * D t₂ ^ b :=
      mul_pos (Real.rpow_pos_of_pos h1pos a) (Real.rpow_pos_of_pos h2pos b)
    linarith [key, hzero]

/-! ### The tilted needle density -/

/-- The exponential of an affine function is log-concave (with equality in the defining
inequality). -/
theorem logConcaveOn_exp_affine {s : Set ℝ} (hs : Convex ℝ s) (p q : ℝ) :
    LogConcaveOn s (fun t => Real.exp (p * t + q)) := by
  refine ⟨hs, fun u _ v _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply le_of_eq
  congr 1
  linear_combination q * hab

/-- **The Gaussian-tilted density is log-concave.**

`t ↦ F t · exp(−(t−t₀)²/(2σ²)) · exp((t−x)²/(2σ²))` — the needle density with the Gaussian
*re-centred at `x`* divided out — is `F` times the exponential of an **affine** function,
because the two quadratics cancel:
`−(t−t₀)² + (t−x)² = 2t(t₀−x) + (x²−t₀²)`.  This is the whole reason the argument works: the
Gaussian factor is what makes the density *strongly* log-concave, and strong log-concavity is
exactly the statement that the tilt by `exp((t−x)²/(2σ²))` is still log-concave. -/
theorem logConcaveOn_gaussianTilt {σ : ℝ} {F : ℝ → ℝ} {t₀ α β x : ℝ}
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F) :
    LogConcaveOn (Set.Icc α β)
      (fun t => F t * Real.exp ((t₀ - x) / σ ^ 2 * t + (x ^ 2 - t₀ ^ 2) / (2 * σ ^ 2))) :=
  LogConcaveOn.mul hFc (logConcaveOn_exp_affine (convex_Icc α β) _ _) hF0
    (fun _ _ => (Real.exp_pos _).le)

/-- **Gaussian domination on one side of any point.**

For `h = F·γ` with `F` log-concave and `γ(t) = exp(−(t−t₀)²/(2σ²))`, and any `x ∈ [α,β]`,
*either* `h t ≤ h x · exp(−(t−x)²/(2σ²))` for every `t ≥ x`, *or* the same for every `t ≤ x`.

The tilted density `D t = h t · exp((t−x)²/(2σ²))` is log-concave
(`Arlib.logConcaveOn_gaussianTilt`) and `D x = h x`, so
`Arlib.logConcaveOn_forall_le_or_forall_le` applies verbatim. -/
theorem gaussian_domination_of_logConcave {σ : ℝ} (hσ : 0 < σ) {F : ℝ → ℝ} {t₀ α β x : ℝ}
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hx : x ∈ Set.Icc α β) :
    (∀ t ∈ Set.Icc x β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))
        ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)) * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)))
      ∨ (∀ t ∈ Set.Icc α x, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))
        ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
          * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2))) := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt hσ
  set D : ℝ → ℝ :=
    fun t => F t * Real.exp ((t₀ - x) / σ ^ 2 * t + (x ^ 2 - t₀ ^ 2) / (2 * σ ^ 2)) with hDdef
  -- `D t = h t · exp((t−x)²/(2σ²))`
  have hDeq : ∀ t : ℝ, D t
      = F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) * Real.exp ((t - x) ^ 2 / (2 * σ ^ 2)) := by
    intro t
    have hexp : (t₀ - x) / σ ^ 2 * t + (x ^ 2 - t₀ ^ 2) / (2 * σ ^ 2)
        = -(t - t₀) ^ 2 / (2 * σ ^ 2) + (t - x) ^ 2 / (2 * σ ^ 2) := by
      field_simp
      ring
    rw [hDdef]
    simp only
    rw [mul_assoc, ← Real.exp_add, hexp]
  have hDx : D x = F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)) := by
    rw [hDeq x]
    simp
  have hDx0 : 0 ≤ D x := by
    rw [hDx]; exact mul_nonneg (hF0 x hx) (Real.exp_pos _).le
  have hmain := logConcaveOn_forall_le_or_forall_le (logConcaveOn_gaussianTilt
    (σ := σ) (t₀ := t₀) (x := x) hF0 hFc) hx hDx0
  -- transport `D t ≤ D x` into the stated form
  have htrans : ∀ t : ℝ, D t ≤ D x →
      F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))
        ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
          * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) := by
    intro t hle
    rw [hDeq t, hDx] at hle
    have hcancel : Real.exp ((t - x) ^ 2 / (2 * σ ^ 2))
        * Real.exp (-((t - x) ^ 2 / (2 * σ ^ 2))) = 1 := by
      rw [← Real.exp_add]; simp
    have hneg : -((t - x) ^ 2 / (2 * σ ^ 2)) = -(t - x) ^ 2 / (2 * σ ^ 2) := by ring
    have hmul := mul_le_mul_of_nonneg_right hle
      (Real.exp_pos (-((t - x) ^ 2 / (2 * σ ^ 2)))).le
    calc F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))
        = F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))
            * Real.exp ((t - x) ^ 2 / (2 * σ ^ 2))
            * Real.exp (-((t - x) ^ 2 / (2 * σ ^ 2))) := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * Real.exp (-((t - x) ^ 2 / (2 * σ ^ 2))) := hmul
      _ = F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) := by
          rw [hneg]
  rcases hmain with h | h
  · exact Or.inl fun t ht => htrans t (h t ht)
  · exact Or.inr fun t ht => htrans t (h t ht)

/-! ### The half-line Gaussian mass -/

/-- `∫_0^∞ e^{−u²/(2σ²)} du = σ√(π/2)`, half of the full Gaussian mass `σ√(2π)`.

This is Mathlib's `integral_gaussian_Ioi` at `b = 1/(2σ²)`; the factor `1/2` it carries is
exactly the "half-line" that makes the constant below `√(2/π)` rather than `1/√(2π)`. -/
theorem integral_Ioi_gaussian {σ : ℝ} (hσ : 0 < σ) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u ^ 2 / (2 * σ ^ 2)))
      = Real.sqrt (Real.pi / 2) * σ := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt hσ
  have hfun : (fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2)))
      = fun u : ℝ => Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2) := by
    funext u
    congr 1
    field_simp
  rw [hfun, integral_gaussian_Ioi]
  have hval : Real.pi / (1 / (2 * σ ^ 2)) = (Real.sqrt (Real.pi / 2) * (2 * σ)) ^ 2 := by
    have hs : Real.sqrt (Real.pi / 2) ^ 2 = Real.pi / 2 :=
      Real.sq_sqrt (by positivity)
    rw [mul_pow, hs]
    field_simp
  rw [hval, Real.sqrt_sq (by positivity)]
  ring

/-- The Gaussian integrand is integrable on `(0,∞)`. -/
theorem integrableOn_Ioi_gaussian {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2))) (Set.Ioi 0) := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt hσ
  have hfun : (fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2)))
      = fun u : ℝ => Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2) := by
    funext u
    congr 1
    field_simp
  rw [hfun]
  exact integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (by positivity)

/-- `∫_0^r e^{−u²/(2σ²)} du ≤ σ√(π/2)` for every `r ≥ 0`: a piece of the half-line. -/
theorem intervalIntegral_gaussian_zero_le {σ : ℝ} (hσ : 0 < σ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ u in (0 : ℝ)..r, Real.exp (-u ^ 2 / (2 * σ ^ 2))) ≤ Real.sqrt (Real.pi / 2) * σ := by
  rw [intervalIntegral.integral_of_le hr, ← integral_Ioi_gaussian hσ]
  refine setIntegral_mono_set (integrableOn_Ioi_gaussian hσ) ?_
    (LE.le.eventuallyLE Set.Ioc_subset_Ioi_self)
  filter_upwards with u using (Real.exp_pos _).le

/-- The Gaussian centred at `x` has mass at most `σ√(π/2)` on any interval to the **right**
of `x`. -/
theorem intervalIntegral_gaussian_right_le {σ : ℝ} (hσ : 0 < σ) {x c : ℝ} (hxc : x ≤ c) :
    (∫ t in x..c, Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2))) ≤ Real.sqrt (Real.pi / 2) * σ := by
  have hshift : (∫ t in x..c, Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)))
      = ∫ u in (0 : ℝ)..(c - x), Real.exp (-u ^ 2 / (2 * σ ^ 2)) := by
    have h := intervalIntegral.integral_comp_sub_right
      (a := x) (b := c) (f := fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2))) x
    simpa using h
  rw [hshift]
  exact intervalIntegral_gaussian_zero_le hσ (by linarith)

/-- The Gaussian centred at `x` has mass at most `σ√(π/2)` on any interval to the **left**
of `x`. -/
theorem intervalIntegral_gaussian_left_le {σ : ℝ} (hσ : 0 < σ) {x c : ℝ} (hcx : c ≤ x) :
    (∫ t in c..x, Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2))) ≤ Real.sqrt (Real.pi / 2) * σ := by
  have hsym : (fun t : ℝ => Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)))
      = fun t : ℝ => Real.exp (-(x - t) ^ 2 / (2 * σ ^ 2)) := by
    funext t
    congr 1
    ring
  have hshift : (∫ t in c..x, Real.exp (-(x - t) ^ 2 / (2 * σ ^ 2)))
      = ∫ u in (0 : ℝ)..(x - c), Real.exp (-u ^ 2 / (2 * σ ^ 2)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := c) (b := x) (f := fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2))) x
    simpa using h
  rw [hsym, hshift]
  exact intervalIntegral_gaussian_zero_le hσ (by linarith)

/-! ### The crux: one of the two tail masses is at most `σ√(π/2)·h(x)` -/

/-- **The crux.**  For `h = F·γ` with `F` log-concave, `γ(t) = exp(−(t−t₀)²/(2σ²))`, and any
`x ∈ [α,β]`, at least one of the two masses `∫_α^x h`, `∫_x^β h` is at most
`σ√(π/2)·h(x)`.

`Arlib.gaussian_domination_of_logConcave` gives a side of `x` on which `h` is dominated by the
Gaussian re-centred at `x` and scaled to agree with `h` there; the mass of that Gaussian on a
half-line is `σ√(π/2)` (`Arlib.intervalIntegral_gaussian_right_le`).

No variance hypothesis, no Brascamp–Lieb: the bound is a direct consequence of `h` being a
log-concave function *times a Gaussian of parameter `σ`* — that is, of its strong
log-concavity, which the variance route discards. -/
theorem needle_tail_mass_le {σ : ℝ} (hσ : 0 < σ) {F : ℝ → ℝ} {t₀ α β x : ℝ}
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β)
    (hx : x ∈ Set.Icc α β) :
    (∫ t in x..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
          ≤ Real.sqrt (Real.pi / 2) * σ * (F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)))
      ∨ (∫ t in α..x, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
          ≤ Real.sqrt (Real.pi / 2) * σ
              * (F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))) := by
  have hx0 : 0 ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)) :=
    mul_nonneg (hF0 x hx) (Real.exp_pos _).le
  rcases gaussian_domination_of_logConcave hσ hF0 hFc hx with hdom | hdom
  · left
    have hmono : (∫ t in x..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
        ≤ ∫ t in x..β, F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) :=
      intervalIntegral.integral_mono_on hx.2
        (intervalIntegrable_of_subinterval hint hx.1 hx.2 le_rfl)
        (Continuous.intervalIntegrable (by fun_prop) _ _) hdom
    rw [intervalIntegral.integral_const_mul] at hmono
    calc (∫ t in x..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
        ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * ∫ t in x..β, Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) := hmono
      _ ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)) * (Real.sqrt (Real.pi / 2) * σ) :=
          mul_le_mul_of_nonneg_left (intervalIntegral_gaussian_right_le hσ hx.2) hx0
      _ = Real.sqrt (Real.pi / 2) * σ
            * (F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))) := by ring
  · right
    have hmono : (∫ t in α..x, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
        ≤ ∫ t in α..x, F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) :=
      intervalIntegral.integral_mono_on hx.1
        (intervalIntegrable_of_subinterval hint le_rfl hx.1 hx.2)
        (Continuous.intervalIntegrable (by fun_prop) _ _) hdom
    rw [intervalIntegral.integral_const_mul] at hmono
    calc (∫ t in α..x, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
        ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))
            * ∫ t in α..x, Real.exp (-(t - x) ^ 2 / (2 * σ ^ 2)) := hmono
      _ ≤ F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2)) * (Real.sqrt (Real.pi / 2) * σ) :=
          mul_le_mul_of_nonneg_left (intervalIntegral_gaussian_left_le hσ hx.1) hx0
      _ = Real.sqrt (Real.pi / 2) * σ
            * (F x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))) := by ring

/-! ### From a half-mass bound to `(1d-2)` -/

/-- **`(1d-2)` from a one-sided mass bound.**

If a nonnegative weight `w` on `[α,β]` satisfies, at every `x`, `min(∫_α^x w, ∫_x^β w) ≤ C·w x`
— stated as a disjunction, which is all the crux produces — then for `α ≤ u ≤ v ≤ β`

  `(v − u)·(∫_α^u w)·(∫_v^β w) ≤ C·(∫_α^β w)·(∫_u^v w)`,

i.e. `(1d-2)` with isoperimetric coefficient `1/C`.

This is the integration step of `Arlib.oneDim_isoperimetry` with the pointwise Cheeger
inequality replaced by the hypothesis: for `x ∈ [u,v]`, `∫_α^u w ≤ ∫_α^x w` and
`∫_v^β w ≤ ∫_x^β w`, and the product of the two tails at `x` is at most `min · max ≤ C·w x·∫_α^β w`. -/
theorem oneDim_isoperimetry_of_tailMass {α β u v C : ℝ} {w : ℝ → ℝ}
    (hw0 : ∀ t ∈ Set.Icc α β, 0 ≤ w t) (hint : IntervalIntegrable w volume α β)
    (hhalf : ∀ x ∈ Set.Icc α β,
      (∫ t in x..β, w t) ≤ C * w x ∨ (∫ t in α..x, w t) ≤ C * w x)
    (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β) :
    (v - u) * ((∫ t in α..u, w t) * (∫ t in v..β, w t))
      ≤ C * ((∫ t in α..β, w t) * (∫ t in u..v, w t)) := by
  have hαβ : α ≤ β := hau.trans (huv.trans hvβ)
  have hL0 : 0 ≤ ∫ t in α..u, w t :=
    intervalIntegral.integral_nonneg hau fun t ht => hw0 t ⟨ht.1, by linarith [ht.2]⟩
  have hR0 : 0 ≤ ∫ t in v..β, w t :=
    intervalIntegral.integral_nonneg hvβ fun t ht => hw0 t ⟨by linarith [ht.1], ht.2⟩
  -- the pointwise domination on `[u,v]`
  have hpt : ∀ x ∈ Set.Icc u v,
      (∫ t in α..u, w t) * (∫ t in v..β, w t) ≤ C * ((∫ t in α..β, w t) * w x) := by
    intro x hx
    have hux : u ≤ x := hx.1
    have hxv : x ≤ v := hx.2
    have hxαβ : x ∈ Set.Icc α β := ⟨by linarith, by linarith⟩
    have hP0 : 0 ≤ ∫ t in α..x, w t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        hw0 t ⟨ht.1, by linarith [ht.2]⟩
    have hQ0 : 0 ≤ ∫ t in x..β, w t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        hw0 t ⟨by linarith [ht.1], ht.2⟩
    have hsplit : (∫ t in α..x, w t) + (∫ t in x..β, w t) = ∫ t in α..β, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hxαβ.1 hxαβ.2)
        (intervalIntegrable_of_subinterval hint hxαβ.1 hxαβ.2 le_rfl)
    have hLP : (∫ t in α..u, w t) ≤ ∫ t in α..x, w t := by
      have hs : (∫ t in α..u, w t) + (∫ t in u..x, w t) = ∫ t in α..x, w t :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_subinterval hint le_rfl hau (by linarith))
          (intervalIntegrable_of_subinterval hint hau hux (by linarith))
      have hnn : 0 ≤ ∫ t in u..x, w t :=
        intervalIntegral.integral_nonneg hux fun t ht =>
          hw0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    have hRQ : (∫ t in v..β, w t) ≤ ∫ t in x..β, w t := by
      have hs : (∫ t in x..v, w t) + (∫ t in v..β, w t) = ∫ t in x..β, w t :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_subinterval hint (by linarith) hxv hvβ)
          (intervalIntegrable_of_subinterval hint (by linarith) hvβ le_rfl)
      have hnn : 0 ≤ ∫ t in x..v, w t :=
        intervalIntegral.integral_nonneg hxv fun t ht =>
          hw0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    have hprod : (∫ t in α..u, w t) * (∫ t in v..β, w t)
        ≤ (∫ t in α..x, w t) * (∫ t in x..β, w t) := mul_le_mul hLP hRQ hR0 hP0
    rcases hhalf x hxαβ with hQ | hP
    · have : (∫ t in α..x, w t) * (∫ t in x..β, w t)
          ≤ (∫ t in α..β, w t) * (C * w x) :=
        mul_le_mul (by linarith) hQ hQ0 (by linarith)
      calc (∫ t in α..u, w t) * (∫ t in v..β, w t)
          ≤ (∫ t in α..x, w t) * (∫ t in x..β, w t) := hprod
        _ ≤ (∫ t in α..β, w t) * (C * w x) := this
        _ = C * ((∫ t in α..β, w t) * w x) := by ring
    · have : (∫ t in α..x, w t) * (∫ t in x..β, w t)
          ≤ (C * w x) * (∫ t in α..β, w t) :=
        mul_le_mul hP (by linarith) hQ0 (by linarith [hP, hP0])
      calc (∫ t in α..u, w t) * (∫ t in v..β, w t)
          ≤ (∫ t in α..x, w t) * (∫ t in x..β, w t) := hprod
        _ ≤ (C * w x) * (∫ t in α..β, w t) := this
        _ = C * ((∫ t in α..β, w t) * w x) := by ring
  -- integrate over `[u,v]`
  have hmono : (∫ _t in u..v, (∫ t in α..u, w t) * (∫ t in v..β, w t))
      ≤ ∫ x in u..v, C * ((∫ t in α..β, w t) * w x) :=
    intervalIntegral.integral_mono_on huv intervalIntegrable_const
      (((intervalIntegrable_of_subinterval hint hau huv hvβ).const_mul _).const_mul _) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  calc (v - u) * ((∫ t in α..u, w t) * (∫ t in v..β, w t)) ≤ _ := hmono
    _ = C * ((∫ t in α..β, w t) * (∫ t in u..v, w t)) := by ring

/-! ### `(1d-2)` at `√(2/π)` -/

/-- `√(2/π)·√(π/2) = 1`. -/
theorem sqrt_two_div_pi_mul_sqrt_pi_div_two :
    Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [← Real.sqrt_mul (by positivity), show 2 / Real.pi * (Real.pi / 2) = 1 by field_simp]
  exact Real.sqrt_one

/-- **`(1d-2)` at the constant `√(2/π) ≈ 0.7979`.**

For a nonnegative log-concave `F` on `[α,β]`, the Gaussian factor
`γ(t) = exp(−(t−t₀)²/(2σ²))`, `ω = F·γ`, and `α ≤ u ≤ v ≤ β`,

  `√(2/π)/σ · (v − u) · (∫_α^u ω) · (∫_v^β ω) ≤ (∫_α^β ω) · (∫_u^v ω)`.

This is inequality `(1d-2)` of Cousins–Vempala (`vol3_journal.tex:501`) with **exactly the
hypotheses they quantify over**, at a constant **strictly larger** than their
`\iso = ln 2 ≈ 0.6931` (`vol3_journal.tex:65`) — hence a strictly stronger statement than the
paper's, and a factor `2.76` stronger than
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`'s `1/(2√3) ≈ 0.2887`.

**Why it beats the paper's own route.**  Cousins–Vempala prove `(1d-2)` by applying
Brascamp–Lieb to get "variance ≤ σ²" (`vol3_journal.tex:504–506`) and then quoting KLS95's
`lem:1d-iso` for a general *isotropic log-concave* density.  That reduction throws away the
Gaussian: after it, the only thing remembered about `ω` is that it is log-concave with a
variance bound.  The proof here keeps the Gaussian.  `ω` is log-concave **times** a Gaussian of
parameter `σ`, i.e. strongly log-concave, and for such a density the tilt
`t ↦ ω(t)·exp((t−x)²/(2σ²))` is still log-concave — so `ω` is dominated on one side of every
point `x` by the Gaussian of parameter `σ` re-centred at `x`
(`Arlib.gaussian_domination_of_logConcave`), whose half-line mass is `σ√(π/2)`.  Neither
Brascamp–Lieb, nor Hensley's bound, nor any variance hypothesis is used. -/
theorem oneDim_isoperimetry_gaussianFactor_sharp {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ)
    (t₀ α β u v : ℝ) (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β)
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β) :
    Real.sqrt (2 / Real.pi) / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
  have hbase := oneDim_isoperimetry_of_tailMass (C := Real.sqrt (Real.pi / 2) * σ)
    (w := fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
    (fun t ht => mul_nonneg (hF0 t ht) (Real.exp_pos _).le) hint
    (fun x hx => needle_tail_mass_le hσ hF0 hFc hint hx) hau huv hvβ
  have hk : 0 ≤ Real.sqrt (2 / Real.pi) / σ := by positivity
  have hkc : Real.sqrt (2 / Real.pi) / σ * (Real.sqrt (Real.pi / 2) * σ) = 1 := by
    calc Real.sqrt (2 / Real.pi) / σ * (Real.sqrt (Real.pi / 2) * σ)
        = Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) * (σ / σ) := by ring
      _ = 1 := by
          rw [sqrt_two_div_pi_mul_sqrt_pi_div_two, div_self (ne_of_gt hσ), mul_one]
  have hmul := mul_le_mul_of_nonneg_left hbase hk
  calc Real.sqrt (2 / Real.pi) / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      = Real.sqrt (2 / Real.pi) / σ * ((v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))) := by ring
    _ ≤ Real.sqrt (2 / Real.pi) / σ * (Real.sqrt (Real.pi / 2) * σ *
          ((∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))) := hmul
    _ = Real.sqrt (2 / Real.pi) / σ * (Real.sqrt (Real.pi / 2) * σ) *
          ((∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) := by ring
    _ = _ := by rw [hkc, one_mul]

/-- `ln 2 ≤ √(2/π)`: `π·(ln 2)² < 3.15 · 0.4805 < 2`. -/
theorem log_two_le_sqrt_two_div_pi : Real.log 2 ≤ Real.sqrt (2 / Real.pi) := by
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : Real.log 2 ^ 2 ≤ 2 / Real.pi := by
    rw [le_div_iff₀ hpi0]
    nlinarith [hlog, hlog0, hpi, hpi0]
  have hs : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  nlinarith [hsq, hs, Real.sqrt_nonneg (2 / Real.pi), hlog0]

/-- **`(1d-2)` at Cousins–Vempala's own constant `ln 2`**, unconditionally.

`Arlib.oneDim_isoperimetry_gaussianFactor_sharp` weakened along `ln 2 ≤ √(2/π)`
(`Arlib.log_two_le_sqrt_two_div_pi`).  This is the binder
`Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim` asks for at `c₂ = ln 2`, so the
whole downstream stack runs at the paper's constant. -/
theorem oneDim_isoperimetry_gaussianFactor_logTwo {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ)
    (t₀ α β u v : ℝ) (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β)
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β) :
    Real.log 2 / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
  have hsharp := oneDim_isoperimetry_gaussianFactor_sharp hσ F t₀ α β u v hau huv hvβ
    hF0 hFc hint
  have hL0 : 0 ≤ ∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) :=
    intervalIntegral.integral_nonneg hau fun t ht =>
      mul_nonneg (hF0 t ⟨ht.1, by linarith [ht.2]⟩) (Real.exp_pos _).le
  have hR0 : 0 ≤ ∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) :=
    intervalIntegral.integral_nonneg hvβ fun t ht =>
      mul_nonneg (hF0 t ⟨by linarith [ht.1], ht.2⟩) (Real.exp_pos _).le
  have hprod : 0 ≤ (v - u) *
      ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
        (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) :=
    mul_nonneg (by linarith) (mul_nonneg hL0 hR0)
  have hcoef : Real.log 2 / σ ≤ Real.sqrt (2 / Real.pi) / σ :=
    div_le_div_of_nonneg_right log_two_le_sqrt_two_div_pi hσ.le
  have hstep := mul_le_mul_of_nonneg_right hcoef hprod
  calc Real.log 2 / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      = Real.log 2 / σ * ((v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))) := by ring
    _ ≤ Real.sqrt (2 / Real.pi) / σ * ((v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))) := hstep
    _ = Real.sqrt (2 / Real.pi) / σ * (v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) := by ring
    _ ≤ _ := hsharp


/-! ### The capstone at `ln 2`, for open/closed partitions -/

section Downstream

variable {n : ℕ}

/-- **`Arlib.gaussianRestricted_isoperimetry_openClosed` at the separation threshold
`d / log 2`.**

Verbatim the same statement, same proof, with exactly one subterm changed: the metric branch of
`hsep` reads `d / log 2 ≤ ‖u − v‖` where the original reads `2√3·d ≤ ‖u − v‖`.  Since
`d / log 2 < 2√3·d` for `d > 0` (`Arlib.metric_threshold_lt_openClosed_threshold`), this is a
**strictly stronger** theorem: the hypothesis it demands is strictly weaker.

The only input that changes is the `(1d-2)` binder of
`Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim`, which is parametric in its
coefficient `c₂`: here it is discharged at `c₂ = log 2` by
`Arlib.oneDim_isoperimetry_gaussianFactor_logTwo` instead of at `c₂ = 1/(2√3)` by
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`. -/
theorem gaussianRestricted_isoperimetry_openClosed_logTwo (hn : 2 ≤ n) {σ d B : ℝ} (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₃ : IsClosed S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  rcases le_or_gt 0 (d / σ) with hdσ | hneg
  · exact gaussianRestricted_isoperimetry_concave_gt_of_oneDim (by omega) hσ
      (Real.log_pos (by norm_num)) hf₀ hfc hh hpart hS₁.measurableSet hS₂.measurableSet
      hS₃.measurableSet hmass hsep
      (hloc_gt_of_localization_ge hn hS₁.measurableSet hS₂.measurableSet hS₃.measurableSet
        (fun A hA hone htwo => exists_needle_openClosed hn h0 hhc hhB hhi hS₁ hS₂ hS₃
          hpart.disjoint₁₂ hpart.disjoint₁₃ hA hdσ hone htwo))
      (fun F t₀ α β u v hau huv hvβ hF0 hFc hint =>
        oneDim_isoperimetry_gaussianFactor_logTwo hσ F t₀ α β u v hau huv hvβ hF0 hFc hint)
  · have hm₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
    have hm₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
    have hm₃ : 0 ≤ ∫ x in S₃, h x := integral_nonneg fun x => h0 x
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (mul_nonneg hm₁ hm₂))
      (mul_nonneg hmass.le hm₃)

/-- **`thm:iso` for the indicator density at the separation threshold `d / log 2`.**

`Arlib.gaussianIndicator_isoperimetry_measurable` with its metric branch at `d / log 2` in place
of `2√3·d` — the threshold the Metropolis-ball-walk consumer actually writes.  The proof is that
theorem's, with two changes:

* the open-enlargement step `Arlib.exists_disjoint_open_enlargement_gaussianIndicator` is invoked
  at the **rescaled** radius `d/(2√3·log 2)`, at which its own `2√3·(·)` threshold *is*
  `d / log 2`, and whose density branch is implied by the one at `d` because
  `2√3·log 2 ≥ 1`;
* the open/closed capstone is
  `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`, i.e. the one that runs `(1d-2)` at
  `log 2`.

Everything else — the continuous approximation, the dominated convergence, the `d' ↑ d` limit —
is unchanged. -/
theorem gaussianIndicator_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d R : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (_hS₂ : MeasurableSet S₂) (_hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) :
    d / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
      ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
  classical
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hσsq : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hh0 : ∀ x, 0 ≤ Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    fun x => Set.indicator_nonneg (fun y _ => (hgpos y).le) x
  have hhi : Integrable (Set.indicator K (gaussianWeightReal (σ ^ 2))) := hgi.indicator hK
  have hm₁ : 0 ≤ ∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hm₂ : 0 ≤ ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hm₃ : 0 ≤ ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hM : 0 ≤ ∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  rcases le_or_gt d 0 with hdle | hd
  · have hds : d / σ ≤ 0 := by
      rw [div_le_iff₀ hσ]
      linarith
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hds (mul_nonneg hm₁ hm₂))
      (mul_nonneg hM hm₃)
  -- from here `0 < d`
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hEq
    rw [hEq] at hK0
    exact hK0 measure_empty
  -- `closure K`: compact, convex, nonempty
  have hCne : (closure K).Nonempty := hKne.closure
  have hCconv : Convex ℝ (closure K) := hKc.closure
  have hCbdd : Bornology.IsBounded (closure K) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := R)).subset ?_
    refine (closure_minimal ?_ Metric.isClosed_closedBall)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hCcomp : IsCompact (closure K) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hCbdd
  -- `(S₁ ∪ S₂)ᶜ = S₃`
  have hS₃eq : (S₁ ∪ S₂)ᶜ = S₃ := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      have hmem : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; trivial
      rcases hmem with (h1 | h2) | h3
      · exact absurd (Or.inl h1) hx
      · exact absurd (Or.inr h2) hx
      · exact h3
    · intro x hx hmem
      rcases hmem with h1 | h2
      · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) hx
      · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) hx
  -- the main estimate, for every `d' ∈ (0, d)`
  have key : ∀ d' : ℝ, 0 < d' → d' < d →
      d' / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
    intro d' hd'0 hd'd
    -- the enlargement machinery is reused *at the rescaled radius* `d/c`, `c = 2√3·log 2`,
    -- which turns its `2√3·(d/c)` threshold into exactly `d/log 2`
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have h3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3
    have hlne : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have hc0 : (0 : ℝ) < 2 * Real.sqrt 3 * Real.log 2 := by positivity
    have hc1 : (1 : ℝ) ≤ 2 * Real.sqrt 3 * Real.log 2 := by
      have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hprod : (1.7 : ℝ) * 0.6931471803 ≤ Real.sqrt 3 * Real.log 2 :=
        mul_le_mul h3.le hl.le (by norm_num) (by linarith)
      nlinarith [hprod]
    have hrescale : ∀ e : ℝ, 2 * Real.sqrt 3 * (e / (2 * Real.sqrt 3 * Real.log 2))
        = e / Real.log 2 := by
      intro e
      field_simp
    have hsep' : ∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * (d / (2 * Real.sqrt 3 * Real.log 2)) ≤ ‖u - v‖ ∨
          4 * (d / (2 * Real.sqrt 3 * Real.log 2) / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v := by
      intro u hu v hv
      rcases hsep u hu v hv with hmetric | hdens
      · exact Or.inl (by rw [hrescale d]; exact hmetric)
      · refine Or.inr (le_trans ?_ hdens)
        have hdd : d / (2 * Real.sqrt 3 * Real.log 2) ≤ d := by
          rw [div_le_iff₀ hc0]
          nlinarith [hd.le, hc1]
        have hn0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
        have hds : d / (2 * Real.sqrt 3 * Real.log 2) / σ ≤ d / σ :=
          div_le_div_of_nonneg_right hdd hσ.le
        nlinarith [hds, hn0]
    obtain ⟨U₁, U₂, hU₁, hU₂, hUdisj, hsub₁, hsub₂, hUsep0⟩ :=
      exists_disjoint_open_enlargement_gaussianIndicator (σ := σ)
        (d := d / (2 * Real.sqrt 3 * Real.log 2))
        (d' := d' / (2 * Real.sqrt 3 * Real.log 2)) hσ (div_pos hd hc0) (div_pos hd'0 hc0)
        (by gcongr) hKR hRσ hpart.disjoint₁₂ hsep'
    have hUsep : ∀ u ∈ U₁, ∀ v ∈ U₂, d' / Real.log 2 ≤ ‖u - v‖ := by
      intro u hu v hv
      have h := hUsep0 u hu v hv
      rwa [hrescale d'] at h
    -- the capstone, applied to the continuous approximations on `U₁, U₂, (U₁ ∪ U₂)ᶜ`
    have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
      { union := Set.union_compl_self (U₁ ∪ U₂)
        disjoint₁₂ := hUdisj
        disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
        disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
    have hcap : ∀ j : ℕ,
        d' / σ * ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
          ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x := by
      intro j
      have hcInf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x (closure K)) :=
        Metric.continuous_infDist_pt _
      have hfc : Continuous
          (fun x : EuclideanSpace ℝ (Fin n) =>
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))) :=
        Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)
      have hjc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x) :=
        hfc.mul (continuous_gaussianWeightReal _)
      have hf1 : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) ≤ 1 := by
        intro x
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
      have hf0 : ∀ x : EuclideanSpace ℝ (Fin n),
          0 < Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := fun x => Real.exp_pos _
      have hjB : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x ≤ 1 := by
        intro x
        have h1 := hf1 x
        have h2 : gaussianWeightReal (σ ^ 2) x ≤ 1 :=
          gaussianWeightReal_le_one hσsq x
        nlinarith [hf0 x, hgpos x]
      have hji : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x) := by
        refine hgi.mono' hjc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x).le (hgpos x).le)]
        nlinarith [hf1 x, hf0 x, hgpos x]
      have hjmass : 0 < ∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
          * gaussianWeightReal (σ ^ 2) x := by
        obtain ⟨z₀, hz₀⟩ := hCne
        have hz₀R : ‖z₀‖ ≤ R := by
          have hsub : closure K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
            refine closure_minimal ?_ Metric.isClosed_closedBall
            intro x hx
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hKR x hx
          have := hsub hz₀
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have hlow : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            Real.exp (-((j : ℝ) * (1 + R))) * Real.exp (-(1 : ℝ) / (2 * σ ^ 2))
              ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
                * gaussianWeightReal (σ ^ 2) x := by
          intro x hx
          rw [Metric.mem_ball, dist_zero_right] at hx
          have hdist : Metric.infDist x (closure K) ≤ 1 + R := by
            refine le_trans (Metric.infDist_le_dist_of_mem hz₀) ?_
            rw [dist_eq_norm]
            have := norm_sub_le x z₀
            linarith
          have h1 : Real.exp (-((j : ℝ) * (1 + R)))
              ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := by
            refine Real.exp_le_exp.mpr ?_
            have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            nlinarith
          have h2 : Real.exp (-(1 : ℝ) / (2 * σ ^ 2)) ≤ gaussianWeightReal (σ ^ 2) x := by
            rw [gaussianWeightReal]
            refine Real.exp_le_exp.mpr ?_
            have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
            have hpos2 : (0 : ℝ) < 2 * σ ^ 2 := by linarith
            rw [div_le_iff₀ hpos2, div_mul_cancel₀ (-(‖x‖ ^ 2)) (ne_of_gt hpos2)]
            linarith
          have h3 : (0 : ℝ) < Real.exp (-((j : ℝ) * (1 + R))) := Real.exp_pos _
          have h4 : (0 : ℝ) < Real.exp (-(1 : ℝ) / (2 * σ ^ 2)) := Real.exp_pos _
          exact mul_le_mul h1 h2 h4.le (hf0 x).le
        have hpos := setIntegral_pos_of_ball_le (g := fun x =>
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x)
          hji (fun x => mul_nonneg (hf0 x).le (hgpos x).le) (S := Set.univ)
          (z := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
          (c := Real.exp (-((j : ℝ) * (1 + R))) * Real.exp (-(1 : ℝ) / (2 * σ ^ 2)))
          one_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Set.subset_univ _) hlow
        rwa [setIntegral_univ] at hpos
      exact gaussianRestricted_isoperimetry_openClosed_logTwo hn hσ
        (f := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))))
        (h := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
          * gaussianWeightReal (σ ^ 2) x)
        (B := 1)
        (fun x => (hf0 x).le)
        (isLogConcave_exp_neg_infDist hCconv hCcomp hCne (Nat.cast_nonneg j))
        (fun x => rfl) hjc hjB hji hpart' hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hjmass
        (fun u hu v hv => Or.inl (hUsep u hu v hv))
    -- pass to the limit `j → ∞`
    have hlim : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        Tendsto (fun j : ℕ => ∫ x in S,
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
          atTop (𝓝 (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) := by
      intro S
      have h := tendsto_setIntegral_expNegInfDist_mul_gaussian (n := n) hσ
        (C := closure K) isClosed_closure hCne S
      rwa [setIntegral_indicator_closure_eq hKc _ S] at h
    have hlimU : Tendsto (fun j : ℕ => ∫ x,
        Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x)
        atTop (𝓝 (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) := by
      have h := hlim Set.univ
      simpa only [MeasureTheory.setIntegral_univ] using h
    have hLHS : Tendsto (fun j : ℕ => d' / σ *
        ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)) atTop
        (𝓝 (d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x))) :=
      ((hlim U₁).mul (hlim U₂)).const_mul (d' / σ)
    have hRHS : Tendsto (fun j : ℕ =>
        (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x) atTop
        (𝓝 ((∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) :=
      hlimU.mul (hlim _)
    have hUineq : d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
      le_of_tendsto_of_tendsto' hLHS hRHS hcap
    -- monotonicity back to `S₁, S₂, S₃`
    have hcut : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          = ∫ x in S ∩ K, gaussianWeightReal (σ ^ 2) x := fun S => setIntegral_indicator hK
    have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
        (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          ≤ ∫ x in T, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      intro S T hST
      exact setIntegral_mono_set hhi.integrableOn
        (Filter.Eventually.of_forall hh0) hST.eventuallyLE
    have hcore₁ : (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₁ ∩ K, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut S₁, hcut (S₁ ∩ K), Set.inter_assoc, Set.inter_self]
    have hcore₂ : (∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₂ ∩ K, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut S₂, hcut (S₂ ∩ K), Set.inter_assoc, Set.inter_self]
    have hsetiii : ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ ∩ K = S₃ ∩ K := by
      ext x
      constructor
      · rintro ⟨hnot, hxK⟩
        refine ⟨?_, hxK⟩
        rw [← hS₃eq]
        intro hmem
        rcases hmem with h1 | h2
        · exact hnot (Or.inl ⟨h1, hxK⟩)
        · exact hnot (Or.inr ⟨h2, hxK⟩)
      · rintro ⟨h3, hxK⟩
        refine ⟨?_, hxK⟩
        rintro (⟨h1, -⟩ | ⟨h2, -⟩)
        · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) h3
        · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) h3
    have hcore₃ : (∫ x in ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ,
          Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut _, hcut S₃, hsetiii]
    have hU₃sub : (U₁ ∪ U₂)ᶜ ⊆ ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ := by
      refine Set.compl_subset_compl.mpr ?_
      exact Set.union_subset_union hsub₁ hsub₂
    have hle₁ : (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcore₁]; exact hmono hsub₁
    have hle₂ : (∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcore₂]; exact hmono hsub₂
    have hle₃ : (∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [← hcore₃]; exact hmono hU₃sub
    have hd'σ : 0 ≤ d' / σ := (div_pos hd'0 hσ).le
    calc d' / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hle₁ hle₂ hm₂ (le_trans hm₁ hle₁)) hd'σ
      _ ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := hUineq
      _ ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
          mul_le_mul_of_nonneg_left hle₃ hM
  -- let `d' ↑ d`
  by_contra hcon
  rw [not_le] at hcon
  set P : ℝ := (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x with hPdef
  set Q : ℝ := (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x with hQdef
  have hQ0 : 0 ≤ Q := mul_nonneg hM hm₃
  have hPnn : 0 ≤ P := mul_nonneg hm₁ hm₂
  have hP : 0 < P := by
    rcases hPnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, mul_zero] at hcon
      linarith
  have hcd : σ * Q / P < d := by
    rw [div_lt_iff₀ hP]
    have hstep : Q * σ < d / σ * P * σ := mul_lt_mul_of_pos_right hcon hσ
    have hrw : d / σ * P * σ = d * P := by field_simp
    rw [hrw] at hstep
    linarith
  set d' : ℝ := (max (σ * Q / P) (d / 2) + d) / 2 with hd'def
  have hmaxlt : max (σ * Q / P) (d / 2) < d := max_lt hcd (by linarith)
  have hd'lt : d' < d := by rw [hd'def]; linarith
  have hd'gt : max (σ * Q / P) (d / 2) < d' := by rw [hd'def]; linarith
  have hhalf : d / 2 < d' := lt_of_le_of_lt (le_max_right _ _) hd'gt
  have hd'pos : 0 < d' := by linarith
  have hcc : σ * Q / P < d' := lt_of_le_of_lt (le_max_left _ _) hd'gt
  rw [div_lt_iff₀ hP] at hcc
  have hkey := key d' hd'pos hd'lt
  have hstep2 : d' / σ * P * σ ≤ Q * σ := mul_le_mul_of_nonneg_right hkey hσ.le
  have hrw2 : d' / σ * P * σ = d' * P := by field_simp
  rw [hrw2] at hstep2
  linarith

/-! ### The consumer's binder, discharged -/

/-- **`hiso` for the Metropolis-filtered Gaussian ball walk, character for character.**

This is the `hiso` binder of `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
(`Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean:284–295`) **verbatim**: the partition,
the four measurability hypotheses, the metric branch
`δ·log 2/√n / log 2 ≤ ‖u − v‖`, the density branch
`4(δ·log 2/√n/σ)√n ≤ d_h(u,v)` and the conclusion
`(δ·log 2/√n/σ)·π(S₁)π(S₂) ≤ π(1)·π(S₃)` at `h = 1_K·gaussianWeightReal σ²`.

`Arlib.hiso_metropolisGaussian_sharp_sqrt` (`Arlib/Convexity/IsoIndicator.lean:828`) states the
same thing with the metric branch at `2√3·(δ·log 2/√n)` — a *strictly stronger* hypothesis
(`Arlib.metric_threshold_lt_openClosed_threshold`), which is why it could not be handed to the
consumer.  That gap is closed here, and it is closed by the `(1d-2)` constant alone: everything
else in the two proofs is identical.

`hKtop` is accepted and unused, so that the argument list is the consumer's. -/
theorem hiso_metropolisGaussian_sharp_sqrt_logTwo (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (_hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n) :
    ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
  fun _S₁ _S₂ _S₃ hpart hS₁ hS₂ hS₃ hsep =>
    gaussianIndicator_isoperimetry_measurable_logTwo hn hσ hK hKc hKR hK0 hRσ hpart hS₁ hS₂ hS₃
      hsep

/-! ### The payoff: the sharp-`√n` conductance bound loses its `hiso` hypothesis -/

/-- **`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge` with `hiso` discharged.**

The only hypothesis of that theorem that this repository could not previously supply was `hiso`
— Cousins–Vempala's `thm:iso` at `d = δ·log 2/√n`, whose metric branch is stated at the
threshold `d / log 2`.  `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` now proves exactly
that binder, so the conductance bound holds outright, with `hRσ : √3·R ≤ 2σ√n` (a bounding
radius compatible with the Gaussian scale) as the only added hypothesis.

The docstring of `conductance_metropolisGaussian_sharp_sqrt_ge` says of `hiso`: "It is **not
proved in this repository**.  Therefore **this theorem is not a mixing-time bound...**".  With
this corollary that caveat no longer applies to the conductance statement itself. -/
theorem conductance_metropolisGaussian_sharp_sqrt_ge_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ Arlib.MarkovChains.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ Arlib.MarkovChains.conductance (Arlib.MarkovChains.metropolisGaussian K δ (σ ^ 2))
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (σ ^ 2))) K) :=
  Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδ hδσ hR hK hKc hKR
    hKtop hK0 hell hfloor
    (hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)

/-! ### Non-vacuity (`CLAUDE.md` §11) -/

/-- **Non-vacuity of `Arlib.oneDim_isoperimetry_gaussianFactor_sharp` and
`Arlib.oneDim_isoperimetry_gaussianFactor_logTwo`.**

Every hypothesis is met outright at `F ≡ 1`, `σ = 1`, `t₀ = 0`, `[α,β] = [-1,1]`,
`u = -1/2`, `v = 1/2`, and the left-hand side is *strictly positive* there — so neither
statement is the trivial `0 ≤ something`. -/
theorem oneDim_isoperimetry_gaussianFactor_sharp_witness :
    ∃ (F : ℝ → ℝ) (σ t₀ α β u v : ℝ),
      0 < σ ∧ α ≤ u ∧ u ≤ v ∧ v ≤ β ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ F t) ∧ LogConcaveOn (Set.Icc α β) F ∧
        IntervalIntegrable
          (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β ∧
        0 < Real.sqrt (2 / Real.pi) / σ * (v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) := by
  have hcont : Continuous fun t : ℝ =>
      (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by fun_prop
  have hpos : ∀ p q : ℝ, p < q →
      0 < ∫ t in p..q, (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
    intro p q hpq
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _) (fun x _ => by positivity) hpq
  refine ⟨fun _ => (1 : ℝ), 1, 0, -1, 1, -(1 / 2), 1 / 2, one_pos, by norm_num, by norm_num,
    by norm_num, fun _ _ => zero_le_one,
    logConcaveOn_const (convex_Icc _ _) zero_le_one, hcont.intervalIntegrable _ _, ?_⟩
  have h1 := hpos (-1) (-(1 / 2)) (by norm_num)
  have h2 := hpos (1 / 2) 1 (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h3 : (0 : ℝ) < Real.sqrt (2 / Real.pi) / 1 * (1 / 2 - -(1 / 2)) := by positivity
  exact mul_pos h3 (mul_pos h1 h2)

/-- **Non-vacuity of `Arlib.gaussianIndicator_isoperimetry_measurable_logTwo`.**

The witness of `Arlib.gaussianIndicator_isoperimetry_measurable_witness` verbatim: its
separation clause is stated at the *larger* threshold `2√3·d`, which implies the one at
`d / log 2` by `Arlib.metric_threshold_lt_openClosed_threshold`.  Every clause is satisfied
outright and the left-hand side is strictly positive. -/
theorem gaussianIndicator_isoperimetry_measurable_logTwo_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d R : ℝ),
      0 < σ ∧ 0 < d ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
      Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (d / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) ∧
      (S₁ ∩ K).Nonempty ∧ (S₂ ∩ K).Nonempty ∧
      0 < d / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) := by
  obtain ⟨K, S₁, S₂, S₃, σ, d, R, hσ, hd, hK, hKc, hKR, hK0, hRσ, hpart, hS₁, hS₂, hS₃,
    hsep, hne₁, hne₂, hposLHS⟩ := gaussianIndicator_isoperimetry_measurable_witness (n := n) hn
  refine ⟨K, S₁, S₂, S₃, σ, d, R, hσ, hd, hK, hKc, hKR, hK0, hRσ, hpart, hS₁, hS₂, hS₃, ?_,
    hne₁, hne₂, hposLHS⟩
  intro u hu v hv
  rcases hsep u hu v hv with hm | hdens
  · exact Or.inl (le_trans (metric_threshold_lt_openClosed_threshold hd).le hm)
  · exact Or.inr hdens

/-! ### Where the old constant `1/(2√3)` was lost -/

/-- **Hensley's bound is saturated by the uniform weight, so the route through `sup w`
cannot give a constant better than `1/(2√3)`.**

`Arlib.oneDim_isoperimetry_variance` obtains its coefficient by showing that a log-concave
weight of second moment `≤ s²·Z` about some point comes arbitrarily close to `Z/(2√3 s)`
somewhere, and then applying `Arlib.oneDim_isoperimetry` at such a point.  Both facts below
hold for `w ≡ 1` on `[0,1]` at `c = 1/2`, `s = 1/(2√3)`:

* the second-moment hypothesis holds **with equality**, `∫₀¹ (t−½)² = 1/12 = s²·∫₀¹ 1`;
* `sup w = 1 = Z/(2√3 s)` **exactly**, so the Hensley step of that proof has no slack.

Hence the entire factor `2√3·ln 2 ≈ 2.4` by which
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` falls short of `ln 2` is lost in the
*other* step — the pointwise Cheeger inequality `Arlib.cheeger_mul_le`, which bounds
`F(x)(1−F(x))` against `sup w` and therefore wastes a factor of up to `4` exactly where
Hensley is tight.  (For this uniform weight the true isoperimetric coefficient is `4 = 2/(√3 s)`,
a factor `4` above what the route delivers.)

The proof here keeps the Gaussian instead and never uses either step. -/
theorem uniform_saturates_hensley :
    (∫ t in (0:ℝ)..1, (t - 1 / 2) ^ 2 * (1 : ℝ))
        = (1 / (2 * Real.sqrt 3)) ^ 2 * ∫ _t in (0:ℝ)..1, (1 : ℝ)
      ∧ ∀ _t ∈ Set.Icc (0:ℝ) 1,
          (1 : ℝ) = (∫ _s in (0:ℝ)..1, (1 : ℝ)) / (2 * Real.sqrt 3 * (1 / (2 * Real.sqrt 3))) := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hZ : (∫ _t in (0:ℝ)..1, (1 : ℝ)) = 1 := by simp
  constructor
  · have h1 : (∫ t in (0:ℝ)..1, (t - 1 / 2) ^ 2 * (1 : ℝ))
        = ∫ t in (0:ℝ)..1, (t - 1 / 2) ^ 2 := by simp
    have h2 : (∫ t in (0:ℝ)..1, (t - 1 / 2) ^ 2) = 1 / 12 := by
      rw [intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u ^ 2) (1/2)]
      norm_num [integral_pow]
    rw [h1, h2, hZ, div_pow, one_pow, mul_pow, hsq]
    norm_num
  · intro _t _
    rw [hZ]
    field_simp

/-! ### The constant `√(2/π)` is exactly this route's ceiling -/

/-- `∫_0^r e^{−u²/(2σ²)} du → σ√(π/2)` as `r → ∞`. -/
theorem tendsto_intervalIntegral_gaussian_atTop {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun r : ℝ => ∫ u in (0:ℝ)..r, Real.exp (-u ^ 2 / (2 * σ ^ 2)))
      Filter.atTop (nhds (Real.sqrt (Real.pi / 2) * σ)) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
    (f := fun u : ℝ => Real.exp (-u ^ 2 / (2 * σ ^ 2))) (b := fun r : ℝ => r)
    (l := Filter.atTop) 0 (integrableOn_Ioi_gaussian hσ) Filter.tendsto_id
  rwa [integral_Ioi_gaussian hσ] at h

/-- **The constant `σ√(π/2)` in `Arlib.needle_tail_mass_le` cannot be lowered**, so the
constant `√(2/π)` of `Arlib.oneDim_isoperimetry_gaussianFactor_sharp` is exactly the ceiling of
this route.

Take `F ≡ 1`, `t₀ = 0`, `x = 0`, so the density is the Gaussian itself and `h x = 1`.  Both of
its tail masses on `[−β,0]` and `[0,β]` equal `∫_0^β e^{−u²/(2σ²)}`, which increases to
`σ√(π/2)`; so for any `C < σ√(π/2)` there is a `β` at which **both** disjuncts of the crux fail.
(This does not bound the best constant for `(1d-2)` itself — only the one this proof can
deliver.  See the module docstring.) -/
theorem exists_gaussian_tails_gt {σ C : ℝ} (hσ : 0 < σ)
    (hC : C < Real.sqrt (Real.pi / 2) * σ) :
    ∃ β : ℝ, 0 < β ∧
      C < (∫ t in (0:ℝ)..β, (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * σ ^ 2))) ∧
      C < ∫ t in (-β)..(0:ℝ), (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * σ ^ 2)) := by
  have hsimp : ∀ p q : ℝ, (∫ t in p..q, (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * σ ^ 2)))
      = ∫ t in p..q, Real.exp (-t ^ 2 / (2 * σ ^ 2)) := by
    intro p q
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [one_mul]
    congr 1
    ring
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      C < ∫ u in (0:ℝ)..r, Real.exp (-u ^ 2 / (2 * σ ^ 2)) :=
    (tendsto_intervalIntegral_gaussian_atTop hσ).eventually_const_lt hC
  obtain ⟨β, hβ0, hβ⟩ := ((Filter.eventually_gt_atTop (0 : ℝ)).and hev).exists
  refine ⟨β, hβ0, ?_, ?_⟩
  · rw [hsimp]; exact hβ
  · rw [hsimp]
    have h := intervalIntegral.integral_comp_neg
      (a := (0:ℝ)) (b := β) (f := fun t : ℝ => Real.exp (-t ^ 2 / (2 * σ ^ 2)))
    have hmirror : (∫ t in (-β)..(0:ℝ), Real.exp (-t ^ 2 / (2 * σ ^ 2)))
        = ∫ t in (0:ℝ)..β, Real.exp (-t ^ 2 / (2 * σ ^ 2)) := by
      rw [neg_zero] at h
      rw [← h]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      congr 1
      ring
    rw [hmirror]
    exact hβ

end Downstream

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.logConcaveOn_forall_le_or_forall_le
#print axioms Arlib.logConcaveOn_exp_affine
#print axioms Arlib.logConcaveOn_gaussianTilt
#print axioms Arlib.gaussian_domination_of_logConcave
#print axioms Arlib.integral_Ioi_gaussian
#print axioms Arlib.integrableOn_Ioi_gaussian
#print axioms Arlib.intervalIntegral_gaussian_zero_le
#print axioms Arlib.intervalIntegral_gaussian_right_le
#print axioms Arlib.intervalIntegral_gaussian_left_le
#print axioms Arlib.needle_tail_mass_le
#print axioms Arlib.oneDim_isoperimetry_of_tailMass
#print axioms Arlib.sqrt_two_div_pi_mul_sqrt_pi_div_two
#print axioms Arlib.oneDim_isoperimetry_gaussianFactor_sharp
#print axioms Arlib.log_two_le_sqrt_two_div_pi
#print axioms Arlib.oneDim_isoperimetry_gaussianFactor_logTwo
#print axioms Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo
#print axioms Arlib.gaussianIndicator_isoperimetry_measurable_logTwo
#print axioms Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo
#print axioms Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex
#print axioms Arlib.oneDim_isoperimetry_gaussianFactor_sharp_witness
#print axioms Arlib.gaussianIndicator_isoperimetry_measurable_logTwo_witness
#print axioms Arlib.uniform_saturates_hensley
#print axioms Arlib.tendsto_intervalIntegral_gaussian_atTop
#print axioms Arlib.exists_gaussian_tails_gt
