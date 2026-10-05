/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogConcave
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.PrekopaLeindler
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One-dimensional Brascamp–Lieb: a log-concave function times a Gaussian

The headline result is `Arlib.brascampLieb_oneDim`: for `σ > 0`, a nonnegative log-concave
`F` on `[α,β]` and the Gaussian factor `γ(t) = exp(−(t − t₀)²/(2σ²))`, there is a point
`c ∈ [α,β]` with

  `∫_α^β (t − c)² F(t)γ(t) dt ≤ σ² ∫_α^β F(t)γ(t) dt`,

i.e. **the probability measure proportional to `F·γ` on `[α,β]` has variance at most
`σ²`**.  The point `c` produced is the barycentre `(∫tF γ)/(∫Fγ)`, which is the optimal
choice: `c ↦ ∫(t−c)²Fγ` is minimised there.

This is the `α = 2` case of the Brascamp–Lieb inequality quoted by Cousins and Vempala
(`1409.6011/vol3_journal.tex:407`), in exactly the form their proof of `thm:iso` uses at
`vol3_journal.tex:506`.  It is the hypothesis `hvar` of
`Arlib.oneDim_isoperimetry_gaussianFactor` (`Arlib/Convexity/ConcaveProfileIso.lean:407`),
and discharging it turns that theorem into `Arlib.gaussianRestricted_isoperimetry`'s `h1d2`
binder verbatim, at the constant `1/(2√3)`.

## Why this is not `Arlib.brascampLieb`

`Arlib.brascampLieb` (`Arlib/Convexity/GaussianCooling/Variance.lean:693`) is the
*needle-specific* inequality `J₂J₀ − J₁² ≤ (σ²/x)J₀²` for the one-parameter exponential
family `s(x,·)`, with **no log-concave factor**.  It does not apply to a general `F`, which
is why this file exists.  Its proof technique (integration by parts) is also not the one
used here, for the reason in the next paragraph.

## No differentiability

The textbook proof writes the density as `e^{−V}` with `V'' ≥ 1/σ²` and integrates by
parts.  A log-concave `F` need not be differentiable — it need not even be continuous at
the two endpoints of its support — so that route would either weaken the statement or force
an approximation argument.  The route taken here needs no regularity of `F` whatsoever:

1. `Arlib.isLogConcave_indicator_of_logConcaveOn` extends `F` by zero to a log-concave `G`
   on all of `ℝ`, and `Arlib.measurable_of_isLogConcave` shows `G` is automatically
   measurable — every strict superlevel set of a log-concave function is convex, hence
   order-connected, hence measurable.  Measurability is therefore *not* a hypothesis.
2. `Arlib.integral_exp_mul_integral_exp_neg_le` is the analytic core: one application of
   `Arlib.prekopa_leindler_one_dim` at `lam = 1/2` gives

     `(∫ e^{k(t−c)}W)(∫ e^{−k(t−c)}W) ≤ e^{σ²k²}(∫W)²`,  `W = G·γ`,

   which says the two-sided Laplace transform is log-concave with modulus `σ²`.  The
   constant `σ²` comes from the completed square
   `σ²k²/2 − ((x+y)/2 − t₀)²/(2σ²) − [k(x−y)/2 − ((x−t₀)²+(y−t₀)²)/(4σ²)]
   = (2σ²k − (x−y))²/(8σ²) ≥ 0` and cannot be improved.
3. `Arlib.exists_mem_Icc_integral_sq_sub_le_of_expBound` expands `e^{±k(t−c)}` to second
   order about the **barycentre**, where the first moment vanishes so the error is `O(k³)`
   rather than `O(k)`, and lets `k → 0`.  The only Taylor estimates used are
   `Arlib.exp_lower_bound_cubic` and `Arlib.exp_upper_bound_quadratic`, both immediate from
   `Real.exp_bound`.

Prékopa–Leindler is used, once, in step 2.  `Arlib.Convexity.OneDimIsoperimetry` avoids it
deliberately; here there is no comparable elementary substitute, because the statement is
genuinely about a *convolution* structure (`k ↦ ∫e^{kt}W` is the Laplace transform of a
log-concave function) rather than about a monotone rearrangement.

## Main results

* `Arlib.convex_setOf_lt_of_isLogConcave`, `Arlib.measurable_of_isLogConcave` — a
  nonnegative log-concave function on `ℝ` is measurable, with no regularity hypothesis.
* `Arlib.isLogConcave_indicator_of_logConcaveOn` — extension by zero off a convex domain
  preserves log-concavity.
* `Arlib.integral_exp_mul_integral_exp_neg_le` — the Prékopa–Leindler step.
* `Arlib.exp_lower_bound_cubic`, `Arlib.exp_upper_bound_quadratic` — the two Taylor bounds.
* `Arlib.integrable_mul_of_bddOn_Icc` — every integrability side condition.
* `Arlib.le_integral_exp_mul_of_barycentre` — the second-order lower bound on the
  exponential moment.
* `Arlib.le_of_forall_pos_small` — the `k → 0` limit, as pure arithmetic.
* `Arlib.exists_mem_Icc_integral_sq_sub_le_of_expBound` — the variance bound, from the
  exponential-moment bound.
* `Arlib.brascampLieb_oneDim` — **the theorem**, in interval-integral form.
* `Arlib.brascampLieb_oneDim_uniform_witness`,
  `Arlib.brascampLieb_oneDim_exp_witness` — non-vacuity: all hypotheses hold, with positive
  total mass, for `F ≡ 1` and for the non-constant `F(t) = e^{−|t|}` on `[−1,1]` at `σ = 1`.

## Two remarks on the printed statement

**The constant.**  Cousins–Vempala state Brascamp–Lieb for the *standard* Gaussian
(`vol3_journal.tex:407`), and apply it at `vol3_journal.tex:506` to a needle whose Gaussian
factor has variance `σ²`, reaching "variance at most `1`" only after their global rescaling
`x = y/σ`.  The intrinsic statement at general `σ` is the one proved here, with `σ²` on the
right; that is also the form `Arlib.oneDim_isoperimetry_gaussianFactor` consumes, and it
matches `Arlib.Convexity.SharpIsoperimetry`'s `d/σ`.  No discrepancy.

**The range `α ≥ 1`.**  Only `α = 2` is used at `vol3_journal.tex:506`, and only `α = 2` is
proved here.  Note that `α ∈ [1,2)` does **not** follow from `α = 2`: Jensen gives
`E|Y|^α ≤ (E|Y|²)^{α/2} ≤ σ^α`, whereas the printed claim is the strictly smaller
`E_γ|x₁|^α = σ^α·E|N(0,1)|^α` (about `0.798·σ` at `α = 1`).  So the printed theorem is
strictly stronger than what is verified here for `α < 2`; nothing in this repository
depends on it.

## Sharpness

`σ²` is not improvable: with `F ≡ 1` on `[−L,L]` the measure is a Gaussian truncated to
`[−L,L]`, whose variance increases to `σ²` as `L → ∞`.  On any bounded interval the
inequality is strict, which is why the conclusion is an inequality.

## No rate claim

Nothing here says, or implies, that any algorithm runs in polynomial time.  This file
proves a single second-moment inequality; it contains no mixing, conductance or complexity
statement.

## References

Brascamp and Lieb, *On extensions of the Brunn–Minkowski and Prékopa–Leindler theorems…*,
J. Funct. Anal. **22** (1976).

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3 (`1409.6011/vol3_journal.tex:404–508`).
-/

namespace Arlib

open MeasureTheory Set

/-! ### Log-concave functions are measurable -/

section Measurability

/-- **The strict superlevel sets of a nonnegative log-concave function are convex.** -/
theorem convex_setOf_lt_of_isLogConcave {G : ℝ → ℝ} (hG : IsLogConcave G)
    (hG0 : ∀ x, 0 ≤ G x) (c : ℝ) : Convex ℝ {x : ℝ | c < G x} := by
  rcases lt_or_ge c 0 with hc | hc
  · have hall : {x : ℝ | c < G x} = (Set.univ : Set ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hc (hG0 x)
    rw [hall]
    exact convex_univ
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  have key := hG.geom_le x y ha hb hab
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · have h1 : (0 : ℝ) < G x ^ a := Real.rpow_pos_of_pos hx a
    have h2 : (0 : ℝ) < G y ^ b := Real.rpow_pos_of_pos hy b
    exact lt_of_lt_of_le (mul_pos h1 h2) key
  · have h1 : c ^ a < G x ^ a := Real.rpow_lt_rpow hc hx ha'
    have h2 : c ^ b < G y ^ b := Real.rpow_lt_rpow hc hy hb'
    have hcc : c ^ a * c ^ b = c := by
      rw [← Real.rpow_add hcpos, hab, Real.rpow_one]
    have := mul_lt_mul'' h1 h2 (Real.rpow_nonneg hc a) (Real.rpow_nonneg hc b)
    rw [hcc] at this
    exact lt_of_lt_of_le this key

/-- **A nonnegative log-concave function on `ℝ` is measurable.**

No continuity or differentiability hypothesis is needed, and none is available: a
log-concave function may be discontinuous at the two endpoints of its support.  What is
true is that every strict superlevel set `{x | c < G x}` is *convex*
(`Arlib.convex_setOf_lt_of_isLogConcave`), hence order-connected, hence measurable
(`Set.OrdConnected.measurableSet`); and a function all of whose strict superlevel sets are
measurable is measurable (`measurable_of_Ioi`). -/
theorem measurable_of_isLogConcave {G : ℝ → ℝ} (hG : IsLogConcave G) (hG0 : ∀ x, 0 ≤ G x) :
    Measurable G :=
  measurable_of_Ioi fun c =>
    (((convex_setOf_lt_of_isLogConcave hG hG0 c).ordConnected).measurableSet :
      MeasurableSet {x : ℝ | c < G x})

end Measurability

/-! ### Extension by zero -/

section Extension

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Extending a log-concave function by zero off its (convex) domain keeps it
log-concave.**

This is the standard way to pass from `LogConcaveOn s F` — the form the one-dimensional
isoperimetry files use — to a statement about a function on the whole line, which is what
`Arlib.prekopa_leindler_one_dim` consumes. -/
theorem isLogConcave_indicator_of_logConcaveOn {s : Set E} {F : E → ℝ}
    (hF : LogConcaveOn s F) (hF0 : ∀ x ∈ s, 0 ≤ F x) :
    IsLogConcave (Set.indicator s F) := by
  have hnn : ∀ x, 0 ≤ Set.indicator s F x :=
    fun x => Set.indicator_nonneg (fun y hy => hF0 y hy) x
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hz : a • x + b • y ∈ s := hF.convex hx hy ha hb hab
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact hF.geom_le hx hy ha hb hab
    · rcases eq_or_ne b 0 with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simp
      · rw [Set.indicator_of_notMem hy, Real.zero_rpow hb', mul_zero]
        exact hnn _
  · rcases eq_or_ne a 0 with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    · rw [Set.indicator_of_notMem hx, Real.zero_rpow ha', zero_mul]
      exact hnn _

end Extension

/-! ### The Prékopa–Leindler step -/

section PLStep

/-- **The two-sided exponential moment of a log-concave function times a Gaussian is
controlled by the Gaussian factor alone.**

For `W = G·γ` with `G` log-concave and `γ(t) = exp(−(t−t₀)²/(2σ²))`, and for every real
`k` and every base point `c`,

  `(∫ e^{k(t−c)} W) · (∫ e^{−k(t−c)} W) ≤ e^{σ²k²} (∫ W)²`.

Equivalently: the two-sided Laplace transform `k ↦ ∫ e^{kt}W(t) dt` is log-concave *with a
quantitative modulus* — its logarithm minus `σ²k²/2` is concave — which is the entire
content of Brascamp–Lieb in one dimension.  The base point `c` is irrelevant (it
contributes `e^{kc}·e^{−kc} = 1`) and is kept only because the caller uses `c = ` the
barycentre.

The proof is one application of `Arlib.prekopa_leindler_one_dim` at `lam = 1/2` to
`f = e^{k(·−c)}W`, `g = e^{−k(·−c)}W`, `h = e^{σ²k²/2}W`.  The pointwise hypothesis splits
into the log-concavity of `G` at the midpoint and the Gaussian identity

  `σ²k²/2 − ((x+y)/2 − t₀)²/(2σ²) − [k(x−y)/2 − ((x−t₀)² + (y−t₀)²)/(4σ²)]
     = (2σ²k − (x−y))²/(8σ²) ≥ 0`,

which is where the constant `σ²` — and nothing smaller — comes from. -/
theorem integral_exp_mul_integral_exp_neg_le {σ t₀ c k : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ}
    (hG : IsLogConcave G) (hG0 : ∀ t, 0 ≤ G t)
    (hW : Integrable fun t => G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
    (hf : Integrable fun t =>
      Real.exp (k * (t - c)) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
    (hg : Integrable fun t =>
      Real.exp (-(k * (t - c))) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) :
    (∫ t, Real.exp (k * (t - c)) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) *
        (∫ t, Real.exp (-(k * (t - c))) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ Real.exp (σ ^ 2 * k ^ 2) *
        (∫ t, G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) ^ 2 := by
  have hGm : Measurable G := measurable_of_isLogConcave hG hG0
  have hW0 : ∀ t, 0 ≤ G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) :=
    fun t => mul_nonneg (hG0 t) (Real.exp_nonneg _)
  have hf0 : ∀ t, 0 ≤ Real.exp (k * (t - c)) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :=
    fun t => mul_nonneg (Real.exp_nonneg _) (hW0 t)
  have hg0 : ∀ t,
      0 ≤ Real.exp (-(k * (t - c))) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :=
    fun t => mul_nonneg (Real.exp_nonneg _) (hW0 t)
  have key := prekopa_leindler_one_dim (lam := 1 / 2)
      (f := fun t => Real.exp (k * (t - c)) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      (g := fun t => Real.exp (-(k * (t - c))) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      (h := fun t => Real.exp (σ ^ 2 * k ^ 2 / 2) *
        (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      (by norm_num) (by norm_num)
      (by fun_prop) (by fun_prop) (by fun_prop)
      hf0 hg0 hf hg (hW.const_mul _) ?_
  · -- square the Prékopa–Leindler conclusion
    rw [integral_const_mul] at key
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h12] at key
    set X := ∫ t, Real.exp (k * (t - c)) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) with hX
    set Y := ∫ t, Real.exp (-(k * (t - c))) * (G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
      with hY
    set A := ∫ t, G t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) with hA
    have hX0 : 0 ≤ X := integral_nonneg hf0
    have hY0 : 0 ≤ Y := integral_nonneg hg0
    have hA0 : 0 ≤ A := integral_nonneg hW0
    have hsqrt : Real.sqrt (X * Y) ≤ Real.exp (σ ^ 2 * k ^ 2 / 2) * A := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hX0 hY0]
      exact key
    have hmul : X * Y ≤ (Real.exp (σ ^ 2 * k ^ 2 / 2) * A) ^ 2 := by
      nlinarith [Real.sq_sqrt (mul_nonneg hX0 hY0), Real.sqrt_nonneg (X * Y), hsqrt]
    refine hmul.trans_eq ?_
    have hdouble : σ ^ 2 * k ^ 2 / 2 + σ ^ 2 * k ^ 2 / 2 = σ ^ 2 * k ^ 2 := by ring
    rw [mul_pow, pow_two (Real.exp (σ ^ 2 * k ^ 2 / 2)), ← Real.exp_add, hdouble]
  · -- the pointwise Prékopa–Leindler hypothesis
    intro x y
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    simp only [h12]
    have hfx : (Real.exp (k * (x - c)) * (G x * Real.exp (-(x - t₀) ^ 2 / (2 * σ ^ 2))))
        ^ (1 / 2 : ℝ)
        = Real.exp (k * (x - c) * (1 / 2) + -(x - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
          * G x ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (Real.exp_nonneg _) (mul_nonneg (hG0 x) (Real.exp_nonneg _)),
        Real.mul_rpow (hG0 x) (Real.exp_nonneg _), ← Real.exp_mul, ← Real.exp_mul,
        Real.exp_add]
      ring
    have hgy : (Real.exp (-(k * (y - c))) * (G y * Real.exp (-(y - t₀) ^ 2 / (2 * σ ^ 2))))
        ^ (1 / 2 : ℝ)
        = Real.exp (-(k * (y - c)) * (1 / 2) + -(y - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
          * G y ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (Real.exp_nonneg _) (mul_nonneg (hG0 y) (Real.exp_nonneg _)),
        Real.mul_rpow (hG0 y) (Real.exp_nonneg _), ← Real.exp_mul, ← Real.exp_mul,
        Real.exp_add]
      ring
    rw [hfx, hgy]
    have hmid : G x ^ (1 / 2 : ℝ) * G y ^ (1 / 2 : ℝ) ≤ G (1 / 2 * x + 1 / 2 * y) := by
      have := hG.geom_le x y (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num)
      simpa only [smul_eq_mul] using this
    have hexp : Real.exp (k * (x - c) * (1 / 2) + -(x - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
        * Real.exp (-(k * (y - c)) * (1 / 2) + -(y - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
        ≤ Real.exp (σ ^ 2 * k ^ 2 / 2)
          * Real.exp (-(1 / 2 * x + 1 / 2 * y - t₀) ^ 2 / (2 * σ ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hid : σ ^ 2 * k ^ 2 / 2 + -(1 / 2 * x + 1 / 2 * y - t₀) ^ 2 / (2 * σ ^ 2)
          - (k * (x - c) * (1 / 2) + -(x - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2)
            + (-(k * (y - c)) * (1 / 2) + -(y - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2)))
          = (2 * σ ^ 2 * k - (x - y)) ^ 2 / (8 * σ ^ 2) := by
        field_simp
        ring
      have hnn : (0:ℝ) ≤ (2 * σ ^ 2 * k - (x - y)) ^ 2 / (8 * σ ^ 2) :=
        div_nonneg (sq_nonneg _) (by positivity)
      linarith
    calc Real.exp (k * (x - c) * (1 / 2) + -(x - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
            * G x ^ (1 / 2 : ℝ)
          * (Real.exp (-(k * (y - c)) * (1 / 2) + -(y - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
            * G y ^ (1 / 2 : ℝ))
        = (Real.exp (k * (x - c) * (1 / 2) + -(x - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2))
            * Real.exp (-(k * (y - c)) * (1 / 2) + -(y - t₀) ^ 2 / (2 * σ ^ 2) * (1 / 2)))
          * (G x ^ (1 / 2 : ℝ) * G y ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (Real.exp (σ ^ 2 * k ^ 2 / 2)
            * Real.exp (-(1 / 2 * x + 1 / 2 * y - t₀) ^ 2 / (2 * σ ^ 2)))
          * G (1 / 2 * x + 1 / 2 * y) := by
          apply mul_le_mul hexp hmid
            (mul_nonneg (Real.rpow_nonneg (hG0 x) _) (Real.rpow_nonneg (hG0 y) _))
            (by positivity)
      _ = Real.exp (σ ^ 2 * k ^ 2 / 2)
          * (G (1 / 2 * x + 1 / 2 * y)
            * Real.exp (-(1 / 2 * x + 1 / 2 * y - t₀) ^ 2 / (2 * σ ^ 2))) := by ring

end PLStep

/-! ### Two elementary bounds on `exp` -/

section ExpBounds

/-- **A cubic lower bound for `exp` on `[-1,1]`**: `1 + x + x²/2 − (2/9)|x|³ ≤ eˣ`.

`Real.exp_bound` at `n = 3` gives `|eˣ − (1 + x + x²/2)| ≤ |x|³ · 4/(3! · 3) = (2/9)|x|³`.
This is the only place where a Taylor expansion of the exponential is used; it is what
converts the multiplicative Prékopa–Leindler bound into a statement about the second
moment. -/
theorem exp_lower_bound_cubic {x : ℝ} (hx : |x| ≤ 1) :
    1 + x + x ^ 2 / 2 - 2 / 9 * |x| ^ 3 ≤ Real.exp x := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h2 := abs_le.mp h
  linarith [h2.1]

/-- **A quadratic upper bound for `exp` on `[0,1]`**: `eʸ ≤ 1 + y + y²`.

`Real.exp_bound` at `n = 2` gives `|eʸ − (1 + y)| ≤ (3/4)y²`. -/
theorem exp_upper_bound_quadratic {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ 1 + y + y ^ 2 := by
  have hy : |y| ≤ 1 := by rwa [abs_of_nonneg hy0]
  have h := Real.exp_bound hy (n := 2) (by norm_num)
  rw [abs_of_nonneg hy0] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h2 := abs_le.mp h
  nlinarith [h2.2, sq_nonneg y]

end ExpBounds

/-! ### Integrability against a bounded factor -/

section Integrability

/-- Multiplying an integrable weight supported in `[α,β]` by a measurable factor that is
bounded on `[α,β]` preserves integrability.  Every integrability side condition below is
discharged by this lemma. -/
theorem integrable_mul_of_bddOn_Icc {W φ : ℝ → ℝ} {α β C : ℝ}
    (hW : Integrable W) (hW0 : ∀ t, 0 ≤ W t)
    (hsupp : ∀ t, t ∉ Set.Icc α β → W t = 0)
    (hφ : Measurable φ) (hbd : ∀ t ∈ Set.Icc α β, |φ t| ≤ C) :
    Integrable fun t => φ t * W t := by
  refine Integrable.mono' (hW.const_mul C) (hφ.aestronglyMeasurable.mul hW.1) ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc α β
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 t)]
    exact mul_le_mul_of_nonneg_right (hbd t ht) (hW0 t)
  · rw [hsupp t ht]
    simp

end Integrability

/-! ### The second-order lower bound on the exponential moment -/

section LowerBound

/-- **The exponential moment of a compactly supported weight, bounded below to second
order.**

If `W ≥ 0` vanishes off `[α,β]`, if `|t − c| ≤ R` there, and if the first moment about `c`
vanishes, then for `|k|·R ≤ 1`

  `∫ W + (k²/2)∫(t−c)²W − (2/9)|k|³R³ ∫ W ≤ ∫ e^{k(t−c)} W`.

The first-moment term has disappeared because `c` is the barycentre; that is the only
reason the error term is `O(k³)` rather than `O(k)`, and it is what makes the limit
`k → 0` in `Arlib.exists_mem_Icc_second_moment_le` give the sharp constant. -/
theorem le_integral_exp_mul_of_barycentre {W : ℝ → ℝ} {α β c k R : ℝ}
    (hW : Integrable W) (hW0 : ∀ t, 0 ≤ W t)
    (hsupp : ∀ t, t ∉ Set.Icc α β → W t = 0)
    (hR : ∀ t ∈ Set.Icc α β, |t - c| ≤ R) (hkR : |k| * R ≤ 1)
    (hzero : (∫ t, (t - c) * W t) = 0) :
    (∫ t, W t) + k ^ 2 / 2 * (∫ t, (t - c) ^ 2 * W t)
        - 2 / 9 * |k| ^ 3 * R ^ 3 * (∫ t, W t)
      ≤ ∫ t, Real.exp (k * (t - c)) * W t := by
  have hI1 : Integrable fun t => (t - c) * W t :=
    integrable_mul_of_bddOn_Icc hW hW0 hsupp (by fun_prop) hR
  have hI2 : Integrable fun t => (t - c) ^ 2 * W t := by
    refine integrable_mul_of_bddOn_Icc (C := R ^ 2) hW hW0 hsupp (by fun_prop) ?_
    intro t ht
    have h1 := hR t ht
    have h2 : |(t - c) ^ 2| = |t - c| ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), sq_abs]
    rw [h2]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hIexp : Integrable fun t => Real.exp (k * (t - c)) * W t := by
    refine integrable_mul_of_bddOn_Icc (C := Real.exp 1) hW hW0 hsupp (by fun_prop) ?_
    intro t ht
    rw [abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
    have h1 := hR t ht
    have h2 : |k * (t - c)| ≤ 1 := by
      rw [abs_mul]
      calc |k| * |t - c| ≤ |k| * R := by
            exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ 1 := hkR
    exact (le_abs_self _).trans h2
  have hA1 : Integrable fun t => (1 - 2 / 9 * |k| ^ 3 * R ^ 3) * W t := hW.const_mul _
  have hA2 : Integrable fun t => k * ((t - c) * W t) := hI1.const_mul k
  have hA3 : Integrable fun t => k ^ 2 / 2 * ((t - c) ^ 2 * W t) := hI2.const_mul _
  have hA23 : Integrable fun t =>
      k * ((t - c) * W t) + k ^ 2 / 2 * ((t - c) ^ 2 * W t) := hA2.add hA3
  have hIlow : Integrable fun t =>
      (1 - 2 / 9 * |k| ^ 3 * R ^ 3) * W t + (k * ((t - c) * W t) + k ^ 2 / 2 * ((t - c) ^ 2 * W t))
      := hA1.add hA23
  have hmono : (∫ t, ((1 - 2 / 9 * |k| ^ 3 * R ^ 3) * W t
        + (k * ((t - c) * W t) + k ^ 2 / 2 * ((t - c) ^ 2 * W t))))
      ≤ ∫ t, Real.exp (k * (t - c)) * W t := by
    refine integral_mono hIlow hIexp ?_
    intro t
    by_cases ht : t ∈ Set.Icc α β
    · have h1 := hR t ht
      have hk : |k * (t - c)| ≤ 1 := by
        rw [abs_mul]
        calc |k| * |t - c| ≤ |k| * R := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ 1 := hkR
      have hexp := exp_lower_bound_cubic hk
      have hcube : |k * (t - c)| ^ 3 ≤ |k| ^ 3 * R ^ 3 := by
        rw [abs_mul, mul_pow]
        have : |t - c| ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have hstep : 1 - 2 / 9 * |k| ^ 3 * R ^ 3 + (k * (t - c) + k ^ 2 / 2 * (t - c) ^ 2)
          ≤ Real.exp (k * (t - c)) := by
        nlinarith [hexp, hcube]
      have := mul_le_mul_of_nonneg_right hstep (hW0 t)
      calc (1 - 2 / 9 * |k| ^ 3 * R ^ 3) * W t
            + (k * ((t - c) * W t) + k ^ 2 / 2 * ((t - c) ^ 2 * W t))
          = (1 - 2 / 9 * |k| ^ 3 * R ^ 3 + (k * (t - c) + k ^ 2 / 2 * (t - c) ^ 2)) * W t := by
            ring
        _ ≤ Real.exp (k * (t - c)) * W t := this
    · simp [hsupp t ht]
  refine le_trans (le_of_eq ?_) hmono
  rw [integral_add hA1 hA23, integral_add hA2 hA3, integral_const_mul,
    integral_const_mul, integral_const_mul, hzero]
  ring

end LowerBound

/-! ### Passing to the limit -/

section Limit

/-- If `v ≤ b + x·K` for every small positive `x`, with `K ≥ 0`, then `v ≤ b`.

This is the only limiting step in the file; it replaces the differentiation under the
integral sign that the textbook proof of Brascamp–Lieb performs. -/
theorem le_of_forall_pos_small {v b K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (hbound : ∀ x : ℝ, 0 < x → x ≤ δ → v ≤ b + x * K) : v ≤ b := by
  by_contra hcon
  have hlt : b < v := not_le.mp hcon
  have hε : 0 < v - b := by linarith
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hxpos : 0 < min δ ((v - b) / (K + 1)) := lt_min hδ (div_pos hε hK1)
  have hstep := hbound _ hxpos (min_le_left _ _)
  have hxK : min δ ((v - b) / (K + 1)) * K < v - b := by
    calc min δ ((v - b) / (K + 1)) * K ≤ (v - b) / (K + 1) * K :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hK
      _ < v - b := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hK1]
          nlinarith
  linarith

end Limit

/-! ### The variance bound -/

section Variance

/-- **The second moment about the barycentre is at most `σ²`, given the two-sided
exponential-moment bound.**

The hypothesis `hPL` is exactly the conclusion of
`Arlib.integral_exp_mul_integral_exp_neg_le`, which is where log-concavity is used; it is
a binder here only to separate the Prékopa–Leindler input from the elementary calculus
that turns it into a variance bound, and it is discharged in the very next theorem.

The argument: let `A = ∫W > 0`, let `c = (∫tW)/A` be the barycentre (which lies in `[α,β]`
because `W` is supported there), and let `V = ∫(t−c)²W`.  For small `x > 0`,

  `A + x²V/2 − (2/9)x³R³A ≤ ∫ e^{±x(t−c)}W`,

so the product of the two exponential moments is at least the square of that quantity,
while `hPL` bounds it by `e^{σ²x²}A²`.  Taking square roots and expanding `e^{σ²x²/2}` to
second order gives `V ≤ σ²A + x·(σ⁴A/2 + (4/9)R³A)`; letting `x → 0` gives `V ≤ σ²A`. -/
theorem exists_mem_Icc_integral_sq_sub_le_of_expBound {σ α β : ℝ} (hσ : 0 < σ) (hαβ : α ≤ β)
    {W : ℝ → ℝ} (hW : Integrable W) (hW0 : ∀ t, 0 ≤ W t)
    (hsupp : ∀ t, t ∉ Set.Icc α β → W t = 0)
    (hPL : ∀ c k : ℝ,
      (∫ t, Real.exp (k * (t - c)) * W t) * (∫ t, Real.exp (-(k * (t - c))) * W t)
        ≤ Real.exp (σ ^ 2 * k ^ 2) * (∫ t, W t) ^ 2) :
    ∃ c ∈ Set.Icc α β, (∫ t, (t - c) ^ 2 * W t) ≤ σ ^ 2 * ∫ t, W t := by
  have hA0 : 0 ≤ ∫ t, W t := integral_nonneg fun t => hW0 t
  rcases eq_or_lt_of_le hA0 with hAz | hApos
  · -- the degenerate case: the weight is null
    refine ⟨α, ⟨le_refl α, hαβ⟩, ?_⟩
    have hae : W =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => hW0 t) hW).mp hAz.symm
    have hz : (fun t => (t - α) ^ 2 * W t) =ᵐ[volume] 0 := by
      filter_upwards [hae] with t ht
      simp [ht]
    rw [integral_congr_ae hz]
    simp [← hAz]
  · -- the main case
    have hIid : Integrable fun t => t * W t := by
      refine integrable_mul_of_bddOn_Icc (C := |α| + |β|) hW hW0 hsupp (by fun_prop) ?_
      intro t ht
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]
      constructor
      · linarith [neg_abs_le α, abs_nonneg β]
      · linarith [le_abs_self β, abs_nonneg α]
    have hshift : ∀ d : ℝ, (∫ t, (t - d) * W t) = (∫ t, t * W t) - d * ∫ t, W t := by
      intro d
      have heq : (fun t => (t - d) * W t) = fun t => t * W t - d * W t := by
        funext t; ring
      rw [heq, integral_sub hIid (hW.const_mul d), integral_const_mul]
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t, t * W t) / (∫ t, W t) := ⟨_, rfl⟩
    have hαc : α ≤ c := by
      have hnn : 0 ≤ ∫ t, (t - α) * W t := integral_nonneg fun t => by
        by_cases ht : t ∈ Set.Icc α β
        · exact mul_nonneg (by linarith [ht.1]) (hW0 t)
        · simp [hsupp t ht]
      rw [hshift α] at hnn
      rw [hc, le_div_iff₀ hApos]
      linarith
    have hcβ : c ≤ β := by
      have hnn : 0 ≤ ∫ t, (β - t) * W t := integral_nonneg fun t => by
        by_cases ht : t ∈ Set.Icc α β
        · exact mul_nonneg (by linarith [ht.2]) (hW0 t)
        · simp [hsupp t ht]
      have heq : (fun t => (β - t) * W t) = fun t => β * W t - t * W t := by
        funext t; ring
      rw [heq, integral_sub (hW.const_mul β) hIid, integral_const_mul] at hnn
      rw [hc, div_le_iff₀ hApos]
      linarith
    refine ⟨c, ⟨hαc, hcβ⟩, ?_⟩
    -- the barycentre kills the first moment
    have hzero : (∫ t, (t - c) * W t) = 0 := by
      rw [hshift c, hc]
      field_simp
      ring
    have hR0 : (0 : ℝ) ≤ β - α := by linarith
    have hRb : ∀ t ∈ Set.Icc α β, |t - c| ≤ β - α := by
      intro t ht
      rw [abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hV0 : 0 ≤ ∫ t, (t - c) ^ 2 * W t :=
      integral_nonneg fun t => mul_nonneg (sq_nonneg _) (hW0 t)
    -- the key estimate, valid for all small positive `x`
    have hmain : ∀ x : ℝ, 0 < x → x ≤ 1 → x * (β - α) ≤ 1 → σ ^ 2 * x ^ 2 / 2 ≤ 1 →
        (∫ t, (t - c) ^ 2 * W t) ≤ σ ^ 2 * (∫ t, W t)
          + x * (σ ^ 4 * (∫ t, W t) / 2 + 4 / 9 * (β - α) ^ 3 * (∫ t, W t)) := by
      intro x hx0 hx1 hxR hxσ
      have habsx : |x| = x := abs_of_pos hx0
      have hlow1 := le_integral_exp_mul_of_barycentre (k := x) hW hW0 hsupp hRb
        (by rw [habsx]; exact hxR) hzero
      have hlow2 := le_integral_exp_mul_of_barycentre (k := -x) hW hW0 hsupp hRb
        (by rw [abs_neg, habsx]; exact hxR) hzero
      rw [habsx] at hlow1
      simp only [abs_neg, habsx, neg_mul, neg_sq] at hlow2
      -- the lower bound is nonnegative
      have hP0 : 0 ≤ (∫ t, W t) + x ^ 2 / 2 * (∫ t, (t - c) ^ 2 * W t)
          - 2 / 9 * x ^ 3 * (β - α) ^ 3 * (∫ t, W t) := by
        have hcube : x ^ 3 * (β - α) ^ 3 ≤ 1 := by
          have : (x * (β - α)) ^ 3 ≤ 1 ^ 3 :=
            pow_le_pow_left₀ (mul_nonneg hx0.le hR0) hxR 3
          nlinarith [this]
        nlinarith [hApos, hV0, sq_nonneg x]
      -- multiply the two lower bounds
      have hprod : ((∫ t, W t) + x ^ 2 / 2 * (∫ t, (t - c) ^ 2 * W t)
            - 2 / 9 * x ^ 3 * (β - α) ^ 3 * (∫ t, W t)) ^ 2
          ≤ Real.exp (σ ^ 2 * x ^ 2) * (∫ t, W t) ^ 2 := by
        refine le_trans ?_ (hPL c x)
        rw [pow_two]
        exact mul_le_mul hlow1 hlow2 hP0 (le_trans hP0 hlow1)
      -- take square roots
      have hQ0 : 0 ≤ Real.exp (σ ^ 2 * x ^ 2 / 2) * (∫ t, W t) :=
        mul_nonneg (Real.exp_nonneg _) hA0
      have hsq : Real.exp (σ ^ 2 * x ^ 2) * (∫ t, W t) ^ 2
          = (Real.exp (σ ^ 2 * x ^ 2 / 2) * (∫ t, W t)) ^ 2 := by
        rw [mul_pow, pow_two (Real.exp (σ ^ 2 * x ^ 2 / 2)), ← Real.exp_add]
        ring_nf
      rw [hsq] at hprod
      have hroot : (∫ t, W t) + x ^ 2 / 2 * (∫ t, (t - c) ^ 2 * W t)
          - 2 / 9 * x ^ 3 * (β - α) ^ 3 * (∫ t, W t)
          ≤ Real.exp (σ ^ 2 * x ^ 2 / 2) * (∫ t, W t) := by
        nlinarith [hprod, hP0, hQ0]
      -- expand the exponential to second order
      have hexpub : Real.exp (σ ^ 2 * x ^ 2 / 2) ≤ 1 + σ ^ 2 * x ^ 2 / 2
          + (σ ^ 2 * x ^ 2 / 2) ^ 2 := exp_upper_bound_quadratic (by positivity) hxσ
      have hfinal := le_trans hroot (mul_le_mul_of_nonneg_right hexpub hA0)
      have hfinal2 : x ^ 2 / 2 * (∫ t, (t - c) ^ 2 * W t)
          ≤ σ ^ 2 * x ^ 2 / 2 * (∫ t, W t) + σ ^ 4 * x ^ 4 / 4 * (∫ t, W t)
            + 2 / 9 * x ^ 3 * (β - α) ^ 3 * (∫ t, W t) := by linarith only [hfinal]
      have hxle : x ^ 4 ≤ x ^ 3 := by
        have hx3 : (0 : ℝ) ≤ x ^ 3 := by positivity
        calc x ^ 4 = x ^ 3 * x := by ring
          _ ≤ x ^ 3 * 1 := mul_le_mul_of_nonneg_left hx1 hx3
          _ = x ^ 3 := by ring
      have hprod2 : σ ^ 4 * x ^ 4 / 4 * (∫ t, W t) ≤ σ ^ 4 * x ^ 3 / 4 * (∫ t, W t) := by
        have h1 : (0 : ℝ) ≤ σ ^ 4 / 4 * (∫ t, W t) := mul_nonneg (by positivity) hA0
        calc σ ^ 4 * x ^ 4 / 4 * (∫ t, W t) = σ ^ 4 / 4 * (∫ t, W t) * x ^ 4 := by ring
          _ ≤ σ ^ 4 / 4 * (∫ t, W t) * x ^ 3 := mul_le_mul_of_nonneg_left hxle h1
          _ = σ ^ 4 * x ^ 3 / 4 * (∫ t, W t) := by ring
      have hposx : (0 : ℝ) < x ^ 2 / 2 := by positivity
      refine le_of_mul_le_mul_left ?_ hposx
      linarith only [hfinal2, hprod2]
    -- let `x → 0`
    refine le_of_forall_pos_small (K := σ ^ 4 * (∫ t, W t) / 2
      + 4 / 9 * (β - α) ^ 3 * (∫ t, W t))
      (δ := min 1 (min (1 / (β - α + 1)) (1 / (σ + 1)))) ?_ ?_ ?_
    · have h1 : 0 ≤ σ ^ 4 * (∫ t, W t) / 2 := by
        apply div_nonneg _ (by norm_num)
        exact mul_nonneg (by positivity) hA0
      have h2 : 0 ≤ 4 / 9 * (β - α) ^ 3 * (∫ t, W t) :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hR0 3)) hA0
      linarith
    · exact lt_min one_pos (lt_min (by positivity) (by positivity))
    · intro x hx0 hxδ
      have hx1 : x ≤ 1 := le_trans hxδ (min_le_left _ _)
      have hxa : x ≤ 1 / (β - α + 1) :=
        le_trans hxδ (le_trans (min_le_right _ _) (min_le_left _ _))
      have hxb : x ≤ 1 / (σ + 1) :=
        le_trans hxδ (le_trans (min_le_right _ _) (min_le_right _ _))
      have hxR : x * (β - α) ≤ 1 := by
        have hpos : (0 : ℝ) < β - α + 1 := by linarith
        rw [le_div_iff₀ hpos] at hxa
        nlinarith
      have hxσ : σ ^ 2 * x ^ 2 / 2 ≤ 1 := by
        have hpos : (0 : ℝ) < σ + 1 := by linarith
        rw [le_div_iff₀ hpos] at hxb
        have h1 : σ * x ≤ 1 := by nlinarith [hx0.le, hσ.le]
        have h2 : (0 : ℝ) ≤ σ * x := mul_nonneg hσ.le hx0.le
        nlinarith [h1, h2]
      exact hmain x hx0 hx1 hxR hxσ

end Variance

/-! ### The theorem -/

section Main

/-- **One-dimensional Brascamp–Lieb for a log-concave function times a Gaussian.**

Let `γ(t) = exp(−(t − t₀)²/(2σ²))` with `σ > 0`, and let `F ≥ 0` be log-concave on `[α,β]`
with `F·γ` interval-integrable there.  Then there is a point `c ∈ [α,β]` — the barycentre
of the measure with density `F·γ` — with

  `∫_α^β (t − c)² F(t)γ(t) dt ≤ σ² ∫_α^β F(t)γ(t) dt`,

i.e. the probability measure proportional to `F·γ` on `[α,β]` has variance at most `σ²`.

This is the `α = 2` case of Brascamp–Lieb (`1409.6011/vol3_journal.tex:407`) in the form
Cousins–Vempala use at `vol3_journal.tex:506`, and it is exactly the hypothesis `hvar` of
`Arlib.oneDim_isoperimetry_gaussianFactor`
(`Arlib/Convexity/ConcaveProfileIso.lean:407`).

**No differentiability of `F` is used, or available.**  The textbook proof writes the
density as `e^{−V}` with `V'' ≥ 1/σ²` and integrates by parts; a log-concave `F` need not
be differentiable, or even continuous at the endpoints of its support.  The route here is:

1. extend `F` by zero to a log-concave `G` on all of `ℝ`
   (`Arlib.isLogConcave_indicator_of_logConcaveOn`) — this is also what makes `G`
   measurable (`Arlib.measurable_of_isLogConcave`), no hypothesis needed;
2. Prékopa–Leindler at `lam = 1/2` bounds the two-sided exponential moments,
   `(∫e^{k(t−c)}W)(∫e^{−k(t−c)}W) ≤ e^{σ²k²}(∫W)²`
   (`Arlib.integral_exp_mul_integral_exp_neg_le`);
3. a second-order expansion of `e^{±k(t−c)}` about the barycentre, where the first moment
   vanishes, turns this into `V ≤ σ²A + O(k)`, and `k → 0` finishes
   (`Arlib.exists_mem_Icc_integral_sq_sub_le_of_expBound`).

**On the printed statement.**  Cousins–Vempala state Brascamp–Lieb for the *standard*
Gaussian and for all `α ≥ 1`; what is proved here is the `α = 2` case at general `σ`,
with the constant `σ²` (not `1`), which is what their own rescaling `x = y/σ` produces and
what `thm:iso` actually consumes.  The `α ≥ 1` range is not verified here and is *not*
implied by the `α = 2` case: Jensen gives only `E|Y|^α ≤ σ^α`, whereas the printed claim
is the strictly smaller `σ^α·E|N(0,1)|^α` (e.g. `√(2/π)·σ` at `α = 1`).  Nothing in this
repository depends on `α ≠ 2`.

**Sharpness.**  `σ²` cannot be lowered: with `F ≡ 1` and `[α,β] = [−L,L]`, the measure is a
Gaussian truncated to `[−L,L]`, whose variance tends to `σ²` as `L → ∞`.  On any bounded
interval the inequality is therefore strict, which is why the statement is an inequality
and not an identity. -/
theorem brascampLieb_oneDim {σ t₀ α β : ℝ} (hσ : 0 < σ) (hαβ : α ≤ β) {F : ℝ → ℝ}
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β) :
    ∃ c ∈ Set.Icc α β,
      (∫ t in α..β, (t - c) ^ 2 * (F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
        ≤ σ ^ 2 * ∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) := by
  -- extend `F` by zero
  have hG : IsLogConcave (Set.indicator (Set.Icc α β) F) :=
    isLogConcave_indicator_of_logConcaveOn hFc hF0
  have hG0 : ∀ t, 0 ≤ Set.indicator (Set.Icc α β) F t :=
    fun t => Set.indicator_nonneg (fun y hy => hF0 y hy) t
  have hW0 : ∀ t, 0 ≤ Set.indicator (Set.Icc α β) F t
      * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) :=
    fun t => mul_nonneg (hG0 t) (Real.exp_nonneg _)
  have hWsupp : ∀ t, t ∉ Set.Icc α β →
      Set.indicator (Set.Icc α β) F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) = 0 := by
    intro t ht
    rw [Set.indicator_of_notMem ht, zero_mul]
  -- the weight is the zero extension of `F·γ`
  have hW_eq : (fun t => Set.indicator (Set.Icc α β) F t
        * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))
      = Set.indicator (Set.Icc α β)
        (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
    funext t
    by_cases ht : t ∈ Set.Icc α β
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  have hconv : ∀ g : ℝ → ℝ,
      (∫ t, Set.indicator (Set.Icc α β) g t) = ∫ t in α..β, g t := by
    intro g
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hαβ]
  have hWint : Integrable fun t => Set.indicator (Set.Icc α β) F t
      * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) := by
    rw [hW_eq]
    exact IntegrableOn.integrable_indicator
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hint) measurableSet_Icc
  -- the exponential factors are bounded on `[α,β]`
  have hexpint : ∀ c k : ℝ, Integrable fun t => Real.exp (k * (t - c))
      * (Set.indicator (Set.Icc α β) F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
    intro c k
    refine integrable_mul_of_bddOn_Icc (C := Real.exp (|k| * (|α - c| + |β - c|)))
      hWint hW0 hWsupp (by fun_prop) ?_
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    rw [abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
    have habs : |t - c| ≤ |α - c| + |β - c| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le (α - c), abs_nonneg (β - c)],
        by linarith [le_abs_self (β - c), abs_nonneg (α - c)]⟩
    calc k * (t - c) ≤ |k * (t - c)| := le_abs_self _
      _ = |k| * |t - c| := abs_mul _ _
      _ ≤ |k| * (|α - c| + |β - c|) := mul_le_mul_of_nonneg_left habs (abs_nonneg k)
  have hPL : ∀ c k : ℝ,
      (∫ t, Real.exp (k * (t - c)) * (Set.indicator (Set.Icc α β) F t
          * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
        * (∫ t, Real.exp (-(k * (t - c))) * (Set.indicator (Set.Icc α β) F t
          * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ Real.exp (σ ^ 2 * k ^ 2) * (∫ t, Set.indicator (Set.Icc α β) F t
          * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) ^ 2 := by
    intro c k
    refine integral_exp_mul_integral_exp_neg_le hσ hG hG0 hWint (hexpint c k) ?_
    simpa only [neg_mul] using hexpint c (-k)
  obtain ⟨c, hcmem, hbound⟩ :=
    exists_mem_Icc_integral_sq_sub_le_of_expBound hσ hαβ hWint hW0 hWsupp hPL
  refine ⟨c, hcmem, ?_⟩
  have hV_eq : (fun t => (t - c) ^ 2 * (Set.indicator (Set.Icc α β) F t
        * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      = Set.indicator (Set.Icc α β)
        (fun t => (t - c) ^ 2 * (F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) := by
    funext t
    by_cases ht : t ∈ Set.Icc α β
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul, mul_zero]
  rw [hV_eq, hconv] at hbound
  rw [hW_eq, hconv] at hbound
  exact hbound

end Main

/-! ### Non-vacuity -/

section Witness

/-- **Non-vacuity, constant weight.**  Every hypothesis of `Arlib.brascampLieb_oneDim`
holds for `F ≡ 1` on `[−1,1]` with `σ = 1`, `t₀ = 0`, and the total mass is strictly
positive — so the conclusion is a genuine constraint on a genuine probability measure (the
standard Gaussian truncated to `[−1,1]`), not `0 ≤ 0`.

This is also the case in which the constant `σ²` is asymptotically attained: replacing
`[−1,1]` by `[−L,L]` and letting `L → ∞` drives the variance of the truncated Gaussian up
to `σ² = 1`. -/
theorem brascampLieb_oneDim_uniform_witness :
    (0 < ∫ t in (-1 : ℝ)..1, (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))) ∧
      ∃ c ∈ Set.Icc (-1 : ℝ) 1,
        (∫ t in (-1 : ℝ)..1,
            (t - c) ^ 2 * ((1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))))
          ≤ (1 : ℝ) ^ 2 * ∫ t in (-1 : ℝ)..1,
            (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
  have hcont : Continuous fun t : ℝ =>
      (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ => (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))) volume (-1) 1 :=
    hcont.intervalIntegrable (-1) 1
  refine ⟨intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => by positivity)
    (by norm_num), ?_⟩
  exact brascampLieb_oneDim (F := fun _ => (1 : ℝ)) one_pos (by norm_num)
    (fun _ _ => zero_le_one) (logConcaveOn_const (convex_Icc _ _) zero_le_one) hint

/-- **Non-vacuity, with a genuinely non-constant log-concave weight.**  Same statement for
`F(t) = e^{−|t|}`, which is log-concave (`−|t|` is concave) and manifestly not constant, so
the theorem is not secretly a statement about Gaussians alone. -/
theorem brascampLieb_oneDim_exp_witness :
    (0 < ∫ t in (-1 : ℝ)..1,
        Real.exp (-|t|) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))) ∧
      ∃ c ∈ Set.Icc (-1 : ℝ) 1,
        (∫ t in (-1 : ℝ)..1,
            (t - c) ^ 2 * (Real.exp (-|t|) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))))
          ≤ (1 : ℝ) ^ 2 * ∫ t in (-1 : ℝ)..1,
            Real.exp (-|t|) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
  have habs : ConvexOn ℝ (Set.univ : Set ℝ) fun t : ℝ => |t| := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = a * |x| + b * |y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hconc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) fun t : ℝ => -|t| :=
    (habs.neg).subset (Set.subset_univ _) (convex_Icc _ _)
  have hcont : Continuous fun t : ℝ =>
      Real.exp (-|t|) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.exp (-|t|) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)))
      volume (-1) 1 := hcont.intervalIntegrable (-1) 1
  refine ⟨intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => by positivity)
    (by norm_num), ?_⟩
  exact brascampLieb_oneDim (F := fun t => Real.exp (-|t|)) one_pos (by norm_num)
    (fun _ _ => (Real.exp_pos _).le) (logConcaveOn_exp hconc) hint

end Witness

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.convex_setOf_lt_of_isLogConcave
#print axioms Arlib.measurable_of_isLogConcave
#print axioms Arlib.isLogConcave_indicator_of_logConcaveOn
#print axioms Arlib.integral_exp_mul_integral_exp_neg_le
#print axioms Arlib.exp_lower_bound_cubic
#print axioms Arlib.exp_upper_bound_quadratic
#print axioms Arlib.integrable_mul_of_bddOn_Icc
#print axioms Arlib.le_integral_exp_mul_of_barycentre
#print axioms Arlib.le_of_forall_pos_small
#print axioms Arlib.exists_mem_Icc_integral_sq_sub_le_of_expBound
#print axioms Arlib.brascampLieb_oneDim
#print axioms Arlib.brascampLieb_oneDim_uniform_witness
#print axioms Arlib.brascampLieb_oneDim_exp_witness
