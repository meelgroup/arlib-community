/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.HitAndRunStep
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatio
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.ChordCompare
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.SphereCoord
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.TV
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.1 of Lovász–Vempala: two nearby points have overlapping one-step laws

This file proves the key lemma connecting geometry to probability for the hit-and-run walk:
if `u` and `v` are close *both* in the cross-ratio distance `d_K` *and* in the Euclidean
distance measured against the median step `F(u)`, then the two one-step distributions
`P_u`, `P_v` are **not** almost disjoint — their total variation distance is bounded away
from `1`.

Lovász–Vempala, *Hit-and-Run from a Corner* (SIAM J. Comput. 35 (2006) 985–1005), state it
as **Lemma 4.1** and attribute it, without proof, to

> L. Lovász, *Hit-and-run mixes fast*, Math. Programming Ser. A **86** (1999) 443–461,

where it is **Lemma 8** (p. 451–454).  Everything below follows that proof.  The source used
here is the author's PDF at `https://faculty.washington.edu/harin/L1.pdf`; the text was
re-extracted with the MathTime/`cmsy` font encodings resolved glyph-by-glyph, so the
relation symbols (`≤`, `≥`, `∈`, `=`, `+`, `[`, `]`) are read from the font's own encoding
vector and not guessed — the failure mode that produced a spurious "bug" report earlier in
this development.

## The shape of the argument

Fix a measurable `A ⊆ K`.  Lovász partitions `A` into four pieces and bounds `P_u` on the
first three:

* `A₁ = {x ∈ A : |x − u| < F(u)}`, with `P_u(A₁) ≤ 1/8` — this is *exactly* equation (4),
  the defining property of `F`;
* `A₂ = {x ∈ A : |⟨x − u, u − v⟩| > n^{-1/2}|x − u||u − v|}`, the steps whose direction is
  **not** almost orthogonal to `u − v`;
* `A₃ = {x ∈ A : |x − u| < (1/3)|u − a(u,x)|}`, the steps that stop close to `u` relative to
  the chord — here the **two-sided** version, see below;
* `S = A \ A₁ \ A₂ \ A₃`.

On `S` the two densities of equation (5) are comparable, and one gets `P_v(S) ≥ c·P_u(S)`.
Summing, `P_u(A) − P_v(A) ≤ P_u(A) − c·P_u(S) ≤ 1 − c·(1 − q)` where `q` bounds
`P_u(A₁ ∪ A₂ ∪ A₃)`.

## The printed `A₃` is one-sided, and with it the lemma is false

Lovász's `A₃` excludes only steps with `|u − a(u,x)| > 3|x − u|` at **one** endpoint
`a(u,x)` of the chord through `u` and `x`.  `Arlib/Convexity/ChordCompare.lean` shows by
explicit counterexample (its module docstring, `n = 2`) that the chord comparison
`ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)` **does not follow** from that single bound, for either
reading of `a(u,x)`: every antecedent can be met while the conclusion fails, `101.0` against
`35.06`.  Earlier versions of this file carried the printed one-sided hypothesis inline, and
were therefore vacuous where it mattered.

What is true, and is proved there as `Arlib.chordDiff_le_two_mul`, is the comparison under
**both** chord bounds.  So `A₃` is taken here as the union

    A₃ = {x : chordLow K u x < −3} ∪ {x : 3 < chordHigh K u x},

i.e. `max |u − a| > 3|x − u|` over the two endpoints `a` of that chord.  Its mass is
**`1/2`**, not `1/3` (`Arlib.MarkovChains.hitAndRun_chord_bad_le`; each half is separately
`≤ 1/3`, and `1/2` is sharp — attained on a chord split by `u` in ratio `1 : 3`).  See
**Constants** below for what this costs.

## What is proved here, and what is assumed

**Proved, with no extra hypothesis:**

* `Arlib.MarkovChains.norm_sub_le_of_almost_orthogonal` — the paper's (10),
  `|x − v| ≤ (1 + 4/n)|x − u|`, from (7) and (8).  Pure algebra in the inner product space.
* `Arlib.MarkovChains.hitAndRunDensity_ge_of_chordLength_le` — **the chord-density
  comparison, the crux**: from `ℓ(v,x)·|x − u| ≤ Λ·|x − v|·ℓ(u,x)` and
  `|x − v| ≤ N·|x − u|`, the density of equation (5) satisfies
  `(ΛNⁿ)⁻¹·hitAndRunDensity K u x ≤ hitAndRunDensity K v x`.  The paper's factor is `Λ = 2`
  (`hitAndRunDensity_ge_of_chordLength_le_two`); it is left as a parameter here because
  raising it shrinks `A₃`, which is where the budget is now tight (see **Constants**).
* `Arlib.MarkovChains.mul_hitAndRunProposal_le` — integrating that comparison against
  equation (5): `c·P_u(S) ≤ P_v(S)`.
* `Arlib.MarkovChains.pow_one_add_four_div_le_exp`, `two_mul_exp_four_lt` — `(1 + 4/n)ⁿ ≤ e⁴`
  and `2e⁴ < 120`, the paper's constant.
* `Arlib.MarkovChains.hitAndRun_ball_medianStep_le` — `P_u(A₁) ≤ 1/8`, from
  `Arlib.hitAndRun_closedBall_le_of_lt_medianStep` by exhausting the open ball.
* `Arlib.MarkovChains.tvLe_of_overlap` — the assembly: a setwise lower bound `c·μ ≤ ν` off a
  set of `μ`-mass `≤ q` gives `TVLe μ ν (1 − c(1 − q))`.
* `Arlib.MarkovChains.tvLe_hitAndRun_of_overlap` — the two combined, for the walk.

**Also consumed, from elsewhere in this repository, and likewise proved:**

* `Arlib.MarkovChains.chordLength_mul_norm_le` (`Arlib/Convexity/ChordCompare.lean`) — the
  chord comparison `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)`, under **both** chord bounds.  Lovász
  proves it by Menelaus' theorem; ChordCompare replaces Menelaus by two explicit convex
  combinations, so no projective geometry is needed.  It used to be an inline hypothesis
  `hchord` of the capstone; **it is now discharged**, and no `hchord` binder survives.
* `Arlib.MarkovChains.hitAndRun_chord_bad_le`, `measurableSet_chordLow_lt`,
  `measurableSet_chordHigh_gt` (same file) — `P_u(A₃) ≤ 1/2` and the measurability of `A₃`.
  These used to be the inline hypotheses `hA3`, `hA3m`; **both are now discharged**, and no
  such binder survives.

**Assumed, as the one remaining inline hypothesis of the capstone `tvLe_hitAndRun_lemma41`**
(no named `Prop` is introduced for it):

* `hcap` — the spherical-cap estimate `P_u(A₂) ≤ q₂`.  This is the paper's "it takes a
  standard computation"; formally it is `σ_{n-1}{θ : |⟨θ, ŵ⟩| > n^{-1/2}} ≤ q₂`, an estimate
  on the distribution of one coordinate of a uniform point of `Sⁿ⁻¹`.
  `Arlib/MarkovChains/Continuous/SphereCoord.lean` supplies the rotation invariance of
  `Measure.toSphere` and reduces `hcap` to a statement about the sphere alone
  (`hitAndRun_almostOrthogonal_le`), and discharges it outright at `q₂ = 1 − 1/n`
  (`hitAndRun_almostOrthogonal_le_one_sub_inv`) — but `1 − 1/n` is far too weak to be useful
  beyond `n = 1`.  What is missing is the density `(1 − t²)^{(n−3)/2}` of `⟨θ, ŵ⟩` together
  with a uniform-in-`n` estimate of its tail at the *root-mean-square* threshold `n^{-1/2}`;
  Mathlib v4.32 has neither.  See **Constants**: the paper's value `1/6` for `q₂` is wrong.

The capstone therefore proves the implication Lemma 4.1 rests on, with its one remaining
geometric input named and visible in its type.  Nothing in this file is a definition that
asserts an unproved identity.

## Constants: the printed `1/6` is wrong, and `1 − 1/500` does **not** survive

Lovász's proof bounds the three bad pieces by `1/8`, `1/6` and `1/3`, rounds the sum up to
`3/4`, rounds `2e⁴ = 109.19…` up to `120`, and concludes `1 − 1/500`.  Two of the three
bounds are wrong, in the same direction, and together they cost the printed constant.

**The `1/6` is not correct.**  The paper defines `C` as the cap `{θ ∈ Sⁿ⁻¹ : ⟨θ, u − v⟩ ≥
n^{-1/2}|u − v|}` and says the probability in question is "the ratio between the surface of
`C` and the surface of the half-sphere", i.e. `2·σ(C) = σ{θ : |⟨θ, ŵ⟩| ≥ n^{-1/2}}`.  That
quantity is `1/2` at `n = 2`, `1 − 3^{-1/2} = 0.4226…` at `n = 3`, and decreases to
`2(1 − Φ(1)) = 0.31731…` as `n → ∞`.  It is **never** below `1/6 = 0.1666…`; the printed
value is off by about a factor of two, which is exactly the factor between a sphere and a
half-sphere.  The one-sided reading `σ(C)` does not rescue it either: `σ(C)` exceeds `1/6`
for every `n ≤ 15` (`0.16714…` at `n = 15`) and only drops below it from `n = 16` on
(`0.16659…`), so `1/6` is not a valid bound under *either* reading.

**The `1/3` is not correct either** — not because the printed bound on the printed `A₃` is
false (it is true: `hitAndRun_chordLow_lt_le`), but because that `A₃` is too small to
support the chord comparison, as shown above.  The `A₃` that does support it has mass `1/2`,
and `1/2` is sharp.

**Consequently the printed `1 − 1/500` fails.**  With `q = 1/8 + q₂(n) + 1/2` the proof
yields `1 − c(1 − q)` with the sharp `c = (2(1 + 4/n)ⁿ)⁻¹`, and `1/(c(1 − q))` is:

| `n`                | 2, 3, 4 | 5      | 6    | 8    | 16   | `n → ∞` |
|--------------------|---------|--------|------|------|------|---------|
| `q₂(n)`            | ≥ 0.391 | 0.3739 | 0.363| 0.351| 0.333| 0.31731 |
| `1/(c(1 − q))`     | —       | 34386  | 3638 | 2102 | 1699 | 1892.8… |

For `2 ≤ n ≤ 4` one has `q ≥ 1`: the lemma yields nothing at all.  (At `n = 1` the cap set is
empty, so `q₂ = 0` and the lemma gives `1 − 3/80`; that is
`tvLe_hitAndRun_lemma41_unconditional`.)  For `n ≥ 5` it yields a real
bound, but the constant is `1892.8…` in the limit, not `500` — worse by a factor of `3.8`,
and worse still (`34386`) at `n = 5`.  **No rounding recovers `1 − 1/500`.**  Before the
`A₃` correction the same computation gave `432` at `n = 2` and `486.7…` as `n → ∞`, i.e.
`1 − 1/500` held with `2.7%` of slack; that slack is gone, and it was the printed `1/3` that
was paying for it.

Retuning the factor `2` of the chord comparison is what would buy it back, and it is why
`hitAndRunDensity_ge_of_chordLength_le` is stated at a general `Λ` here: a larger `Λ` shrinks
`A₃` faster than it shrinks `c`.  `Arlib/Convexity/ChordCompare.lean` reports that at
`Λ = 8` the confinement relaxes to `ρ ≤ 9 − 8/Λ = 8`, `μ ≤ 8 − 9/Λ = 6.875` and the bad set
drops to mass `≈ 0.236`, giving `q ≈ 0.861` even at the crude `q₂ = 1/2` and a
**dimension-free** `1 − 1/3143`.  That still does not reach `1 − 1/500`; carrying it out
needs `Λ`-parametric versions of `chordDiff_le_two_mul` and `volume_inter_scale_union_le`,
both of which hard-code `2` and `3` in `ChordCompare.lean`, so it is not done here.

This file hard-codes none of these numbers.  `tvLe_hitAndRun_lemma41` is parametric in `q₂`
and returns the sharp `1 − (1 − q)/(2(1 + 4/n)ⁿ)` with `q = 1/8 + q₂ + 1/2`, so a caller who
can prove a cap bound gets whatever constant that bound supports.

**The corollary `tvLe_hitAndRun_lemma41_of_half` has been deleted.**  It recorded the
dimension-free instance `q₂ = 1/2`, concluding `1 − 1/2880`.  With `q = 1/8 + 1/2 + 1/2 =
9/8 > 1` the budget is exhausted and `1 − c(1 − q) > 1`: the conclusion `1 − 1/2880` is no
longer derivable, and keeping the corollary would have meant keeping a statement whose
hypotheses cannot deliver it.  **The figure `1 − 1/2880` is lost**, and with it every
dimension-free constant this file can currently offer: there is no dimension-free `q₂ < 3/8`,
since `q₂(2) = 1/2` and `q₂(3) = 0.4226…`.  What replaces it is
`tvLe_hitAndRun_lemma41_of_le_three_eighths`, still parametric in `q₂` but rounded to
`1 − (3/8 − q₂)/120`, and `tvLe_hitAndRun_lemma41_unconditional`, the only statement here
with **no** unproved hypothesis at all — which, as the table shows, is non-trivial only at
`n = 1`.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal RealInnerProductSpace

namespace Arlib.MarkovChains

open Arlib

variable {n : ℕ}

/-! ## The Euclidean estimate (10) -/

/-- **The paper's (10).**  If the step `x − u` is long compared with `u − v` (the paper's
(7), here `√n·|u − v| ≤ 2|x − u|`) and is almost orthogonal to `u − v` (the paper's (8),
here `√n·|⟨x − u, u − v⟩| ≤ |x − u|·|u − v|`), then `|x − v| ≤ (1 + 4/n)|x − u|`.

The two hypotheses give `|u − v|² ≤ (4/n)|x − u|²` and `2⟨x − u, u − v⟩ ≤ (4/n)|x − u|²`,
whence `|x − v|² ≤ (1 + 8/n)|x − u|² ≤ (1 + 4/n)²|x − u|²`. -/
theorem norm_sub_le_of_almost_orthogonal (hn : n ≠ 0)
    (u v x : EuclideanSpace ℝ (Fin n))
    (h7 : Real.sqrt n * ‖u - v‖ ≤ 2 * ‖x - u‖)
    (h8 : Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖) :
    ‖x - v‖ ≤ (1 + 4 / (n : ℝ)) * ‖x - u‖ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hxu : (0 : ℝ) ≤ ‖x - u‖ := norm_nonneg _
  have huv : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hxv : (0 : ℝ) ≤ ‖x - v‖ := norm_nonneg _
  have hdecomp : x - v = (x - u) + (u - v) := by abel
  have hsq : ‖x - v‖ ^ 2
      = ‖x - u‖ ^ 2 + 2 * ⟪x - u, u - v⟫ + ‖u - v‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real]
  -- `2⟨x−u,u−v⟩ ≤ (4/n)|x−u|²`
  have hinner : ⟪x - u, u - v⟫ ≤ |⟪x - u, u - v⟫| := le_abs_self _
  have habs : Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|)
      ≤ 2 * ‖x - u‖ * ‖x - u‖ := by
    calc Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|)
        ≤ Real.sqrt n * (‖x - u‖ * ‖u - v‖) := by
          exact mul_le_mul_of_nonneg_left h8 hspos.le
      _ = ‖x - u‖ * (Real.sqrt n * ‖u - v‖) := by ring
      _ ≤ ‖x - u‖ * (2 * ‖x - u‖) := mul_le_mul_of_nonneg_left h7 hxu
      _ = 2 * ‖x - u‖ * ‖x - u‖ := by ring
  have hcross : (n : ℝ) * |⟪x - u, u - v⟫| ≤ 2 * ‖x - u‖ * ‖x - u‖ := by
    calc (n : ℝ) * |⟪x - u, u - v⟫|
        = Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|) := by rw [← mul_assoc, hs]
      _ ≤ _ := habs
  -- `|u−v|² ≤ (4/n)|x−u|²`
  have hnormsq : (n : ℝ) * ‖u - v‖ ^ 2 ≤ 4 * ‖x - u‖ ^ 2 := by
    have hkey : (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
        ≤ (2 * ‖x - u‖) * (2 * ‖x - u‖) :=
      mul_le_mul h7 h7 (by positivity) (by positivity)
    have hexp : (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
        = (n : ℝ) * ‖u - v‖ ^ 2 := by
      rw [show (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
          = (Real.sqrt n * Real.sqrt n) * ‖u - v‖ ^ 2 by ring, hs]
    have hexp2 : (2 * ‖x - u‖) * (2 * ‖x - u‖) = 4 * ‖x - u‖ ^ 2 := by ring
    linarith [hkey, hexp, hexp2]
  -- put the pieces together
  have hkey : ‖x - v‖ ^ 2 ≤ ((1 + 4 / (n : ℝ)) * ‖x - u‖) ^ 2 := by
    set d : ℝ := 4 / (n : ℝ) with hd
    set X : ℝ := ‖x - u‖ ^ 2 with hX
    have h1 : 2 * ⟪x - u, u - v⟫ ≤ d * X := by
      rw [hd, hX, div_mul_eq_mul_div, le_div_iff₀ hnR]
      nlinarith [hcross, mul_le_mul_of_nonneg_left hinner hnR.le]
    have h2 : ‖u - v‖ ^ 2 ≤ d * X := by
      rw [hd, hX, div_mul_eq_mul_div, le_div_iff₀ hnR]
      nlinarith [hnormsq]
    have hexp : ((1 + d) * ‖x - u‖) ^ 2 = X + 2 * (d * X) + d ^ 2 * X := by
      simp only [hX]; ring
    have hpos : 0 ≤ d ^ 2 * X := by rw [hX]; positivity
    rw [hsq, hexp]
    linarith
  nlinarith [hkey, hxv, mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 4 / (n : ℝ)) hxu]

/-! ## `(1 + 4/n)ⁿ ≤ e⁴` -/

/-- `(1 + 4/n)ⁿ ≤ e⁴` for every `n`. -/
theorem pow_one_add_four_div_le_exp (n : ℕ) :
    (1 + 4 / (n : ℝ)) ^ n ≤ Real.exp 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    nlinarith [Real.add_one_le_exp (4 : ℝ)]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (1 + 4 / (n : ℝ)) ≤ Real.exp (4 / (n : ℝ)) := by
      have := Real.add_one_le_exp (4 / (n : ℝ))
      linarith
    calc (1 + 4 / (n : ℝ)) ^ n ≤ (Real.exp (4 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((n : ℝ) * (4 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
      _ = Real.exp 4 := by rw [mul_div_cancel₀ _ hnR.ne']

/-- `2e⁴ < 120` — the paper's rounding of `2e⁴ = 109.19…`. -/
theorem two_mul_exp_four_lt : 2 * Real.exp 4 < 120 := by
  have h : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
    exact pow_lt_pow_left₀ h1 h0.le (by norm_num)
  rw [h]
  nlinarith [this]

/-- `(2(1 + 4/n)ⁿ)⁻¹ ≥ 1/120`: the paper's constant `1/120` is a valid, if lossy,
substitute for the sharp `(2(1 + 4/n)ⁿ)⁻¹`. -/
theorem one_div_le_inv_two_mul_pow (n : ℕ) :
    (1 : ℝ) / 120 ≤ 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) := by
  have hpos : (0 : ℝ) < (1 + 4 / (n : ℝ)) ^ n := by positivity
  have h := pow_one_add_four_div_le_exp n
  have h2 : 2 * (1 + 4 / (n : ℝ)) ^ n < 120 := by
    nlinarith [two_mul_exp_four_lt]
  exact one_div_le_one_div_of_le (by positivity) h2.le

/-! ## The chord-density comparison — the crux -/

/-- **The one-step density comparison of Lovász's proof.**

Given the two pointwise facts the paper establishes on `S`,

* the chord bound `ℓ(v,x)·|x − u| ≤ Λ·|x − v|·ℓ(u,x)` (Menelaus, `hchord`), and
* the norm bound `|x − v| ≤ N·|x − u|` (the paper's (10), `hnorm`),

the integrand of equation (5) at `v` dominates `(ΛNⁿ)⁻¹` times the integrand at `u`.

The paper's factor is `Λ = 2` (`hitAndRunDensity_ge_of_chordLength_le_two`).  It is left as
a parameter because the two places it enters the final constant pull in opposite directions:
a larger `Λ` weakens `c = (ΛNⁿ)⁻¹` linearly but relaxes the chord confinement that defines
`A₃`, whose mass falls off faster — see the module docstring.

No convexity, measurability or boundedness is used: this is arithmetic in `ℝ≥0∞` on the
closed form `hitAndRunDensity K u x = (ℓ(u,x)·|x − u|^{n−1})⁻¹`. -/
theorem hitAndRunDensity_ge_of_chordLength_le (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} {u v x : EuclideanSpace ℝ (Fin n)}
    (hxu : x ≠ u) {N L : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hnorm : ‖x - v‖ ≤ N * ‖x - u‖)
    (hchord : chordLength K v x * ENNReal.ofReal ‖x - u‖
      ≤ ENNReal.ofReal L * (ENNReal.ofReal ‖x - v‖ * chordLength K u x)) :
    (ENNReal.ofReal (L * N ^ n))⁻¹ * hitAndRunDensity K u x ≤ hitAndRunDensity K v x := by
  have hxu0 : (0 : ℝ) < ‖x - u‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hxu
  have hcpos : (0 : ℝ) < L * N ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (L * N ^ n) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hcpos
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set A : ℝ≥0∞ := chordLength K u x * ENNReal.ofReal (‖x - u‖ ^ (n - 1)) with hA
  set B : ℝ≥0∞ := chordLength K v x * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) with hB
  -- the key inequality `B ≤ c * A`
  have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
  have hpow : ‖x - v‖ * ‖x - v‖ ^ (n - 1) = ‖x - v‖ ^ n := by
    rw [mul_comm, ← pow_succ, hn1]
  have hpowu : ‖x - u‖ ^ (n - 1) * ‖x - u‖ = ‖x - u‖ ^ n := by
    rw [← pow_succ, hn1]
  have hmain : B * ENNReal.ofReal ‖x - u‖ ≤ c * A * ENNReal.ofReal ‖x - u‖ := by
    have step1 : B * ENNReal.ofReal ‖x - u‖
        = (chordLength K v x * ENNReal.ofReal ‖x - u‖)
            * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) := by
      rw [hB]; ring
    have step2 : (chordLength K v x * ENNReal.ofReal ‖x - u‖)
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        ≤ (ENNReal.ofReal L * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) :=
      mul_le_mul' hchord le_rfl
    have hprod : ENNReal.ofReal ‖x - v‖ * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        = ENNReal.ofReal (‖x - v‖ ^ n) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _), hpow]
    have step3 : (ENNReal.ofReal L * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        = ENNReal.ofReal L * chordLength K u x * ENNReal.ofReal (‖x - v‖ ^ n) := by
      calc (ENNReal.ofReal L * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
            * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
          = ENNReal.ofReal L * chordLength K u x
              * (ENNReal.ofReal ‖x - v‖ * ENNReal.ofReal (‖x - v‖ ^ (n - 1))) := by ring
        _ = _ := by rw [hprod]
    have step4 : ENNReal.ofReal (‖x - v‖ ^ n) ≤ ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖x - v‖ ^ n ≤ (N * ‖x - u‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) hnorm n
        _ = N ^ n * ‖x - u‖ ^ n := by rw [mul_pow]
    have hsplit1 : ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n)
        = ENNReal.ofReal (N ^ n) * (ENNReal.ofReal (‖x - u‖ ^ (n - 1))
            * ENNReal.ofReal ‖x - u‖) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖x - u‖ ^ (n - 1)), hpowu,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ N ^ n)]
    have hsplit2 : c = ENNReal.ofReal L * ENNReal.ofReal (N ^ n) := by
      rw [hc, ENNReal.ofReal_mul hL.le]
    have step5 : ENNReal.ofReal L * chordLength K u x
          * ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n)
        = c * A * ENNReal.ofReal ‖x - u‖ := by
      rw [hsplit1, hA, hsplit2]
      ring
    calc B * ENNReal.ofReal ‖x - u‖ = _ := step1
      _ ≤ _ := step2
      _ = ENNReal.ofReal L * chordLength K u x * ENNReal.ofReal (‖x - v‖ ^ n) := step3
      _ ≤ ENNReal.ofReal L * chordLength K u x
            * ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n) := mul_le_mul' le_rfl step4
      _ = _ := step5
  have hne : ENNReal.ofReal ‖x - u‖ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hxu0
  have hBA : B ≤ c * A :=
    (ENNReal.mul_le_mul_iff_left hne ENNReal.ofReal_ne_top).1 hmain
  -- invert
  have : (c * A)⁻¹ ≤ B⁻¹ := ENNReal.inv_le_inv.2 hBA
  calc c⁻¹ * hitAndRunDensity K u x = (c * A)⁻¹ := by
        rw [hitAndRunDensity, ← hA, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
    _ ≤ B⁻¹ := this
    _ = hitAndRunDensity K v x := by rw [hitAndRunDensity, ← hB]

/-- **The density comparison at the paper's factor `Λ = 2`**, the form
`Arlib.MarkovChains.chordLength_mul_norm_le` supplies. -/
theorem hitAndRunDensity_ge_of_chordLength_le_two (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} {u v x : EuclideanSpace ℝ (Fin n)}
    (hxu : x ≠ u) {N : ℝ} (hN : 0 < N)
    (hnorm : ‖x - v‖ ≤ N * ‖x - u‖)
    (hchord : chordLength K v x * ENNReal.ofReal ‖x - u‖
      ≤ 2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x)) :
    (ENNReal.ofReal (2 * N ^ n))⁻¹ * hitAndRunDensity K u x ≤ hitAndRunDensity K v x := by
  refine hitAndRunDensity_ge_of_chordLength_le hn hxu hN (by norm_num : (0:ℝ) < 2) hnorm ?_
  rwa [ENNReal.ofReal_ofNat]

/-- **Integrating the density comparison** against equation (5).  If on `S ∩ K` the
one-step density at `v` dominates `c` times the one at `u`, then `c·P_u(S) ≤ P_v(S)`. -/
theorem mul_hitAndRunProposal_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (u v : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ x ∈ S ∩ K, c * hitAndRunDensity K u x ≤ hitAndRunDensity K v x) :
    c * hitAndRunProposal K u S ≤ hitAndRunProposal K v S := by
  rw [hitAndRunProposal_eq_density hKm u hS, hitAndRunProposal_eq_density hKm v hS]
  have hint : c * ∫⁻ x in S ∩ K, hitAndRunDensity K u x
      ≤ ∫⁻ x in S ∩ K, hitAndRunDensity K v x := by
    rw [← lintegral_const_mul' _ _ hc]
    exact setLIntegral_mono' (hS.inter hKm) h
  calc c * (2 / sphereArea n * ∫⁻ x in S ∩ K, hitAndRunDensity K u x)
      = 2 / sphereArea n * (c * ∫⁻ x in S ∩ K, hitAndRunDensity K u x) := by ring
    _ ≤ 2 / sphereArea n * ∫⁻ x in S ∩ K, hitAndRunDensity K v x :=
        mul_le_mul' le_rfl hint

/-! ## `P_u(A₁) ≤ 1/8` -/

/-- **The paper's `P(x ∈ A₁) ≤ 1/8`.**  The *open* ball of radius `F(u)` about `u` carries
at most `1/8` of the one-step law: it is the increasing union of the closed balls of radius
`F(u) − 1/(m+1)`, on each of which
`Arlib.hitAndRun_closedBall_le_of_lt_medianStep` applies. -/
theorem hitAndRun_ball_medianStep_le (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) :
    hitAndRun K u (Metric.ball u (medianStep K u)) ≤ 1 / 8 := by
  set r : ℝ := medianStep K u with hr
  set c : ℕ → ℝ := fun m => r - 1 / (m + 1) with hcdef
  have hmono : Monotone fun m : ℕ => Metric.closedBall u (c m) := by
    intro a b hab
    refine Metric.closedBall_subset_closedBall ?_
    have : (1 : ℝ) / (b + 1) ≤ 1 / (a + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    simp only [hcdef]
    linarith
  have hunion : (⋃ m : ℕ, Metric.closedBall u (c m)) = Metric.ball u r := by
    ext y
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Metric.mem_ball]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
      simp only [hcdef] at hm
      linarith
    · intro hy
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0:ℝ) < r - dist y u by linarith)
      exact ⟨m, by simp only [hcdef]; linarith⟩
  have hle : ∀ m : ℕ, hitAndRun K u (Metric.closedBall u (c m)) ≤ 1 / 8 := by
    intro m
    refine hitAndRun_closedBall_le_of_lt_medianStep ?_
    have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
    simp only [hcdef]
    linarith
  have htend := tendsto_measure_iUnion_atTop (μ := hitAndRun K u) hmono
  rw [hunion] at htend
  exact le_of_tendsto htend (Filter.Eventually.of_forall hle)

/-! ## The total-variation assembly -/

/-- **From a setwise lower bound off a small set to a total-variation bound.**

If `μ Bad ≤ q` and `c·μ S ≤ ν S` for every measurable `S` disjoint from `Bad`, then
`μ A − ν A ≤ (1 − c) + c·q = 1 − c(1 − q)` for every measurable `A`: this is the last
display of Lovász's proof. -/
theorem tvLe_of_overlap {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Bad : Set Ω} (hBadm : MeasurableSet Bad) {c q : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq0 : 0 ≤ q)
    (hq : μ Bad ≤ ENNReal.ofReal q)
    (hcomp : ∀ S : Set Ω, MeasurableSet S → Disjoint S Bad →
      ENNReal.ofReal c * μ S ≤ ν S) :
    TVLe μ ν (ENNReal.ofReal (1 - c * (1 - q))) := by
  refine tvLe_of_forall_le fun A hA => ?_
  have hAd : MeasurableSet (A \ Bad) := hA.diff hBadm
  have hdisj : Disjoint (A \ Bad) Bad := Set.disjoint_sdiff_left
  have hkey : ENNReal.ofReal c * μ (A \ Bad) ≤ ν A :=
    (hcomp _ hAd hdisj).trans (measure_mono Set.sdiff_subset)
  -- move to reals
  set a : ℝ := (μ A).toReal with ha
  set m : ℝ := (μ (A \ Bad)).toReal with hm
  set b : ℝ := (ν A).toReal with hb
  have ha1 : a ≤ 1 := by
    rw [ha, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hsplit : a ≤ m + q := by
    have h1 : μ A ≤ μ (A \ Bad) + ENNReal.ofReal q := by
      refine (measure_le_inter_add_sdiff μ A Bad).trans ?_
      rw [add_comm]
      exact add_le_add le_rfl ((measure_mono Set.inter_subset_right).trans hq)
    have := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0] at this
  have hcm : c * m ≤ b := by
    have := ENNReal.toReal_mono (measure_ne_top ν A) hkey
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at this
  have hfinal : a ≤ b + (1 - c * (1 - q)) := by nlinarith [hsplit, hcm, ha1, hc0, hc1, ha0]
  have hμA : μ A = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hνA : ν A = ENNReal.ofReal b := by
    rw [hb, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμA, hνA, ← ENNReal.ofReal_add hb0 (by nlinarith [hfinal, hb0, ha0])]
  exact ENNReal.ofReal_le_ofReal hfinal

/-! ## The two combined, for the walk -/

/-- **The walk's version of `tvLe_of_overlap`.**  When both walks move with probability one
(`hmoveu`, `hmovev` — the lazy atom of `hitAndRun` is empty), a pointwise density comparison
on `Badᶜ ∩ K` gives a total-variation bound on the one-step laws. -/
theorem tvLe_hitAndRun_of_overlap [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)}
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    {Bad : Set (EuclideanSpace ℝ (Fin n))} (hBadm : MeasurableSet Bad) {c q : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq0 : 0 ≤ q)
    (hq : hitAndRun K u Bad ≤ ENNReal.ofReal q)
    (hdens : ∀ x ∈ K, x ∉ Bad →
      ENNReal.ofReal c * hitAndRunDensity K u x ≤ hitAndRunDensity K v x) :
    TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c * (1 - q))) := by
  have hu : ∀ t : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet t →
      hitAndRun K u t = hitAndRunProposal K u t := by
    intro t ht
    rw [hitAndRun_apply_set hKm u ht, hmoveu, tsub_self, zero_mul, add_zero]
  have hv : ∀ t : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet t →
      hitAndRun K v t = hitAndRunProposal K v t := by
    intro t ht
    rw [hitAndRun_apply_set hKm v ht, hmovev, tsub_self, zero_mul, add_zero]
  refine tvLe_of_overlap hBadm hc0 hc1 hq0 hq ?_
  intro S hS hdisj
  rw [hu S hS, hv S hS]
  refine mul_hitAndRunProposal_le hKm u v hS ENNReal.ofReal_ne_top ?_
  rintro x ⟨hxS, hxK⟩
  exact hdens x hxK (Set.disjoint_left.1 hdisj hxS)

/-! ## Lemma 4.1 -/

/-- **Lemma 4.1 of Lovász–Vempala = Lemma 8 of Lovász (1999).**

If `d_K(u,v) < 1/8` and `|u − v| < (2/√n)·F(u)`, then `d_TV(P_u, P_v)` is bounded away
from `1`.

Everything the paper's proof needs is now discharged **except the spherical-cap estimate**:

* `P_u(A₁) ≤ 1/8` — equation (4), the defining property of `F` — is
  `hitAndRun_ball_medianStep_le`.
* the chord comparison `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)` (Lovász's Menelaus step) is
  `Arlib.MarkovChains.chordLength_mul_norm_le`.  It used to be an inline hypothesis
  `hchord`; **there is no `hchord` binder any more.**  Its price is the geometric side
  conditions `hKc`, `hKcl`, `hKb`, `hu`, `hv`, `huv`, `ha`, `hb` below, all of which the
  paper assumes silently.
* `P_u(A₃) ≤ 1/2` and the measurability of `A₃` are
  `Arlib.MarkovChains.hitAndRun_chord_bad_le`, `measurableSet_chordLow_lt`,
  `measurableSet_chordHigh_gt`.  These used to be the inline hypotheses `hA3`, `hA3m`;
  **there are no `hA3`/`hA3m` binders any more.**
* `hcap`, the paper's `P_u(A₂) ≤ q₂`, is the **one remaining unproved input**.  The paper's
  value `q₂ = 1/6` is *wrong*; the true value ranges from `1/2` at `n = 2` down to
  `2(1 − Φ(1)) = 0.3173…`.  The statement is parametric in `q₂` for exactly that reason.
  `Arlib.MarkovChains.hitAndRun_almostOrthogonal_le_one_sub_inv` discharges it at
  `q₂ = 1 − 1/n`, which is useful only at `n = 1`.

**The two chord conditions that replace the paper's `A₃`.**  `A₃` is taken here as the
*union* `{x : chordLow K u x < −3} ∪ {x : 3 < chordHigh K u x}`, not the paper's one-sided
`{x : chordLow K u x < −3}`.  The one-sided version does not imply the chord comparison —
`Arlib/Convexity/ChordCompare.lean` exhibits a counterexample — so an earlier version of
this theorem, which carried the printed hypothesis inline, was **vacuous** wherever it
mattered.  The correction costs `1/3 → 1/2` in the budget.

`ha : chordLow K u v < 0` and `hb : 1 < chordHigh K u v` say that the chord through `u` and
`v` extends strictly beyond each of them; they hold whenever `u, v ∈ interior K`, by
`Arlib.chordLow_neg_of_mem_interior` and `Arlib.one_lt_chordHigh_of_mem_interior`.

The constant returned is the *sharp* one, `1 − (1 − q)/(2(1 + 4/n)ⁿ)` with
`q = 1/8 + q₂ + 1/2`.  It is a real bound only for `q₂ < 3/8`; the paper's `1 − 1/500` is
**not** among its values, and neither is any dimension-free constant.  See the module
docstring. -/
theorem tvLe_hitAndRun_lemma41 (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u)
    {q₂ : ℝ} (hq₂0 : 0 ≤ q₂)
    (hcap : hitAndRun K u
        {x : EuclideanSpace ℝ (Fin n) |
          ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal q₂) :
    TVLe (hitAndRun K u) (hitAndRun K v)
      (ENNReal.ofReal
        (1 - 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) * (1 - (1 / 8 + q₂ + 1 / 2)))) := by
  haveI : NeZero n := ⟨hn⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  set N : ℝ := 1 + 4 / (n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcpos : (0 : ℝ) < 2 * N ^ n := by positivity
  -- the three bad pieces; `A₃` is the *two-sided* chord condition
  set A₁ : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u (medianStep K u) with hA₁
  set A₂ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|} with hA₂
  set A₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x} with hA₃def
  set Bad : Set (EuclideanSpace ℝ (Fin n)) := A₁ ∪ A₂ ∪ A₃ with hBad
  have hA₁m : MeasurableSet A₁ := measurableSet_ball
  have hA₂m : MeasurableSet A₂ := by
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin n) => ‖x - u‖ * ‖u - v‖ := by fun_prop
    have h2 : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
        Real.sqrt n * |⟪x - u, u - v⟫| := by
      exact continuous_const.mul ((continuous_id.sub continuous_const).inner
        continuous_const).abs
    exact measurableSet_lt h1.measurable h2.measurable
  have hA₃m : MeasurableSet A₃ :=
    (measurableSet_chordLow_lt hKm hKc hKb hu).union
      (measurableSet_chordHigh_gt hKm hKc hKb hu)
  have hBadm : MeasurableSet Bad := (hA₁m.union hA₂m).union hA₃m
  -- the mass of `Bad`: `1/8 + q₂ + 1/2`
  have hA3 : hitAndRun K u A₃ ≤ ENNReal.ofReal (1 / 2) :=
    hitAndRun_chord_bad_le hKm hKc hKb hu
  have hq : hitAndRun K u Bad ≤ ENNReal.ofReal (1 / 8 + q₂ + 1 / 2) := by
    refine (measure_union_le _ _).trans ?_
    refine ((add_le_add ((measure_union_le _ _).trans
      (add_le_add (hitAndRun_ball_medianStep_le K u) hcap)) hA3)).trans ?_
    rw [ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1/8 + q₂) (by norm_num : (0:ℝ) ≤ 1/2),
      ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/8) hq₂0]
    have : (1 : ℝ≥0∞) / 8 = ENNReal.ofReal (1 / 8) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [this]
  -- the density comparison off `Bad`
  have hdens : ∀ x ∈ K, x ∉ Bad →
      ENNReal.ofReal (1 / (2 * N ^ n)) * hitAndRunDensity K u x
        ≤ hitAndRunDensity K v x := by
    intro x hxK hxBad
    have h1 : x ∉ A₁ := fun h => hxBad (Or.inl (Or.inl h))
    have h2 : x ∉ A₂ := fun h => hxBad (Or.inl (Or.inr h))
    have h3 : x ∉ A₃ := fun h => hxBad (Or.inr h)
    have hFle : medianStep K u ≤ ‖x - u‖ := by
      by_contra hcon
      refine h1 ?_
      rw [hA₁, Metric.mem_ball, dist_eq_norm]
      exact lt_of_not_ge hcon
    have h8 : Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖ := by
      rw [hA₂, Set.mem_setOf_eq, not_lt] at h2
      exact h2
    -- the two chord conditions, from `x ∉ A₃`
    obtain ⟨hlow, hhigh⟩ : (-3 : ℝ) ≤ chordLow K u x ∧ chordHigh K u x ≤ 3 := by
      rw [hA₃def, Set.mem_union, not_or, Set.mem_setOf_eq, Set.mem_setOf_eq,
        not_lt, not_lt] at h3
      exact h3
    -- the paper's (7)
    have h7 : Real.sqrt n * ‖u - v‖ ≤ 2 * ‖x - u‖ := by
      have : ‖u - v‖ < 2 / Real.sqrt n * ‖x - u‖ :=
        lt_of_lt_of_le hFu (by
          apply mul_le_mul_of_nonneg_left hFle
          positivity)
      have hmul := (mul_lt_mul_of_pos_left this hspos)
      rw [show Real.sqrt n * (2 / Real.sqrt n * ‖x - u‖) = 2 * ‖x - u‖ by
        field_simp] at hmul
      exact hmul.le
    have hFpos : 0 < medianStep K u := by
      rcases le_or_gt (medianStep K u) 0 with hle | hgt
      · exfalso
        have h2s : (0 : ℝ) < 2 / Real.sqrt n := by positivity
        have hnp : 2 / Real.sqrt n * medianStep K u ≤ 0 := by nlinarith [h2s, hle]
        have := norm_nonneg (u - v)
        linarith [hFu]
      · exact hgt
    have hxu : x ≠ u := by
      intro h
      rw [h] at hFle
      simp only [sub_self, norm_zero] at hFle
      linarith
    have hnorm : ‖x - v‖ ≤ N * ‖x - u‖ :=
      norm_sub_le_of_almost_orthogonal hn u v x h7 h8
    -- the chord comparison, proved rather than assumed
    have hch := chordLength_mul_norm_le hKc hKcl hKb hu hv hxK huv ha hb hdK hlow hhigh
    have := hitAndRunDensity_ge_of_chordLength_le_two (K := K) hn hxu hNpos hnorm hch
    rwa [show ENNReal.ofReal (1 / (2 * N ^ n)) = (ENNReal.ofReal (2 * N ^ n))⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos hcpos]]
  refine tvLe_hitAndRun_of_overlap hKm hmoveu hmovev hBadm ?_ ?_ ?_ hq hdens
  · positivity
  · have hone : (1 : ℝ) ≤ N ^ n := by
      refine one_le_pow₀ ?_
      rw [hN]
      have : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
      linarith
    rw [div_le_one hcpos]
    linarith
  · linarith

/-- **Lemma 4.1 at the paper's rounding `2(1 + 4/n)ⁿ ≤ 120`.**

`1 − (3/8 − q₂)/120`, for any cap bound `q₂ ≤ 3/8`.  This is the replacement for the deleted
`tvLe_hitAndRun_lemma41_of_half`.

**The figure `1 − 1/2880` recorded by that corollary is lost.**  It came from the
dimension-free cap bound `q₂ = 1/2` together with the paper's `P_u(A₃) ≤ 1/3`, giving a
budget `q = 1/8 + 1/2 + 1/3 < 1`.  With the corrected two-sided `A₃` the budget is
`q = 1/8 + 1/2 + 1/2 = 9/8 > 1`, so `1 − c(1 − q) > 1` and the conclusion `1 − 1/2880` is
simply not derivable — the corollary was deleted rather than restated, because a corollary
whose hypotheses cannot deliver its conclusion is worse than none.

No dimension-free replacement exists at present: `q₂ < 3/8` is needed, but the true cap
probability is `1/2` at `n = 2` and `0.4226…` at `n = 3`.  Any caller of this corollary is
therefore implicitly restricted to `n ≥ 5`, and gets `1 − 1/1892.8…` at best — not the
paper's `1 − 1/500`.  See the module docstring. -/
theorem tvLe_hitAndRun_lemma41_of_le_three_eighths (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u)
    {q₂ : ℝ} (hq₂0 : 0 ≤ q₂) (hq₂ : q₂ ≤ 3 / 8)
    (hcap : hitAndRun K u
        {x : EuclideanSpace ℝ (Fin n) |
          ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal q₂) :
    TVLe (hitAndRun K u) (hitAndRun K v)
      (ENNReal.ofReal (1 - (3 / 8 - q₂) / 120)) := by
  refine (tvLe_hitAndRun_lemma41 hn hKc hKcl hKm hKb hu hv huv hmoveu hmovev ha hb hdK hFu
    hq₂0 hcap).mono (ENNReal.ofReal_le_ofReal ?_)
  have h := one_div_le_inv_two_mul_pow n
  nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : (0:ℝ) ≤ 3 / 8 - q₂)]

/-- **Lemma 4.1 with no unproved hypothesis whatsoever.**

`Arlib.MarkovChains.hitAndRun_almostOrthogonal_le_one_sub_inv` discharges `hcap` at
`q₂ = 1 − 1/n`, so this corollary carries only geometric side conditions.  It is the *entire*
unconditional content of Lemma 4.1 available in this repository, and it is **non-trivial only
at `n = 1`**, where it gives `1 − 3/80`: for `n ≥ 2` the budget `1/8 + (1 − 1/n) + 1/2` is at
least `1`, so the returned bound is `≥ 1` and says nothing.

That is not a defect of this corollary but the honest state of the cap estimate: `1 − 1/n` is
the best that the constraint `∑ᵢ ⟪θ,eᵢ⟫² = 1` alone yields, and the sharp value `0.3173…`
needs the density of `⟪θ,ŵ⟫`, which Mathlib v4.32 does not have.  No non-vacuity witness is
formalised here; the side conditions are the ordinary ones (an interval, two nearby interior
points, at cross-ratio distance `< 1/8`). -/
theorem tvLe_hitAndRun_lemma41_unconditional (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u) :
    TVLe (hitAndRun K u) (hitAndRun K v)
      (ENNReal.ofReal
        (1 - 1 / (2 * (1 + 4 / (n : ℝ)) ^ n)
          * (1 - (1 / 8 + (1 - 1 / (n : ℝ)) + 1 / 2)))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : n ≠ 0 := hn
    positivity
  refine tvLe_hitAndRun_lemma41 hn hKc hKcl hKm hKb hu hv huv hmoveu hmovev ha hb hdK hFu
    ?_ (hitAndRun_almostOrthogonal_le_one_sub_inv hn hKm u v)
  have : (1 : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnR]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  linarith

/-! ### Axiom profile -/

section AxiomCheck

#print axioms norm_sub_le_of_almost_orthogonal
#print axioms pow_one_add_four_div_le_exp
#print axioms two_mul_exp_four_lt
#print axioms one_div_le_inv_two_mul_pow
#print axioms hitAndRunDensity_ge_of_chordLength_le
#print axioms hitAndRunDensity_ge_of_chordLength_le_two
#print axioms mul_hitAndRunProposal_le
#print axioms hitAndRun_ball_medianStep_le
#print axioms tvLe_of_overlap
#print axioms tvLe_hitAndRun_of_overlap
#print axioms tvLe_hitAndRun_lemma41
#print axioms tvLe_hitAndRun_lemma41_of_le_three_eighths
#print axioms tvLe_hitAndRun_lemma41_unconditional

end AxiomCheck

end Arlib.MarkovChains
