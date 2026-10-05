/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalk
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Conductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Metropolis-filtered ball walk for the Gaussian-restricted density

Cousins-Vempala, *Gaussian cooling and `O*(n^3)` algorithms for volume and Gaussian
volume*, Figure 2 (`../gaussian-cooling-vempala/vol3_journal.tex:266`), run their volume
algorithm on a chain whose stationary law is **not** uniform on the body but the
*Gaussian-restricted* density `∝ 1_K(x)·e^{-‖x‖²/(2s)}`.  The chain is the ball walk with
a Metropolis filter: from `x`,

* propose `y` uniformly at random in the ball `x + δBₙ`;
* accept with probability `1_K(y) · min(1, g(y)/g(x))` where `g(x) = e^{-‖x‖²/(2s)}`;
* otherwise stay at `x`.

This module builds that chain as a genuine `ProbabilityTheory.Kernel` on
`EuclideanSpace ℝ (Fin n)` and proves the two structural facts a conductance argument
needs before it can start: the kernel is Markov, and the Gaussian-restricted measure on
`K` is reversible — hence invariant — for it.

`Arlib/Convexity/GaussianCooling/Unblock.lean:80` recorded this kernel as the single
missing object between the isoperimetric input proved there and the §4 conductance
statement at the generality Cousins-Vempala need; `Arlib.MarkovChains.ballWalk`
(`BallWalk.lean:24`) deliberately omits the filter and is stationary for the *uniform*
measure only.  This file supplies the object; it does **not** supply a conductance bound
(see "Scope" below).

## Main definitions

* `Arlib.MarkovChains.gaussianWeight s x = e^{-‖x‖²/(2s)}` (in `ℝ≥0∞`, via
  `gaussianWeightReal` in `ℝ`) — the unnormalised Gaussian weight.  It is total in `s`:
  at `s = 0` the real division gives `g ≡ 1` and the walk degenerates to the ball walk,
  and every statement whose content needs `g` to decay carries `0 < s`.
* `Arlib.MarkovChains.metropolisAccept s x y = min(1, g(y)/g(x))` — the **acceptance
  probability**.  The body's indicator `1_K(y)` is *not* part of it; it enters through the
  proposal measure, which is Lebesgue measure restricted to `K`.
* `Arlib.MarkovChains.metropolisDensity s δ x y = 1[y ∈ x + δBₙ]·min(1, g(y)/g(x))` — the
  **unnormalised one-step density**.
* `Arlib.MarkovChains.metropolisMove K δ s x` — the **probability that a step moves**,
  `vol(x + δBₙ)⁻¹ ∫_{K ∩ (x + δBₙ)} min(1, g(y)/g(x)) dy`.  This is the Metropolis
  analogue of the ball walk's local conductance `Arlib.MarkovChains.ell`.
* `Arlib.MarkovChains.metropolisGaussian K δ s` — **the kernel**:

      vol(x + δBₙ)⁻¹ • (volume.restrict K).withDensity (p(x, ·))  +  (1 - m(x)) • dirac x,

  the accepted proposals plus an atom at `x` carrying exactly the rejected mass.  Unlike
  `ballWalk` it needs **no** measurability hypothesis on `K` to be a kernel at all, so
  there is no fallback branch and no `dif`: `metropolisGaussian` is unconditionally the
  real object.

## Main results

* `Arlib.MarkovChains.measurable_setLIntegral_metropolisDensity` — the fiddly
  measurability: `x ↦ ∫_{B ∩ (x + δBₙ)} min(1, g(y)/g(x)) dy` is measurable.  It comes out
  of *joint* continuity of `(x, y) ↦ min(1, g(y)/g(x))` — the denominator `g(x)` is
  continuous and never zero — cut off by the indicator of `{(x,y) | dist x y < δ}`, and
  then one application of `Measurable.lintegral_prod_right'`.
* `Arlib.MarkovChains.isMarkovKernel_metropolisGaussian` — **the walk is a Markov
  kernel**, for every `K` (measurable or not), every `δ` and every `s`, including the
  degenerate `δ ≤ 0` where the proposal ball is empty and the walk is the identity.
* `Arlib.MarkovChains.gaussianWeight_mul_metropolisAccept` — **the crux**:
  `g(x)·min(1, g(y)/g(x)) = min(g(x), g(y))`, which is *symmetric* in `x` and `y`.  This
  is the entire mathematical content of the Metropolis construction, and it makes detailed
  balance here no harder than for the unfiltered ball walk: with the ball relation
  `dist x y < δ` symmetric as well, the flow weight `g(x)·p(x,y)` is symmetric outright
  (`gaussianWeight_mul_metropolisDensity_comm`).
* `Arlib.MarkovChains.isReversible_metropolisGaussian`,
  `Arlib.MarkovChains.invariant_metropolisGaussian` — **detailed balance for the
  Gaussian-restricted measure** `Arlib.uniformOn (volume.withDensity g) K`, and therefore
  (via the landed `Arlib.MarkovChains.IsReversible.invariant`) its invariance.  No
  convexity of `K`, no positivity of `δ` or `s`, and no bound relating `δ` to `K` is
  needed.  The proof is `flow_metropolisGaussian` — which splits the flow into a moving
  part and a stay-put part — followed by Tonelli
  (`lintegral_gaussianWeight_mul_metropolisDensity_comm`).
* `Arlib.MarkovChains.exists_metropolisGaussian_witness` — the non-vacuity witness
  (`CLAUDE.md` §11) on the unit ball: the target really is a probability measure, the walk
  really moves (`metropolisMove_unitBall_pos`, quantitatively
  `exp_le_metropolisMove_unitBall`), and the filter really rejects
  (`metropolisAccept_zero_lt_one`), so this is not the unfiltered ball walk in disguise.

## Degenerate cases: three warnings

**`n = 0`.**  `EuclideanSpace ℝ (Fin 0)` is a single point of `volume` one, so `{x}` is
*not* null and `P_x({x}ᶜ) = m(x)` is **false** there;
`metropolisGaussian_apply_compl_singleton` carries `[NeZero n]`.  Nothing else does: the
kernel, its Markov property and reversibility are all correct at `n = 0`.

**`δ ≤ 0` and null `K`.**  `ℝ≥0∞` divides by zero to zero, so `metropolisMove K δ s x = 0`
when the proposal ball is null, and the kernel degenerates to `dirac x` — still Markov,
still reversible, but with nothing to say.

**`s ≤ 0`.**  The definitions are total in `s` (`x / 0 = 0` in `ℝ`, so `s = 0` gives
`g ≡ 1`), and the kernel, the Markov property and reversibility hold for every real `s`.
Only the statements about the *shape* of `g` — `g ≤ 1`, the acceptance from the origin,
and the whole witness section — carry `0 < s`.

## Scope: what is deliberately absent

There is **no conductance bound and no mixing bound in *this file*, in any form** — not as
a theorem, not as an assumed predicate, not as a definition whose name asserts one.  What
this file supplies is the object such a bound is *about*, together with the reversibility
that any conductance argument presupposes.

⚠ **This section used to say the bound did not exist anywhere, and that turning the
isoperimetric input into one "is a separate piece of work".  Both halves are now out of
date** (corrected 2026-08-11); it misled at least one reader into believing the chain had
no conductance bound at all.  Two now exist, and the split mirrors
`BallWalkConductance` (exponential) versus `SpeedyConductanceSharp` (sharp):

* `Arlib.MarkovChains.conductance_metropolisGaussian_ge`
  (`MetropolisConductance.lean`) — unconditional on convex bodies, but its acceptance floor
  is the density *sandwich* `α = e^{-R²/(2s)}`, which at Cousins–Vempala parameters is
  `e^{-n/2}`: **exponentially small**.
* `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`
  (`MetropolisConductanceSharp.lean`) — routed through
  `Arlib.MarkovChains.conductance_speedyGaussian_ge`, with acceptance floor
  `a = e^{-(2Rδ+δ²)/(2s)}`, a **constant** in that regime.  It carries `thm:iso` as a
  binder, needs a radius bound `∀ x ∈ K, ‖x‖ ≤ R` that the ball-walk theorems do not, and
  lands at `Ω(δ·log 2/(σ·n))` rather than `Ω(δ·log 2/(σ·√n))`.

A structural fact worth recording here, since it is a fact about *this kernel*: the
`ℓ`-floor in `hoverlap` **cannot** be dropped for `metropolisGaussian` the way
`Arlib.MarkovChains.overlap_speedyWalk_convex` drops it for the speedy walk.  `speedyWalk`
normalises by `vol(B(x,δ) ∩ K)`, i.e. it *conditions* on landing in `K`, so `ell` cancels;
`metropolisGaussian` normalises by `vol(B(x,δ))` and parks rejected mass on a Dirac at `x`.
For `u ∈ T` that Dirac term vanishes, so `P u Tᶜ ≤ ell K δ u` and `P v T ≤ ell K δ v`, and a
thin convex cone with `u, v` near the apex drives both to `0`.  The floor is a
counterexample-backed necessity, not a gap in the proof.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## The Gaussian weight -/

/-- The **unnormalised Gaussian weight** `e^{-‖x‖²/(2s)}`, as a real number. -/
noncomputable def gaussianWeightReal (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (2 * s))

theorem gaussianWeightReal_pos (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < gaussianWeightReal s x := Real.exp_pos _

theorem gaussianWeightReal_ne_zero (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s x ≠ 0 := (gaussianWeightReal_pos s x).ne'

@[simp] theorem gaussianWeightReal_zero (s : ℝ) :
    gaussianWeightReal s (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  simp [gaussianWeightReal]

theorem continuous_gaussianWeightReal (s : ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal s x :=
  Real.continuous_exp.comp (((continuous_norm.pow 2).neg).div_const _)

/-- For `s > 0` the Gaussian weight is at most its value `1` at the origin. -/
theorem gaussianWeightReal_le_one {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s x ≤ 1 := by
  rw [gaussianWeightReal, Real.exp_le_one_iff, neg_div]
  exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith))

/-- For `s > 0` the Gaussian weight is *strictly* below `1` away from the origin.  This is
what makes the acceptance filter non-trivial. -/
theorem gaussianWeightReal_lt_one {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : gaussianWeightReal s x < 1 := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [gaussianWeightReal, Real.exp_lt_one_iff, neg_div]
  exact neg_neg_iff_pos.2 (div_pos (by positivity) (by linarith))

/-- **A uniform lower bound on the Gaussian weight over a bounded region**: on `‖x‖ ≤ r`
the weight is at least `e^{-r²/(2s)}`, which is strictly positive. -/
theorem exp_le_gaussianWeightReal {s : ℝ} (hs : 0 < s) {r : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ r) :
    Real.exp (-r ^ 2 / (2 * s)) ≤ gaussianWeightReal s x := by
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have hsq : ‖x‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg x]
  have hinv : (0 : ℝ) < (2 * s)⁻¹ := inv_pos.2 h2
  rw [gaussianWeightReal, Real.exp_le_exp, div_eq_mul_inv, div_eq_mul_inv]
  nlinarith

/-- The **Gaussian weight** `e^{-‖x‖²/(2s)}` as an element of `ℝ≥0∞`.  It is the density,
with respect to Lebesgue measure, of the unnormalised measure whose restriction to a body
`K` is the Cousins-Vempala target `∝ 1_K(x)·e^{-‖x‖²/(2s)}`. -/
noncomputable def gaussianWeight (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianWeightReal s x)

theorem gaussianWeight_pos (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : 0 < gaussianWeight s x :=
  ENNReal.ofReal_pos.2 (gaussianWeightReal_pos s x)

theorem gaussianWeight_ne_zero (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≠ 0 := (gaussianWeight_pos s x).ne'

theorem gaussianWeight_ne_top (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≠ ⊤ := ENNReal.ofReal_ne_top

@[simp] theorem gaussianWeight_zero (s : ℝ) :
    gaussianWeight s (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  rw [gaussianWeight, gaussianWeightReal_zero, ENNReal.ofReal_one]

theorem measurable_gaussianWeight (s : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => gaussianWeight s x :=
  (continuous_gaussianWeightReal s).measurable.ennreal_ofReal

theorem gaussianWeight_le_one {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≤ 1 := by
  rw [gaussianWeight, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (gaussianWeightReal_le_one hs x)

theorem gaussianWeight_lt_one {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    gaussianWeight s x < 1 := by
  rw [gaussianWeight, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (gaussianWeightReal_lt_one hs hx)

/-- `ENNReal.ofReal` commutes with `min`; used to move the acceptance probability between
its `ℝ≥0∞` form (the definition) and its real form (where continuity is visible). -/
private theorem ofReal_min_aux (a b : ℝ) :
    ENNReal.ofReal (min a b) = min (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]

/-! ## The acceptance probability -/

/-- The **Metropolis acceptance probability** `min(1, g(y)/g(x))` for the Gaussian weight
`g(x) = e^{-‖x‖²/(2s)}`: the probability with which a proposal `y` made from `x` is
accepted, *given* that `y` lies in the body.  The indicator `1_K(y)` of the body is not
part of this definition; it enters in `metropolisGaussian`, where the proposal measure is
restricted to `K`. -/
noncomputable def metropolisAccept (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  min 1 (gaussianWeight s y / gaussianWeight s x)

theorem metropolisAccept_le_one (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    metropolisAccept s x y ≤ 1 := min_le_left _ _

/-- The acceptance probability in real form, `ofReal (min 1 (g(y)/g(x)))`.  Since the
Gaussian weight never vanishes, this is where all the analytic facts about
`metropolisAccept` — continuity above, and the identity `g(x)·a(x,y) = min(g x, g y)`
below — are proved. -/
theorem metropolisAccept_eq_ofReal (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    metropolisAccept s x y
      = ENNReal.ofReal (min 1 (gaussianWeightReal s y / gaussianWeightReal s x)) := by
  rw [ofReal_min_aux, ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos (gaussianWeightReal_pos s x)]
  rfl

/-- **The acceptance probability is jointly continuous in `(x, y)`.**  This is the source
of every measurability statement in the file: the denominator `g(x)` is continuous and
never zero, so the quotient is continuous, and `ENNReal.ofReal` is continuous. -/
theorem continuous_metropolisAccept (s : ℝ) :
    Continuous fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      metropolisAccept s p.1 p.2 := by
  simp_rw [metropolisAccept_eq_ofReal]
  refine ENNReal.continuous_ofReal.comp (continuous_const.min ?_)
  exact ((continuous_gaussianWeightReal s).comp continuous_snd).div
    ((continuous_gaussianWeightReal s).comp continuous_fst)
    fun p => gaussianWeightReal_ne_zero s p.1

/-- **The crux of reversibility**: `g(x)·min(1, g(y)/g(x)) = min(g(x), g(y))`, an
expression *symmetric* in `x` and `y`.  This is the whole reason a Metropolis filter
produces a reversible chain, and it is why detailed balance below is no harder than for
the unfiltered ball walk. -/
theorem gaussianWeight_mul_metropolisAccept (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x * metropolisAccept s x y
      = min (gaussianWeight s x) (gaussianWeight s y) := by
  have hxpos : 0 < gaussianWeightReal s x := gaussianWeightReal_pos s x
  rw [metropolisAccept_eq_ofReal, gaussianWeight, gaussianWeight,
    ← ENNReal.ofReal_mul hxpos.le, ← ofReal_min_aux]
  congr 1
  rcases le_total (gaussianWeightReal s y) (gaussianWeightReal s x) with h | h
  · rw [min_eq_right ((div_le_one hxpos).2 h), min_eq_right h]
    field_simp
  · rw [min_eq_left ((one_le_div hxpos).2 h), min_eq_left h, mul_one]

/-! ## The one-step density -/

/-- The **unnormalised one-step density** of the walk: `1[y ∈ x + δBₙ] · min(1, g(y)/g(x))`,
i.e. the acceptance probability restricted to the proposal ball.  Dividing by
`vol(δBₙ)` and multiplying by `1_K(y)` gives the density of the moving part of the kernel
with respect to Lebesgue measure. -/
noncomputable def metropolisDensity (s δ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (Metric.ball x δ).indicator (metropolisAccept s x) y

theorem metropolisDensity_le_indicator (s δ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    metropolisDensity s δ x y ≤ (Metric.ball x δ).indicator 1 y := by
  rw [metropolisDensity]
  by_cases hy : y ∈ Metric.ball x δ
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    exact metropolisAccept_le_one s x y
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- **The one-step density is jointly measurable.**  It is the acceptance probability —
continuous by `continuous_metropolisAccept` — cut off by the indicator of the measurable
set `{(x, y) | dist x y < δ}` of `ℝⁿ × ℝⁿ`. -/
theorem measurable_metropolisDensity (s δ : ℝ) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      metropolisDensity s δ p.1 p.2 := by
  have hset : MeasurableSet
      {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | dist p.1 p.2 < δ} :=
    measurableSet_lt continuous_dist.measurable measurable_const
  have h : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      metropolisDensity s δ p.1 p.2)
      = {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | dist p.1 p.2 < δ}.indicator
          (fun p => metropolisAccept s p.1 p.2) := by
    funext p
    have hiff : p ∈ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        dist q.1 q.2 < δ} ↔ p.2 ∈ Metric.ball p.1 δ := by
      simp [Metric.mem_ball, dist_comm]
    by_cases hp : p ∈ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        dist q.1 q.2 < δ}
    · rw [Set.indicator_of_mem hp, metropolisDensity, Set.indicator_of_mem (hiff.1 hp)]
    · rw [Set.indicator_of_notMem hp, metropolisDensity,
        Set.indicator_of_notMem (fun hm => hp (hiff.2 hm))]
  rw [h]
  exact (continuous_metropolisAccept s).measurable.indicator hset

/-- **The `x`-marginal integral of the density is measurable in `x`**, for *every* set `B`
(measurable or not — the restricted measure takes care of it).  This is the "fiddly"
measurability the construction of the kernel needs: it says
`x ↦ ∫_{B ∩ (x + δBₙ)} min(1, g(y)/g(x)) dy` is measurable.  Given joint measurability of
the integrand it is one application of `Measurable.lintegral_prod_right'`. -/
theorem measurable_setLIntegral_metropolisDensity (s δ : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) :
    Measurable fun x => ∫⁻ y in B, metropolisDensity s δ x y :=
  (measurable_metropolisDensity s δ).lintegral_prod_right'
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict B)

/-- The **flow weight** `g(x)·1[y ∈ x + δBₙ]·min(1, g(y)/g(x))` is jointly measurable. -/
theorem measurable_gaussianWeight_mul_metropolisDensity (s δ : ℝ) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianWeight s p.1 * metropolisDensity s δ p.1 p.2 :=
  ((measurable_gaussianWeight s).comp measurable_fst).mul (measurable_metropolisDensity s δ)

theorem measurable_setLIntegral_gaussianWeight_mul_metropolisDensity (s δ : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) :
    Measurable fun x => ∫⁻ y in B, gaussianWeight s x * metropolisDensity s δ x y :=
  (measurable_gaussianWeight_mul_metropolisDensity s δ).lintegral_prod_right'
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict B)

/-- **Detailed balance, pointwise.**  `g(x)·p(x,y) = 1[dist x y < δ]·min(g x, g y)`, where
`p` is the unnormalised one-step density. -/
theorem gaussianWeight_mul_metropolisDensity (s δ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x * metropolisDensity s δ x y
      = (Metric.ball x δ).indicator
          (fun z => min (gaussianWeight s x) (gaussianWeight s z)) y := by
  rw [metropolisDensity]
  by_cases hy : y ∈ Metric.ball x δ
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, gaussianWeight_mul_metropolisAccept]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

/-- **The symmetry that gives reversibility**: `g(x)·p(x,y) = g(y)·p(y,x)`.  Both sides are
`min(g x, g y)` when `dist x y < δ` and `0` otherwise; `dist` is symmetric and `min` is
commutative. -/
theorem gaussianWeight_mul_metropolisDensity_comm (s δ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x * metropolisDensity s δ x y
      = gaussianWeight s y * metropolisDensity s δ y x := by
  rw [gaussianWeight_mul_metropolisDensity, gaussianWeight_mul_metropolisDensity]
  by_cases h : y ∈ Metric.ball x δ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Metric.mem_ball_comm.1 h), min_comm]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hm => h (Metric.mem_ball_comm.1 hm))]

/-! ## The probability of moving -/

/-- The **probability that a step actually moves**,

    m(x) = vol(x + δBₙ)⁻¹ · ∫_{K ∩ (x + δBₙ)} min(1, g(y)/g(x)) dy,

i.e. the chance that the proposal lands in `K` *and* survives the acceptance test.  It is
the Metropolis analogue of the ball walk's local conductance `Arlib.MarkovChains.ell`,
to which it reduces when `g` is constant.  As with `ell`, `ℝ≥0∞` divides by zero to zero,
so `m(x) = 0` when the proposal ball is null. -/
noncomputable def metropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ)

theorem metropolisMove_apply (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    metropolisMove K δ s x
      = (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ) := rfl

/-- **The probability of moving is a probability.**  The acceptance probability is at most
`1`, so the numerator is at most `vol(x + δBₙ)`.  This is what makes the stay-put mass
`1 - m(x)` an exact complement rather than a lossy truncated subtraction. -/
theorem metropolisMove_le_one (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : metropolisMove K δ s x ≤ 1 := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc ∫⁻ y in K, metropolisDensity s δ x y
      ≤ ∫⁻ y in K, (Metric.ball x δ).indicator 1 y :=
        lintegral_mono fun y => metropolisDensity_le_indicator s δ x y
    _ ≤ ∫⁻ y, (Metric.ball x δ).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = volume (Metric.ball x δ) := by
        rw [lintegral_indicator measurableSet_ball]
        simp

/-- **The probability of moving is a measurable function of the current point.**  The
numerator is `measurable_setLIntegral_metropolisDensity` and the denominator is a constant
(`volume_ball_eq`). -/
theorem measurable_metropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Measurable (metropolisMove K δ s) := by
  have h : metropolisMove K δ s = fun x => (∫⁻ y in K, metropolisDensity s δ x y) /
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    funext x
    rw [metropolisMove_apply, volume_ball_eq]
  rw [h]
  exact (measurable_setLIntegral_metropolisDensity s δ K).div_const _

/-! ## The kernel -/

/-- **The Metropolis-filtered ball walk for the Gaussian-restricted density**
(Cousins-Vempala, *Gaussian cooling and `O*(n³)` algorithms for volume and Gaussian
volume*, Figure 2, `../gaussian-cooling-vempala/vol3_journal.tex:266`).  From `x`:

* propose `y` uniformly in the ball `x + δBₙ`;
* accept with probability `1_K(y) · min(1, g(y)/g(x))`, where `g(x) = e^{-‖x‖²/(2s)}`;
* otherwise stay at `x`.

As a measure this is

    vol(x + δBₙ)⁻¹ • (volume.restrict K).withDensity (p(x, ·))  +  (1 - m(x)) • dirac x

with `p(x, y) = 1[y ∈ x + δBₙ]·min(1, g(y)/g(x))` the unnormalised one-step density
(`metropolisDensity`) and `m(x)` the total probability of moving (`metropolisMove`).

Unlike `Arlib.MarkovChains.ballWalk`, **no measurability hypothesis on `K` is needed to
build the kernel**: `Measure.restrict` is defined for an arbitrary set and the
measurability of `x ↦ P_x(t)` goes through the jointly measurable integrand rather than
through a volume of an intersection.  Measurability of `K` is needed only for
reversibility, where the target measure is restricted to `K`. -/
noncomputable def metropolisGaussian (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun x := (volume (Metric.ball x δ))⁻¹ •
        (volume.restrict K).withDensity (metropolisDensity s δ x)
      + (1 - metropolisMove K δ s x) • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hrw : ∀ x : EuclideanSpace ℝ (Fin n),
        ((volume (Metric.ball x δ))⁻¹ •
              (volume.restrict K).withDensity (metropolisDensity s δ x)
            + (1 - metropolisMove K δ s x) • Measure.dirac x) t
          = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
              (∫⁻ y in t ∩ K, metropolisDensity s δ x y)
            + (1 - metropolisMove K δ s x) * t.indicator 1 x := by
      intro x
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        withDensity_apply _ ht, Measure.restrict_restrict ht, Measure.dirac_apply' _ ht,
        volume_ball_eq]
    simp_rw [hrw]
    exact ((measurable_setLIntegral_metropolisDensity s δ (t ∩ K)).const_mul _).add
      ((measurable_const.sub (measurable_metropolisMove K δ s)).mul (measurable_one.indicator ht))

/-- Unfolding lemma for `metropolisGaussian`. -/
theorem metropolisGaussian_apply (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    metropolisGaussian K δ s x
      = (volume (Metric.ball x δ))⁻¹ •
          (volume.restrict K).withDensity (metropolisDensity s δ x)
        + (1 - metropolisMove K δ s x) • Measure.dirac x := rfl

/-- **The value of the kernel on a measurable event.**  The mass splits into the moving
part `vol(x + δBₙ)⁻¹ ∫_{t ∩ K} p(x, y) dy` and the stay-put part `(1 - m(x))·1[x ∈ t]`. -/
theorem metropolisGaussian_apply_set (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    metropolisGaussian K δ s x t
      = (volume (Metric.ball x δ))⁻¹ * (∫⁻ y in t ∩ K, metropolisDensity s δ x y)
        + (1 - metropolisMove K δ s x) * t.indicator 1 x := by
  rw [metropolisGaussian_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, withDensity_apply _ ht, Measure.restrict_restrict ht,
    Measure.dirac_apply' _ ht]

/-- **The Metropolis walk is a Markov kernel**, for every set `K` (measurable or not) and
every `δ`, `s`.  Its total mass is `m(x) + (1 - m(x))`, which is `1` because
`metropolisMove_le_one` makes the truncated subtraction exact. -/
instance isMarkovKernel_metropolisGaussian (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    IsMarkovKernel (metropolisGaussian K δ s) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [metropolisGaussian_apply_set K δ s x MeasurableSet.univ, Set.univ_inter,
    Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one, ← ENNReal.div_eq_inv_mul,
    ← metropolisMove_apply]
  exact add_tsub_cancel_of_le (metropolisMove_le_one K δ s x)

/-! ## Reversibility -/

/-- **The flow of the Metropolis walk, split into its two parts.**  For the unnormalised
Gaussian-restricted measure `pi = (volume.withDensity g).restrict K`,

    flow(S, T) = vol(δBₙ)⁻¹ · ∫_{S ∩ K} ∫_{T ∩ K} g(x)·p(x, y) dy dx
                 + ∫_{T ∩ S ∩ K} g(x)·(1 - m(x)) dx.

The first term is the mass that actually moves from `S` into `T`; the second is the mass
that stays put, and it is only present where `S` and `T` overlap.  Written this way both
terms are visibly symmetric under exchanging `S` and `T` — the first by
`lintegral_gaussianWeight_mul_metropolisDensity_comm`, which is Tonelli plus
`gaussianWeight_mul_metropolisDensity_comm`, the second because the domain of integration
is symmetric. -/
theorem flow_metropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ s : ℝ) {S T : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    flow (metropolisGaussian K δ s)
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)).restrict K) S T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            (∫⁻ x in S ∩ K, ∫⁻ y in T ∩ K,
              gaussianWeight s x * metropolisDensity s δ x y)
        + ∫⁻ x in T ∩ (S ∩ K), gaussianWeight s x * (1 - metropolisMove K δ s x) := by
  have hker : Measurable fun x : EuclideanSpace ℝ (Fin n) => metropolisGaussian K δ s x T :=
    (metropolisGaussian K δ s).measurable_coe hT
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      gaussianWeight s x * metropolisGaussian K δ s x T
        = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            (∫⁻ y in T ∩ K, gaussianWeight s x * metropolisDensity s δ x y)
          + T.indicator (fun z => gaussianWeight s z * (1 - metropolisMove K δ s z)) x := by
    intro x
    rw [metropolisGaussian_apply_set K δ s x hT, mul_add, volume_ball_eq,
      lintegral_const_mul' _ _ (gaussianWeight_ne_top s x)]
    congr 1
    · ring
    · by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]
  rw [flow, Measure.restrict_restrict hS,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianWeight s) hker
      (hS.inter hK)]
  simp only [Pi.mul_apply]
  simp_rw [hpt]
  rw [lintegral_add_left
      ((measurable_setLIntegral_gaussianWeight_mul_metropolisDensity s δ (T ∩ K)).const_mul _),
    lintegral_const_mul _
      (measurable_setLIntegral_gaussianWeight_mul_metropolisDensity s δ (T ∩ K)),
    lintegral_indicator hT, Measure.restrict_restrict hT]

/-- **The two-sided integral of the flow weight is symmetric.**  Tonelli
(`lintegral_lintegral_swap`, applicable because the integrand is jointly measurable and
Lebesgue measure is `SFinite`) followed by the pointwise symmetry
`g(x)·p(x,y) = g(y)·p(y,x)`. -/
theorem lintegral_gaussianWeight_mul_metropolisDensity_comm (s δ : ℝ)
    (A B : Set (EuclideanSpace ℝ (Fin n))) :
    (∫⁻ x in A, ∫⁻ y in B, gaussianWeight s x * metropolisDensity s δ x y)
      = ∫⁻ x in B, ∫⁻ y in A, gaussianWeight s x * metropolisDensity s δ x y := by
  rw [lintegral_lintegral_swap
    (measurable_gaussianWeight_mul_metropolisDensity s δ).aemeasurable]
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  exact gaussianWeight_mul_metropolisDensity_comm s δ x y

/-- **The Metropolis walk satisfies detailed balance for the unnormalised
Gaussian-restricted measure** `(volume.withDensity g).restrict K`, `g(x) = e^{-‖x‖²/(2s)}`.
The proof is the symmetry of the two terms of `flow_metropolisGaussian`.  No convexity of
`K`, no positivity of `δ` or of `s`, and no bound relating `δ` to `K` is required. -/
theorem isReversible_metropolisGaussian_restrict {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    IsReversible (metropolisGaussian K δ s)
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)).restrict K) := by
  intro S T hS hT
  have h2 : T ∩ (S ∩ K) = S ∩ (T ∩ K) := by
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [flow_metropolisGaussian hK δ s hS hT, flow_metropolisGaussian hK δ s hT hS,
    lintegral_gaussianWeight_mul_metropolisDensity_comm s δ (S ∩ K) (T ∩ K), h2]

/-- **The Metropolis walk is reversible for the Gaussian-restricted probability measure on
`K`** — the target `∝ 1_K(x)·e^{-‖x‖²/(2s)}` of the Cousins-Vempala algorithm.  Immediate
from `isReversible_metropolisGaussian_restrict` and `IsReversible.smul`, since
`Arlib.uniformOn μ K = (μ K)⁻¹ • μ.restrict K`.

Note the statement is *true but empty* when `(volume.withDensity g) K` is `0` or `⊤`,
where `uniformOn` is the zero measure;
`isProbabilityMeasure_gaussianUniformOn_unitBall` discharges that guard on the
witness. -/
theorem isReversible_metropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    IsReversible (metropolisGaussian K δ s)
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) :=
  (isReversible_metropolisGaussian_restrict hK δ s).smul _

/-- **The Gaussian-restricted measure on `K` is invariant for the Metropolis walk.**
Detailed balance (`isReversible_metropolisGaussian`) plus the landed
`IsReversible.invariant`.  This is the stationarity claim that every mixing statement
about the Gaussian-cooling chain presupposes, and it is the object
`Arlib/Convexity/GaussianCooling/Unblock.lean` records as missing. -/
theorem invariant_metropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel.Invariant (metropolisGaussian K δ s)
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) :=
  (isReversible_metropolisGaussian hK δ s).invariant

/-! ## Non-vacuity witness

Everything above is a true statement about the zero measure or about a kernel that never
moves unless the guards below are discharged.  They are, on the unit ball, for every
dimension `n ≥ 1`, every step `0 < δ ≤ 1` and every temperature `s > 0`. -/

/-- **From the origin the acceptance test is exactly the Gaussian weight.**  `g(0) = 1` is
the maximum of `g` when `s > 0`, so `min(1, g(y)/g(0)) = g(y)`. -/
theorem metropolisAccept_zero_left {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin n)) :
    metropolisAccept s 0 y = gaussianWeight s y := by
  rw [metropolisAccept, gaussianWeight_zero, div_one, min_eq_right (gaussianWeight_le_one hs y)]

/-- **The filter is non-trivial**: from the origin every proposal `y ≠ 0` is rejected with
positive probability.  This is what distinguishes `metropolisGaussian` from the unfiltered
`Arlib.MarkovChains.ballWalk`, whose acceptance probability is identically `1` inside the
body. -/
theorem metropolisAccept_zero_lt_one {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ≠ 0) : metropolisAccept s 0 y < 1 := by
  rw [metropolisAccept_zero_left hs]
  exact gaussianWeight_lt_one hs hy

/-- **A lower bound for the Gaussian mass of a ball centred at the origin**: the weight is
at least `e^{-r²/(2s)}` throughout `rBₙ`. -/
theorem mul_volume_ball_le_withDensity_gaussianWeight {s : ℝ} (hs : 0 < s) (r : ℝ) :
    ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * s))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
  rw [withDensity_apply _ measurableSet_ball]
  calc ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * s))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * s))) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight s y := by
        refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
        refine ENNReal.ofReal_le_ofReal (exp_le_gaussianWeightReal hs ?_)
        simpa using (Metric.mem_ball.1 hy).le

/-- The Gaussian-restricted measure of the unit ball is not zero — the first guard on the
witness. -/
theorem withDensity_gaussianWeight_unitBall_ne_zero {s : ℝ} (hs : 0 < s) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le ?_ (mul_volume_ball_le_withDensity_gaussianWeight hs 1))
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' volume_unitBall_ne_zero

/-- The Gaussian-restricted measure of the unit ball is finite — the second guard on the
witness.  Here `s > 0` matters: it is what makes `g ≤ 1`. -/
theorem withDensity_gaussianWeight_unitBall_ne_top {s : ℝ} (hs : 0 < s) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := by
  have h : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [withDensity_apply _ measurableSet_ball]
    calc ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, gaussianWeight s y
        ≤ ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 :=
          setLIntegral_mono' measurableSet_ball fun y _ => gaussianWeight_le_one hs y
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by simp
  exact ne_top_of_le_ne_top volume_unitBall_ne_top h

/-- **The Gaussian-restricted measure on the unit ball is a genuine probability measure.**
This is what stops `isReversible_metropolisGaussian` and `invariant_metropolisGaussian`
from being statements about the zero measure. -/
theorem isProbabilityMeasure_gaussianUniformOn_unitBall {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  Arlib.isProbabilityMeasure_uniformOn _ (withDensity_gaussianWeight_unitBall_ne_zero hs)
    (withDensity_gaussianWeight_unitBall_ne_top hs)

/-- **The walk moves with probability exactly `m(x)`**: `P_x({x}ᶜ) = m(x)`.

The stay-put atom contributes nothing to `{x}ᶜ`, and the moving part loses nothing by
deleting `{x}`, since singletons are Lebesgue-null.  That last step is where `[NeZero n]`
is used, and it is not removable: in `EuclideanSpace ℝ (Fin 0)` the whole space is one
atom of volume one and `{x}ᶜ = ∅`. -/
theorem metropolisGaussian_apply_compl_singleton [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    metropolisGaussian K δ s x {x}ᶜ = metropolisMove K δ s x := by
  rw [metropolisGaussian_apply_set K δ s x (measurableSet_singleton x).compl,
    Set.indicator_of_notMem (by simp), mul_zero, add_zero, ← ENNReal.div_eq_inv_mul,
    metropolisMove_apply]
  congr 1
  rw [show ({x}ᶜ ∩ K : Set (EuclideanSpace ℝ (Fin n))) = K \ {x} by
    rw [Set.sdiff_eq, Set.inter_comm]]
  exact setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton x))

/-- **The witness kernel really moves.**  From the centre of the unit ball with step
`0 < δ ≤ 1` and temperature `s > 0`, the walk leaves its current point with probability at
least `e^{-δ²/(2s)} > 0`: the stay-put atom is not carrying all the mass.

The bound is the honest one — unlike the unfiltered ball walk, whose escape probability
from the centre is exactly `1`, a Metropolis step is rejected with positive probability,
and `e^{-δ²/(2s)}` is a lower bound on the acceptance probability throughout the proposal
ball. -/
theorem exp_le_metropolisMove_unitBall {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (Real.exp (-δ ^ 2 / (2 * s)))
      ≤ metropolisMove (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s 0 := by
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 hδ).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hfun : metropolisAccept s (0 : EuclideanSpace ℝ (Fin n)) = gaussianWeight s :=
    funext (metropolisAccept_zero_left hs)
  have hlast : ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      metropolisDensity s δ 0 y
      = ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, gaussianWeight s y := by
    simp_rw [metropolisDensity, hfun]
    rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball hδ1)]
  rw [metropolisMove_apply, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop), hlast,
    ← withDensity_apply _ measurableSet_ball]
  exact mul_volume_ball_le_withDensity_gaussianWeight hs δ

/-- **The probability of moving is strictly positive** on the witness. -/
theorem metropolisMove_unitBall_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < metropolisMove (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s 0 :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _))
    (exp_le_metropolisMove_unitBall hs hδ hδ1)

/-- **The non-vacuity witness (`CLAUDE.md` §11), packaged.**  For every dimension `n ≥ 1`,
every step `0 < δ ≤ 1` and every temperature `s > 0` there is a body `K` — the unit ball —
such that

* `K` is measurable, so `isReversible_metropolisGaussian` applies to it;
* the Gaussian-restricted measure `Arlib.uniformOn (volume.withDensity g) K` is a genuine
  probability measure, not the zero measure;
* `metropolisGaussian K δ s` is a Markov kernel, reversible for it, and leaves it
  invariant;
* the walk leaves its current point with strictly positive probability — the stay-put atom
  does not carry all the mass;
* and the acceptance filter is non-trivial: from the centre every proposal `y ≠ 0` is
  rejected with positive probability, so this is genuinely the Metropolis chain and not
  the unfiltered ball walk in disguise.

Without this every result above could be a true statement about a degenerate object. -/
theorem exists_metropolisGaussian_witness [NeZero n] {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 < s) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧
        IsProbabilityMeasure (Arlib.uniformOn
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) K) ∧
        IsMarkovKernel (metropolisGaussian K δ s) ∧
        IsReversible (metropolisGaussian K δ s) (Arlib.uniformOn
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) K) ∧
        Kernel.Invariant (metropolisGaussian K δ s) (Arlib.uniformOn
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) K) ∧
        0 < metropolisMove K δ s 0 ∧
        metropolisGaussian K δ s 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ
            = metropolisMove K δ s 0 ∧
        0 < metropolisGaussian K δ s 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ ∧
        ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 → metropolisAccept s 0 y < 1 := by
  refine ⟨Metric.ball 0 1, measurableSet_ball,
    isProbabilityMeasure_gaussianUniformOn_unitBall hs, isMarkovKernel_metropolisGaussian _ _ _,
    isReversible_metropolisGaussian measurableSet_ball δ s,
    invariant_metropolisGaussian measurableSet_ball δ s,
    metropolisMove_unitBall_pos hs hδ hδ1,
    metropolisGaussian_apply_compl_singleton _ δ s 0, ?_,
    fun y hy => metropolisAccept_zero_lt_one hs hy⟩
  rw [metropolisGaussian_apply_compl_singleton _ δ s 0]
  exact metropolisMove_unitBall_pos hs hδ hδ1

end Arlib.MarkovChains
