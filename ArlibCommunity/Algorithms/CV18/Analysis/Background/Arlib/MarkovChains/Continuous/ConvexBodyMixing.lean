/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoBall
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.UnitBallMixing

/-!
# Unconditional mixing of the ball walk on a general bounded convex body

`Arlib.MarkovChains.Continuous.UnitBallMixing` composes the Markov-chain stack end to end
for one fixed body, the Euclidean unit ball.  This file does the same for an *arbitrary*
bounded convex body `K` that contains a ball `B(c, γ)` — the object a sampling oracle
actually receives (a Kannan–Vempala inflated polytope, say), rather than a normalised
special case.

Two hypotheses which every quantitative theorem in the stack
(`Arlib.MarkovChains.conductance_ballWalk_ge`,
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk`) carries inline are discharged here:

* the **isoperimetric inequality** `hiso`, by `Arlib.uniformOn_iso_of_convex`, which proves
  it for every bounded convex body at `κ = (1/2)ⁿ/D` with no further assumption;
* the **local-conductance floor** `hell`, by `le_ell_of_convex_of_ball_subset` below, the
  one piece of new mathematics in this file, at `θ = (γ/(γ+D))ⁿ`.

Both are theorems, not assumed predicates: nothing below is a `def`, `structure`, `class`
or named `Prop` that asserts a geometric inequality it does not prove.

## The local-conductance argument

For `x ∈ K` put `λ = δ/(γ+D)` and `y = (1-λ)·x + λ·c`.  Since `K` is convex and
`B(c,γ) ⊆ K`, the shrunken ball `(1-λ)·x + λ·B(c,γ) = B(y, λγ)` lies in `K`; and since
`dist y x = λ·dist c x ≤ λD`, that ball also lies in `B(x, δ)`, because
`λγ + λD = λ(γ+D) = δ`.  Comparing Lebesgue volumes of the two balls gives
`ell K δ x ≥ (λγ/δ)ⁿ = (γ/(γ+D))ⁿ`.

This is a *cruder* constant than the `(γ/(2D))ⁿ` one might aim for, and no attempt is made
to optimise it; only positivity is used downstream.  Note the proof needs only
`δ ≤ γ + D`, though the statements below assume the more familiar `δ ≤ γ`.

## The honest scope, which is not the polynomial-time result

`κ = (1/2)ⁿ/D` and `θ = (γ/(γ+D))ⁿ` are both **exponentially small in the dimension `n`**,
so the conductance bound obtained here is exponentially small and the mixing time it feeds
into is exponentially large in `n`.  **This is not a polynomial-time sampler and must not
be quoted as one.**  What it is: a statement about a general convex body in which the
isoperimetry, the local conductance, the Cheeger inequality, the `L²` decay and the
total-variation bound are all *discharged simultaneously* rather than assumed.  The route
to a polynomial constant is unchanged and still open — the localization argument, whose
remaining obstruction is recorded as (P1) in `Arlib/Convexity/PositionalCut.lean`.

## Main results

* `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset` — the local-conductance floor.
* `Arlib.MarkovChains.conductance_ballWalk_convex` — an unconditional conductance bound.
* `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_convex` — the capstone: unconditional
  total-variation mixing of the lazy ball walk on `K` to `Arlib.uniformOn volume K`, which
  by `Arlib.MarkovChains.isReversible_ballWalk` is *exactly* its stationary measure, so
  there is no residual bias term in the conclusion.
* `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` — the same for an inflated
  polytope `Arlib.Polytope.inflate A b κ`, the downstream consumer's object.
* `Arlib.MarkovChains.exists_unconditional_mixing_convex`,
  `Arlib.MarkovChains.exists_unconditional_mixing_convex_unitBall`,
  `Arlib.MarkovChains.exists_unconditional_mixing_polytope` — the non-vacuity witnesses
  (`CLAUDE.md` §11), the last two with a concrete body (the unit ball; the cube `[-1,1]ⁿ`)
  so that the geometric hypothesis bundle is demonstrably satisfiable.
-/

open MeasureTheory
open scoped ENNReal

namespace Arlib.MarkovChains

variable {n : ℕ}

/-- **The local-conductance floor of the ball walk on a convex body with an inscribed
ball**, proved outright.

Assumed: `K` convex; `B(c,γ) ⊆ K` with `γ > 0`; `D` bounds the distance between any two
points of `K`; the step size satisfies `0 < δ ≤ γ`.  Nothing else — in particular no
measurability, no volume bound, and no isoperimetry.

Proved: `ell K δ x ≥ (γ/(γ+D))ⁿ` at *every* `x ∈ K`, where
`ell K δ x = vol(B(x,δ) ∩ K) / vol(B(x,δ))` is the probability that a ball-walk step from
`x` is accepted.  This is the `hell` hypothesis of `conductance_ballWalk_ge` and
`mixesWithin_lazy_ballWalk` at `θ = (γ/(γ+D))ⁿ`.

The witness is the ball `B(y, λγ)` with `λ = δ/(γ+D)` and `y = (1-λ)·x + λ·c`, which lies
in `B(x,δ) ∩ K`: in `K` by convexity (it is the image of `B(c,γ) ⊆ K` under the homothety
towards `x`), and in `B(x,δ)` because `λγ + λ·dist c x ≤ λ(γ+D) = δ`.  The constant is not
optimised; see the module docstring. -/
theorem le_ell_of_convex_of_ball_subset
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) :
    ∀ x ∈ K, ENNReal.ofReal ((γ / (γ + D)) ^ n) ≤ ell K δ x := by
  intro x hx
  have hcK : c ∈ K := hball (Metric.mem_ball_self hγ)
  have hD0 : 0 ≤ D := by simpa using hD x hx x hx
  set L : ℝ := γ + D with hL
  have hLpos : (0:ℝ) < L := by rw [hL]; linarith
  set lam : ℝ := δ / L with hlam
  have hlam0 : (0:ℝ) < lam := div_pos hδ hLpos
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hLpos, hL]; linarith
  have hlamL : lam * L = δ := by
    rw [hlam]; field_simp
  set y : EuclideanSpace ℝ (Fin n) := (1 - lam) • x + lam • c with hy
  have hyx : dist y x = lam * dist c x := by
    have hd : y - x = lam • (c - x) := by rw [hy]; module
    rw [dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, ← dist_eq_norm]
  have hsub : Metric.ball y (lam * γ) ⊆ Metric.ball x δ ∩ K := by
    intro z hz
    rw [Metric.mem_ball] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball]
      have h1 : dist c x ≤ D := hD c hcK x hx
      have h2 : lam * dist c x ≤ lam * D := by
        exact mul_le_mul_of_nonneg_left h1 hlam0.le
      calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ < lam * γ + lam * D := by rw [hyx]; linarith
        _ = δ := by rw [← hlamL, hL]; ring
    · have hw : c + lam⁻¹ • (z - y) ∈ Metric.ball c γ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have he : c + lam⁻¹ • (z - y) - c = lam⁻¹ • (z - y) := by module
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hlam0),
          ← dist_eq_norm, inv_mul_eq_div, div_lt_iff₀ hlam0]
        rw [mul_comm] at hz
        exact hz
      have hzeq : z = (1 - lam) • x + lam • (c + lam⁻¹ • (z - y)) := by
        rw [smul_add, smul_inv_smul₀ hlam0.ne', hy]; module
      rw [hzeq]
      exact hconv hx (hball hw) (by linarith) hlam0.le (by ring)
  have hbx0 : volume (Metric.ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hbxt : volume (Metric.ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hvy : volume (Metric.ball y (lam * γ))
      = ENNReal.ofReal ((lam * γ) ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) y
      (by positivity : (0:ℝ) < lam * γ)
    rwa [finrank_euclideanSpace_fin] at h
  have hvx : volume (Metric.ball x δ)
      = ENNReal.ofReal (δ ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x hδ
    rwa [finrank_euclideanSpace_fin] at h
  have hpow : (γ / L) ^ n * δ ^ n = (lam * γ) ^ n := by
    rw [← mul_pow]
    congr 1
    rw [hlam]; field_simp
  rw [ell_apply, ENNReal.le_div_iff_mul_le (Or.inl hbx0) (Or.inl hbxt)]
  calc ENNReal.ofReal ((γ / L) ^ n) * volume (Metric.ball x δ)
      = ENNReal.ofReal ((lam * γ) ^ n)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        rw [hvx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpow]
    _ = volume (Metric.ball y (lam * γ)) := hvy.symm
    _ ≤ volume (Metric.ball x δ ∩ K) := measure_mono hsub

/-- **A body of positive volume in dimension `≥ 1` has a positive diameter bound.**

Assumed: `1 ≤ n`, `volume K ≠ 0`, some `c ∈ K`, and `D` bounds all pairwise distances in
`K`.  Proved: `0 < D`.  This is what makes the isoperimetric constant `(1/2)ⁿ/D` of
`Arlib.uniformOn_iso_of_convex` positive, which the mixing theorem requires; if `D` were
`0` then `K ⊆ closedBall c 0`, a null set in dimension `≥ 1`. -/
theorem pos_of_diam_bound (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK0 : volume K ≠ 0)
    {c : EuclideanSpace ℝ (Fin n)} (hcK : c ∈ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) : 0 < D := by
  have hD0 : 0 ≤ D := by simpa using hD c hcK c hcK
  rcases hD0.lt_or_eq with h | h
  · exact h
  exfalso
  apply hK0
  have hsub : K ⊆ Metric.closedBall c D := by
    intro z hz
    simpa [Metric.mem_closedBall] using hD z hz c hcK
  have hmono := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub
  rw [Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin n))) c hD0,
    finrank_euclideanSpace_fin, ← h, zero_pow (by omega : n ≠ 0)] at hmono
  simpa using hmono

/-- **An unconditional conductance bound for the ball walk on a bounded convex body with
an inscribed ball.**

Assumed: only geometry and measure-theoretic regularity of `K` — measurable, convex, of
positive finite volume, all pairwise distances bounded by `D`, containing a ball
`B(c,γ)` with `0 < δ ≤ γ`, and `1 ≤ n`.  **No isoperimetric inequality and no local
conductance bound is assumed**: the former is supplied by `Arlib.uniformOn_iso_of_convex`
at `κ = (1/2)ⁿ/D`, the latter by `le_ell_of_convex_of_ball_subset` at `θ = (γ/(γ+D))ⁿ`.

Proved: the conductance of `ballWalk K δ` with respect to its own stationary measure
`Arlib.uniformOn volume K` is at least `min (θ/16) (κ·θ²·δ/n / 64)`.  Both constants are
exponentially small in `n`; see the module docstring. -/
theorem conductance_ballWalk_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) :
    min (ENNReal.ofReal ((γ / (γ + D)) ^ n) / 16)
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ n / D)
          * ENNReal.ofReal (((γ / (γ + D)) ^ n) ^ 2 * δ / (n : ℝ)) / 64)
      ≤ conductance (ballWalk K δ) (Arlib.uniformOn volume K) := by
  have hcK : c ∈ K := hball (Metric.mem_ball_self hγ)
  have hDpos : 0 < D := pos_of_diam_bound hn hK0 hcK hD
  refine conductance_ballWalk_ge hn hK hK0 hKtop hδ
    (θ := (γ / (γ + D)) ^ n) (by positivity)
    (le_ell_of_convex_of_ball_subset hconv hγ hball hD hδ hδγ)
    (kappa := ENNReal.ofReal ((1 / 2 : ℝ) ^ n / D)) ?_
  exact Arlib.uniformOn_iso_of_convex hconv hK hK0 hKtop hD

/-- **Unconditional total-variation mixing of the lazy ball walk on a bounded convex body
with an inscribed ball.**  The capstone of this file.

Assumed: `1 ≤ n`; `K` measurable, convex, of positive finite volume, with all pairwise
distances bounded by `D` and containing a ball `B(c,γ)`; a step size `0 < δ ≤ γ`; an
`M`-warm start `mu0` with `1 ≤ M`; an accuracy `eps > 0`; and enough steps `t`.
**There is no `hiso` and no `hell` hypothesis** — the isoperimetric inequality is
discharged by `Arlib.uniformOn_iso_of_convex` and the local-conductance floor by
`le_ell_of_convex_of_ball_subset`, both inside the proof.

Proved: after `t` steps the law of the lazy ball walk started from `mu0` is within `eps`
in total variation of `Arlib.uniformOn volume K`.  That target is *exactly* the stationary
measure of `ballWalk K δ` (`isReversible_ballWalk`, `invariant_ballWalk`), so there is no
residual bias term in the conclusion: the only error is `eps`.

The step count is exponential in `n`; see the module docstring.  The remaining hypotheses
`hwarm` and `ht` are not geometric, and `exists_unconditional_mixing_convex` (and, with a
concrete body, `exists_unconditional_mixing_convex_unitBall`) discharges them. -/
theorem mixesWithin_lazy_ballWalk_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume K))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min ((γ / (γ + D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / D * ((γ / (γ + D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) mu0 t (ENNReal.ofReal eps) := by
  have hcK : c ∈ K := hball (Metric.mem_ball_self hγ)
  have hDpos : 0 < D := pos_of_diam_bound hn hK0 hcK hD
  refine mixesWithin_lazy_ballWalk hn hK hK0 hKtop hδ
    (θ := (γ / (γ + D)) ^ n) (by positivity)
    (le_ell_of_convex_of_ball_subset hconv hγ hball hD hδ hδγ)
    (kappa := (1 / 2 : ℝ) ^ n / D) (by positivity) ?_ hM hwarm heps ht
  exact Arlib.uniformOn_iso_of_convex hconv hK hK0 hKtop hD

/-- **Non-vacuity, general form** (`CLAUDE.md` §11).

`mixesWithin_lazy_ballWalk_convex` still carries `hwarm` and `ht`; a theorem whose
remaining hypotheses were unsatisfiable would be worthless.  They are not: the stationary
measure is a `1`-warm start for itself, and the step count is a natural number.

Assumed: exactly the geometric hypotheses on `K` and `δ`, plus `eps > 0`.  Proved: an
actual starting law and step count exist for which the mixing conclusion holds. -/
theorem exists_unconditional_mixing_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      MixesWithin (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) mu0 t
        (ENNReal.ofReal eps) := by
  haveI hprob : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  refine ⟨Arlib.uniformOn volume K, hprob,
    conductanceMixingTime 1
      (min ((γ / (γ + D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / D * ((γ / (γ + D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps, ?_⟩
  refine mixesWithin_lazy_ballWalk_convex hn hK hconv hK0 hKtop hD hγ hball hδ hδγ
    (M := 1) le_rfl ?_ heps le_rfl
  simp only [ENNReal.ofReal_one]
  exact isWarm_one_self (Arlib.uniformOn volume K)

/-- **The convex-body theorem, instantiated on the unit ball** (`c = 0`, `γ = 1`, `D = 2`),
so that its geometric hypothesis bundle is demonstrably satisfiable by a real body, and so
that its constants can be compared with the direct route.

Assumed: `1 ≤ n`, `0 < δ ≤ 1`, an `M`-warm start, `eps > 0`, enough steps.  No geometry.

Proved: the same total-variation conclusion as
`mixesWithin_lazy_ballWalk_unitBall_uncond`, but reached through the general convex-body
theorem.  The constants are *weaker* than the direct route's, as expected: here
`θ = (1/3)ⁿ` versus `(1/2)ⁿ` there, and `κ = (1/2)ⁿ/2` versus `(1/2)ⁿ⁺¹` there — the latter
two agree, and the `θ` gap is the price of `le_ell_of_convex_of_ball_subset`'s unoptimised
constant. -/
theorem mixesWithin_lazy_ballWalk_unitBall_convexRoute (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (((1:ℝ) / 3) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / 2 * (((1:ℝ) / 3) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) mu0 t
      (ENNReal.ofReal eps) := by
  have hdiam : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, dist x y ≤ (2:ℝ) := by
    intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    have := dist_triangle x (0 : EuclideanSpace ℝ (Fin n)) y
    rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) y] at this
    linarith
  refine mixesWithin_lazy_ballWalk_convex hn measurableSet_ball (convex_ball _ _)
    volume_unitBall_ne_zero volume_unitBall_ne_top (D := 2) hdiam (c := 0) (γ := 1)
    one_pos subset_rfl hδ hδ1 hM hwarm heps ?_
  rw [show ((1:ℝ) / (1 + 2)) = 1 / 3 by norm_num]
  exact ht

/-- **Non-vacuity with a concrete body** (`CLAUDE.md` §11).

Assumed: `1 ≤ n`, `0 < δ ≤ 1`, `eps > 0`.  Nothing else — the body is the fixed set
`Metric.ball 0 1` and every hypothesis of `mixesWithin_lazy_ballWalk_convex` is discharged
for it.  Proved: a starting law and a step count exist for which the lazy ball walk on the
unit ball mixes to within `eps`.  This exhibits a fully unconditional mixing statement
obtained through the *general convex-body* route: no isoperimetry assumed, no local
conductance assumed, no warm start assumed, and no property of the body assumed. -/
theorem exists_unconditional_mixing_convex_unitBall (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) mu0 t
        (ENNReal.ofReal eps) := by
  have hdiam : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, dist x y ≤ (2:ℝ) := by
    intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    have := dist_triangle x (0 : EuclideanSpace ℝ (Fin n)) y
    rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) y] at this
    linarith
  exact exists_unconditional_mixing_convex hn measurableSet_ball (convex_ball _ _)
    volume_unitBall_ne_zero volume_unitBall_ne_top hdiam (c := 0) (γ := 1) one_pos
    subset_rfl hδ hδ1 heps

/-- **A set containing a ball of positive radius has positive volume.**  Assumed:
`B(c,γ) ⊆ K` with `γ > 0`.  Proved: `volume K ≠ 0`.  Lets the polytope corollary below
avoid a separate volume hypothesis. -/
theorem volume_ne_zero_of_ball_subset {K : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hball : Metric.ball c γ ⊆ K) :
    volume K ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume c hγ) (measure_mono hball))

/-- **A set of bounded diameter has finite volume.**  Assumed: `c ∈ K` and `D` bounds all
pairwise distances in `K`.  Proved: `volume K ≠ ⊤`, since `K ⊆ closedBall c D`. -/
theorem volume_ne_top_of_diam_bound {K : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} (hcK : c ∈ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) : volume K ≠ ⊤ := by
  have hsub : K ⊆ Metric.closedBall c D := fun z hz => by
    simpa [Metric.mem_closedBall] using hD z hz c hcK
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) measure_closedBall_lt_top)

/-- **Unconditional mixing of the lazy ball walk on an inflated polytope.**

This is `mixesWithin_lazy_ballWalk_convex` specialised to `Arlib.Polytope.inflate A b κ`,
the Kannan–Vempala inflated polytope that the downstream sampling oracle actually
receives.  Convexity and measurability come from `Arlib.Polytope.convex_inflate` and
`Arlib.Polytope.measurableSet_inflate`, and the volume hypotheses are derived from the
diameter bound and the inscribed ball, so the caller supplies neither.  (For the
un-inflated polytope use `κ = 0` and `Arlib.Polytope.inflate_zero`.)

Assumed: `1 ≤ n`; the polytope has all pairwise distances bounded by `D` and contains a
ball `B(c,γ)`; `0 < δ ≤ γ`; an `M`-warm start; `eps > 0`; enough steps.  No isoperimetry
and no local-conductance hypothesis.  Note that boundedness and the inscribed ball are
*hypotheses about the family `A, b, κ`*, not consequences of it — an unbounded or
lower-dimensional polytope simply does not satisfy them;
`exists_unconditional_mixing_polytope` shows they are satisfiable.

Proved: total-variation mixing to `Arlib.uniformOn volume (Arlib.Polytope.inflate A b κ)`,
which is exactly the walk's stationary measure.  The step count is exponential in `n`. -/
theorem mixesWithin_lazy_ballWalk_polytope {ι : Type*} (hn : 1 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ)
    {D : ℝ} (hD : ∀ x ∈ Arlib.Polytope.inflate A b κ,
      ∀ y ∈ Arlib.Polytope.inflate A b κ, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ Arlib.Polytope.inflate A b κ)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn volume (Arlib.Polytope.inflate A b κ)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min ((γ / (γ + D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / D * ((γ / (γ + D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (Arlib.Polytope.inflate A b κ) δ))
      (Arlib.uniformOn volume (Arlib.Polytope.inflate A b κ)) mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_lazy_ballWalk_convex hn (Arlib.Polytope.measurableSet_inflate A b κ)
    (Arlib.Polytope.convex_inflate A b κ)
    (volume_ne_zero_of_ball_subset hγ hball)
    (volume_ne_top_of_diam_bound (hball (Metric.mem_ball_self hγ)) hD)
    hD hγ hball hδ hδγ hM hwarm heps ht

/-- **Non-vacuity of the polytope form** (`CLAUDE.md` §11): the cube `[-1,1]ⁿ`.

`mixesWithin_lazy_ballWalk_polytope` assumes the polytope is bounded and contains a ball;
neither follows from the shape of `A`, `b`, `κ`, so a witness is required or the corollary
could be vacuous.  Here it is: the `2n` constraints `±xᵢ ≤ 1`, i.e. `A` ranging over
`±eᵢ` indexed by `Fin n × Bool` with `b ≡ 1` and `κ = 0`, cut out the cube `[-1,1]ⁿ`, which
contains `B(0,1)` and has diameter at most `2√n`.

Assumed: `1 ≤ n`, `0 < δ ≤ 1`, `eps > 0`.  Proved: an explicit finite constraint family, a
starting law and a step count exist such that the unit ball is contained in the resulting
polytope and the lazy ball walk on it mixes to within `eps`.  The `⊆` conjunct is part of
the statement precisely so that the witness cannot be a degenerate or empty polytope. -/
theorem exists_unconditional_mixing_polytope (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ (ι : Type) (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
      (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ Arlib.Polytope.inflate A b 0 ∧
      MixesWithin (lazy (ballWalk (Arlib.Polytope.inflate A b 0) δ))
        (Arlib.uniformOn volume (Arlib.Polytope.inflate A b 0)) mu0 t (ENNReal.ofReal eps) := by
  classical
  set A : Fin n × Bool → EuclideanSpace ℝ (Fin n) :=
    fun p => if p.2 then EuclideanSpace.single p.1 (1:ℝ)
      else -EuclideanSpace.single p.1 (1:ℝ) with hA
  set b : Fin n × Bool → ℝ := fun _ => 1 with hb
  -- membership in the cube, both directions
  have hin : ∀ x : EuclideanSpace ℝ (Fin n),
      (∀ i, |x i| ≤ 1) → x ∈ Arlib.Polytope.inflate A b 0 := by
    intro x hx
    rw [Arlib.Polytope.mem_inflate]
    rintro ⟨i, s⟩
    have hxi := abs_le.1 (hx i)
    cases s <;>
      simp [hA, hb, EuclideanSpace.inner_single_left, inner_neg_left] <;> linarith [hxi.1, hxi.2]
  have hout : ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ Arlib.Polytope.inflate A b 0 → ∀ i, |x i| ≤ 1 := by
    intro x hx i
    have h1 := hx (i, true)
    have h2 := hx (i, false)
    simp [hA, hb, EuclideanSpace.inner_single_left, inner_neg_left] at h1 h2
    exact abs_le.2 ⟨by linarith, h1⟩
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ Arlib.Polytope.inflate A b 0 := by
    intro x hx
    have hxn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    refine hin x fun i => ?_
    have := PiLp.norm_apply_le (p := 2) x i
    rw [Real.norm_eq_abs] at this
    linarith
  have hD : ∀ x ∈ Arlib.Polytope.inflate A b 0, ∀ y ∈ Arlib.Polytope.inflate A b 0,
      dist x y ≤ 2 * Real.sqrt (n : ℝ) := by
    intro x hx y hy
    have hxi := hout x hx
    have hyi := hout y hy
    rw [EuclideanSpace.dist_eq]
    have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ 4 * (n : ℝ) := by
      have hle : ∀ i ∈ Finset.univ, dist (x i) (y i) ^ 2 ≤ (4:ℝ) := by
        intro i _
        have h1 := abs_le.1 (hxi i)
        have h2 := abs_le.1 (hyi i)
        have : dist (x i) (y i) = |x i - y i| := Real.dist_eq _ _
        rw [this, sq_abs]
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, (4:ℝ) := Finset.sum_le_sum hle
        _ = 4 * (n : ℝ) := by simp [mul_comm]
    calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (4 * (n:ℝ)) :=
          Real.sqrt_le_sqrt hsum
      _ = 2 * Real.sqrt (n : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show Real.sqrt 4 = 2 by
              rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
  obtain ⟨mu0, hprob, t, hmix⟩ := exists_unconditional_mixing_convex hn
    (Arlib.Polytope.measurableSet_inflate A b 0) (Arlib.Polytope.convex_inflate A b 0)
    (volume_ne_zero_of_ball_subset one_pos hball)
    (volume_ne_top_of_diam_bound (hball (Metric.mem_ball_self one_pos)) hD)
    hD one_pos hball hδ hδ1 heps
  exact ⟨Fin n × Bool, A, b, mu0, hprob, t, hball, hmix⟩

/-! ### Axiom audit

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms le_ell_of_convex_of_ball_subset
#print axioms pos_of_diam_bound
#print axioms conductance_ballWalk_convex
#print axioms mixesWithin_lazy_ballWalk_convex
#print axioms exists_unconditional_mixing_convex
#print axioms mixesWithin_lazy_ballWalk_unitBall_convexRoute
#print axioms exists_unconditional_mixing_convex_unitBall
#print axioms volume_ne_zero_of_ball_subset
#print axioms volume_ne_top_of_diam_bound
#print axioms mixesWithin_lazy_ballWalk_polytope
#print axioms exists_unconditional_mixing_polytope

end Arlib.MarkovChains
