/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoBall
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance

/-!
# The first unconditional instance of the mixing chain

Every quantitative theorem in this development's Markov-chain stack —
`Arlib.MarkovChains.conductance_ballWalk_ge`, `Arlib.MarkovChains.cheeger`,
`Arlib.MarkovChains.mixesWithin_of_conductance`,
`Arlib.MarkovChains.mixesWithin_lazy_ballWalk` — carries an isoperimetric inequality
`hiso` as an *inline hypothesis*.  None of them proves one.  For as long as that was true
the whole chain was conditional: a stack of true implications with nothing established to
feed them.

`Arlib.uniformOn_iso_unitBall` (`Arlib/Convexity/IsoBall.lean`) closes that, for the
Euclidean unit ball, at `κ = (1/2)^(n+1)`, with no hypotheses at all.  This file composes
it with the rest of the stack.  The results below assume **no geometric hypothesis
whatsoever** — only that the walk is run from a warm start for enough steps.

## The honest scope, which is not the polynomial-time result

`κ = 2^(n+1)⁻¹` is *exponentially small in the dimension*, so the conductance bound
`min (θ/16) (κ·θ²·δ/n / 64)` obtained here is exponentially small too, and the mixing time
it feeds into is exponentially large in `n`.  **This is not a polynomial-time sampler and
must not be quoted as one.**

What it is: the first statement in this development where the isoperimetry, the local
conductance, the Cheeger inequality, the `L²` decay and the total-variation bound are all
*discharged simultaneously* rather than assumed.  A weak constant proved unconditionally
settles something a sharp constant assumed for all bodies cannot — that the four theorems
actually compose, and that their joint hypotheses are satisfiable by a real body.

The route to a polynomial constant is unchanged and still open: it is the localization
argument, whose remaining obstruction is recorded as (P1) in
`Arlib/Convexity/PositionalCut.lean`.  `Arlib.uniformOn_iso_of_convex` gives `κ = 2⁻ⁿ/D`
for *every* bounded convex body by an elementary chord argument that deliberately does not
touch that obstruction; `Arlib.uniformOn_dyerFrieze_dim_one` gives the sharp `κ = 2/D`, but
only in dimension one.

## Main results

* `Arlib.MarkovChains.conductance_ballWalk_unitBall` — an unconditional lower bound on the
  conductance of the ball walk on `Metric.ball 0 1`.
* `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_unitBall_uncond` — unconditional
  total-variation mixing of the lazy ball walk to `Arlib.uniformOn volume (Metric.ball 0 1)`,
  which by `Arlib.MarkovChains.isReversible_ballWalk` is *exactly* its stationary measure —
  there is no approximation in the target.
* `Arlib.MarkovChains.exists_unconditional_mixing_unitBall` — a non-vacuity witness
  (`CLAUDE.md` §11): an actual starting law and step count for which the conclusion holds,
  so the theorem above is not a statement about an unsatisfiable warm start.

  **It is a degenerate witness, and an earlier revision of this docstring advertised it as
  *the* non-vacuity check without saying so.** It discharges the warm start with
  `isWarm_one_self`, i.e. it takes `mu0` to be the walk's *own stationary measure* at
  `M = 1`. A chain started at stationarity is already mixed, so `MixesWithin` holds at every
  `t` for reasons having nothing to do with conductance, isoperimetry, or anything else this
  file composes. It establishes that the hypothesis bundle is inhabited — a real and
  necessary check — and establishes **nothing** about the conclusion.

  This is the failure mode where a bundle is non-vacuous yet *forced*: the witness meets the
  hypotheses only by collapsing the very quantity the theorem is about. `#print axioms` is
  blind to it, because nothing is ever *assumed* — the degeneracy lives in *which objects*
  satisfy the hypotheses.

  **Use `Arlib.MarkovChains.exists_unconditional_mixing_unitBall_nonstationary`**
  (`Arlib/MarkovChains/Continuous/WarmStart.lean`) instead. It starts from the uniform law
  on the half-radius ball, which is `2ⁿ`-warm and **provably not** the stationary measure —
  `mu0 ≠ π` is a conjunct *inside* the existential, so that witness cannot be satisfied by
  the stationary measure. Its content is a strict superset of this one's.

  The general lesson, worth applying to every witness in this development: exhibiting *some*
  inhabitant is not enough, because the extremal "ideal" instance satisfies almost anything
  and is both the easiest to construct and the worst possible choice. The mechanical form of
  the check is a *pair* — two structurally different inhabitants differing in the parameter
  in question — since that proves the parameter is not forced without anyone having to guess
  in advance which parameter to care about.
-/

open MeasureTheory
open scoped ENNReal

namespace Arlib.MarkovChains

/-- A rewriting of `((1:ℝ)/2)^n` into the form `ofReal_le_ell_unitBall` produces.  Kept
separate because both forms occur in the surrounding API and `norm_num` cannot bridge them
under a binder. -/
theorem one_div_two_pow_eq (n : ℕ) : ((1:ℝ)/2) ^ n = (1:ℝ)/2 ^ n := by
  rw [div_pow]; norm_num

/-- **The local-conductance hypothesis of the ball walk, discharged on the unit ball.**
`ofReal_le_ell_unitBall` in the shape `conductance_ballWalk_ge` and
`mixesWithin_lazy_ballWalk` expect: `θ = 1/2ⁿ` works for every `δ ∈ (0, 1]`. -/
theorem ofReal_le_ell_unitBall' {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ENNReal.ofReal ((1:ℝ)/2 ^ n) ≤ ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x := by
  intro x hx
  have h := ofReal_le_ell_unitBall hδ hδ1 hx
  rwa [one_div_two_pow_eq] at h

/-- **An unconditional conductance bound for the ball walk on the unit ball.**

Both hypotheses that `conductance_ballWalk_ge` leaves open are discharged here: the
isoperimetric inequality by `Arlib.uniformOn_iso_unitBall` (at `κ = (1/2)^(n+1)`) and the
local-conductance floor by `ofReal_le_ell_unitBall'` (at `θ = 1/2ⁿ`).  Nothing is assumed
about the body — it is a fixed, explicit set.

The bound is exponentially small in `n`; see the module docstring. -/
theorem conductance_ballWalk_unitBall (n : ℕ) (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    min (ENNReal.ofReal ((1:ℝ)/2 ^ n) / 16)
      (ENNReal.ofReal ((1/2:ℝ) ^ (n+1))
        * ENNReal.ofReal ((((1:ℝ)/2 ^ n)) ^ 2 * δ / (n : ℝ)) / 64)
      ≤ conductance (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
          (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  conductance_ballWalk_ge hn measurableSet_ball
    (ne_of_gt (Metric.measure_ball_pos volume _ one_pos)) (ne_of_lt measure_ball_lt_top) hδ
    (θ := (1:ℝ)/2 ^ n) (by positivity) (ofReal_le_ell_unitBall' hδ hδ1)
    (kappa := ENNReal.ofReal ((1/2:ℝ) ^ (n+1))) (Arlib.uniformOn_iso_unitBall n)

/-- **Unconditional total-variation mixing of the lazy ball walk on the unit ball.**

The target `Arlib.uniformOn volume (Metric.ball 0 1)` is *exactly* the stationary measure
of `ballWalk` (`isReversible_ballWalk`, `invariant_ballWalk`), so unlike the speedy-walk
route of `SpeedyToUniform.lean` there is no residual bias term in the conclusion: the only
error is `eps`, and it decays with the step count.

Remaining hypotheses are `hwarm` (the start is `M`-warm) and `ht` (enough steps).  Neither
is geometric; `exists_unconditional_mixing_unitBall` discharges both on a concrete instance.

The step count is exponential in `n`; see the module docstring. -/
theorem mixesWithin_lazy_ballWalk_unitBall_uncond (n : ℕ) (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (((1:ℝ)/2 ^ n) / 32)
        ((1/2:ℝ) ^ (n+1) * ((1:ℝ)/2 ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) mu0 t
      (ENNReal.ofReal eps) :=
  mixesWithin_lazy_ballWalk hn measurableSet_ball
    (ne_of_gt (Metric.measure_ball_pos volume _ one_pos)) (ne_of_lt measure_ball_lt_top) hδ
    (θ := (1:ℝ)/2 ^ n) (by positivity) (ofReal_le_ell_unitBall' hδ hδ1)
    (kappa := (1/2:ℝ) ^ (n+1)) (by positivity) (Arlib.uniformOn_iso_unitBall n)
    hM hwarm heps ht

/-- **Every measure is `1`-warm with respect to itself.**  The witness's warm start. -/
theorem isWarm_one_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    IsWarm 1 μ μ := fun S _ => by simp

/-- **Non-vacuity** (`CLAUDE.md` §11).  `mixesWithin_lazy_ballWalk_unitBall_uncond` still
carries `hwarm` and `ht`; a theorem whose remaining hypotheses were unsatisfiable would be
worthless.  They are not: the stationary measure itself is a `1`-warm start, and the step
count is a natural number, so the conclusion genuinely holds for a concrete instance.

This exhibits a fully unconditional mixing statement — no isoperimetry assumed, no local
conductance assumed, no warm start assumed. -/
theorem exists_unconditional_mixing_unitBall (n : ℕ) (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
        (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) mu0 t
        (ENNReal.ofReal eps) := by
  haveI hprob : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top
  refine ⟨Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1), hprob,
    conductanceMixingTime 1
      (min (((1:ℝ)/2 ^ n) / 32)
        ((1/2:ℝ) ^ (n+1) * ((1:ℝ)/2 ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps, ?_⟩
  refine mixesWithin_lazy_ballWalk_unitBall_uncond n hn hδ hδ1 (M := 1) le_rfl ?_ heps le_rfl
  simp only [ENNReal.ofReal_one]
  exact isWarm_one_self
    (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))

end Arlib.MarkovChains
