/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance

/-!
# The speedy walk on a convex body

Cousins-Vempala (`../gaussian-cooling-vempala/vol3_journal.tex:829`) analyse not the ball walk
itself but the **speedy walk**: the subsequence of *proper* steps of the ball walk, i.e.
"from `x`, resample uniformly from `x + delta*B` until the sample lands in `K`".
Equivalently, the one-step distribution from `x` is the uniform measure on
`B(x, delta) ∩ K` rather than the uniform measure on `B(x, delta)` with the rejected mass
returned to `x`.

The point of the change is the **stationary measure**.  The ball walk is reversible for the
*uniform* measure on `K`; the speedy walk is reversible for the measure with density
proportional to the local conductance `ell`.  That reweighting is what removes the
`hell : ∀ x ∈ K, theta ≤ ell K delta x` hypothesis of
`Arlib.MarkovChains.conductance_ballWalk_ge`, whose only proved witness `theta = 2⁻ⁿ`
(`ofReal_le_ell_unitBall`) certifies an exponential step count.

## Main definitions

* `Arlib.MarkovChains.speedyWalk K delta` — the speedy-walk kernel.  On a measurable `K` it
  is `(vol(B(x,delta) ∩ K))⁻¹ • volume.restrict (B(x,delta) ∩ K)` plus an atom at `x`
  carrying mass `1` exactly when `B(x,delta) ∩ K` is null (so that the kernel is Markov
  everywhere, including at points from which the walk can never move).
* `Arlib.MarkovChains.ellMeasure K delta` — the unnormalised **`ell`-weighted measure**
  `(volume.restrict K).withDensity (ell K delta)`, i.e. `ell(x) dx` on `K`.
* `Arlib.MarkovChains.ellProb K delta` — its normalisation to a probability measure.

## Main results

* `Arlib.MarkovChains.isMarkovKernel_speedyWalk` — the speedy walk is a Markov kernel.
* `Arlib.MarkovChains.ell_mul_speedyWalk` — the crux identity
  `ell(x) * P_x(T) = vol(B(x,delta))⁻¹ * vol(T ∩ K ∩ B(x,delta))`, unconditionally.  The
  `ell(x)` of the weight cancels the `ell(x)` in the denominator of the kernel, leaving the
  *symmetric* ball kernel; this is the whole content of the next item.
* `Arlib.MarkovChains.isReversible_speedyWalk`,
  `Arlib.MarkovChains.isReversible_speedyWalk_prob`,
  `Arlib.MarkovChains.invariant_speedyWalk` — **detailed balance for the `ell`-weighted
  measure**, and hence its invariance.  This is the hypothesis `Cheeger.lean` and
  `L2Mixing.lean` consume.
* `Arlib.MarkovChains.image_homothety_subset_of_convex`,
  `Arlib.MarkovChains.volume_inter_ball_le_of_convex` — the **multiplicative overlap
  estimate** for a convex body: the homothety of ratio `1 - ‖u-v‖/delta` centred at the
  midpoint of `u` and `v` maps `B(u,delta) ∩ K` into `B(u,delta) ∩ K ∩ B(v,delta)`, whence
  `vol(B(u,delta) ∩ K) ≤ vol(B(u,delta) ∩ K ∩ B(v,delta)) + (n‖u-v‖/delta)·vol(B(u,delta) ∩ K)`.
* `Arlib.MarkovChains.one_le_speedyWalk_add_speedyWalk_compl` — **the one-step overlap bound
  with no local-conductance hypothesis at all**:
  `1 ≤ P_u(T) + P_v(Tᶜ) + n‖u-v‖/delta` for `u, v ∈ K`.  Contrast
  `ell_le_ballWalk_add_ballWalk_compl`, whose left-hand side is `ell(u)`.
* `Arlib.MarkovChains.lt_dist_of_speedyWalk_lt` — separation `delta/(2n)` from an absolute
  `1/4` threshold, where `lt_dist_of_ballWalk_lt` needs `theta/4`.
* `Arlib.MarkovChains.ellMeasure_univ_ne_zero`,
  `Arlib.MarkovChains.exists_smallSet_of_absolutelyContinuous` — the non-degeneracy the
  mixing theorem needs, for a target measure that is *not* uniform.
* `Arlib.MarkovChains.conductance_speedyWalk_ge` — the conductance bound, with **no `hell`**:
  `Φ ≥ min(1/16, kappa*delta/(128*n))` given an isoperimetric inequality for `ellProb K delta`.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk` and its unit-ball instance — the mixing
  consequence, in `conductanceMixingTime M (min (1/32) (kappa*delta/(256 n))) eps` steps.

## What the reweighting buys, precisely

`conductance_ballWalk_ge` needs `ell(u) ≥ theta` at every `u ∈ K` because its overlap bound
reads `ell(u) ≤ P_u(T) + P_v(Tᶜ) + n‖u-v‖/(2 delta)`: a body with a sharp corner has points
of tiny `ell`, and there the *uniform* ball walk really does move rarely.  For the speedy
walk the one-step distribution is normalised by `vol(B(u,delta) ∩ K) = ell(u)·vol(delta Bₙ)`,
so the same geometry gives `1 ≤ P_u(T) + P_v(Tᶜ) + n‖u-v‖/delta` — a **constant** on the
left.  So `theta` does not become `3/4`: it **disappears from the statement**, and the
certified conductance `min(1/16, kappa*delta/(128 n))` is polynomial in `n` whenever `kappa`
and `delta` are.

Two inputs make this work and both are recorded honestly:

1. **Convexity of `K`** (`hconv : Convex ℝ K`) is now used, where `conductance_ballWalk_ge`
   used none.  It is what turns the additive midpoint estimate
   `volume_ball_le_volume_inter_ball_add` (a loss of `n t/(2 delta)` *of the whole ball*)
   into the multiplicative `volume_inter_ball_le_of_convex` (a loss of `n t/delta` *of
   `B(u,delta) ∩ K`*).  Without convexity the speedy walk gains nothing: the additive
   estimate leaves `ell(u)` on the left exactly as before.  This is the elementary stand-in
   for Lemma 3.5 of [KLS95] that `vol3_journal.tex:592` invokes; it costs the same one
   factor of `√n` already recorded as caveat 1 of `BallWalkConductance.lean`.
2. **The target measure is `ellProb K delta`, not the uniform measure on `K`.**  See the
   next section — this is the price, and it is not negotiable.

## The target measure: read this before composing with anything

The speedy walk's stationary distribution is `ellProb K delta`, the law with density
proportional to `ell` on `K`.  It is **not** `Arlib.uniformOn volume K`, and it is not the
uniform measure on any subset of `K` either.  Consequently:

* `Arlib.PointwiseRoute.theorem2_of_mixesWithin` — and therefore Kannan-Vempala Theorem 2 as
  formalised in this library — is stated for the *uniform* measure on `K`, and **nothing in
  this file composes with it.**  There is deliberately no `theorem2_of_lazy_speedyWalk`
  here: writing one would require a bridge from `ellProb K delta` to
  `Arlib.uniformOn volume K` that is not proved.
* Cousins-Vempala recover uniform samples from the speedy walk through the holding-time
  correspondence (the ball walk is the speedy walk with each state held a `Geom(ell(x))`
  number of steps, and `(density ∝ ell) × (mean holding time 1/ell) = uniform`).  That
  correspondence is **not formalised here**, and it is the one remaining structural gap
  between this file and a uniform sampler on `K`.
* `ellMeasure_le_volume_inter` and `ellMeasure_add_volume_le` quantify the gap
  unconditionally and without division: the density of `ellMeasure K delta` relative to
  Lebesgue measure on `K` is at most `1`, and its *local* deficit on any `S` is at most its
  *global* deficit `vol(K) - ∫_K ell`.  Under `Arlib.MarkovChains.IsSmooth K delta s` that
  global deficit is at most `s·vol(K)`, from which `ellProb K delta` and
  `Arlib.uniformOn volume K` are within `s/(1-s)` in total variation — an arithmetic step
  that is **not carried out in Lean here**, so no theorem below claims it.

`SpeedyPoints K delta = {x | 3/4 ≤ ell K delta x}` plays **no role** in any theorem below.
`three_quarters_le_ell_of_mem_speedyPoints` records that `ell ≥ 3/4` is free there — it is
literally the definition — but nothing consumes it, because the results need no lower bound
on `ell` at all.  This is deliberate: `K ⊆ SpeedyPoints K delta` is vacuous for a bounded `K`
(a supporting hyperplane at a boundary point forces `ell ≤ 1/2` there; that fact is *not*
formalised in this file), and restricting the walk to `K' = K ∩ SpeedyPoints K delta` only
moves the problem, since the overlap estimate for a walk living on `K'` would need
`K' ⊆ SpeedyPoints K' delta`, vacuous for the same reason.  The escape is not to restrict
the state space; it is the multiplicative overlap estimate of item 1 above.

## Scope: what is deliberately absent

There is **no `def`, `structure` or named `Prop` in this file asserting an isoperimetric
inequality, a conductance bound, a mixing bound, or a bound on `vol(K \ K')`.**  Every such
input is an inline `∀`-hypothesis of the theorem that consumes it.  The only `def`s are
`StuckPoints`, `speedyWalkAux`, `speedyWalk`, `ellMeasure` and `ellProb`, all plain
constructions.  There is no theorem here about the uniform measure on `K`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. Points the speedy walk cannot leave

A point `x` with `vol(B(x,δ) ∩ K) = 0` proposes only rejected points, so the speedy walk —
which is the ball walk conditioned on proposing an accepted point — is undefined there.  The
kernel below parks such a point at itself.  These are exactly the points of `ell = 0`, and
they carry no `ell`-weight, so they are invisible to every statement about the stationary
measure. -/

/-- The points from which the speedy walk cannot move: `vol(B(x,δ) ∩ K) = 0`, equivalently
`ell K δ x = 0` (`mem_stuckPoints_iff`).  A plain definition; nothing is asserted about how
big this set is. -/
def StuckPoints (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := {x | ell K δ x = 0}

/-- **`ell` vanishes exactly where the proposal never lands in `K`.**  Unconditional: when
`δ ≤ 0` the proposal ball is empty and both sides hold. -/
theorem mem_stuckPoints_iff {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ StuckPoints K δ ↔ volume (Metric.ball x δ ∩ K) = 0 := by
  rw [StuckPoints, Set.mem_setOf_eq, ell_apply, ENNReal.div_eq_zero_iff]
  simp [measure_ball_lt_top.ne]

/-- `StuckPoints K δ` is measurable when `K` is: it is a level set of `ell K δ`. -/
theorem measurableSet_stuckPoints {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : MeasurableSet (StuckPoints K δ) :=
  (measurable_ell hK δ) (measurableSet_singleton 0)

/-- **The `ell`-weight annihilates the stuck points.**  This is why the holding atom of the
speedy walk never appears in any flow computation. -/
theorem ell_mul_stuck_indicator (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (c : ℝ≥0∞) :
    ell K δ x * ((StuckPoints K δ).indicator (fun _ => c) x) = 0 := by
  by_cases hx : x ∈ StuckPoints K δ
  · rw [show ell K δ x = 0 from hx, zero_mul]
  · rw [Set.indicator_of_notMem hx, mul_zero]

/-! ## 2. The kernel -/

/-- **The speedy walk on a measurable `K`.**  From `x`, the measure

    (vol(B(x,δ) ∩ K))⁻¹ • volume.restrict (B(x,δ) ∩ K)  +  1[x stuck] • dirac x

is the uniform distribution on the accepted part of the proposal ball — the ball walk
conditioned on making a proper step — with a holding atom at the points where that
conditioning is undefined.  `speedyWalk` is the version that does not carry the
measurability proof; use that one. -/
noncomputable def speedyWalkAux (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (δ : ℝ) : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun x := (volume (Metric.ball x δ ∩ K))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
      + (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hden : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
        (volume (Metric.ball x δ ∩ K))⁻¹ := by
      have h : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          volume (Metric.ball x δ ∩ K) := by
        simpa [Set.inter_comm] using measurable_volume_inter_ball hK δ
      exact h.inv
    have hnum : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
        volume ((t ∩ K) ∩ Metric.ball x δ) := measurable_volume_inter_ball (ht.inter hK) δ
    have hrw : ∀ x : EuclideanSpace ℝ (Fin n),
        ((volume (Metric.ball x δ ∩ K))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
            + (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x • Measure.dirac x) t
          = (volume (Metric.ball x δ ∩ K))⁻¹ * volume ((t ∩ K) ∩ Metric.ball x δ)
            + (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x * t.indicator 1 x := by
      intro x
      have hset : t ∩ (Metric.ball x δ ∩ K) = (t ∩ K) ∩ Metric.ball x δ := by
        ext y; simp only [Set.mem_inter_iff]; tauto
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        Measure.restrict_apply ht, Measure.dirac_apply' _ ht, hset]
    simp_rw [hrw]
    exact (hden.mul hnum).add
      ((measurable_one.indicator (measurableSet_stuckPoints hK δ)).mul
        (measurable_one.indicator ht))

/-- Unfolding lemma for `speedyWalkAux`. -/
theorem speedyWalkAux_apply (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    speedyWalkAux K hK δ x
      = (volume (Metric.ball x δ ∩ K))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
        + (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x • Measure.dirac x := rfl

open scoped Classical in
/-- **The speedy walk with `δ`-steps on `K`** (`vol3_journal.tex:829`): from `x`, resample
uniformly from `x + δBₙ` until the sample lands in `K`, and move there.

Defined as `speedyWalkAux` when `K` is measurable and as the identity kernel otherwise, so
that `speedyWalk` is a function of `K` and `δ` alone; every statement about its *value*
assumes `MeasurableSet K`. -/
noncomputable def speedyWalk (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  if hK : MeasurableSet K then speedyWalkAux K hK δ else Kernel.deterministic id measurable_id

open scoped Classical in
/-- On a measurable `K`, `speedyWalk` is `speedyWalkAux`. -/
theorem speedyWalk_eq {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ) :
    speedyWalk K δ = speedyWalkAux K hK δ := dif_pos hK

/-- **The value of the speedy walk on a measurable event.** -/
theorem speedyWalk_apply_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    speedyWalk K δ x t
      = (volume (Metric.ball x δ ∩ K))⁻¹ * volume (t ∩ (Metric.ball x δ ∩ K))
        + (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x * t.indicator 1 x := by
  rw [speedyWalk_eq hK, speedyWalkAux_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.restrict_apply ht,
    Measure.dirac_apply' _ ht]

/-- **The speedy walk is a Markov kernel**, for every `K` and every `δ`.  Where the
proposal can be accepted, the uniform measure on the accepted set has mass `1` and the
holding atom is absent; where it cannot, the holding atom carries all the mass. -/
instance isMarkovKernel_speedyWalkAux (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ : ℝ) : IsMarkovKernel (speedyWalkAux K hK δ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have h := speedyWalk_apply_set hK δ x (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
  rw [speedyWalk_eq hK] at h
  rw [h, Set.univ_inter, Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one]
  by_cases hx : x ∈ StuckPoints K δ
  · rw [Set.indicator_of_mem hx, mem_stuckPoints_iff.1 hx]
    simp
  · rw [Set.indicator_of_notMem hx, add_zero]
    exact ENNReal.inv_mul_cancel (fun h => hx (mem_stuckPoints_iff.2 h))
      (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left))

open scoped Classical in
instance isMarkovKernel_speedyWalk (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    IsMarkovKernel (speedyWalk K δ) := by
  unfold speedyWalk
  split_ifs with hK
  · exact isMarkovKernel_speedyWalkAux K hK δ
  · infer_instance

/-! ## 3. The `ell`-weighted measure and the crux identity -/

/-- The **`ell`-weighted measure** `ell(x) dx` on `K` — the unnormalised stationary measure
of the speedy walk.  A plain construction. -/
noncomputable def ellMeasure (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) := (volume.restrict K).withDensity (ell K δ)

/-- The total `ell`-weight of `K`, `∫_K ell`. -/
theorem ellMeasure_univ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    ellMeasure K δ Set.univ = ∫⁻ x in K, ell K δ x := by
  rw [ellMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The `ell`-weighted measure is absolutely continuous for Lebesgue measure. -/
theorem ellMeasure_absolutelyContinuous (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    ellMeasure K δ ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- **The total `ell`-weight is finite**: `ell ≤ 1`, so `∫_K ell ≤ vol(K)`. -/
theorem ellMeasure_univ_le (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    ellMeasure K δ Set.univ ≤ volume K := by
  rw [ellMeasure_univ]
  calc ∫⁻ x in K, ell K δ x ≤ ∫⁻ _ in K, (1 : ℝ≥0∞) :=
        lintegral_mono fun x => ell_le_one K δ x
    _ = volume K := by rw [setLIntegral_one]

/-- **The `ell`-weighted measure lives on `K`.** -/
theorem ellMeasure_compl_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : ellMeasure K δ Kᶜ = 0 := by
  rw [ellMeasure, withDensity_apply _ hK.compl, Measure.restrict_restrict hK.compl,
    Set.inter_comm, Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

/-- **Set integrals against the `ell`-weight.** -/
theorem setLIntegral_ellMeasure {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) {g : _ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x in S, g x ∂(ellMeasure K δ) = ∫⁻ x in S ∩ K, ell K δ x * g x := by
  rw [ellMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_ell hK δ) hg hS,
    Measure.restrict_restrict hS]
  rfl

/-- **The crux identity.**  For every `x` and every measurable `T`,

    ell(x) * P_x(T)  =  vol(δBₙ)⁻¹ * vol(T ∩ K ∩ B(x,δ)),

where `P` is the speedy walk.  The `ell(x)` supplied by the stationary weight cancels
exactly the `vol(B(x,δ) ∩ K)` in the denominator of the kernel, and the holding atom is
annihilated because it sits only where `ell(x) = 0`.  What is left is the *symmetric* ball
relation, so reversibility follows in three lines.

No hypothesis on `δ` or on `vol(K)` is needed: at a stuck `x` both sides are `0`. -/
theorem ell_mul_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) :
    ell K δ x * speedyWalk K δ x T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹
        * volume ((T ∩ K) ∩ Metric.ball x δ) := by
  have hset : T ∩ (Metric.ball x δ ∩ K) = (T ∩ K) ∩ Metric.ball x δ := by
    ext y; simp only [Set.mem_inter_iff]; tauto
  have hb0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) = volume (Metric.ball x δ) :=
    (volume_ball_eq x δ).symm
  have hatop : volume (Metric.ball x δ ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  have hell : ell K δ x
      = volume (Metric.ball x δ ∩ K) * (volume (Metric.ball x δ))⁻¹ := by
    rw [ell_apply, div_eq_mul_inv]
  rw [speedyWalk_apply_set hK δ x hT, hset, hb0, mul_add,
    show ell K δ x * ((StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x * T.indicator 1 x)
        = (ell K δ x * (StuckPoints K δ).indicator (fun _ => (1 : ℝ≥0∞)) x) * T.indicator 1 x from
      (mul_assoc _ _ _).symm,
    ell_mul_stuck_indicator, zero_mul, add_zero]
  rcases eq_or_ne (volume (Metric.ball x δ ∩ K)) 0 with h0 | h0
  · have hsub : (T ∩ K) ∩ Metric.ball x δ ⊆ Metric.ball x δ ∩ K := by
      rintro y ⟨⟨-, hyK⟩, hyb⟩
      exact ⟨hyb, hyK⟩
    have hc : volume ((T ∩ K) ∩ Metric.ball x δ) = 0 := measure_mono_null hsub h0
    simp [hc]
  · rw [hell,
      show volume (Metric.ball x δ ∩ K) * (volume (Metric.ball x δ))⁻¹ *
            ((volume (Metric.ball x δ ∩ K))⁻¹ * volume ((T ∩ K) ∩ Metric.ball x δ))
          = (volume (Metric.ball x δ ∩ K) * (volume (Metric.ball x δ ∩ K))⁻¹) *
            ((volume (Metric.ball x δ))⁻¹ * volume ((T ∩ K) ∩ Metric.ball x δ)) by ring,
      ENNReal.mul_inv_cancel h0 hatop, one_mul]

/-! ## 4. Reversibility -/

/-- **The flow of the speedy walk against the `ell`-weight** is the symmetric ball kernel:

    flow(S, T) = vol(δBₙ)⁻¹ * ∫_{K ∩ S} vol((T ∩ K) ∩ B(x,δ)) dx.

Immediate from `ell_mul_speedyWalk`. -/
theorem flow_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    flow (speedyWalk K δ) (ellMeasure K δ) S T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
          ∫⁻ x in S ∩ K, volume ((T ∩ K) ∩ Metric.ball x δ) := by
  rw [flow_apply, setLIntegral_ellMeasure hK δ hS (Kernel.measurable_coe _ hT)]
  rw [lintegral_congr fun x => ell_mul_speedyWalk hK δ x hT]
  exact lintegral_const_mul _ (measurable_volume_inter_ball (hT.inter hK) δ)

/-- **The speedy walk satisfies detailed balance for the `ell`-weighted measure.**

This is the load-bearing structural fact: `Cheeger.lean` and `L2Mixing.lean` both consume
`IsReversible`.  No convexity, no positivity of `δ`, and no bound on `vol(K)` is needed —
after `ell_mul_speedyWalk` the statement is exactly the symmetry of the ball relation
(`lintegral_volume_inter_ball_comm`). -/
theorem isReversible_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : IsReversible (speedyWalk K δ) (ellMeasure K δ) := by
  intro S T hS hT
  rw [flow_speedyWalk hK δ hS hT, flow_speedyWalk hK δ hT hS,
    lintegral_volume_inter_ball_comm (hS.inter hK) (hT.inter hK) δ]

/-! ## 5. Normalisation -/

/-- The **`ell`-weighted probability measure** on `K`: the stationary distribution of the
speedy walk.  A plain construction; `isProbabilityMeasure_ellProb` gives the guards under
which it is a probability measure. -/
noncomputable def ellProb (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (ellMeasure K δ Set.univ)⁻¹ • ellMeasure K δ

/-- `ellProb` is a probability measure exactly when the total `ell`-weight is positive and
finite; finiteness is automatic once `vol(K) < ⊤` (`ellMeasure_univ_le`). -/
theorem isProbabilityMeasure_ellProb {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    (h0 : ellMeasure K δ Set.univ ≠ 0) (htop : ellMeasure K δ Set.univ ≠ ⊤) :
    IsProbabilityMeasure (ellProb K δ) := by
  refine ⟨?_⟩
  rw [ellProb, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- **The speedy walk is reversible for its stationary probability measure.** -/
theorem isReversible_speedyWalk_prob {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) : IsReversible (speedyWalk K δ) (ellProb K δ) :=
  (isReversible_speedyWalk hK δ).smul _

/-- **The `ell`-weighted probability measure is invariant for the speedy walk.** -/
theorem invariant_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : Kernel.Invariant (speedyWalk K δ) (ellProb K δ) :=
  (isReversible_speedyWalk_prob hK δ).invariant

/-- **`ellProb` lives on `K`.** -/
theorem ellProb_compl_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : ellProb K δ Kᶜ = 0 := by
  rw [ellProb, Measure.smul_apply, smul_eq_mul, ellMeasure_compl_eq_zero hK δ, mul_zero]

/-- **`ellProb` is absolutely continuous for Lebesgue measure.** -/
theorem ellProb_absolutelyContinuous (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    ellProb K δ ≪ volume := by
  intro s hs
  rw [ellProb, Measure.smul_apply, smul_eq_mul, ellMeasure_absolutelyContinuous K δ hs, mul_zero]

/-! ## 6. The multiplicative overlap estimate (convexity)

`volume_ball_le_volume_inter_ball_add` (`BallWalkConductance.lean`) says that two `δ`-balls
at centre distance `t` lose at most an `n t/(2δ)` fraction *of the ball* by intersecting.
That is an **additive** loss, and for the speedy walk it is useless: the one-step
distribution from `u` is normalised by `vol(B(u,δ) ∩ K)`, which may be far smaller than
`vol(B(u,δ))`, so a loss measured against the ball swamps it.

Convexity upgrades it to a **multiplicative** estimate against `vol(B(u,δ) ∩ K)` itself:
contracting `B(u,δ) ∩ K` towards the midpoint `m` of `u` and `v` by the factor
`λ = 1 - t/δ` lands it inside `B(u,δ) ∩ K ∩ B(v,δ)`, because `m ∈ K` (convexity) and every
contraction towards `m` stays in `K` (convexity again) while moving at most `(1-λ)·t/2`
closer to each centre.  Haar scaling turns the factor `λ` into `λⁿ` and Bernoulli turns
`λⁿ` into `1 - n t/δ`.

This is the elementary stand-in for Lemma 3.5 of [KLS95] (`vol3_journal.tex:592`), which
keeps a constant fraction at separation `δ/√n`; the contraction keeps a constant fraction
only at separation `δ/n`, which is the one factor of `√n` recorded as caveat 1 of
`BallWalkConductance.lean`. -/

/-- **The contraction towards the midpoint stays in both balls and in `K`.**  For a convex
`K` and `u, v ∈ K` at distance `t < δ`, the homothety of ratio `λ = 1 - t/δ` centred at the
midpoint maps `B(u,δ) ∩ K` into `B(u,δ) ∩ K ∩ B(v,δ)`.

The three membership checks are: `λ • y + (1-λ) • m ∈ K` by convexity; distance to `u` at
most `λ‖y-u‖ + (1-λ)t/2 < λδ + (1-λ)δ = δ`; and distance to `v` at most
`λ(‖y-u‖+t) + (1-λ)t/2 < δ`, which is where the choice `1 - λ = t/δ` is used. -/
theorem image_homothety_subset_of_convex {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K)
    {δ : ℝ} (hδ : 0 < δ) (hlt : dist u v < δ) :
    AffineMap.homothety (midpoint ℝ u v) (1 - dist u v / δ) '' (Metric.ball u δ ∩ K)
      ⊆ (Metric.ball u δ ∩ K) ∩ Metric.ball v δ := by
  set t : ℝ := dist u v with ht
  have ht0 : 0 ≤ t := dist_nonneg
  set lam : ℝ := 1 - t / δ with hlam
  have hlam0 : 0 < lam := by
    rw [hlam, sub_pos, div_lt_one hδ]; exact hlt
  have hlam1 : lam ≤ 1 := by
    have h : 0 ≤ t / δ := by positivity
    rw [hlam]; linarith
  have hlamd : lam * δ = δ - t := by rw [hlam]; field_simp
  set m : EuclideanSpace ℝ (Fin n) := midpoint ℝ u v with hm
  have hmK : m ∈ K := hconv.midpoint_mem hu hv
  have hmu : ‖m - u‖ = t / 2 := by
    rw [ht, hm, ← dist_eq_norm, dist_midpoint_left]
    simp [div_eq_inv_mul]
  have hmv : ‖m - v‖ = t / 2 := by
    rw [ht, hm, ← dist_eq_norm, dist_midpoint_right]
    simp [div_eq_inv_mul]
  rintro z ⟨y, ⟨hyb, hyK⟩, rfl⟩
  have hyu : ‖y - u‖ < δ := by
    have h : dist y u < δ := Metric.mem_ball.1 hyb
    rwa [dist_eq_norm] at h
  have hyv : ‖y - v‖ < δ + t := by
    have h : dist y v ≤ dist y u + dist u v := dist_triangle _ _ _
    rw [dist_eq_norm y v, dist_eq_norm y u, ← ht] at h
    linarith
  have hz : AffineMap.homothety m lam y = lam • y + (1 - lam) • m := by
    rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have habs1 : ‖lam‖ = lam := by rw [Real.norm_eq_abs, abs_of_pos hlam0]
  have habs2 : ‖1 - lam‖ = 1 - lam := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hexp : (1 - lam) * (t / 2) = t / 2 - lam * t / 2 := by ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, hz,
      show lam • y + (1 - lam) • m - u = lam • (y - u) + (1 - lam) • (m - u) by module]
    have h1 : lam * ‖y - u‖ < lam * δ := mul_lt_mul_of_pos_left hyu hlam0
    have h2 : 0 ≤ lam * t := mul_nonneg hlam0.le ht0
    calc ‖lam • (y - u) + (1 - lam) • (m - u)‖
        ≤ ‖lam • (y - u)‖ + ‖(1 - lam) • (m - u)‖ := norm_add_le _ _
      _ = lam * ‖y - u‖ + (1 - lam) * ‖m - u‖ := by
          rw [norm_smul, norm_smul, habs1, habs2]
      _ < δ := by rw [hmu, hexp]; linarith
  · rw [hz]; exact hconv hyK hmK hlam0.le (by linarith) (by ring)
  · rw [Metric.mem_ball, dist_eq_norm, hz,
      show lam • y + (1 - lam) • m - v = lam • (y - v) + (1 - lam) • (m - v) by module]
    have h1 : lam * ‖y - v‖ < lam * δ + lam * t := by
      have h := mul_lt_mul_of_pos_left hyv hlam0
      rwa [mul_add] at h
    have hkey : 0 ≤ t - lam * t := by nlinarith [ht0, hlam1]
    calc ‖lam • (y - v) + (1 - lam) • (m - v)‖
        ≤ ‖lam • (y - v)‖ + ‖(1 - lam) • (m - v)‖ := norm_add_le _ _
      _ = lam * ‖y - v‖ + (1 - lam) * ‖m - v‖ := by
          rw [norm_smul, norm_smul, habs1, habs2]
      _ < δ := by rw [hmv, hexp]; linarith

/-- **The multiplicative overlap estimate for a convex body.**

    vol(B(u,δ) ∩ K)  ≤  vol(B(u,δ) ∩ K ∩ B(v,δ))  +  (n t/δ) · vol(B(u,δ) ∩ K),   t = ‖u-v‖.

Contrast `volume_ball_le_volume_inter_ball_add`, whose correction term is a fraction of
`vol(B(u,δ))` rather than of `vol(B(u,δ) ∩ K)`.  The difference is exactly what makes the
speedy walk's overlap bound a constant instead of `ell(u)`.

Stated additively so that the regime `n t ≥ δ`, where the claim is vacuous, is handled
without truncated `ℝ≥0∞` subtraction; `1 ≤ n` is used only there. -/
theorem volume_inter_ball_le_of_convex (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K)
    {δ : ℝ} (hδ : 0 < δ) :
    volume (Metric.ball u δ ∩ K)
      ≤ volume ((Metric.ball u δ ∩ K) ∩ Metric.ball v δ)
        + ENNReal.ofReal ((n : ℝ) * dist u v / δ) * volume (Metric.ball u δ ∩ K) := by
  set t : ℝ := dist u v with ht
  have ht0 : 0 ≤ t := dist_nonneg
  by_cases hcase : δ ≤ t
  · have h1 : (1:ℝ) ≤ (n : ℝ) * t / δ := by
      rw [le_div_iff₀ hδ, one_mul]
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith
    have h1' : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) * t / δ) := ENNReal.one_le_ofReal.2 h1
    calc volume (Metric.ball u δ ∩ K) = 1 * volume (Metric.ball u δ ∩ K) := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((n : ℝ) * t / δ) * volume (Metric.ball u δ ∩ K) := by gcongr
      _ ≤ _ := le_add_self
  · rw [not_le] at hcase
    set lam : ℝ := 1 - t / δ with hlam
    have hlam0 : 0 < lam := by rw [hlam, sub_pos, div_lt_one hδ]; exact hcase
    have hsub := image_homothety_subset_of_convex hconv hu hv hδ hcase
    have hvol : volume (AffineMap.homothety (midpoint ℝ u v) lam '' (Metric.ball u δ ∩ K))
        = ENNReal.ofReal (lam ^ n) * volume (Metric.ball u δ ∩ K) := by
      have h := Measure.addHaar_image_homothety
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (midpoint ℝ u v) lam
        (Metric.ball u δ ∩ K)
      rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ n)] at h
      exact h
    have hbern : (1:ℝ) - (n : ℝ) * t / δ ≤ lam ^ n := by
      have hm1 : (-1:ℝ) ≤ lam := by
        rw [hlam]
        have : t / δ < 1 := (div_lt_one hδ).2 hcase
        linarith
      have hpow := one_add_mul_sub_le_pow hm1 n
      have hsub' : lam - 1 = -(t / δ) := by rw [hlam]; ring
      rw [hsub'] at hpow
      have hd : (n:ℝ) * (-(t / δ)) = -((n : ℝ) * t / δ) := by ring
      rw [hd] at hpow
      linarith
    have hkey : (1:ℝ) ≤ lam ^ n + (n : ℝ) * t / δ := by linarith
    have hsum : (1:ℝ≥0∞) ≤ ENNReal.ofReal (lam ^ n) + ENNReal.ofReal ((n : ℝ) * t / δ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.one_le_ofReal.2 hkey
    calc volume (Metric.ball u δ ∩ K) = 1 * volume (Metric.ball u δ ∩ K) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal (lam ^ n) + ENNReal.ofReal ((n : ℝ) * t / δ))
            * volume (Metric.ball u δ ∩ K) := by gcongr
      _ = ENNReal.ofReal (lam ^ n) * volume (Metric.ball u δ ∩ K)
            + ENNReal.ofReal ((n : ℝ) * t / δ) * volume (Metric.ball u δ ∩ K) := add_mul _ _ _
      _ ≤ volume ((Metric.ball u δ ∩ K) ∩ Metric.ball v δ)
            + ENNReal.ofReal ((n : ℝ) * t / δ) * volume (Metric.ball u δ ∩ K) := by
          gcongr
          rw [← hvol]
          exact measure_mono hsub

/-! ## 7. One-step overlap for the speedy walk: no local-conductance hypothesis -/

/-- **The one-step overlap bound for the speedy walk.**  For a convex `K`, any `u, v ∈ K`
with `u` not stuck, and any measurable `T`,

    1  ≤  P_u(T) + P_v(Tᶜ) + n‖u - v‖/δ.

Compare `ell_le_ballWalk_add_ballWalk_compl`, where the left-hand side is `ell(u)`.  The
improvement is the whole point of the speedy walk: `P_u` divides by `vol(B(u,δ) ∩ K)`, and
`volume_inter_ball_le_of_convex` measures the overlap loss against the *same* quantity, so
the two cancel.  Consequently no hypothesis of the form `ell ≥ θ` appears anywhere
downstream.

The proof: both one-step laws dominate the uniform law on `C = B(u,δ) ∩ K ∩ B(v,δ)`,
normalised by at most `M = max(vol(B(u,δ) ∩ K), vol(B(v,δ) ∩ K))`; `T` and `Tᶜ` cut `C` in
two; and `volume_inter_ball_le_of_convex`, applied at whichever of `u, v` attains `M`, gives
`M ≤ vol(C) + (n t/δ)·M`.  Multiplying through by `M⁻¹` is the statement. -/
theorem one_le_speedyWalk_add_speedyWalk_compl (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K)
    (hu0 : u ∉ StuckPoints K δ) {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    1 ≤ speedyWalk K δ u T + speedyWalk K δ v Tᶜ
      + ENNReal.ofReal ((n : ℝ) * dist u v / δ) := by
  set au : ℝ≥0∞ := volume (Metric.ball u δ ∩ K) with hau
  set av : ℝ≥0∞ := volume (Metric.ball v δ ∩ K) with hav
  set C : Set (EuclideanSpace ℝ (Fin n)) := (Metric.ball u δ ∩ K) ∩ Metric.ball v δ with hC
  have hCm : MeasurableSet C := (measurableSet_ball.inter hK).inter measurableSet_ball
  have hautop : au ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  have havtop : av ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  have hau0 : au ≠ 0 := fun h => hu0 (mem_stuckPoints_iff.2 h)
  set M : ℝ≥0∞ := max au av with hM
  have hM0 : M ≠ 0 := by
    intro h
    exact hau0 (nonpos_iff_eq_zero.1 (h ▸ le_max_left au av))
  have hMtop : M ≠ ⊤ := by
    rw [hM]; rcases max_cases au av with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
  set r : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * dist u v / δ) with hr
  -- the two one-step laws dominate the uniform law on `C`
  have hdom : ∀ (x : EuclideanSpace ℝ (Fin n)) (A : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet A → volume (Metric.ball x δ ∩ K) ≤ M →
      A ∩ C ⊆ A ∩ (Metric.ball x δ ∩ K) →
      M⁻¹ * volume (A ∩ C) ≤ speedyWalk K δ x A := by
    intro x A hA hle hsub
    rw [speedyWalk_apply_set hK δ x hA]
    exact le_trans (mul_le_mul' (ENNReal.inv_le_inv.2 hle) (measure_mono hsub)) le_self_add
  have h1 : M⁻¹ * volume (T ∩ C) ≤ speedyWalk K δ u T := by
    refine hdom u T hT (le_max_left _ _) ?_
    rintro y ⟨hyT, ⟨hyb, hyK⟩, -⟩
    exact ⟨hyT, hyb, hyK⟩
  have h2 : M⁻¹ * volume (Tᶜ ∩ C) ≤ speedyWalk K δ v Tᶜ := by
    refine hdom v Tᶜ hT.compl (le_max_right _ _) ?_
    rintro y ⟨hyT, ⟨-, hyK⟩, hyb⟩
    exact ⟨hyT, hyb, hyK⟩
  have h3 : volume (T ∩ C) + volume (Tᶜ ∩ C) = volume C := by
    have h := measure_inter_add_sdiff (μ := volume) C hT
    rwa [Set.inter_comm C T, Set.sdiff_eq, Set.inter_comm C Tᶜ] at h
  have hsum : M⁻¹ * volume C ≤ speedyWalk K δ u T + speedyWalk K δ v Tᶜ := by
    rw [← h3, mul_add]
    exact add_le_add h1 h2
  -- the overlap estimate at whichever centre attains the maximum
  have hswap : (Metric.ball v δ ∩ K) ∩ Metric.ball u δ = C := by
    rw [hC]; ext y; simp only [Set.mem_inter_iff]; tauto
  have hMle : M ≤ volume C + r * M := by
    rcases max_cases au av with ⟨hmax, -⟩ | ⟨hmax, -⟩
    · rw [hM, hmax, hau, hr]
      exact volume_inter_ball_le_of_convex hn hconv hu hv hδ
    · rw [hM, hmax, hav, hr, dist_comm u v]
      have h := volume_inter_ball_le_of_convex hn hconv hv hu hδ
      rwa [hswap] at h
  calc (1:ℝ≥0∞) = M⁻¹ * M := (ENNReal.inv_mul_cancel hM0 hMtop).symm
    _ ≤ M⁻¹ * (volume C + r * M) := by gcongr
    _ = M⁻¹ * volume C + r * (M⁻¹ * M) := by ring
    _ = M⁻¹ * volume C + r := by rw [ENNReal.inv_mul_cancel hM0 hMtop, mul_one]
    _ ≤ (speedyWalk K δ u T + speedyWalk K δ v Tᶜ) + r := by gcongr

/-- **Separation from overlap, with an absolute constant.**  If a step from `u` enters `T`
with probability less than `1/4` and a step from `v` enters `Tᶜ` with probability less than
`1/4`, then `‖u - v‖ > δ/(2n)`.

This is `lt_dist_of_ballWalk_lt` with `θ` replaced by the absolute constant `1`, which is
the entire quantitative gain of this file. -/
theorem lt_dist_of_speedyWalk_lt (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hconv : Convex ℝ K) {δ : ℝ} (hδ : 0 < δ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) (hu0 : u ∉ StuckPoints K δ)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T)
    (hu' : 4 * speedyWalk K δ u T < 1) (hv' : 4 * speedyWalk K δ v Tᶜ < 1) :
    δ / (2 * (n : ℝ)) < dist u v := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hov := one_le_speedyWalk_add_speedyWalk_compl hn hK hconv hδ hu hv hu0 hT
  have hXtop : (4:ℝ≥0∞) * ENNReal.ofReal ((n:ℝ) * dist u v / δ) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hstep : (2:ℝ≥0∞) + 2 < 2 + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / δ) := by
    calc (2:ℝ≥0∞) + 2 = 4 := by norm_num
      _ ≤ 4 * (speedyWalk K δ u T + speedyWalk K δ v Tᶜ
            + ENNReal.ofReal ((n:ℝ) * dist u v / δ)) := by
          calc (4:ℝ≥0∞) = 4 * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr
      _ = 4 * speedyWalk K δ u T + 4 * speedyWalk K δ v Tᶜ
            + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / δ) := by ring
      _ < 1 + 1 + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / δ) :=
          ENNReal.add_lt_add_right hXtop (ENNReal.add_lt_add hu' hv')
      _ = 2 + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / δ) := by norm_num
  have hgt : (2:ℝ≥0∞) < 4 * ENNReal.ofReal ((n:ℝ) * dist u v / δ) :=
    (ENNReal.add_lt_add_iff_left (by norm_num)).1 hstep
  have e2 : (4:ℝ≥0∞) * ENNReal.ofReal ((n:ℝ) * dist u v / δ)
      = ENNReal.ofReal (4 * ((n:ℝ) * dist u v / δ)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    simp
  rw [e2] at hgt
  have hpos : (0:ℝ) < 4 * ((n:ℝ) * dist u v / δ) := by
    by_contra hc
    rw [not_lt] at hc
    rw [ENNReal.ofReal_eq_zero.2 hc] at hgt
    exact absurd hgt (by simp)
  have hgt2 : ENNReal.ofReal (2:ℝ) < ENNReal.ofReal (4 * ((n:ℝ) * dist u v / δ)) := by
    rwa [show ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) from by simp]
  have hreal : (2:ℝ) < 4 * ((n:ℝ) * dist u v / δ) := (ENNReal.ofReal_lt_ofReal_iff hpos).1 hgt2
  have h := mul_lt_mul_of_pos_right hreal hδ
  have he : 4 * ((n:ℝ) * dist u v / δ) * δ = 4 * ((n:ℝ) * dist u v) := by
    field_simp
  rw [he] at h
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (n:ℝ))]
  nlinarith [h]

/-! ## 8. Non-degeneracy of the stationary measure

Three facts the conductance and mixing theorems need, none of them about the walk:

* the total `ell`-weight of a body of positive volume is positive, so `ellProb` is a genuine
  probability measure and not the zero measure;
* the stuck points carry no `ell`-weight, so they may be deleted from every covering
  argument;
* a probability measure absolutely continuous for Lebesgue measure has a measurable set of
  mass in `(0, 1/2]`, so the conductance is not the empty infimum `⊤` and `L²` contains a
  non-constant function. -/

/-- **The stuck points carry no `ell`-weight.**  Immediate: `ell` vanishes on them. -/
theorem ellMeasure_stuckPoints {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : ellMeasure K δ (StuckPoints K δ) = 0 := by
  rw [ellMeasure, withDensity_apply _ (measurableSet_stuckPoints hK δ),
    setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) (measurableSet_stuckPoints hK δ)
      (fun x hx => hx), lintegral_zero]

/-- The stuck points are null for the normalised measure too. -/
theorem ellProb_stuckPoints {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : ellProb K δ (StuckPoints K δ) = 0 := by
  rw [ellProb, Measure.smul_apply, smul_eq_mul, ellMeasure_stuckPoints hK δ, mul_zero]

/-- **A body of positive volume has positive total `ell`-weight**, for every `δ > 0`.

If every ball of radius `δ/2` met `K` in a null set then a countable dense family of such
balls would cover `K` and force `vol(K) = 0`.  So some `A = K ∩ B(x₀, δ/2)` has positive
volume, and every `y ∈ A` has `B(x₀, δ/2) ⊆ B(y, δ)`, hence `ell(y) ≥ vol(A)/vol(δBₙ) > 0`.
Integrating that over `A` gives the claim.

Without this `ellProb` would be the zero measure and every statement about it vacuous. -/
theorem ellMeasure_univ_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) {δ : ℝ} (hδ : 0 < δ) : ellMeasure K δ Set.univ ≠ 0 := by
  classical
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hvb
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  -- some ball of radius `δ/2` meets `K` in a set of positive volume
  have hex : ∃ x0 : EuclideanSpace ℝ (Fin n), volume (K ∩ Metric.ball x0 (δ / 2)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨D, hDc, hDd⟩ :=
      TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin n))
    have hcov : K ⊆ ⋃ d ∈ D, K ∩ Metric.ball d (δ / 2) := by
      intro x hx
      have hx' : x ∈ closure D := by rw [hDd.closure_eq]; trivial
      obtain ⟨d, hdD, hdx⟩ := Metric.mem_closure_iff.1 hx' (δ / 2) (by positivity)
      exact Set.mem_biUnion hdD ⟨hx, Metric.mem_ball.2 hdx⟩
    exact hK0 (measure_mono_null hcov
      ((measure_biUnion_null_iff hDc).2 fun d _ => hcon d))
  obtain ⟨x0, hx0⟩ := hex
  set A : Set (EuclideanSpace ℝ (Fin n)) := K ∩ Metric.ball x0 (δ / 2) with hA
  have hAm : MeasurableSet A := hK.inter measurableSet_ball
  have hAtop : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
  have hAK : A ⊆ K := Set.inter_subset_left
  -- every point of `A` has local conductance at least `vol(A)/vol(δBₙ)`
  have hlow : ∀ y ∈ A, volume A / vb ≤ ell K δ y := by
    intro y hy
    have hsub : A ⊆ Metric.ball y δ ∩ K := by
      rintro z ⟨hzK, hzb⟩
      refine ⟨?_, hzK⟩
      rw [Metric.mem_ball] at hzb ⊢
      have hy2 : dist y x0 < δ / 2 := Metric.mem_ball.1 hy.2
      calc dist z y ≤ dist z x0 + dist x0 y := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by rw [dist_comm x0 y]; linarith
        _ = δ := by ring
    rw [ell_apply, volume_ball_eq y δ, ← hvb]
    exact ENNReal.div_le_div_right (measure_mono hsub) vb
  have hpos : 0 < volume A / vb * volume A :=
    ENNReal.mul_pos (ENNReal.div_pos hx0 hvbtop).ne' hx0
  rw [ellMeasure_univ]
  refine ne_of_gt (lt_of_lt_of_le hpos ?_)
  calc volume A / vb * volume A = ∫⁻ _ in A, volume A / vb := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in A, ell K δ x := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hAm] with x hx using hlow x hx
    _ ≤ ∫⁻ x in K, ell K δ x :=
        lintegral_mono' (Measure.restrict_mono hAK le_rfl) le_rfl

/-- **A probability measure absolutely continuous for Lebesgue measure cuts `ℝⁿ` in half**:
some measurable set has mass in `(0, 1/2]`.

Suppose not; then every measurable set has mass `0` or more than `1/2`.  Let `R` be the
infimum of the radii `r` with `pi(B(0,r)) > 1/2`.  Every strictly smaller ball has mass `0`,
hence so does `B(0,R)` (a countable increasing union of them), while every strictly larger
ball has mass more than `1/2`.  The decreasing sets `B(0, R + 1/(k+1)) \ B(0,R)` therefore
all have mass more than `1/2` and intersect in the sphere `‖x‖ = R`, which is Lebesgue-null
and so `pi`-null.  Continuity from above gives `1/2 ≤ 0`.

This is the non-degeneracy `Arlib.MarkovChains.mixesWithin_of_conductance` needs, in a form
that applies to any target measure with a density — in particular to `ellProb`, which is
not uniform. -/
theorem exists_smallSet_of_absolutelyContinuous (hn : 1 ≤ n)
    (pi : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure pi]
    (hac : pi ≪ (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ 1 / 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (by rw [finrank_euclideanSpace_fin]; omega)
  have hdich : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      pi S = 0 ∨ 1 / 2 < pi S := by
    intro S hS
    rcases eq_or_ne (pi S) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (hcon S hS (zero_lt_iff.2 h))
  have hmono : ∀ r r' : ℝ, r ≤ r' →
      pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
        ≤ pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r') :=
    fun _ _ h => measure_mono (Metric.ball_subset_ball h)
  set B : Set ℝ :=
    {r : ℝ | 1 / 2 < pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)} with hBdef
  have hBmem : ∀ r : ℝ, r ∈ B ↔
      1 / 2 < pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := fun _ => Iff.rfl
  have hBne : B.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ m : ℕ, pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (m : ℝ)) = 0 := by
      intro m
      refine (hdich _ measurableSet_ball).resolve_right fun h => ?_
      exact absurd ((hBmem (m : ℝ)).2 h) (hemp ▸ Set.notMem_empty _)
    have hcov : (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
        = ⋃ m : ℕ, Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (m : ℝ) := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Metric.mem_ball, dist_zero_right, true_iff]
      obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
      exact ⟨m, hm⟩
    have h1 : pi Set.univ = 0 := by rw [hcov]; exact measure_iUnion_null hall
    rw [measure_univ] at h1
    exact one_ne_zero h1
  have hBpos : ∀ r ∈ B, (0 : ℝ) ≤ r := by
    intro r hr
    by_contra hneg
    push_neg at hneg
    have hemp : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r = ∅ :=
      Metric.ball_eq_empty.2 hneg.le
    have h := (hBmem r).1 hr
    rw [hemp, measure_empty] at h
    exact absurd h (by simp)
  have hBbd : BddBelow B := ⟨0, hBpos⟩
  set R : ℝ := sInf B with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_csInf hBne hBpos
  have hlt : ∀ r : ℝ, r < R → pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = 0 := by
    intro r hr
    have hrB : r ∉ B := fun h => absurd (csInf_le hBbd h) (not_le.2 hr)
    rw [hBmem r, not_lt] at hrB
    exact (hdich _ measurableSet_ball).resolve_right (not_lt.2 hrB)
  have hballR : pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) = 0 := by
    have hcov : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
        = ⋃ k : ℕ, Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R - 1 / (k + 1)) := by
      ext x
      simp only [Set.mem_iUnion, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0:ℝ) < R - ‖x‖)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have hpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hcov]
    refine measure_iUnion_null fun k => hlt _ ?_
    have hpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hgt : ∀ r : ℝ, R < r →
      1 / 2 < pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    intro r hr
    obtain ⟨b, hbB, hbr⟩ := exists_lt_of_csInf_lt hBne hr
    exact lt_of_lt_of_le ((hBmem b).1 hbB) (hmono b r hbr.le)
  -- the shrinking annuli
  set E : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k =>
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + 1 / (k + 1)) \
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R with hEdef
  have hEm : ∀ k, MeasurableSet (E k) := fun k => measurableSet_ball.diff measurableSet_ball
  have hEanti : Antitone E := by
    intro k l hkl
    refine Set.diff_subset_diff_left (Metric.ball_subset_ball ?_)
    have h1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (0:ℝ) < (l : ℝ) + 1 := by positivity
    have : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkl 1
    have := one_div_le_one_div_of_le h1 this
    linarith
  have hEhalf : ∀ k : ℕ, 1 / 2 < pi (E k) := by
    intro k
    have hkpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + 1 / (k + 1))
        ⊆ E k ∪ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
      intro x hx
      by_cases hxR : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
      · exact Or.inr hxR
      · exact Or.inl ⟨hx, hxR⟩
    calc (1:ℝ≥0∞) / 2 < pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + 1 / (k + 1))) :=
          hgt _ (by linarith)
      _ ≤ pi (E k) + pi (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = pi (E k) := by rw [hballR, add_zero]
  have hiInter : (⋂ k, E k) = Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) R := by
    ext x
    simp only [Set.mem_iInter, hEdef, Set.mem_diff, Metric.mem_ball, Metric.mem_sphere,
      dist_zero_right, not_lt]
    constructor
    · intro hx
      refine le_antisymm ?_ (hx 0).2
      by_contra hgtx
      push_neg at hgtx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0:ℝ) < ‖x‖ - R)
      exact absurd (hx k).1 (by push_neg; linarith)
    · intro hx k
      have hkpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact ⟨by rw [hx]; linarith, by rw [hx]⟩
  have hsphere : pi (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) R) = 0 :=
    hac (Measure.addHaar_sphere volume 0 R)
  have hfin : ∃ k : ℕ, pi (E k) ≠ ⊤ := ⟨0, measure_ne_top pi _⟩
  have hkey : pi (⋂ k, E k) = ⨅ k, pi (E k) :=
    hEanti.measure_iInter (fun k => (hEm k).nullMeasurableSet) hfin
  rw [hiInter, hsphere] at hkey
  have hhalf : (1:ℝ≥0∞) / 2 ≤ ⨅ k, pi (E k) := le_iInf fun k => (hEhalf k).le
  rw [← hkey] at hhalf
  exact absurd hhalf (by simp)

/-- **`ellProb` is a probability measure** on a body of positive finite volume, for every
positive step. -/
theorem isProbabilityMeasure_ellProb_of_volume {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (ellProb K δ) :=
  isProbabilityMeasure_ellProb (ellMeasure_univ_ne_zero hK hK0 hδ)
    (ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ))

/-! ## 9. The conductance bound, with no local-conductance hypothesis

The proof is the three-way partition of `conductance_ballWalk_ge` (`vol3_journal.tex:657`),
with two changes.  First, the separation input is `lt_dist_of_speedyWalk_lt`, whose threshold
is the absolute constant `1/4` rather than `θ/4`, so **`hell` is gone**.  Second, the
stationary measure is `ellProb K δ`, so the isoperimetric hypothesis is stated for *that*
measure — which is the right thing to assume, since `ell` is a convolution of two indicators
of convex sets and hence log-concave, making `ellProb` a log-concave measure exactly like the
uniform measure on `K`.

The stuck points are deleted along with `Kᶜ` in every covering step; they are `ellProb`-null
(`ellProb_stuckPoints`), so nothing is lost. -/

/-- **The conductance of the speedy walk on a convex body**, given an isoperimetric
inequality for its stationary measure:

    Φ(speedy walk on K with δ-steps)  ≥  min(1/16, κ·δ/(128·n)).

The contrast with `conductance_ballWalk_ge` is the point of this file: **there is no
hypothesis of the form `ell ≥ θ`**, and correspondingly no `θ` in the bound.  The first
branch is an absolute constant instead of `θ/16`, and the second is `κδ/(128n)` instead of
`κθ²δ/(64n)`.  With the only *proved* witness for the ball walk's `θ` being `2⁻ⁿ`
(`ofReal_le_ell_unitBall`), that is the difference between an exponential and a polynomial
step count.

Hypotheses that carry content, all inline:

* `hconv` — **`K` is convex.**  Used only through `volume_inter_ball_le_of_convex`, and
  genuinely needed: without it the overlap loss is measured against `vol(B(u,δ))` rather than
  `vol(B(u,δ) ∩ K)` and the `θ` comes back.
* `hiso` — the **isoperimetric inequality for `ellProb K δ`**, spelled out.  Nothing here
  proves it; Mathlib has no isoperimetric inequality for log-concave densities
  (`CV-ROADMAP.md` §3).  Note it is stated for `ellProb K δ`, *not* for the uniform measure
  on `K`; those are different hypotheses.

The remaining hypotheses are non-degeneracy guards: `1 ≤ n`, `K` measurable with
`0 < vol(K) < ∞`, and `0 < δ`.

Against the paper (`vol3_journal.tex:746`, `Φ ≥ δ/(250σ√n)`): the shape `min(const, κd/const)`
is the same and the separation `d = δ/(2n)` replaces the paper's `δ/√n`, the one factor of
`√n` that the elementary contraction estimate costs against [KLS95, Lemma 3.5]. -/
theorem conductance_speedyWalk_ge (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) {kappa : ℝ≥0∞}
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B)) :
    min (1 / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64)
      ≤ conductance (speedyWalk K δ) (ellProb K δ) := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdpos : (0:ℝ) < δ / (2 * (n : ℝ)) := by positivity
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := ellProb K δ with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    speedyWalk K δ with hPdef
  have hrev : IsReversible P pi := isReversible_speedyWalk_prob hK δ
  -- the good part of `K`: in `K` and not stuck.  Its complement is `pi`-null.
  set K0 : Set (EuclideanSpace ℝ (Fin n)) := K ∩ (StuckPoints K δ)ᶜ with hK0def
  have hK0m : MeasurableSet K0 := hK.inter (measurableSet_stuckPoints hK δ).compl
  have hK0K : K0 ⊆ K := Set.inter_subset_left
  have hK0c : pi K0ᶜ = 0 := by
    have hset : K0ᶜ = Kᶜ ∪ StuckPoints K δ := by
      rw [hK0def, Set.compl_inter, compl_compl]
    rw [hset]
    exact measure_union_null (ellProb_compl_eq_zero hK δ) (ellProb_stuckPoints hK δ)
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hcompl : pi S + pi Sᶜ = 1 := by
    rw [measure_add_measure_compl hSm, measure_univ]
  have hSc : (1:ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have h1 : (1:ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1:ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  set S1 : Set (EuclideanSpace ℝ (Fin n)) := (S ∩ K0) ∩ {x | 4 * P x Sᶜ < 1} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) := (K0 \ S) ∩ {x | 4 * P x S < 1} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hK0m).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm.compl).const_mul 4) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hK0m.diff hSm).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm).const_mul 4) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ K0) ∧ 4 * P x Sᶜ < 1) := by
    intro x; rw [hS1def]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ K0 ∧ x ∉ S) ∧ 4 * P x S < 1) := by
    intro x; rw [hS2def]; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1K : S1 ⊆ K := fun x hx => hK0K ((hmem1 x).1 hx).1.2
  have hS2K : S2 ⊆ K := fun x hx => hK0K ((hmem2 x).1 hx).1.1
  -- the flow accounting
  have hSA : S \ (S1 ∪ K0ᶜ) = (S ∩ K0) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ K0ᶜ) = (K0 \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ K0ᶜ), (1:ℝ≥0∞) ≤ 4 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ K0ᶜ), (1:ℝ≥0∞) ≤ 4 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, hc⟩)
  have hflow : pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) ≤ 8 * flow P pi S Sᶜ := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hK0m.compl)
      (hS2m.union hK0m.compl) hA' hB'
    rw [hSA, hSB, one_mul] at h
    calc pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) ≤ 2 * (4 * flow P pi S Sᶜ) := h
      _ = 8 * flow P pi S Sᶜ := by ring
  -- coverings
  have hpart : pi ((K \ S1) \ S2) ≤ pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) := by
    have hsub : (K \ S1) \ S2 ⊆ (((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) ∪ K0ᶜ := by
      rintro x ⟨⟨hxK, hxS1⟩, hxS2⟩
      by_cases hxK0 : x ∈ K0
      · by_cases hxS : x ∈ S
        · exact Or.inl (Or.inl ⟨⟨hxS, hxK0⟩, hxS1⟩)
        · exact Or.inl (Or.inr ⟨⟨hxK0, hxS⟩, hxS2⟩)
      · exact Or.inr hxK0
    calc pi ((K \ S1) \ S2) ≤ pi ((((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) ∪ K0ᶜ) :=
          measure_mono hsub
      _ ≤ pi (((S ∩ K0) \ S1) ∪ ((K0 \ S) \ S2)) + pi K0ᶜ := measure_union_le _ _
      _ ≤ (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2) := by rw [hK0c, add_zero]
  have hcov1 : pi S ≤ pi ((S ∩ K0) \ S1) + pi S1 := by
    have hsub : S ⊆ (((S ∩ K0) \ S1) ∪ S1) ∪ K0ᶜ := by
      intro x hx
      by_cases hxK : x ∈ K0
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · exact Or.inl (Or.inl ⟨⟨hx, hxK⟩, hxS1⟩)
      · exact Or.inr hxK
    calc pi S ≤ pi ((((S ∩ K0) \ S1) ∪ S1) ∪ K0ᶜ) := measure_mono hsub
      _ ≤ pi (((S ∩ K0) \ S1) ∪ S1) + pi K0ᶜ := measure_union_le _ _
      _ ≤ pi ((S ∩ K0) \ S1) + pi S1 + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ K0) \ S1) + pi S1 := by rw [hK0c, add_zero]
  have hcov2 : pi Sᶜ ≤ pi ((K0 \ S) \ S2) + pi S2 := by
    have hsub : Sᶜ ⊆ (((K0 \ S) \ S2) ∪ S2) ∪ K0ᶜ := by
      intro x hx
      by_cases hxK : x ∈ K0
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · exact Or.inl (Or.inl ⟨⟨hxK, hx⟩, hxS2⟩)
      · exact Or.inr hxK
    calc pi Sᶜ ≤ pi ((((K0 \ S) \ S2) ∪ S2) ∪ K0ᶜ) := measure_mono hsub
      _ ≤ pi (((K0 \ S) \ S2) ∪ S2) + pi K0ᶜ := measure_union_le _ _
      _ ≤ pi ((K0 \ S) \ S2) + pi S2 + pi K0ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((K0 \ S) \ S2) + pi S2 := by rw [hK0c, add_zero]
  -- the separation, with an absolute constant
  have hsep : ∀ u ∈ S1, ∀ v ∈ S2, δ / (2 * (n : ℝ)) ≤ dist u v := by
    intro u hu v hv
    have hu1 := (hmem1 u).1 hu
    have hv1 := (hmem2 v).1 hv
    have huK : u ∈ K := hK0K hu1.1.2
    have hvK : v ∈ K := hK0K hv1.1.1
    have hu0 : u ∉ StuckPoints K δ := hu1.1.2.2
    have hu8 : 4 * speedyWalk K δ u Sᶜ < 1 := by rw [hPdef] at hu1; exact hu1.2
    have hv8 : 4 * speedyWalk K δ v Sᶜᶜ < 1 := by
      rw [compl_compl, hPdef] at *
      exact hv1.2
    exact (lt_dist_of_speedyWalk_lt hn hK hconv hδ huK hvK hu0 hSm.compl hu8 hv8).le
  -- the two branches
  have hkey : pi S ≤ 16 * flow P pi S Sᶜ
      ∨ kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) * pi S ≤ 64 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ K0) \ S1)
    · left
      calc pi S ≤ 2 * pi ((S ∩ K0) \ S1) := hc1
        _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr; exact le_self_add
        _ ≤ 2 * (8 * flow P pi S Sᶜ) := by gcongr
        _ = 16 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((K0 \ S) \ S2)
    · left
      calc pi S ≤ pi Sᶜ := hShalf.trans hSc
        _ ≤ 2 * pi ((K0 \ S) \ S2) := hc2
        _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr; exact le_add_self
        _ ≤ 2 * (8 * flow P pi S Sᶜ) := by gcongr
        _ = 16 * flow P pi S Sᶜ := by ring
    right
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi ((S ∩ K0) \ S1) + pi S1) := by gcongr
          _ = 2 * pi ((S ∩ K0) \ S1) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi ((K0 \ S) \ S2) + pi S2) := by gcongr
          _ = 2 * pi ((K0 \ S) \ S2) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h2half : (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := by
      have hhalf : (2:ℝ≥0∞) * (1 / 2) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      calc (1:ℝ≥0∞) = 2 * (1 / 2) := hhalf.symm
        _ ≤ 2 * pi Sᶜ := by gcongr
    have h3 : (1:ℝ≥0∞) ≤ 4 * pi S2 := by
      calc (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := h2half
        _ ≤ 2 * (2 * pi S2) := by gcongr
        _ = 4 * pi S2 := by ring
    have hprod : pi S ≤ 8 * (pi S1 * pi S2) := by
      calc pi S = pi S * 1 := (mul_one _).symm
        _ ≤ 2 * pi S1 * (4 * pi S2) := mul_le_mul' h1.le h3
        _ = 8 * (pi S1 * pi S2) := by ring
    have hisoS := hiso (δ / (2 * (n : ℝ))) hdpos S1 S2 hS1m hS2m hS1K hS2K hsep
    calc kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) * pi S
        ≤ kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) * (8 * (pi S1 * pi S2)) := by gcongr
      _ = 8 * (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) * pi S1 * pi S2) := by ring
      _ ≤ 8 * pi ((K \ S1) \ S2) := by gcongr
      _ ≤ 8 * (pi ((S ∩ K0) \ S1) + pi ((K0 \ S) \ S2)) := by gcongr
      _ ≤ 8 * (8 * flow P pi S Sᶜ) := by gcongr
      _ = 64 * flow P pi S Sᶜ := by ring
  have hswap : ∀ a b c : ℝ≥0∞, a / c * b = a * b / c := by
    intro a b c
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  rcases hkey with h | h
  · calc min ((1:ℝ≥0∞) / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) * pi S
        ≤ (1:ℝ≥0∞) / 16 * pi S := by gcongr; exact min_le_left _ _
      _ = 1 * pi S / 16 := hswap _ _ _
      _ = pi S / 16 := by rw [one_mul]
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)
  · calc min ((1:ℝ≥0∞) / 16) (kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) * pi S
        ≤ kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64 * pi S := by
          gcongr; exact min_le_right _ _
      _ = kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) * pi S / 64 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)

/-! ## 10. End to end: the lazy speedy walk mixes -/

/-- **The lazy speedy walk on a convex `K` mixes to total variation `eps`, from an `M`-warm
start, in

    conductanceMixingTime M (min (1/32) (κ·δ/(256·n))) eps

steps** — i.e. `O(φ⁻² log(M/eps))` steps with `φ = min(1/32, κδ/(256n))`.

Compare `mixesWithin_lazy_ballWalk`, whose `φ` is `min(θ/32, κθ²δ/(128n))` and whose only
proved `θ` is `2⁻ⁿ`.  **Here there is no `θ`**, so the step count is
`O((n/(κδ))² log(M/eps))`: polynomial in `n` whenever `κ` and `δ` are.  The price is
convexity of `K` (`hconv`) and the target measure, which is `ellProb K δ` — see the module
docstring, and `ellMeasure_add_volume_le` for the quantitative comparison with the uniform
measure.

The only unproved input is `hiso`, written out inline; it is an isoperimetric inequality for
`ellProb K δ`, not for the uniform measure on `K`.

See `mixesWithin_lazy_speedyWalk_unitBall` for the check that the hypothesis bundle is
jointly satisfiable rather than vacuously composed. -/
theorem mixesWithin_lazy_speedyWalk (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (ellProb K δ) mu0 t (ENNReal.ofReal eps) := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrev : IsReversible (lazy (speedyWalk K δ)) (ellProb K δ) :=
    isReversible_lazy (isReversible_speedyWalk_prob hK δ)
  have hpsd : HasNonnegSpectrum (lazy (speedyWalk K δ)) (ellProb K δ) :=
    hasNonnegSpectrum_lazy (isReversible_speedyWalk_prob hK δ)
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous hn (ellProb K δ) (ellProb_absolutelyContinuous K δ)
  have hne := rayleighSet_nonempty_of_smallSet (lazy (speedyWalk K δ)) hS0m hS0pos hS0half
  set phi : ℝ := min (1 / 32) (kappa * δ / (256 * (n : ℝ))) with hphidef
  have hphi0 : 0 < phi := lt_min (by norm_num) (by positivity)
  have hphi1 : phi ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hcond := conductance_speedyWalk_ge hn hK hconv hK0 hKtop hδ
    (kappa := ENNReal.ofReal kappa) hiso
  have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
    rw [ENNReal.ofReal_mul hphi0.le]
    norm_num
  have hbranch1 : ENNReal.ofReal phi * 2 ≤ (1 : ℝ≥0∞) / 16 := by
    have h16 : ((1:ℝ≥0∞) / 16) = ENNReal.ofReal ((1:ℝ) / 16) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num
    rw [h16, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := min_le_left (1 / 32 : ℝ) (kappa * δ / (256 * (n : ℝ)))
    rw [← hphidef] at this
    linarith
  have hbranch2 : ENNReal.ofReal phi * 2
      ≤ ENNReal.ofReal kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64 := by
    have hrhs : ENNReal.ofReal kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64
        = ENNReal.ofReal (kappa * (δ / (2 * (n : ℝ))) / 64) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),
        ENNReal.ofReal_mul hkappa.le]
      norm_num
    rw [hrhs, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_right (1 / 32 : ℝ) (kappa * δ / (256 * (n : ℝ)))
    rw [← hphidef] at hmin
    have heq : kappa * δ / (256 * (n : ℝ)) * 2 = kappa * (δ / (2 * (n : ℝ))) / 64 := by
      field_simp
      ring
    nlinarith [hmin]
  have hlazy : ENNReal.ofReal phi
      ≤ conductance (lazy (speedyWalk K δ)) (ellProb K δ) := by
    rw [conductance_lazy]
    have hstep : ENNReal.ofReal phi
        ≤ min ((1:ℝ≥0∞) / 16)
            (ENNReal.ofReal kappa * ENNReal.ofReal (δ / (2 * (n : ℝ))) / 64) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      exact le_min hbranch1 hbranch2
    exact hstep.trans (by gcongr)
  have hcondtop : conductance (lazy (speedyWalk K δ)) (ellProb K δ) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num)
      (conductance_le_one _ _ ⟨S0, hS0m, hS0pos, hS0half⟩)
  have hphireal : phi ≤ (conductance (lazy (speedyWalk K δ)) (ellProb K δ)).toReal := by
    have h := ENNReal.toReal_mono hcondtop hlazy
    rwa [ENNReal.toReal_ofReal hphi0.le] at h
  exact mixesWithin_of_conductance hrev hpsd hne hM hwarm hphi0 hphi1 heps hphireal ht

/-! ## 11. Non-vacuity and the speedy-point hypothesis

Two checks.  First that the hypothesis bundle of `mixesWithin_lazy_speedyWalk` is jointly
satisfiable — the unit ball discharges everything except `hiso`.  Second, the promise of item
3 of the brief: on `SpeedyPoints K δ` the bound `ell ≥ 3/4` holds *by definition*, so it is
free rather than assumed.  Note where that lands: the results above need **no** lower bound
on `ell` at all, so the free `3/4` is not consumed anywhere.  It is recorded because it is
the hypothesis the ball-walk route needs and cannot get. -/

/-- **`ell ≥ 3/4` is free on `SpeedyPoints`, by definition.**  This is the analogue of
`hell` for the speedy walk, and it costs nothing — no geometry, no measurability, no
positivity.  Contrast `ofReal_le_ell_unitBall`, which is the *proved* witness for the ball
walk and gives only `θ = 2⁻ⁿ`.

It is deliberately not used below: `conductance_speedyWalk_ge` needs no lower bound on `ell`
whatsoever, because the reweighting has already divided it out.  The reason a lower bound
cannot simply be *assumed* at `θ = 3/4` is that `K ⊆ SpeedyPoints K δ` is vacuous for any
bounded body, and restricting the walk to `K' = K ∩ SpeedyPoints K δ` only moves the problem:
the overlap estimate for a walk living on `K'` needs `K' ⊆ SpeedyPoints K' δ`, which is
vacuous for the same reason. -/
theorem three_quarters_le_ell_of_mem_speedyPoints {K : Set (EuclideanSpace ℝ (Fin n))}
    {δ : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ SpeedyPoints K δ) :
    (3 : ℝ≥0∞) / 4 ≤ ell K δ x := hx

/-- **Speedy points are never stuck**: `ell ≥ 3/4 > 0`. -/
theorem notMem_stuckPoints_of_mem_speedyPoints {K : Set (EuclideanSpace ℝ (Fin n))}
    {δ : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ SpeedyPoints K δ) :
    x ∉ StuckPoints K δ := by
  intro hstuck
  have h : (3 : ℝ≥0∞) / 4 ≤ 0 := by
    rw [← show ell K δ x = 0 from hstuck]
    exact hx
  exact absurd h (by simp)

/-- **Every hypothesis of `mixesWithin_lazy_speedyWalk` except the isoperimetric one, jointly
discharged on the unit ball.**  The body is the open unit ball — convex, measurable, of
positive finite volume — the start is the target itself (hence `1`-warm), and the step count
is a concrete natural number.  What remains carried is exactly `hiso`.

Note what is *absent* compared with `mixesWithin_lazy_ballWalk_unitBall`: there is no `θ`,
so no exponentially small constant enters the step count. -/
theorem mixesWithin_lazy_speedyWalk_unitBall (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B →
      A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      B ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ A
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ B
        ≤ ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ
            ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ A) \ B))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime 1 (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
      (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
      (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ) t
      (ENNReal.ofReal eps) := by
  haveI : IsProbabilityMeasure (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ) :=
    isProbabilityMeasure_ellProb_of_volume measurableSet_ball volume_unitBall_ne_zero
      volume_unitBall_ne_top hδ
  refine mixesWithin_lazy_speedyWalk hn measurableSet_ball (convex_ball _ _)
    volume_unitBall_ne_zero volume_unitBall_ne_top hδ hkappa hiso le_rfl ?_ heps ht
  simpa using IsWarm.refl (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)

/-- **The witness in packaged form.**  For every dimension `n ≥ 1` and every step `δ > 0`
there is a convex body `K` — the unit ball — such that the speedy walk on it is a Markov
kernel, reversible for a genuine probability measure `ellProb K δ`, which leaves it
invariant, and whose stuck set is null.  Without this every result above could be a true
statement about the zero measure. -/
theorem exists_speedyWalk_witness {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ Convex ℝ K ∧ IsProbabilityMeasure (ellProb K δ) ∧
        IsMarkovKernel (speedyWalk K δ) ∧
        IsReversible (speedyWalk K δ) (ellProb K δ) ∧
        Kernel.Invariant (speedyWalk K δ) (ellProb K δ) ∧
        ellProb K δ (StuckPoints K δ) = 0 :=
  ⟨Metric.ball 0 1, measurableSet_ball, convex_ball _ _,
    isProbabilityMeasure_ellProb_of_volume measurableSet_ball volume_unitBall_ne_zero
      volume_unitBall_ne_top hδ,
    isMarkovKernel_speedyWalk _ _, isReversible_speedyWalk_prob measurableSet_ball δ,
    invariant_speedyWalk measurableSet_ball δ, ellProb_stuckPoints measurableSet_ball δ⟩

/-! ## 12. How far `ellProb K δ` is from the uniform measure on `K`

The stationary measure of the speedy walk is `ell(x) dx / ∫_K ell`, not `dx / vol(K)`.  The
two lemmas below pin the difference **without any hypothesis**, in a subtraction-free form
that stays honest in `ℝ≥0∞`:

* `ellMeasure_le_volume_inter` — the unnormalised `ell`-weight of a set never exceeds its
  volume (`ell ≤ 1`);
* `ellMeasure_add_volume_le` — `vol(S ∩ K) + ∫_K ell ≤ ∫_{S∩K} ell + vol(K)`, i.e. the
  *deficit* `vol(S∩K) - ∫_{S∩K} ell` is at most the global deficit `vol(K) - ∫_K ell`.

Under `Arlib.MarkovChains.IsSmooth K δ s` the global deficit is at most `s·vol(K)`, so the
two measures agree to within `s/(1-s)` in total variation; that division is arithmetic and is
**not** carried out here, so no theorem in this file claims a total-variation bound between
`ellProb K δ` and `Arlib.uniformOn volume K`.  A caller who needs uniform samples on `K` must
supply that step (or the Cousins-Vempala holding-time correspondence) themselves. -/

/-- **The `ell`-weight of a set never exceeds its volume**, since `ell ≤ 1`. -/
theorem ellMeasure_le_volume_inter (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ellMeasure K δ S ≤ volume (S ∩ K) := by
  rw [ellMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  calc ∫⁻ x in S ∩ K, ell K δ x ≤ ∫⁻ _ in S ∩ K, (1 : ℝ≥0∞) :=
        lintegral_mono fun x => ell_le_one K δ x
    _ = volume (S ∩ K) := by rw [setLIntegral_one]

/-- **The local deficit is at most the global deficit**:

    vol(S ∩ K) + ∫_K ell  ≤  ∫_{S ∩ K} ell + vol(K).

Both sides split over `S ∩ K` and `K \ S`, after which the claim is `∫_{K\S} ell ≤ vol(K\S)`.
This is the subtraction-free form of "the density of `ellMeasure` relative to Lebesgue
measure on `K` is within the smoothness deficit of the constant `1`". -/
theorem ellMeasure_add_volume_le (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    volume (S ∩ K) + ellMeasure K δ Set.univ ≤ ellMeasure K δ S + volume K := by
  have hsplitK : (∫⁻ x in S ∩ K, ell K δ x) + (∫⁻ x in K \ S, ell K δ x)
      = ∫⁻ x in K, ell K δ x := by
    have h := lintegral_add_compl (μ := volume.restrict K) (ell K δ) hS
    rw [Measure.restrict_restrict hS, Measure.restrict_restrict hS.compl,
      show Sᶜ ∩ K = K \ S by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
        tauto] at h
    exact h
  have hsplitV : volume K = volume (S ∩ K) + volume (K \ S) := by
    have h := measure_inter_add_sdiff (μ := volume) K hS
    rw [Set.inter_comm K S] at h
    exact h.symm
  have hdiff : ∫⁻ x in K \ S, ell K δ x ≤ volume (K \ S) := by
    calc ∫⁻ x in K \ S, ell K δ x ≤ ∫⁻ _ in K \ S, (1 : ℝ≥0∞) :=
          lintegral_mono fun x => ell_le_one K δ x
      _ = volume (K \ S) := by rw [setLIntegral_one]
  have hSval : ellMeasure K δ S = ∫⁻ x in S ∩ K, ell K δ x := by
    rw [ellMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  rw [ellMeasure_univ, hSval, ← hsplitK, hsplitV]
  calc volume (S ∩ K) + ((∫⁻ x in S ∩ K, ell K δ x) + (∫⁻ x in K \ S, ell K δ x))
      ≤ volume (S ∩ K) + ((∫⁻ x in S ∩ K, ell K δ x) + volume (K \ S)) := by gcongr
    _ = (∫⁻ x in S ∩ K, ell K δ x) + (volume (S ∩ K) + volume (K \ S)) :=
        add_left_comm _ _ _

/-! ## Axiom check -/

#print axioms isMarkovKernel_speedyWalk
#print axioms ell_mul_speedyWalk
#print axioms flow_speedyWalk
#print axioms isReversible_speedyWalk
#print axioms isReversible_speedyWalk_prob
#print axioms invariant_speedyWalk
#print axioms image_homothety_subset_of_convex
#print axioms volume_inter_ball_le_of_convex
#print axioms one_le_speedyWalk_add_speedyWalk_compl
#print axioms lt_dist_of_speedyWalk_lt
#print axioms ellMeasure_stuckPoints
#print axioms ellMeasure_univ_ne_zero
#print axioms exists_smallSet_of_absolutelyContinuous
#print axioms isProbabilityMeasure_ellProb_of_volume
#print axioms conductance_speedyWalk_ge
#print axioms mixesWithin_lazy_speedyWalk
#print axioms three_quarters_le_ell_of_mem_speedyPoints
#print axioms mixesWithin_lazy_speedyWalk_unitBall
#print axioms exists_speedyWalk_witness
#print axioms ellMeasure_le_volume_inter
#print axioms ellMeasure_add_volume_le

end Arlib.MarkovChains
