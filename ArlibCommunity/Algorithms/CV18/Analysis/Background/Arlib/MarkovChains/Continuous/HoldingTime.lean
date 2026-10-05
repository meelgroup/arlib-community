/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyWalk

/-!
# The holding-time correspondence between the ball walk and the speedy walk

`Arlib/MarkovChains/Continuous/BallWalk.lean` builds the ball walk, whose stationary measure
is **exactly** `Arlib.uniformOn volume K`, and `Arlib/MarkovChains/Continuous/SpeedyWalk.lean`
builds the speedy walk, whose conductance is bounded with *no* local-conductance hypothesis
but whose stationary measure is `ellProb K δ`, the law with density proportional to
`ell K δ`.  This file relates the two chains directly, rather than comparing their
stationary measures numerically the way
`Arlib/MarkovChains/Continuous/SpeedyToUniform.lean` does.

The relation is a **time change**.  One step of the ball walk from `x` is: with probability
`ell K δ x` take exactly the step the speedy walk would take, and with the remaining
probability stay at `x`.  So the ball walk is the speedy walk with each state `x` held for a
`Geom(ell K δ x)` number of steps, of mean `(ell K δ x)⁻¹`, and
`(density ∝ ell) × (mean holding time (ell)⁻¹) = (density ∝ 1)` — which is exactly why the
ball walk's stationary measure is uniform while the speedy walk's is not.  Both halves of
that sentence are proved below, the first as `ballWalk_eq_ell_smul_speedyWalk_add` and the
second as `ellMeasure_withDensity_inv_ell`.

## Main results

**The one-step decomposition.**

* `Arlib.MarkovChains.ballWalk_apply_eq_ell_mul_speedyWalk_add` — for measurable `T`,
  `ballWalk K δ x T = ell K δ x * speedyWalk K δ x T + (1 - ell K δ x) * T.indicator 1 x`.
* `Arlib.MarkovChains.ballWalk_eq_ell_smul_speedyWalk_add` — the same statement as an
  equality of measures,
  `ballWalk K δ x = ell K δ x • speedyWalk K δ x + (1 - ell K δ x) • dirac x`.
* `Arlib.MarkovChains.ballWalk_apply_compl_eq_ell_mul_speedyWalk` — the escape identity
  `ballWalk K δ x Aᶜ = ell K δ x * speedyWalk K δ x Aᶜ` for `x ∈ A`: the holding mass lands
  on `x ∈ A` and therefore contributes nothing to `Aᶜ`.

**The exact conductance relation.**

* `Arlib.MarkovChains.flow_ballWalk_eq_flow_speedyWalk` — for **disjoint** `S` and `T` the
  two chains have the *same* ergodic flow, each against its own unnormalised stationary
  measure:
  `flow (ballWalk K δ) (volume.restrict K) S T = flow (speedyWalk K δ) (ellMeasure K δ) S T`.
  Unconditional (no positivity, no finiteness, no convexity).  This is the Dirichlet-form
  comparison in both directions with constant exactly `1`.
* `Arlib.MarkovChains.conductanceOn_ballWalk_mul_volume_inter` and its normalised twin
  `Arlib.MarkovChains.conductanceOn_ballWalk_uniformOn_mul_volume_inter` — **the exact
  conductance relation**
  `Φ_ball(A) · vol(A ∩ K) = Φ_speedy(A) · ellMeasure(A)`,
  stated multiplicatively so that no `ℝ≥0∞` division appears.
* `Arlib.MarkovChains.conductanceOn_ballWalk_le_conductanceOn_speedyWalk` — the inequality
  that follows, `Φ_ball(A) ≤ Φ_speedy(A)`, because `ellMeasure(A) ≤ vol(A ∩ K)`.
* `Arlib.MarkovChains.le_conductanceOn_ballWalk_of_mul_le` — the converse *with its
  hypothesis made explicit*: `c · vol(A ∩ K) ≤ ellMeasure(A)` gives
  `c · Φ_speedy(A) ≤ Φ_ball(A)`.  See "What is not proved" below for why that hypothesis is
  not available for the sets that matter.

**The holding-time identity.**

* `Arlib.MarkovChains.volume_inter_stuckPoints_eq_zero` — for `δ > 0` the stuck points meet
  `K` in a Lebesgue-null set, so `ell K δ > 0` almost everywhere on `K`.
* `Arlib.MarkovChains.ellMeasure_withDensity_inv_ell` — **the prize of this file**:
  `(ellMeasure K δ).withDensity (ell K δ)⁻¹ = volume.restrict K`.  Reweighting the speedy
  walk's stationary measure by the *mean holding time* returns Lebesgue measure on `K`
  **exactly** — there is no error term anywhere in this statement.
* `Arlib.MarkovChains.lintegral_inv_ell_ellMeasure` — its scalar form,
  `∫ (ell)⁻¹ dellMeasure = vol(K)`.
* `Arlib.MarkovChains.mul_lintegral_inv_ell_ellProb_le_one`,
  `Arlib.MarkovChains.lintegral_inv_ell_ellProb_le` — **the multiplicative cost**: under
  `IsSmooth K δ s` the mean holding time in stationarity is at most `(1 - s)⁻¹`, i.e. one
  speedy step costs at most `(1 - s)⁻¹` ball-walk steps on average.

**Non-vacuity.**

* `Arlib.MarkovChains.exists_holdingTime_witness` — the unit ball with `0 < δ ≤ 1/2` and the
  concentric half-ball satisfy every guard of every theorem above simultaneously, with
  `uniformOn volume K` and `ellProb K δ` genuine probability measures and both
  `vol(A ∩ K)` and `ellMeasure K δ A` strictly positive and finite.

## What is not proved

This is the honest scope statement; nothing below claims more.

1. **No lower bound on the ball walk's conductance is proved, and none follows from the
   speedy walk's.**  `conductanceOn_ballWalk_mul_volume_inter` is an *equality*, and it makes
   the obstruction exact: `Φ_ball(A) = Φ_speedy(A) · ellMeasure(A)/vol(A ∩ K)`, so a lower
   bound on `Φ_ball` needs a lower bound on the *average of `ell` over `A`*, for every
   admissible `A`.  `IsSmooth K δ s` bounds that average over `A = K` only, and a set `A`
   hugging the boundary of `K` has a much smaller average.  The uniform-in-`x` route is
   worse: the only proved pointwise bound for a convex body is `ell ≥ 2⁻ⁿ`
   (`Arlib.MarkovChains.ofReal_le_ell_unitBall` and `conductance_ballWalk_ge` in
   `BallWalkConductance.lean`), which certifies an exponential step count.  This is not a gap
   in the proof: the ball walk's conductance really is smaller than the speedy walk's, by the
   exact factor computed here.
2. **No mixing-time statement for the ball walk is proved here.**  The step from the
   one-step decomposition to "the ball walk's `t`-step law is close to `uniformOn volume K`"
   requires the *trajectory*-level correspondence: conditionally on the sequence of accepted
   positions `Y₀, Y₁, …` the holding times are independent geometrics with parameters
   `ell K δ (Yᵢ)`, so the ball walk at time `t` is `Y_{N t}` for a random index `N t` that is
   **not** independent of `Y`.  Turning `mul_lintegral_inv_ell_ellProb_le_one` (a statement
   about the mean holding time *in stationarity*) into a concentration bound for `N t`
   along a trajectory is the missing step.

   **This note used to say the blocker was that `ProbabilityTheory.Kernel.traj`-level
   machinery "no file in this library currently has". That was wrong on both counts.**
   Mathlib v4.32 ships the full Ionescu–Tulcea development
   (`Mathlib/Probability/Kernel/IonescuTulcea/{PartialTraj,Traj,Maps}.lean`), and this
   repository was *already* using it — `Ttc/Coupling/Family.lean` calls
   `Kernel.trajMeasure` for the Poisson family. `TrajTransfer.lean` now builds the
   trajectory layer on it: `condDistrib_pathMeasure_ballWalk` lifts
   `ballWalk_eq_ell_smul_speedyWalk_add` from one step to the law of the whole path,
   and `pathMeasure_ballWalk_dirac_holdsUntil` /
   `lintegral_exitTime_pathMeasure_ballWalk` prove each sojourn is exactly
   `Geometric (ell K δ x)` with mean exactly `(ell K δ x)⁻¹` — which closes the
   interpretive gap in item 3 below, since the density `(ell)⁻¹` is now *proved* to be
   a mean holding time rather than a formal reciprocal.

   **What is still missing is the time change itself**, and it is ordinary work rather
   than a missing API: extracting the jump chain `Y₀, Y₁, …` and the counting process
   `N t` from a path, and proving `ω_t = Y_{N t}`, needs measurability of the
   successive jump times, which nothing here has yet.
3. **`ellMeasure_withDensity_inv_ell` is a statement about measures, not about kernels.**  It
   says the reweighting is exact; it does *not* by itself say that the ball walk converges to
   the reweighted measure, which is `invariant_ballWalk` (already proved in `BallWalk.lean`)
   plus item 2.

## Conventions

Everything is stated for the *unnormalised* pairs `(ballWalk, volume.restrict K)` and
`(speedyWalk, ellMeasure K δ)` first, because in that form the flow identity is
unconditional and division-free; the normalised pairs `(ballWalk, uniformOn volume K)` and
`(speedyWalk, ellProb K δ)` are recovered through `conductanceOn_smul`, which costs the
guards `0 < vol(K) < ⊤` and `0 < ∫_K ell`.

No `def`, `structure` or named `Prop` is introduced by this file.  Every hypothesis is an
inline hypothesis of the theorem that consumes it.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 0. A conductance identity valid at zero measure

`Conductance.flow_eq_conductanceOn_mul` needs `0 < pi S`.  The product form survives the
degenerate case, because `ℝ≥0∞` multiplication kills the zero factor and
`Conductance.flow_le` kills the flow; that is what lets the comparison below be stated
without a positivity guard on `A`. -/

section General

/-- **Cancelling a positive finite factor on the right in `ℝ≥0∞`.**  From `a * c ≤ b * c`
with `c ≠ 0` and `c ≠ ⊤` one gets `a ≤ b`, by multiplying through by `c⁻¹`.  Both guards are
needed: at `c = 0` and at `c = ⊤` the hypothesis carries no information. -/
theorem le_of_mul_le_mul_right_of_ne {a b c : ℝ≥0∞} (h : a * c ≤ b * c) (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) : a ≤ b := by
  have h' : a * c * c⁻¹ ≤ b * c * c⁻¹ := mul_le_mul_left h _
  rwa [mul_assoc, ENNReal.mul_inv_cancel hc0 hct, mul_one, mul_assoc,
    ENNReal.mul_inv_cancel hc0 hct, mul_one] at h'

variable {Om : Type*} [MeasurableSpace Om]

/-- **The escape flow is the conductance times the measure**, with no positivity hypothesis.

Assumes only that `P` is a Markov kernel and that `pi S` is finite.  At `pi S = 0` both
sides are `0`: the left because `a * 0 = 0` in `ℝ≥0∞`, the right because the flow out of `S`
is at most `pi S` (`flow_le`).  This is `flow_eq_conductanceOn_mul` with its positivity
hypothesis removed. -/
theorem conductanceOn_mul_measure (P : Kernel Om Om) [IsMarkovKernel P] (pi : Measure Om)
    {S : Set Om} (hfin : pi S ≠ ⊤) : conductanceOn P pi S * pi S = flow P pi S Sᶜ := by
  rcases eq_or_ne (pi S) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact (le_antisymm ((flow_le P pi S Sᶜ).trans h0.le) (zero_le)).symm
  · exact flow_eq_conductanceOn_mul P pi (pos_iff_ne_zero.2 h0) hfin

end General

/-! ## 1. The one-step decomposition

The ball walk from `x` is a two-point mixture of the speedy walk from `x` and the point mass
at `x`, with weights `ell K δ x` and `1 - ell K δ x`.  This is the exact sense in which "the
ball walk is the speedy walk with geometric holding times", read one step at a time. -/

/-- **The ball walk is the speedy walk held at `x`.**  For every measurable `T`,

    ballWalk K δ x T = ell K δ x * speedyWalk K δ x T + (1 - ell K δ x) * 1[x ∈ T].

Assumes only `MeasurableSet K` and `MeasurableSet T`; no positivity of `δ`, no convexity, no
bound on `vol K`.  At a stuck `x` (where `ell K δ x = 0` and the speedy walk parks at `x`)
both sides are `1[x ∈ T]`.

Proved by matching `ballWalk_apply_set` against `ell_mul_speedyWalk`: the `ell K δ x` of the
mixture weight cancels the normalising `vol(B(x,δ) ∩ K)` inside the speedy kernel, leaving
the ball walk's own proposal term. -/
theorem ballWalk_apply_eq_ell_mul_speedyWalk_add {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    ballWalk K δ x T
      = ell K δ x * speedyWalk K δ x T + (1 - ell K δ x) * T.indicator 1 x := by
  have hset : T ∩ (Metric.ball x δ ∩ K) = (T ∩ K) ∩ Metric.ball x δ := by
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [ballWalk_apply_set hK δ x hT, ell_mul_speedyWalk hK δ x hT, hset, volume_ball_eq]

/-- **The one-step decomposition as an equality of measures**:

    ballWalk K δ x = ell K δ x • speedyWalk K δ x + (1 - ell K δ x) • dirac x.

Assumes only `MeasurableSet K`.  This is the statement that a single ball-walk step is
"take a speedy step with probability `ell K δ x`, otherwise stay put", which is the
one-step content of the holding-time correspondence. -/
theorem ballWalk_eq_ell_smul_speedyWalk_add {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ballWalk K δ x
      = ell K δ x • speedyWalk K δ x + (1 - ell K δ x) • Measure.dirac x := by
  ext T hT
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply' _ hT, ballWalk_apply_eq_ell_mul_speedyWalk_add hK δ x hT]

/-- **The holding mass is invisible to any event the walk is not already in.**  If `x ∉ T`
then the stay-put atom contributes nothing, so

    ballWalk K δ x T = ell K δ x * speedyWalk K δ x T.

Assumes `MeasurableSet K` and `MeasurableSet T`. -/
theorem ballWalk_apply_eq_ell_mul_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) (hx : x ∉ T) :
    ballWalk K δ x T = ell K δ x * speedyWalk K δ x T := by
  rw [ballWalk_apply_eq_ell_mul_speedyWalk_add hK δ x hT, Set.indicator_of_notMem hx, mul_zero,
    add_zero]

/-- **The escape identity.**  From a point `x` of `A`, the ball walk leaves `A` exactly when
the speedy walk does, at rate `ell K δ x`:

    ballWalk K δ x Aᶜ = ell K δ x * speedyWalk K δ x Aᶜ.

Assumes `MeasurableSet K`, `MeasurableSet A` and `x ∈ A`.  This is the identity every
conductance comparison in this file is built on. -/
theorem ballWalk_apply_compl_eq_ell_mul_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ A) :
    ballWalk K δ x Aᶜ = ell K δ x * speedyWalk K δ x Aᶜ :=
  ballWalk_apply_eq_ell_mul_speedyWalk hK δ x hA.compl (by simpa using hx)

/-! ## 2. The exact conductance relation

Weighted by their own unnormalised stationary measures, the two chains have *identical*
ergodic flows between disjoint sets.  Everything in this section is a consequence. -/

/-- **The two chains have the same ergodic flow between disjoint sets**:

    flow (ballWalk K δ) (volume.restrict K) S T = flow (speedyWalk K δ) (ellMeasure K δ) S T
      whenever `Disjoint S T`.

Assumes `MeasurableSet K`, `MeasurableSet S`, `MeasurableSet T` and disjointness — nothing
else: no positivity of `δ`, no convexity, no bound on `vol K`.

Both flows were already computed in terms of the symmetric ball relation
(`flow_ballWalk`, `flow_speedyWalk`); they differ only by the ball walk's holding term
`∫_{T ∩ S ∩ K} (1 - ell)`, whose domain of integration is empty when `S` and `T` are
disjoint.

This is the Dirichlet-form comparison "in both directions with the exact constant": the
constant is `1`. -/
theorem flow_ballWalk_eq_flow_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint S T) :
    flow (ballWalk K δ) (volume.restrict K) S T
      = flow (speedyWalk K δ) (ellMeasure K δ) S T := by
  have hempty : T ∩ (S ∩ K) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
    exact Set.disjoint_left.1 hd hy.2.1 hy.1
  rw [flow_ballWalk hK δ hS hT, flow_speedyWalk hK δ hS hT, hempty]
  simp

/-- **The escape flows agree**:

    flow (ballWalk K δ) (volume.restrict K) S Sᶜ = flow (speedyWalk K δ) (ellMeasure K δ) S Sᶜ.

Assumes `MeasurableSet K` and `MeasurableSet S`.  Specialisation of
`flow_ballWalk_eq_flow_speedyWalk` to `T = Sᶜ`. -/
theorem flow_ballWalk_compl_eq_flow_speedyWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) :
    flow (ballWalk K δ) (volume.restrict K) S Sᶜ
      = flow (speedyWalk K δ) (ellMeasure K δ) S Sᶜ :=
  flow_ballWalk_eq_flow_speedyWalk hK δ hS hS.compl disjoint_compl_right

/-- **The exact conductance relation**, unnormalised form:

    Φ_ball(A) · vol(A ∩ K)  =  Φ_speedy(A) · ellMeasure(A),

where `Φ_ball` is `conductanceOn (ballWalk K δ) (volume.restrict K)` and `Φ_speedy` is
`conductanceOn (speedyWalk K δ) (ellMeasure K δ)`.

Assumes `MeasurableSet K`, `MeasurableSet A` and `vol K ≠ ⊤`; in particular **no positivity
hypothesis on `A`** — at `vol(A ∩ K) = 0` both sides are `0`
(`conductanceOn_mul_measure`).

The product form is deliberate: it carries the same information as the quotient
`Φ_ball(A) = Φ_speedy(A) · ellMeasure(A)/vol(A ∩ K)` without any `ℝ≥0∞` division. -/
theorem conductanceOn_ballWalk_mul_volume_inter {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hKtop : volume K ≠ ⊤) :
    conductanceOn (ballWalk K δ) (volume.restrict K) A * volume (A ∩ K)
      = conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * ellMeasure K δ A := by
  have hb : (volume.restrict K) A = volume (A ∩ K) := Measure.restrict_apply hA
  have hbtop : (volume.restrict K) A ≠ ⊤ := by
    rw [hb]
    exact ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  have hstop : ellMeasure K δ A ≠ ⊤ := by
    refine ne_top_of_le_ne_top hbtop ?_
    rw [hb]
    exact ellMeasure_le_volume_inter K δ hA
  rw [← hb, conductanceOn_mul_measure _ _ hbtop, conductanceOn_mul_measure _ _ hstop,
    flow_ballWalk_compl_eq_flow_speedyWalk hK δ hA]

/-- **The exact conductance relation**, for the two *probability* measures:

    Φ_ball(A) · vol(A ∩ K)  =  Φ_speedy(A) · ellMeasure(A),

with `Φ_ball = conductanceOn (ballWalk K δ) (Arlib.uniformOn volume K)` and
`Φ_speedy = conductanceOn (speedyWalk K δ) (ellProb K δ)`.

Assumes `MeasurableSet K`, `MeasurableSet A`, `0 < vol K < ⊤` and `∫_K ell ≠ 0`.  The four
guards are exactly what makes the two normalising constants positive and finite, so that
`conductanceOn_smul` transports `conductanceOn_ballWalk_mul_volume_inter` unchanged; they are
discharged for the unit ball in `exists_holdingTime_witness`. -/
theorem conductanceOn_ballWalk_uniformOn_mul_volume_inter {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) (hL0 : ellMeasure K δ Set.univ ≠ 0) :
    conductanceOn (ballWalk K δ) (Arlib.uniformOn volume K) A * volume (A ∩ K)
      = conductanceOn (speedyWalk K δ) (ellProb K δ) A * ellMeasure K δ A := by
  have hLtop : ellMeasure K δ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ)
  rw [Arlib.uniformOn_def,
    conductanceOn_smul _ _ (ENNReal.inv_ne_zero.2 hKtop) (ENNReal.inv_ne_top.2 hK0),
    ellProb, conductanceOn_smul _ _ (ENNReal.inv_ne_zero.2 hLtop) (ENNReal.inv_ne_top.2 hL0)]
  exact conductanceOn_ballWalk_mul_volume_inter hK δ hA hKtop

/-- **The ball walk's conductance is at most the speedy walk's, set by set**:

    Φ_ball(A) ≤ Φ_speedy(A).

Assumes `MeasurableSet K`, `MeasurableSet A`, `vol(A ∩ K) ≠ 0` and `vol K ≠ ⊤`.

Immediate from the exact relation and `ellMeasure(A) ≤ vol(A ∩ K)` (`ell ≤ 1`).  Note the
direction: **this inequality is useless for transferring a conductance lower bound from the
speedy walk to the ball walk**, and it is not an artefact of the proof — by the exact
relation the loss is precisely the average of `ell` over `A`, and that average genuinely
tends to `0` for sets hugging the boundary of `K`.  `le_conductanceOn_ballWalk_of_mul_le` is
the converse and states the hypothesis one would have to supply. -/
theorem conductanceOn_ballWalk_le_conductanceOn_speedyWalk
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (h0 : volume (A ∩ K) ≠ 0)
    (hKtop : volume K ≠ ⊤) :
    conductanceOn (ballWalk K δ) (volume.restrict K) A
      ≤ conductanceOn (speedyWalk K δ) (ellMeasure K δ) A := by
  have htop : volume (A ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  have hkey := conductanceOn_ballWalk_mul_volume_inter hK δ hA hKtop
  have hle : conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * ellMeasure K δ A
      ≤ conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * volume (A ∩ K) :=
    mul_le_mul_right (ellMeasure_le_volume_inter K δ hA) _
  exact le_of_mul_le_mul_right_of_ne (hkey.trans_le hle) h0 htop

/-- **The converse, with its hypothesis in the open.**  If the `ell`-weight of `A` is at
least a `c`-fraction of the volume of `A ∩ K` — i.e. if the *average of `ell` over `A`* is at
least `c` — then

    c · Φ_speedy(A) ≤ Φ_ball(A).

Assumes `MeasurableSet K`, `MeasurableSet A`, `vol K ≠ ⊤`, `vol(A ∩ K) ≠ 0` and the stated
bound `c * vol(A ∩ K) ≤ ellMeasure K δ A`.

This lemma is stated to make the obstruction precise, not because the hypothesis is
available: to bound `conductance (ballWalk K δ) (uniformOn volume K)` one needs it for
*every* admissible `A`, and `IsSmooth K δ s` supplies it only for `A = K`.  Nothing in this
library proves it for all `A` with a `c` better than the exponentially small `2⁻ⁿ` of
`BallWalkConductance.lean`. -/
theorem le_conductanceOn_ballWalk_of_mul_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : c * volume (A ∩ K) ≤ ellMeasure K δ A) (hKtop : volume K ≠ ⊤)
    (h0 : volume (A ∩ K) ≠ 0) :
    c * conductanceOn (speedyWalk K δ) (ellMeasure K δ) A
      ≤ conductanceOn (ballWalk K δ) (volume.restrict K) A := by
  have htop : volume (A ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  have hkey := conductanceOn_ballWalk_mul_volume_inter hK δ hA hKtop
  refine le_of_mul_le_mul_right_of_ne ?_ h0 htop
  calc c * conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * volume (A ∩ K)
      = conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * (c * volume (A ∩ K)) := by ring
    _ ≤ conductanceOn (speedyWalk K δ) (ellMeasure K δ) A * ellMeasure K δ A :=
        mul_le_mul_right hc _
    _ = conductanceOn (ballWalk K δ) (volume.restrict K) A * volume (A ∩ K) := hkey.symm

/-! ## 3. The holding-time identity

The mean holding time of the ball walk at `x` is `(ell K δ x)⁻¹`.  Weighting the speedy
walk's stationary measure `ell(x) dx` by it gives `dx` — Lebesgue measure on `K`, exactly.
The only thing to check is that the reweighting is not corrupted by the points where
`ell = 0`, and those form a null subset of `K` as soon as `δ > 0`. -/

/-- **The stuck points are Lebesgue-null inside `K`**, for every `δ > 0` and every `K`
(measurability of `K` is not needed).

If `x ∈ K` has `vol(B(x,δ) ∩ K) = 0` then every ball of radius `δ/2` centred within `δ/2` of
`x` also meets `K ∩ StuckPoints` in a null set, because it is contained in `B(x,δ)`.  A
countable dense set of centres covers `K ∩ StuckPoints` by such balls, so the whole set is
null.

This is what makes `ell K δ` almost everywhere positive on `K`, hence invertible. -/
theorem volume_inter_stuckPoints_eq_zero (K : Set (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hδ : 0 < δ) : volume (K ∩ StuckPoints K δ) = 0 := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin n))
  have hcov : K ∩ StuckPoints K δ ⊆
      ⋃ d ∈ D, (K ∩ StuckPoints K δ) ∩ Metric.ball d (δ / 2) := by
    intro x hx
    have hx' : x ∈ closure D := by rw [hDd.closure_eq]; trivial
    obtain ⟨d, hdD, hdx⟩ := Metric.mem_closure_iff.1 hx' (δ / 2) (by positivity)
    exact Set.mem_biUnion hdD ⟨hx, Metric.mem_ball.2 hdx⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hDc).2 fun d _ => ?_)
  rcases Set.eq_empty_or_nonempty ((K ∩ StuckPoints K δ) ∩ Metric.ball d (δ / 2)) with
    he | ⟨z, hz⟩
  · rw [he]
    exact measure_empty
  · refine measure_mono_null (fun y hy => ?_) (mem_stuckPoints_iff.1 hz.1.2)
    have h1 : dist y d < δ / 2 := Metric.mem_ball.1 hy.2
    have h2 : dist z d < δ / 2 := Metric.mem_ball.1 hz.2
    refine ⟨Metric.mem_ball.2 ?_, hy.1.1⟩
    calc dist y z ≤ dist y d + dist d z := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by rw [dist_comm d z]; exact add_lt_add h1 h2
      _ = δ := by ring

/-- **`ell K δ` is almost everywhere non-zero on `K`.**  Assumes `MeasurableSet K` and
`δ > 0`.  Restatement of `volume_inter_stuckPoints_eq_zero`. -/
theorem ae_restrict_ell_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᵐ x ∂(volume.restrict K), ell K δ x ≠ 0 := by
  rw [ae_iff]
  have hset : {x : EuclideanSpace ℝ (Fin n) | ¬ ell K δ x ≠ 0} = StuckPoints K δ := by
    ext x
    simp [StuckPoints]
  rw [hset, Measure.restrict_apply' hK, Set.inter_comm]
  exact volume_inter_stuckPoints_eq_zero K hδ

/-- **The holding-time identity.**

    (ellMeasure K δ).withDensity (ell K δ)⁻¹ = volume.restrict K.

Assumes `MeasurableSet K` and `δ > 0`, and **nothing else** — no convexity, no smoothness,
no bound on `vol K`.

In words: the speedy walk's (unnormalised) stationary measure `ell(x) dx` on `K`, reweighted
by the mean holding time `(ell x)⁻¹` of the ball walk at `x`, is *exactly* Lebesgue measure
on `K`.  There is no error term: this is the reason the ball walk's stationary measure is
exactly `Arlib.uniformOn volume K` (`invariant_ballWalk`) while the speedy walk's is
`ellProb K δ`, and it is the measure-level form of the correspondence
`(density ∝ ell) × (mean holding time (ell)⁻¹) = uniform`.

It is a statement about *measures only*.  It does not assert anything about the ball walk's
convergence; see the module docstring, "What is not proved", item 2. -/
theorem ellMeasure_withDensity_inv_ell {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) :
    (ellMeasure K δ).withDensity (fun x => (ell K δ x)⁻¹) = volume.restrict K := by
  rw [ellMeasure]
  exact withDensity_inv_same (measurable_ell hK δ) (ae_restrict_ell_ne_zero hK hδ)
    (Filter.Eventually.of_forall fun x =>
      ((ell_le_one K δ x).trans_lt ENNReal.one_lt_top).ne)

/-- **The total mean holding time**: `∫ (ell K δ)⁻¹ dellMeasure = vol(K)`.

Assumes `MeasurableSet K` and `δ > 0`.  The scalar form of `ellMeasure_withDensity_inv_ell`,
obtained by evaluating both measures on `Set.univ`. -/
theorem lintegral_inv_ell_ellMeasure {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x, (ell K δ x)⁻¹ ∂(ellMeasure K δ) = volume K := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ)
    (ellMeasure_withDensity_inv_ell hK hδ)
  simpa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h

/-- **`IsSmooth` in terms of `ellMeasure`**: `(1 - s) · vol(K) ≤ ellMeasure K δ univ`.

This is `IsSmooth K δ s` with `∫_K ell` written as the total mass of `ellMeasure K δ`. -/
theorem ellMeasure_univ_ge_of_isSmooth {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {s : ℝ≥0∞} (hs : IsSmooth K δ s) : (1 - s) * volume K ≤ ellMeasure K δ Set.univ := by
  rw [ellMeasure_univ]
  exact hs

/-- **The multiplicative cost of the time change.**  Under `IsSmooth K δ s`,

    (1 - s) · ∫ (ell K δ)⁻¹ dellProb ≤ 1,

i.e. the mean holding time of the ball walk, averaged over the speedy walk's stationary
distribution, is at most `(1 - s)⁻¹`.  Equivalently: in stationarity one speedy step costs at
most `(1 - s)⁻¹` ball-walk steps on average.

Assumes `MeasurableSet K`, `δ > 0`, `vol K ≠ 0`, `vol K ≠ ⊤` and `IsSmooth K δ s`.  Stated
multiplicatively so that it says the right thing at `s = 1` (where the bound is vacuous) and
carries no `ℝ≥0∞` division; `lintegral_inv_ell_ellProb_le` is the divided form.

This is the constant referred to in the module docstring: `s` is a *factor on the step
count*, not a floor on the error.  It is **not** a mixing statement — see "What is not
proved", item 2. -/
theorem mul_lintegral_inv_ell_ellProb_le_one {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {s : ℝ≥0∞} (hs : IsSmooth K δ s) :
    (1 - s) * ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ) ≤ 1 := by
  have hL0 : ellMeasure K δ Set.univ ≠ 0 := ellMeasure_univ_ne_zero hK hK0 hδ
  have hLtop : ellMeasure K δ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ)
  have hint : ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ)
      = (ellMeasure K δ Set.univ)⁻¹ * volume K := by
    rw [ellProb, lintegral_smul_measure, smul_eq_mul, lintegral_inv_ell_ellMeasure hK hδ]
  rw [hint]
  calc (1 - s) * ((ellMeasure K δ Set.univ)⁻¹ * volume K)
      = (ellMeasure K δ Set.univ)⁻¹ * ((1 - s) * volume K) := by ring
    _ ≤ (ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ Set.univ :=
        mul_le_mul_right (ellMeasure_univ_ge_of_isSmooth hs) _
    _ = 1 := ENNReal.inv_mul_cancel hL0 hLtop

/-- **The mean holding time is at most `(1 - s)⁻¹`.**  The divided form of
`mul_lintegral_inv_ell_ellProb_le_one`, valid when `s < 1`.

Assumes `MeasurableSet K`, `δ > 0`, `vol K ≠ 0`, `vol K ≠ ⊤`, `IsSmooth K δ s` and `s < 1`. -/
theorem lintegral_inv_ell_ellProb_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {s : ℝ≥0∞} (hs : IsSmooth K δ s) (hs1 : s < 1) :
    ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ) ≤ (1 - s)⁻¹ := by
  have hpos : (1 : ℝ≥0∞) - s ≠ 0 := (tsub_pos_of_lt hs1).ne'
  refine ENNReal.le_inv_iff_mul_le.2 ?_
  rw [mul_comm]
  exact mul_lintegral_inv_ell_ellProb_le_one hK hδ hK0 hKtop hs

/-! ## 4. Non-vacuity

`volume K ∈ {0, ⊤}` makes `Arlib.uniformOn volume K` the zero measure and several statements
above true-but-empty.  The unit ball discharges every guard at once. -/

/-- **Set values of `ellMeasure`**: `ellMeasure K δ S = ∫_{S ∩ K} ell`.  Assumes
`MeasurableSet S`. -/
theorem ellMeasure_apply_eq_setLIntegral (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ellMeasure K δ S = ∫⁻ x in S ∩ K, ell K δ x := by
  rw [ellMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]

/-- **The `ell`-weight of the concentric half-ball of the unit ball is its volume**, for
`0 < δ ≤ 1/2`: the half-ball sits inside `B(0, 1 - δ)`, where the local conductance is
identically `1` (`ell_unitBall_eq_one_of_mem`). -/
theorem ellMeasure_unitBall_half {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ellMeasure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
      = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Metric.ball_subset_ball (by norm_num)
  rw [ellMeasure_apply_eq_setLIntegral _ δ measurableSet_ball,
    Set.inter_eq_self_of_subset_left hsub,
    setLIntegral_congr_fun (g := fun _ => (1 : ℝ≥0∞)) measurableSet_ball
      (fun x hx => ell_unitBall_eq_one_of_mem hδ
        (Metric.ball_subset_ball (by linarith) hx)),
    setLIntegral_one]

/-- **The non-vacuity witness (`CLAUDE.md` section 11).**  For every dimension `n` and every
step `0 < δ ≤ 1/2` there are a body `K` — the unit ball — and a test set `A` — the concentric
half-ball — such that

* `K` and `A` are measurable and `0 < vol K < ⊤`, so `ballWalk K δ` and `speedyWalk K δ` are
  the real kernels and not the fallback;
* `Arlib.uniformOn volume K` and `ellProb K δ` are genuine probability measures, not the zero
  measure;
* the total `ell`-weight `ellMeasure K δ univ` is non-zero, which is the guard
  `conductanceOn_ballWalk_uniformOn_mul_volume_inter` needs;
* both `vol(A ∩ K)` and `ellMeasure K δ A` are **strictly positive and finite**, so the exact
  conductance relation is not the identity `0 = 0`;
* the holding-time identity `(ellMeasure K δ).withDensity (ell K δ)⁻¹ = volume.restrict K`
  holds, with `volume.restrict K` a non-zero measure;
* the exact conductance relation holds for this `K` and this `A`.

What this witness does **not** claim: that either conductance is positive.  A positive lower
bound on `conductanceOn (speedyWalk K δ) (ellProb K δ) A` is `conductance_speedyWalk_ge`
territory and needs an isoperimetric input; nothing in this file provides one. -/
theorem exists_holdingTime_witness {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ K A : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ MeasurableSet A ∧
        volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        IsProbabilityMeasure (Arlib.uniformOn volume K) ∧
        IsProbabilityMeasure (ellProb K δ) ∧
        ellMeasure K δ Set.univ ≠ 0 ∧
        0 < volume (A ∩ K) ∧ volume (A ∩ K) ≠ ⊤ ∧
        0 < ellMeasure K δ A ∧ ellMeasure K δ A ≠ ⊤ ∧
        (ellMeasure K δ).withDensity (fun x => (ell K δ x)⁻¹) = volume.restrict K ∧
        conductanceOn (ballWalk K δ) (Arlib.uniformOn volume K) A * volume (A ∩ K)
          = conductanceOn (speedyWalk K δ) (ellProb K δ) A * ellMeasure K δ A := by
  refine ⟨Metric.ball 0 1, Metric.ball 0 (1 / 2), measurableSet_ball, measurableSet_ball,
    volume_unitBall_ne_zero, volume_unitBall_ne_top, isProbabilityMeasure_uniformOn_unitBall,
    isProbabilityMeasure_ellProb_of_volume measurableSet_ball volume_unitBall_ne_zero
      volume_unitBall_ne_top hδ,
    ellMeasure_univ_ne_zero measurableSet_ball volume_unitBall_ne_zero hδ, ?_, ?_, ?_, ?_,
    ellMeasure_withDensity_inv_ell measurableSet_ball hδ,
    conductanceOn_ballWalk_uniformOn_mul_volume_inter measurableSet_ball δ measurableSet_ball
      volume_unitBall_ne_zero volume_unitBall_ne_top
      (ellMeasure_univ_ne_zero measurableSet_ball volume_unitBall_ne_zero hδ)⟩
  · rw [Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball (by norm_num : (1:ℝ)/2 ≤ 1))]
    exact Metric.measure_ball_pos volume 0 (by norm_num)
  · rw [Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball (by norm_num : (1:ℝ)/2 ≤ 1))]
    exact measure_ball_lt_top.ne
  · rw [ellMeasure_unitBall_half hδ hδ1]
    exact Metric.measure_ball_pos volume 0 (by norm_num)
  · rw [ellMeasure_unitBall_half hδ hδ1]
    exact measure_ball_lt_top.ne

/-! ## Axiom audit

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else (in particular `sorryAx`) means the
file is not finished. -/

#print axioms le_of_mul_le_mul_right_of_ne
#print axioms conductanceOn_mul_measure
#print axioms ballWalk_apply_eq_ell_mul_speedyWalk_add
#print axioms ballWalk_eq_ell_smul_speedyWalk_add
#print axioms ballWalk_apply_eq_ell_mul_speedyWalk
#print axioms ballWalk_apply_compl_eq_ell_mul_speedyWalk
#print axioms flow_ballWalk_eq_flow_speedyWalk
#print axioms flow_ballWalk_compl_eq_flow_speedyWalk
#print axioms conductanceOn_ballWalk_mul_volume_inter
#print axioms conductanceOn_ballWalk_uniformOn_mul_volume_inter
#print axioms conductanceOn_ballWalk_le_conductanceOn_speedyWalk
#print axioms le_conductanceOn_ballWalk_of_mul_le
#print axioms volume_inter_stuckPoints_eq_zero
#print axioms ae_restrict_ell_ne_zero
#print axioms ellMeasure_withDensity_inv_ell
#print axioms lintegral_inv_ell_ellMeasure
#print axioms ellMeasure_univ_ge_of_isSmooth
#print axioms mul_lintegral_inv_ell_ellProb_le_one
#print axioms lintegral_inv_ell_ellProb_le
#print axioms ellMeasure_apply_eq_setLIntegral
#print axioms ellMeasure_unitBall_half
#print axioms exists_holdingTime_witness

end Arlib.MarkovChains
