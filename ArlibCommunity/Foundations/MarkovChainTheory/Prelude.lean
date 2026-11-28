/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Markov chains on a general measurable space: shared definitions

The definitions that the surface theorems of `ArlibCommunity.Foundations.MarkovChainTheory` are
stated in: the ergodic flow and the conductance of a Markov kernel, reversibility, running a
chain for `t` steps, the mixing predicate and mixing-time formulas, and the local conductance of
the ball walk.

Only definitions live here.  Their basic lemmas are in `MarkovChainTheory/Basic/`; each
theorem's own definitions are in its `Model/Prelude.lean`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **ergodic flow** from `S` to `T`: `∫_S P_x(T) dpi(x)`, the probability
that a single step of the chain started from `pi` begins in `S` and ends in `T`.

This is the continuous-state analogue of the finite-state
`∑_{x ∈ S} ∑_{y ∈ T} pi x * P x y`. -/
noncomputable def flow (pi : Measure Ω) (P : Kernel Ω Ω) (S T : Set Ω) : ℝ≥0∞ :=
  ∫⁻ x in S, P x T ∂pi

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The conductance **of a single set** `S`: the conditional probability that a
step of the chain started from `pi` conditioned on `S` escapes `S`,
`Φ(S) = flow(S, Sᶜ) / pi(S)`.

Because `ℝ≥0∞` divides by zero to zero, this is `0` whenever `pi S = 0`; the
lemmas below therefore all assume `0 < pi S`. -/
noncomputable def conductance (pi : Measure Ω) (P : Kernel Ω Ω) (S : Set Ω) : ℝ≥0∞ :=
  flow pi P S Sᶜ / pi S

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sets the conductance infimum ranges over: measurable sets of positive
measure that are no larger than the threshold `thr`.  The positivity is what
keeps `conductance` from being the junk value `0`; see the module docstring. -/
def smallSets (pi : Measure Ω) (thr : ℝ≥0∞) : Set (Set Ω) :=
  {S : Set Ω | MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ thr}

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The conductance **relative to a threshold** `thr`: the infimum of
`conductance` over the measurable sets of positive measure at most `thr`. -/
noncomputable def globalConductanceWithin (pi : Measure Ω) (P : Kernel Ω Ω) (thr : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ S ∈ smallSets pi thr, conductance pi P S

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The conductance** of a Markov chain with kernel `P` and invariant
probability measure `pi`:

`Φ = inf { flow(S, Sᶜ) / pi(S) : S measurable, 0 < pi(S) ≤ 1/2 }`.

The cut-off at `1/2` is the usual one for a probability measure; see
`globalConductanceWithin` for the version with an explicit threshold. -/
noncomputable def globalConductance (pi : Measure Ω) (P : Kernel Ω Ω) : ℝ≥0∞ :=
  globalConductanceWithin pi P (1 / 2)

end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One step of the Markov chain with kernel `P`**, as a map on laws: if the current
state is distributed as `μ`, the next state is distributed as `μ.bind P`.

This is Mathlib's `P ∘ₘ μ` under a name that reads as an action on the *measure*, which is
the direction the sampler literature runs it in. -/
noncomputable def step (P : Kernel Ω Ω) (μ : Measure Ω) : Measure Ω := μ.bind P

end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The law of the chain after `t` steps**, started from `μ` and driven by `P`. -/
noncomputable def iterate (P : Kernel Ω Ω) (μ : Measure Ω) : ℕ → Measure Ω
  | 0 => μ
  | t + 1 => step P (iterate P μ t)

end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The sampler guarantee**: started from `μ₀` and run for `t` steps, the chain with
kernel `P` is within total variation distance `ε` of `pi`. -/
def MixesWithin (P : Kernel Ω Ω) (pi : Measure Ω) (μ₀ : Measure Ω) (t : ℕ) (ε : ℝ≥0∞) : Prop :=
  TVLe (iterate P μ₀ t) pi ε

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The explicit mixing time `⌈log (M / ε) / c⌉`. -/
noncomputable def mixingTime (M c eps : ℝ) : ℕ := ⌈Real.log (M / eps) / c⌉₊

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The mixing time in Lovász–Simonovits form: `c = phi²/2`, `M ↦ √M`. -/
noncomputable def conductanceMixingTime (M phi eps : ℝ) : ℕ :=
  mixingTime (Real.sqrt M) (phi ^ 2 / 2) eps

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **local conductance** at `x`,
`ℓ(x) = vol(K ∩ (x + δBₙ)) / vol(x + δBₙ)` ([CV18]): the fraction of the
proposal ball that lies inside `K`, equivalently the probability that a single step of
the ball walk from `x` actually moves (`ballWalk_apply_compl_singleton`).

The denominator is the volume of the ball *centred at `x`*, which by translation
invariance (`volume_ball_eq`) is the `vol(δBₙ)` of the paper.  Because `ℝ≥0∞` divides by
zero to zero, `ell K δ x = 0` whenever `δ ≤ 0`; that is the same convention under which
the kernel degenerates to `dirac x`, so the two agree. -/
noncomputable def ell (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  volume (Metric.ball x δ ∩ K) / volume (Metric.ball x δ)

end

section
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **lazy version of a one-step law**: stay put with probability `1/2`, otherwise take a
step distributed as `law x`. -/
noncomputable def lazyLaw (law : Ω → Measure Ω) (x : Ω) : Measure Ω :=
  (2 : ℝ≥0∞)⁻¹ • law x + (2 : ℝ≥0∞)⁻¹ • Measure.dirac x

end

end ArlibCommunity.Foundations.MarkovChainTheory
