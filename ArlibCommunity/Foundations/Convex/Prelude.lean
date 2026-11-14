/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Convex.Basic

/-!
# Convex geometry: shared definitions

The definitions that the surface theorems of `ArlibCommunity.Foundations.Convex` are stated
in: the uniform measure on a set and conditioning on a set, log-concavity, the needle map and
the density distance, three-way partitions, the Gaussian weight, chords and the cross-ratio
distance of a convex body, total variation and warmness between measures, and polytopes.

Only definitions live here.  Their basic lemmas are in `Convex/Basic/`; each theorem's own
definitions are in its `Model/Prelude.lean`.
-/

namespace ArlibCommunity.Foundations.Convex

section
open MeasureTheory
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of a `μ`-distributed draw **conditioned on landing in `S`**: the
restriction of `μ` to `S`, renormalised by `μ S`.

With the Mathlib convention `x / 0 = 0` (and `(∞)⁻¹ = 0`) this is the zero
measure when `μ S` is `0` or `∞`; the interesting hypotheses `μ S ≠ 0` and
`μ S ≠ ∞` are carried explicitly by the lemmas that need them. -/
noncomputable def condOn (μ : Measure Ω) (S : Set Ω) : Measure Ω :=
  (μ S)⁻¹ • μ.restrict S

end

section
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The uniform measure on `S`**: `μ` restricted to `S`, renormalised by `μ S`.

This is definitionally `ArlibCommunity.Foundations.Convex.condOn μ S`; the two names record two readings of one
measure.  `condOn μ S` is "the law of a `μ`-draw conditioned on landing in `S`";
`uniformOn μ S` is "the uniform distribution on `S`", which is what that conditioned law
*is* when `μ` is the ambient volume.  Consumers of a volume algorithm want the second
reading, so the abbreviation exists; but it is the same object, and every lemma about
`condOn` applies to it unchanged.

It is a probability measure exactly when `μ S ∉ {0, ∞}` — see
`isProbabilityMeasure_uniformOn`.  Outside that range Mathlib's `(0)⁻¹ = ⊤` and
`(⊤)⁻¹ = 0` conventions make it the zero measure or an infinite one; the guards are
carried explicitly by the lemmas that need them. -/
noncomputable abbrev uniformOn (μ : Measure Ω) (S : Set Ω) : Measure Ω := condOn μ S

end

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Log-concavity on a set.** `f` is log-concave on `s` when `s` is convex and

  `f x ^ a * f y ^ b ≤ f (a • x + b • y)`

for all `x, y ∈ s` and all weights `a, b ≥ 0` with `a + b = 1`, the exponentiation being
`Real.rpow`.

The shape of the statement deliberately mirrors Mathlib's `ConcaveOn`. Nonnegativity of
`f` is *not* part of the definition; the lemmas that need it take it as a hypothesis. -/
def LogConcaveOn (s : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f x ^ a * f y ^ b ≤ f (a • x + b • y)

end

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Log-concavity on the whole space**, i.e. log-concavity on `Set.univ`. -/
def IsLogConcave (f : E → ℝ) : Prop :=
  LogConcaveOn (Set.univ : Set E) f

end

section
open MeasureTheory Set
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The line through `a` in direction `v`**, parameterised by `ℝ`: `t ↦ a + t • v`.

The paper's needle is the restriction of the density to the image of this map, over a
parameter interval. -/
def needleMap (a v : E) : ℝ → E := fun t => a + t • v

end

section
open MeasureTheory Set
variable {E : Type*}

/-- **The `f`-distance between two points**, `d_f(u,v) = |f u − f v| / max (f u) (f v)`. -/
noncomputable def densDist (f : E → ℝ) (u v : E) : ℝ := |f u - f v| / max (f u) (f v)

end

section
open MeasureTheory Set
variable {E : Type*}

/-- **A three-way partition of `K`**: `S₁ ∪ S₂ ∪ S₃ = K` with the three parts pairwise
disjoint.

This is the shape the isoperimetric inequality is quantified over: `S₁` and `S₂` are the
two separated parts and `S₃` is the "boundary" whose measure is bounded below.
Measurability is *not* bundled — it is carried as a separate hypothesis by the lemmas
that integrate over the parts, so that the definition stays purely set-theoretic. -/
structure IsPartition3 (K S₁ S₂ S₃ : Set E) : Prop where
  /-- The three parts cover `K` exactly. -/
  union : S₁ ∪ S₂ ∪ S₃ = K
  /-- `S₁` and `S₂` are disjoint. -/
  disjoint₁₂ : Disjoint S₁ S₂
  /-- `S₁` and `S₃` are disjoint. -/
  disjoint₁₃ : Disjoint S₁ S₃
  /-- `S₂` and `S₃` are disjoint. -/
  disjoint₂₃ : Disjoint S₂ S₃

end

section
open scoped ENNReal
variable {n : ℕ}

/-- The **unnormalised Gaussian weight** `e^{-‖x‖²/(2s)}`, as a real number. -/
noncomputable def gaussianWeightReal (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (2 * s))

end

section
open scoped ENNReal
variable {n : ℕ}

/-- The **Gaussian weight** `e^{-‖x‖²/(2s)}` as an element of `ℝ≥0∞`: the density, with respect
to Lebesgue measure, of the unnormalised measure whose restriction to a body `K` is the target
`∝ 1_K(x)·e^{-‖x‖²/(2s)}`. -/
noncomputable def gaussianWeight (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianWeightReal s x)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- The chord `ℓ(u,v) ∩ K` read in the affine coordinate on `ℓ(u,v)` that sends `u` to `0` and
`v` to `1`: the set of `t : ℝ` with `u + t(v − u) ∈ K`. -/
def chordParam (K : Set E) (u v : E) : Set ℝ :=
  (AffineMap.lineMap u v : ℝ → E) ⁻¹' K

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- The parameter of the chord endpoint on the far side of `u`. -/
noncomputable def chordLow (K : Set E) (u v : E) : ℝ := sInf (chordParam K u v)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- The parameter of the chord endpoint on the far side of `v`. -/
noncomputable def chordHigh (K : Set E) (u v : E) : ℝ := sSup (chordParam K u v)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- `p`, the endpoint of the chord `ℓ(u,v) ∩ K` beyond `u`. -/
noncomputable def chordStart (K : Set E) (u v : E) : E :=
  AffineMap.lineMap u v (chordLow K u v)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- `q`, the endpoint of the chord `ℓ(u,v) ∩ K` beyond `v`. -/
noncomputable def chordEnd (K : Set E) (u v : E) : E :=
  AffineMap.lineMap u v (chordHigh K u v)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- **The cross-ratio (Hilbert) distance** `d_K(u,v) = |u−v| |p−q| / (|p−u| |v−q|)`, where
`p` and `q` are the endpoints of the chord of `K` through `u` and `v`, in the order
`p, u, v, q`. -/
noncomputable def crossRatioDist (K : Set E) (u v : E) : ℝ :=
  dist u v * dist (chordStart K u v) (chordEnd K u v) /
    (dist (chordStart K u v) u * dist v (chordEnd K u v))

end

section
open MeasureTheory Set
open scoped ENNReal
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ ν ξ : Measure Ω} {ε ε' δ p : ℝ≥0∞} {S : Set Ω}

/-- **Total variation distance at most `ε`**: every measurable event has the same mass under `μ`
and `ν` up to an additive `ε`,

  `∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`.

For probability measures this says `sup_S |μ S - ν S| ≤ ε`, the total-variation distance in the
`[0, 1]` normalization; Mathlib's `MeasureTheory.etvDist` is twice this quantity. -/
def TVLe (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε

end

section
open MeasureTheory Set
open scoped ENNReal
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ ν ξ : Measure Ω} {ε ε' δ p : ℝ≥0∞} {S : Set Ω}

/-- **`M`-warmness**: `μ S ≤ M * ν S` for every measurable `S`, i.e. `sup_S μ S / ν S ≤ M`.
This is the warm-start parameter of the volume-computation literature. -/
def IsWarm (M : ℝ≥0∞) (μ ν : Measure Ω) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ M * ν S

end

section
namespace Polytope
open MeasureTheory Set Pointwise
open scoped InnerProductSpace
variable {n : ℕ} {ι : Type*}

/-- The polytope `{x | ∀ i, ⟪A i, x⟫ ≤ b i}` cut out by the linear inequalities
with normals `A i` and offsets `b i`. -/
def body (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i}

end Polytope
end

section
namespace Polytope
open MeasureTheory Set Pointwise
open scoped InnerProductSpace
variable {n : ℕ} {ι : Type*}

/-- The `κ`-**inflation** of `body A b`: every facet hyperplane is displaced
outwards by the metric distance `κ`, i.e. its offset grows by `κ‖A i‖`.
Negative `κ` deflates. -/
def inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i + κ * ‖A i‖}

end Polytope
end

end ArlibCommunity.Foundations.Convex
