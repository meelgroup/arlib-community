/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Model.Prelude
import ArlibCommunity.Foundations.Convex.Basic.Polytope
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Kannan–Vempala problem setting

The input is a polytope `P = {x | ⟪Aᵢ, x⟫ ≤ bᵢ}` with finitely many facets, together with
the two parameters of the inflation: `c ≥ 0`, which tunes the loss `e^{−c²/2}`, and an upper
bound `r ≥ 1` on the number of facets, which pays for the union bound over facets.

The algorithm needs a continuous sampler on the inflated polytope `P'`.  Its contract,
`AlmostUniformSampler`, asks for a density that is within a factor `1 ± ε` of uniform
**pointwise** on `P'`.  This is stronger than closeness in total variation, and it is what
the relative-error statement needs; see `Analysis/Theorem2.lean`.
-/

namespace ArlibCommunity.Algorithms.KV97

open MeasureTheory
open scoped InnerProductSpace

/-- A polytope with `ι` facets in `ℝⁿ`, and the inflation parameters `c` and `r`. -/
structure Problem (n : ℕ) (ι : Type*) [Fintype ι] where
  /-- Facet normals. -/
  A : ι → State n
  /-- Facet offsets: the polytope is `{x | ⟪A i, x⟫ ≤ b i}`. -/
  b : ι → ℝ
  /-- The free inflation parameter; the loss is `e^{−c²/2}`. -/
  c : ℝ
  /-- An upper bound on the number of facets. -/
  r : ℝ
  c_nonneg : 0 ≤ c
  one_le_r : 1 ≤ r
  card_le_r : (Fintype.card ι : ℝ) ≤ r

/-- The polytope `P = {x | ⟪A i, x⟫ ≤ b i}`. -/
def Problem.body {n : ℕ} {ι : Type*} [Fintype ι] (p : Problem n ι) : Set (State n) :=
  ArlibCommunity.Foundations.Convex.Polytope.body p.A p.b

section
variable {n : ℕ} {ι : Type*}

/-- **The inflated polytope `P'` of Kannan–Vempala's Theorem 2**: the body
`{x | A x ≤ b}` with every facet pushed outwards by the metric displacement
`κ = c + √(2 log r)`. -/
noncomputable def inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (c r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ArlibCommunity.Foundations.Convex.Polytope.inflate A b (kappaOf c r)

end

/-- The inflated polytope `P'` of a problem. -/
noncomputable def Problem.inflatedBody {n : ℕ} {ι : Type*} [Fintype ι] (p : Problem n ι) :
    Set (State n) :=
  inflated p.A p.b p.c p.r

section
variable {n : ℕ}

/-- **The sampler's density is pointwise almost uniform on `S`.**

The continuous analogue of `eq:almostuniform` (`sections/related.tex:21`): `f` is
a density on `S` whose value at every point is within a `(1±ε)` factor of the
uniform density `1/V`. See the module docstring for why this, and not a
total-variation bound, is the right hypothesis. -/
def PointwiseAlmostUniform (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) (V ε : ℝ) : Prop :=
  ∀ p ∈ S, (1 - ε) / V ≤ f p ∧ f p ≤ (1 + ε) / V

end

/-- **The sampler contract**: the sampler's law on `S` has a measurable density that is
pointwise within a factor `1 ± ε` of the uniform density `1/V`. -/
def AlmostUniformSampler {n : ℕ} (sampler : Measure (State n)) (S : Set (State n))
    (V ε : ℝ) : Prop :=
  ∃ f : State n → ℝ, Measurable f ∧ PointwiseAlmostUniform f S V ε ∧
    sampler = (volume.restrict S).withDensity (fun q => ENNReal.ofReal (f q))

end ArlibCommunity.Algorithms.KV97
