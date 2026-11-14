/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hit-and-run: model vocabulary

The one-step law of hit-and-run: a uniform direction on the unit sphere, then a uniform point on
the chord of the body through the current point in that direction.  Also the explicit mixing
deadline of the unconditional theorem.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The total mass of `Measure.toSphere`: the surface area `vol_{n-1}(∂B)` of the unit
sphere. -/
noncomputable def sphereArea (n : ℕ) : ℝ≥0∞ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The uniform (normalised surface) measure on the unit sphere of directions. -/
noncomputable def unifSphere (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (sphereArea n)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The parameter set of the chord. -/
def chordSet (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {t | u + t • v ∈ K}

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The density of the hit-and-run step in direction/parameter coordinates. -/
noncomputable def chordDensity (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) : ℝ≥0∞ :=
  (volume (chordSet K u (p.1 : EuclideanSpace ℝ (Fin n))))⁻¹ *
    K.indicator 1 (u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)))

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- **The hit-and-run proposal from `u`.** -/
noncomputable def hitAndRunProposal (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (((unifSphere n).prod volume).withDensity (chordDensity K u)).map
    (fun p => u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)))

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

/-- **The unconditional hit-and-run mixing deadline**: `2⁶⁴ · n² · D² · log(8M/ε²)`.

This is `4 · lsThreshold M phi ε` at the conductance `phi = 1/(2³¹·n·D)` that
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond_pow` delivers: `lsThreshold M phi ε = log(8M/ε²)/phi²`
and `1/phi² = 2⁶²·n²D²`, and the factor `4` is `conductance_lazy` (laziness halves the
conductance and the deadline is quadratic in `1/phi`).  Identified with that product by
`hrDeadlineUncond_eq`.

`D` is a bound on the **diameter** of `K`, not on its circumradius; see
`tvLe_iterate_lazy_hitAndRun_uncond_ball` for the `R`-form, which costs a further `4`. -/
noncomputable def hrDeadlineUncond (n : ℕ) (D M eps : ℝ) : ℝ :=
  2 ^ 64 * (n : ℝ) ^ 2 * D ^ 2 * Real.log (8 * M / eps ^ 2)

end

section
open MeasureTheory
variable {n : ℕ}

/-- **One step of hit-and-run** from `u`: move according to `hitAndRunProposal K u`, and stay
at `u` with the remaining probability `1 - hitAndRunProposal K u univ` (the mass of directions
whose chord through `u` is degenerate). -/
noncomputable def hitAndRunStep (K : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  hitAndRunProposal K u + (1 - hitAndRunProposal K u Set.univ) • Measure.dirac u

end

end ArlibCommunity.Foundations.MarkovChainTheory
