/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude

/-!
# The ball walk: model vocabulary

The one-step law of the ball walk with step size `δ` on a body `K`: propose a uniform point of
the ball `B(x, δ)`, move there if it lies in `K`, and otherwise stay at `x`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-- **One step of the ball walk**: the uniform law on `B(x, δ) ∩ K`, scaled by the probability
`ell K δ x` of landing in `K`, plus the stay-put mass `1 - ell K δ x` at `x`. -/
noncomputable def ballWalkStep (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume (Metric.ball x δ))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
    + (1 - ell K δ x) • Measure.dirac x

end ArlibCommunity.Foundations.MarkovChainTheory
