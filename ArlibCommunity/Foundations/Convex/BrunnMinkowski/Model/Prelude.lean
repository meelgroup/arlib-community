/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude

/-!
# Brunn–Minkowski: model vocabulary

The slices of a body by the hyperplanes `{x | x₀ = t}`, which Brunn's theorem is about.
-/

namespace ArlibCommunity.Foundations.Convex

section
open MeasureTheory Set Pointwise
open scoped ENNReal
variable {m : ℕ}

/-- The slice of `K ⊆ ℝ^(m+1)` at first coordinate `t`, viewed as a subset of `ℝ^m`. -/
def slice (K : Set (Fin (m + 1) → ℝ)) (t : ℝ) : Set (Fin m → ℝ) :=
  {y | (Fin.cons t y : Fin (m + 1) → ℝ) ∈ K}

end

end ArlibCommunity.Foundations.Convex
