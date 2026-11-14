/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Kannan–Vempala lattice sampling: model vocabulary

The small vocabulary the statement is written in: points of `ℝⁿ`, lattice points of `ℤⁿ`,
the tent function that drives randomized rounding, and the facet displacement `κ` by which
the polytope is inflated.  Proofs live under `Analysis/`; this directory is the audit
surface, laid out like `Algorithms/HitAndRun`.
-/

namespace ArlibCommunity.Algorithms.KV97

/-- Points of the ambient space `ℝⁿ`. -/
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Lattice points: integer vectors in `ℤⁿ`. -/
abbrev LatticePoint (n : ℕ) := Fin n → ℤ

/-- A lattice point, seen as a point of `ℝⁿ`. -/
noncomputable def toState {n : ℕ} (z : LatticePoint n) : State n :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

/-- The triangular displacement density `1 − |u|` on `[−1,1]`, zero outside. -/
noncomputable def tent (u : ℝ) : ℝ := max (1 - |u|) 0

/-- **The facet displacement `κ = c + √(2 log r)`.** `P` is inflated by `κ‖Aᵢ‖` on
each facet to form `P'`; the `√(2 log r)` term is what pays for the union bound
over `r` facets, and `c` is the free parameter that tunes the loss. -/
noncomputable def kappaOf (c r : ℝ) : ℝ := c + Real.sqrt (2 * Real.log r)

end ArlibCommunity.Algorithms.KV97
