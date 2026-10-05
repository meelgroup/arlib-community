/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Hit-and-run: model vocabulary

The small, paper-facing vocabulary used by the formalization.  Proofs and the
measure-theoretic implementation live under `Analysis/`; this directory is the
audit surface, following the layout used by DNFStream.
-/

namespace ArlibCommunity.Algorithms.HitAndRun

/-- The state space of hit-and-run in dimension `n`. -/
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A possible state-space restriction for the walk. -/
abbrev Body (n : ℕ) := Set (State n)

/-- The proved (corrected, conservative) mixing deadline.

The `2^64` coefficient is the fully discharged coefficient in this
formalization.  It deliberately does not repeat the smaller printed constant
of [Lov99], whose overlap-lemma arithmetic does not establish that constant. -/
noncomputable def deadline (n : ℕ) (D M eps : ℝ) : ℝ :=
  2 ^ 64 * (n : ℝ) ^ 2 * D ^ 2 * Real.log (8 * M / eps ^ 2)

end ArlibCommunity.Algorithms.HitAndRun
