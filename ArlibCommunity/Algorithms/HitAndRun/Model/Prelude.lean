/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Hit-and-run: model vocabulary

The small, paper-facing vocabulary used by the formalization.  Proofs and the
measure-theoretic implementation live under `Analysis/`; this directory is the
audit surface, following the layout used by DNFStream.
-/

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory
open scoped ENNReal

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

/-- **Total variation distance at most `ε`**: every measurable event has the
same mass under `μ` and `ν` up to an additive `ε`,

  `∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`.

For probability measures this says `sup_S |μ S - ν S| ≤ ε`, i.e. the
total-variation distance in the `[0, 1]` normalization (Mathlib's `etvDist`
is twice this quantity). -/
def TVLe {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε

end ArlibCommunity.Algorithms.HitAndRun
