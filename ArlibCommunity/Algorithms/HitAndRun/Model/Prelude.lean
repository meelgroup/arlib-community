/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hit-and-run: model vocabulary

The small, paper-facing vocabulary used by the formalization: the state space, the
mixing deadline, total-variation closeness, the laws of the random numbers the program
reads, and the caps of one step of the program (`WalkParams`, `walkParams`).  Proofs
live under `Analysis/`; this directory is the audit surface.
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

/-! ## The random numbers -/

/-- The standard Gaussian law on `ℝⁿ`: `n` independent standard Gaussian coordinates. -/
noncomputable def standardGaussian (n : ℕ) : Measure (State n) :=
  ProbabilityTheory.stdGaussian (State n)

instance standardGaussian_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussian n) := by
  unfold standardGaussian
  infer_instance

/-- The uniform law on `[0, 1]`. -/
noncomputable def uniformUnit : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit :=
  ⟨by simp [uniformUnit]⟩

/-! ## The caps of one step -/

/-- **The parameters of the program**: the diameter bound `D` it brackets chords with, the
number `bisectionSteps` of halvings on each side of a chord, the number `rejectionTries`
of tries for a point of the chord, and the number `steps` of walk steps. -/
structure WalkParams where
  D : ℝ
  bisectionSteps : ℕ
  rejectionTries : ℕ
  steps : ℕ

/-- **The parameters for accuracy `ε`** from a warm start of warmness `M`, in dimension
`n`, with diameter bound `D`, for `m` steps:

* `bisectionSteps = ⌈log₂(16·m·M·n·D/ε)⌉`: after that many halvings a chord of length at
  least `4D·2^{-k}` is bracketed within twice its length;
* `rejectionTries = ⌈log₂(8·m·M/ε)⌉`: then that many tries all miss with probability at
  most `2^{-r}`.

Together they make the probability that some step gives up at most `ε/4`. -/
noncomputable def walkParams (n : ℕ) (D M eps : ℝ) (m : ℕ) : WalkParams where
  D := D
  bisectionSteps := ⌈Real.logb 2 (16 * m * M * n * D / eps)⌉₊
  rejectionTries := ⌈Real.logb 2 (8 * m * M / eps)⌉₊
  steps := m

end ArlibCommunity.Algorithms.HitAndRun
