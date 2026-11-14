/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Pointwise mixing: model vocabulary

Pointwise closeness of two measures, minorisation, and uniform minorisation of a kernel.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal _root_.Topology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`μ` is pointwise `ε`-close to `ν`**: `μ` has a density with respect to `ν` and that
density lies in `[1 - ε, 1 + ε]` almost everywhere. -/
def PointwiseClose (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  μ ≪ ν ∧ ∀ᵐ x ∂ν, 1 - ε ≤ μ.rnDeriv ν x ∧ μ.rnDeriv ν x ≤ 1 + ε

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal _root_.Topology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`μ` minorises `ν` at rate `m`**: `m * ν S ≤ μ S` for every measurable `S`, i.e.
`m • ν ≤ μ`. The mirror image of `ArlibCommunity.Foundations.Convex.IsWarm`. -/
def Minorises (m : ℝ≥0∞) (μ ν : Measure Ω) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → m * ν S ≤ μ S

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal _root_.Topology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Uniform minorisation (Doeblin's condition)**: from *every* state the kernel already
covers a `c`-fraction of the stationary measure,

  `∀ x, ∀ measurable S, c * pi S ≤ P x S`.

Equivalently `c • pi ≤ P x` for every `x`. -/
def UniformMinorisation (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ≥0∞) : Prop :=
  ∀ x : Ω, Minorises c (P x) pi

end

end ArlibCommunity.Foundations.MarkovChainTheory
