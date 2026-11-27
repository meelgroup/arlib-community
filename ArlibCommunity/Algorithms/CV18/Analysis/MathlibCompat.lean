/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Mathlib compatibility for the CV18 analysis

Mathlib 4.35 removed `MeasureTheory.Measure.isProbabilityMeasure_map`, which took
an `AEMeasurable f μ` hypothesis. It became an unconditional instance: under the
current definition of `Measure.map`, `μ.map f` is a probability measure for every
`f` (a non-measurable `f` maps to a Dirac measure).

The CV18 proofs call the old lemma, with its measurability argument, at more than
150 sites. `isProbabilityMeasure_map_of_aemeasurable` keeps those call sites
unchanged. The hypothesis is no longer needed and is ignored.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- `μ.map f` is a probability measure. Signature-compatible replacement for the
removed `MeasureTheory.Measure.isProbabilityMeasure_map`; the measurability
hypothesis is kept only so that existing call sites remain valid. -/
theorem isProbabilityMeasure_map_of_aemeasurable {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (_hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  inferInstance

end ArlibCommunity.Algorithms.CV18
