/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Analysis.PointwiseMixing
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Pointwise mixing

A chain whose kernel uniformly minorises its stationary law at rate `c` becomes pointwise `ε`-close to stationarity — a density ratio within `1 ± ε` — once `(1-c)^t` is small; and closeness in total variation does not imply pointwise closeness.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Uniform minorisation gives pointwise mixing.** -/
theorem pointwiseClose_iterate {Ω : Type*} [MeasurableSpace Ω] {P : Kernel Ω Ω}
    {pi μ : Measure Ω} {c M ε : ℝ≥0∞} [IsMarkovKernel P] [IsProbabilityMeasure pi]
    [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi)
    (hw : IsWarm M μ pi) {t : ℕ} (h₁ : (1 - c) ^ t ≤ ε) (h₂ : (1 - c) ^ t * (M - 1) ≤ ε) :
    PointwiseClose (iterate P μ t) pi ε :=
  pointwiseClose_iterate_of_uniformMinorisation hmin hc hinv hw h₁ h₂

/-- **Total-variation closeness does not give pointwise closeness**: for every `δ > 0` there are
two probability laws within total variation `δ` that are not pointwise `ε`-close. -/
theorem exists_tvLe_not_pointwiseClose' {δ ε : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδε : (1 + ε) * δ < 1) :
    ∃ μ ν : Measure Bool, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      μ ≪ ν ∧ TVLe μ ν δ ∧ ¬ PointwiseClose μ ν ε :=
  exists_tvLe_not_pointwiseClose hδ0 hδε

#foundationsModelClosure pointwiseClose_iterate
#print axioms pointwiseClose_iterate
#foundationsModelClosure exists_tvLe_not_pointwiseClose'
#print axioms exists_tvLe_not_pointwiseClose'

end ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing
