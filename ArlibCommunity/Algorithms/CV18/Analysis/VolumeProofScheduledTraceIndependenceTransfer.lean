/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependencePerturbation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceCapstoneExecutable

/-! # Transferring phase independence to the capped scheduled trace -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Reduce the executable trace's finite Lemma 7.17(c) premise to a nearby
probability law.  This is the exact interface for a live/good prefix: prove
the warm-chain independence theorem on the repaired law, dominate the actual
trace law by it up to `delta`, and fit the resulting `3 * delta` loss in the
paper's dependence budget. -/
theorem scheduledFigureOneTrace_independence_of_reference
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : ℕ → Measure (ScheduledBalancedCoolingTrace q.n))
    (hrefProb : ∀ i, IsProbabilityMeasure (reference i))
    (delta : ℕ → ENNReal) (hdelta : ∀ i, delta i ≠ ⊤)
    (epsilon : ℕ → ℝ)
    (hdom : ∀ i, i < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
        (reference i) (delta i))
    (hindReference : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (epsilon i)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (reference i))
    (hbudget : ∀ i, i < figureOneDependentPhaseCount q →
      epsilon i + 3 * (delta i).toReal ≤ figureOneDependentEpsilon q) :
    ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) := by
  intro i hi
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure (reference i) := hrefProb i
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct
      (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I)
      (fun j => (measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const) i
  have hY : Measurable Y :=
    (measurable_scheduledBalancedTracePhaseVariable q (i + 1)).min
      measurable_const
  have htransfer := ApproxIndepFun.of_measureLeUpTo
    mu (reference i) (hdelta i) X Y hX hY (hdom i hi)
      (hindReference i hi)
  exact htransfer.mono (hbudget i hi)

#print axioms scheduledFigureOneTrace_independence_of_reference

end ArlibCommunity.Algorithms.CV18
