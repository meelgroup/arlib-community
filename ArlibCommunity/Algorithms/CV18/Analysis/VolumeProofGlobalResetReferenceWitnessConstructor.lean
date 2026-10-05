/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalResetReferenceFinalAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLocalResetDependenceBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledReferenceCoordinateExtension

/-!
# Constructor for the final global reset-reference witness

This module is the adapter between the finite chronological recurrence and
the final CV18 capstone.  The recurrence only supplies facts about recorded
one-based coordinates.  The total coordinate extension and all global
transition/reset/boundary arithmetic are discharged here.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Package a completed chronological trace recurrence into the sole witness
consumed by the unconditional final assembly. -/
noncomputable def GlobalResetReferenceWitness.of_finite_trace_reference
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hreference : IsProbabilityMeasure reference)
    (hmem : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      MemLp (scheduledBalancedTracePhaseVariable q j) 2 reference)
    (hmean : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ∂reference) =
        figureOneChronologicalRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
          ∂reference) ≤
        (figureOneChronologicalMomentFactor q j +
            figureOneExecutableMomentSlack q / 8) *
          figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun epsilon
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I reference
            (figureOneScheduledReferenceCoordinateExtension q I))
          (figureOneChronologicalTruncatedPhase q I
            (figureOneScheduledReferenceCoordinateExtension q I)) i)
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I) (i + 1))
        reference)
    (htrace : MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
      reference (figureOneScheduledGlobalOuterStepError q)) :
    GlobalResetReferenceWitness q I := by
  let _ : IsProbabilityMeasure reference := hreference
  let W := figureOneScheduledReferenceCoordinateExtension q I
  let boundary := scheduledBalancedStationaryTargetError q +
    ∑ phase ∈ Finset.range (terminalPhaseSteps q),
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q
  have hWmeas : ∀ j, Measurable (W j) := fun j =>
    measurable_figureOneScheduledReferenceCoordinateExtension q I j
  have hW0 : ∀ j trace, 0 ≤ W j trace := fun j trace =>
    figureOneScheduledReferenceCoordinateExtension_nonnegative q I j trace
  have hWmem : ∀ j, MemLp (W j) 2 reference := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q
    · change MemLp
        (figureOneScheduledReferenceCoordinateExtension q I j) 2 reference
      rw [figureOneScheduledReferenceCoordinateExtension_eq_of_used
        q I hj.1 hj.2]
      exact hmem j hj.1 hj.2
    · simpa only [W] using
        figureOneScheduledReferenceCoordinateExtension_memLp_of_not_used
          q I reference hj
  have hWmean : ∀ j, (∫ trace, W j trace ∂reference) =
      figureOneChronologicalRawMean q I j := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q
    · change (∫ trace,
          figureOneScheduledReferenceCoordinateExtension q I j trace
            ∂reference) = _
      rw [figureOneScheduledReferenceCoordinateExtension_eq_of_used
        q I hj.1 hj.2]
      exact hmean j hj.1 hj.2
    · simpa only [W] using
        integral_figureOneScheduledReferenceCoordinateExtension_of_not_used
          q I reference hj
  have hWsecond : ∀ j, (∫ trace, W j trace ^ 2 ∂reference) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2 := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q
    · change (∫ trace,
          figureOneScheduledReferenceCoordinateExtension q I j trace ^ 2
            ∂reference) ≤ _
      rw [figureOneScheduledReferenceCoordinateExtension_eq_of_used
        q I hj.1 hj.2]
      exact hsecond j hj.1 hj.2
    · simpa only [W] using
        integral_sq_figureOneScheduledReferenceCoordinateExtension_le_of_not_used
          q I reference hj
  have hproductMeas : Measurable (fun trace => initialGaussianIntegral q *
      dependentPhaseSampleProduct W
        (figureOneDependentPhaseCount q) trace) := by
    apply measurable_const.mul
    unfold dependentPhaseSampleProduct
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j _ => hWmeas (j + 1)
  have hproduct : MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
        (fun trace => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (scheduledBalancedTracePhaseVariable q)
            (figureOneDependentPhaseCount q) trace))
      (reference.map (fun trace => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) trace))
      (figureOneScheduledGlobalOuterStepError q) := by
    have hmapped := htrace.map hproductMeas
    have hfun : (fun trace => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) trace) =
      (fun trace => initialGaussianIntegral q *
        dependentPhaseSampleProduct
          (scheduledBalancedTracePhaseVariable q)
          (figureOneDependentPhaseCount q) trace) := by
      funext trace
      rw [dependentPhaseSampleProduct_referenceCoordinateExtension_eq q I]
    rw [← hfun]
    exact hmapped
  refine
    { reference := reference
      isProbabilityMeasure := hreference
      W := W
      coordinate_measurable := hWmeas
      coordinate_nonnegative := hW0
      coordinate_memLp := hWmem
      coordinate_mean := hWmean
      coordinate_second := hWsecond
      epsilon := epsilon
      epsilon_nonnegative := hepsilon0
      epsilon_le := hepsilon
      approxIndep := hind
      error := figureOneScheduledGlobalOuterStepError q
      boundary := boundary
      product_leUpTo := hproduct
      error_le := ?_
      boundary_le := ?_ }
  · exact figureOneScheduledGlobalOuterStepError_le_reset_add_boundary q
  · exact figureOneFinalScheduledCountReferenceError_le_boundaryReserve q

#print axioms GlobalResetReferenceWitness.of_finite_trace_reference

end

end ArlibCommunity.Algorithms.CV18
