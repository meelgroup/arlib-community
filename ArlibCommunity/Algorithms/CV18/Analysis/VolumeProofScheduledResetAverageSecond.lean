/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledShadowAverageThirdMoment

/-!
# Equation (6) on the fixed-cost exact-shadow reference

This module assembles the structural and analytic pieces: one common
exact-coordinate reference, transported Lemma 7.17 independence, exact
coordinate moments, prefix `L³`, and the unbounded equation-(6) recurrence.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- A scheduled Gaussian phase admits a fixed-cost reference whose empirical
average satisfies equation (6) with the explicit transported dependence
coefficient. -/
theorem exists_scheduledRetainedResetReference_average_secondMoment_with_state
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {A mean factor : ℝ} (hA : 0 < A) (hmean0 : 0 ≤ mean)
    (hcoordinateMean :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ mean)
    (hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor * mean ^ 2)
    (hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ A ^ 3) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I phase ∧
      MemLp (fun history =>
        sequentialPrefixSum
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)))) count history /
            (count : ℝ)) 2 reference ∧
      (∫ history,
          sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) ∂reference) =
        ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)) x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) ∧
      (∫ history,
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
          3 * (figureOneDependentEpsilon q +
              3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
                (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * A ^ 2 := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, hstate, hind⟩ :=
    exists_scheduledRetainedResetReference_all_approxIndep_with_state
      q I phase count hcount hcountMax
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let Y : ℕ → RetainedSampleHistory (AmbientSpace q.n) → ℝ :=
    retainedSampleObservation weight
  let epsilon := figureOneDependentEpsilon q +
    3 * (scheduledResetReferenceError q (count - 1)).toReal
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hYmeas : ∀ j, Measurable (Y j) :=
    fun j => measurable_retainedSampleObservation hweight j
  have hY0 : ∀ j, j < count → ∀ history, 0 ≤ Y j history := by
    intro j _hj history
    unfold Y retainedSampleObservation retainedOptionWeight
    cases history.1 j <;> simp [weight, gaussianRatioWeight_nonnegative]
  have hY3 : ∀ j, j < count → MemLp (Y j) 3 reference := by
    intro j hj
    simpa [Y, weight] using
      memLp_retainedSampleObservation_three_of_map_eq
        q I phase j reference (hcoordinates j hj)
  have hYmean : ∀ j, j < count →
      ∫ history, Y j history ∂reference ≤ mean := by
    intro j hj
    rw [show (∫ history, Y j history ∂reference) =
        ∫ x, weight x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) by
      simpa [Y, weight] using
        integral_retainedSampleObservation_eq_gaussianMean_of_map_eq
          q I phase j reference (hcoordinates j hj)]
    simpa [weight] using hcoordinateMean
  have hYsecond : ∀ j, j < count →
      (∫ history, Y j history ^ 2 ∂reference) ≤ factor * mean ^ 2 := by
    intro j hj
    rw [show (∫ history, Y j history ^ 2 ∂reference) =
        ∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) by
      simpa [Y, weight] using
        integral_retainedSampleObservation_sq_eq_gaussianSecond_of_map_eq
          q I phase j reference (hcoordinates j hj)]
    simpa [weight] using hcoordinateSecond
  have hYcube : ∀ j, j < count →
      (∫ history, Y j history ^ 3 ∂reference) ≤ A ^ 3 := by
    intro j hj
    rw [show (∫ history, Y j history ^ 3 ∂reference) =
        ∫ x, weight x ^ 3
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) by
      simpa [Y, weight] using
        integral_retainedSampleObservation_cube_eq_gaussianThird_of_map_eq
          q I phase j reference (hcoordinates j hj)]
    simpa [weight] using hcoordinateThird
  have hprefix := exactShadowHistory_prefix_thirdMoment_le
    q I phase count reference hcoordinates hA hcoordinateThird
  have havgMem :=
    (integral_exactShadowHistory_average_sq_le_gaussianSecond
      q I phase count hcount reference hcoordinates).1
  have havgMean := integral_exactShadowHistory_average_eq_gaussianMean
    q I phase count hcount reference hcoordinates
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    have hdependent : 0 < figureOneDependentEpsilon q := by
      unfold figureOneDependentEpsilon
      have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
        exact_mod_cast figureOneDependentPhaseCount_pos q
      exact div_pos (sq_pos_of_pos q.heps.1)
        (mul_pos
          (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
    positivity
  have havg := sequentialAverage_secondMoment_le_of_approxIndepPrefix_thirdMoment
    reference hYmeas count hcount hA hmean0 hepsilon hY0 hY3 hYmean
      hYsecond (fun i hi => (hprefix i hi).1)
      (fun i hi => by simpa [Y, weight] using (hprefix i hi).2)
      hYcube (by simpa [epsilon, Y, weight] using hind)
  refine ⟨reference, hreferenceProb, hmlu, hstate, ?_, ?_, ?_⟩
  · simpa [Y, weight, sequentialPrefixSum] using havgMem
  · simpa [Y, weight, sequentialPrefixSum] using havgMean
  · simpa [epsilon, Y, weight] using havg

/-- Compatibility form of the Gaussian reset reference when its exact final
retained-state marginal is not needed by the caller. -/
theorem exists_scheduledRetainedResetReference_average_secondMoment
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {A mean factor : ℝ} (hA : 0 < A) (hmean0 : 0 ≤ mean)
    (hcoordinateMean :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ mean)
    (hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor * mean ^ 2)
    (hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ A ^ 3) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      MemLp (fun history =>
        sequentialPrefixSum
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)))) count history /
            (count : ℝ)) 2 reference ∧
      (∫ history,
          sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) ∂reference) =
        ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)) x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) ∧
      (∫ history,
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
          3 * (figureOneDependentEpsilon q +
              3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
                (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * A ^ 2 := by
  obtain ⟨reference, hprob, hmlu, _hstate, hmem, hmean, hsecond⟩ :=
    exists_scheduledRetainedResetReference_average_secondMoment_with_state
      q I phase count hcount hcountMax hA hmean0 hcoordinateMean
        hcoordinateSecond hcoordinateThird
  exact ⟨reference, hprob, hmlu, hmem, hmean, hsecond⟩

#print axioms
  exists_scheduledRetainedResetReference_average_secondMoment_with_state
#print axioms exists_scheduledRetainedResetReference_average_secondMoment

end

end ArlibCommunity.Algorithms.CV18
