/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorPrefixIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianPhaseMean

/-!
# Second moment of the initialized scheduled collector average

This is the concrete equation-(6) adapter for the Gaussian phase shadow.  It
uses the now-verified all-coordinate Lemma 7.17(b) estimate and leaves only
the one-coordinate first/second moment and support estimates as premises.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The normalized exact-first retained-sum shadow satisfies CV18 equation
(6), once the coordinate marginals have the stated moment and support
bounds. -/
theorem integral_initializedScheduledGaussianShadow_average_sq_le_of_coordinate_moments
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {B mean factor : ℝ}
    (hB0 : 0 ≤ B) (hmean0 : 0 ≤ mean)
    (hobs0 : ∀ r, r < count →
      ∀ history : RetainedSampleHistory (AmbientSpace q.n),
        0 ≤ retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) r history)
    (hobsB : ∀ r, r < count →
      ∀ history : RetainedSampleHistory (AmbientSpace q.n),
        retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) r history ≤ B)
    (hmean : ∀ r, r < count →
      (∫ history, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) r history
        ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) ≤
          mean)
    (hsecond : ∀ r, r < count →
      (∫ history, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) r history ^ 2
        ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) ≤
          factor * mean ^ 2) :
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (∫ state, (state.1 / (count : ℝ)) ^ 2
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)) ≤
      (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
        figureOneDependentEpsilon q * (1 - 1 / (count : ℝ)) * B ^ 2 := by
  dsimp only
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let historyLaw :=
    initializedScheduledRetainedHistoryLaw q I phase (count - 1)
  let initialSum : Measure (ℝ × Option (AmbientSpace q.n)) :=
    exact.map fun x => (weight x, some x)
  let _ : IsProbabilityMeasure historyLaw :=
    initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
      q I phase (count - 1)
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have havg := sequentialAverage_secondMoment_le_of_approxIndepPrefix
    historyLaw
    (fun r => measurable_retainedSampleObservation hweight r)
    count hcount0 hB0 hmean0 (figureOneDependentEpsilon_nonneg q)
    hobs0 hobsB hmean hsecond
    (approxIndepFun_initializedScheduledRetainedHistory_all
      q I phase count hcountMax)
  have hlaw := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K
    (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)).1
    (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)).2
    weight hweight exact (count - 1)
  rw [← hlaw]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ count)]
  rw [integral_map
    (measurable_retainedSampleHistoryToSum hweight count).aemeasurable
    ((measurable_fst.div_const (count : ℝ)).pow_const 2).aestronglyMeasurable]
  simpa [historyLaw, initializedScheduledRetainedHistoryLaw, initialSum,
    exact, K, weight, retainedSampleHistoryToSum, sequentialPrefixSum,
    Nat.sub_add_cancel hcount0] using havg

#print axioms
  integral_initializedScheduledGaussianShadow_average_sq_le_of_coordinate_moments

end ArlibCommunity.Algorithms.CV18
