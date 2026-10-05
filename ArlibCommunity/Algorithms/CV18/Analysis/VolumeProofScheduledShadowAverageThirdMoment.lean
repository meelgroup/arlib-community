/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentAverageThirdMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledShadowAverageMean
import Mathlib.Analysis.MeanInequalities

/-!
# Third moments of exact-shadow scheduled averages

Exact coordinate marginals transfer the Gaussian third moment to every
recorded observation.  The finite-sum power-mean inequality then supplies
the prefix moment required by the unbounded equation-(6) recurrence.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- An exact optional coordinate has exactly the Gaussian-ratio third
moment. -/
theorem integral_retainedSampleObservation_cube_eq_gaussianThird_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I phase) :
    (∫ history, retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) j history ^ 3 ∂reference) =
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hcoordinateMeas : Measurable
      (fun history : RetainedSampleHistory (AmbientSpace q.n) => history.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hoption : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  calc
    (∫ history, retainedSampleObservation weight j history ^ 3 ∂reference) =
        ∫ result, retainedOptionWeight weight result ^ 3
          ∂reference.map (fun history => history.1 j) := by
      rw [integral_map hcoordinateMeas.aemeasurable
        (hoption.pow_const 3).aestronglyMeasurable]
      rfl
    _ = ∫ result, retainedOptionWeight weight result ^ 3
          ∂scheduledRetainedExactSome q I phase := by rw [hcoordinate]
    _ = ∫ x, weight x ^ 3
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
      unfold scheduledRetainedExactSome
      rw [integral_map measurable_some.aemeasurable
        (hoption.pow_const 3).aestronglyMeasurable]
      rfl

/-- Exact coordinate marginals also transfer `L³` membership. -/
theorem memLp_retainedSampleObservation_three_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I phase) :
    MemLp (retainedSampleObservation
      (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))) j) 3 reference := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  let coord : RetainedSampleHistory (AmbientSpace q.n) →
      Option (AmbientSpace q.n) := fun history => history.1 j
  have hcoord : Measurable coord :=
    (measurable_pi_apply j).comp measurable_fst
  have hoption : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  rw [show retainedSampleObservation weight j =
      retainedOptionWeight weight ∘ coord by rfl]
  rw [← memLp_map_measure_iff hoption.aestronglyMeasurable hcoord.aemeasurable]
  change MemLp (retainedOptionWeight weight) 3
    (reference.map (fun history => history.1 j))
  rw [hcoordinate]
  unfold scheduledRetainedExactSome
  rw [memLp_map_measure_iff hoption.aestronglyMeasurable measurable_some.aemeasurable]
  simpa [weight, Function.comp_def, retainedOptionWeight] using
    gaussianRatioWeight_memLp q I (scheduleValue_pos q phase)
      (scheduleValue_pos q (phase + 1)) 3

/-- Exact coordinate cube bounds imply the `L³` prefix bounds required by
the sequential covariance recurrence. -/
theorem exactShadowHistory_prefix_thirdMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcoordinates : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase)
    {A : ℝ} (hA : 0 < A)
    (hthird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ A ^ 3) :
    ∀ i, i ≤ count →
      MemLp (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) i) 3 reference ∧
      (∫ history, sequentialPrefixSum
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)))) i history ^ 3 ∂reference) ≤
        ((i : ℝ) * A) ^ 3 := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let Y : ℕ → RetainedSampleHistory (AmbientSpace q.n) → ℝ :=
    retainedSampleObservation weight
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hYmeas : ∀ j, Measurable (Y j) :=
    fun j => measurable_retainedSampleObservation hweight j
  have hY0 : ∀ j history, 0 ≤ Y j history := by
    intro j history
    unfold Y retainedSampleObservation retainedOptionWeight
    cases history.1 j <;> simp [weight, gaussianRatioWeight_nonnegative]
  have hY3 : ∀ j, j < count → MemLp (Y j) 3 reference := by
    intro j hj
    simpa [Y, weight] using
      memLp_retainedSampleObservation_three_of_map_eq
        q I phase j reference (hcoordinates j hj)
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
    simpa [weight] using hthird
  intro i hi
  have hprefixLp : MemLp (sequentialPrefixSum Y i) 3 reference := by
    induction i with
    | zero =>
        change MemLp (fun _ : RetainedSampleHistory
          (AmbientSpace q.n) => (0 : ℝ)) 3 reference
        exact MemLp.zero
    | succ i ih =>
        have hiCount : i < count := by omega
        have hrec : sequentialPrefixSum Y (i + 1) =
            fun history => sequentialPrefixSum Y i history + Y i history := by
          funext history
          simpa [sequentialPrefixSum, Nat.succ_eq_add_one] using
            (Finset.sum_range_succ (fun j => Y j history) i)
        rw [hrec]
        exact (ih (by omega)).add (hY3 i hiCount)
  refine ⟨by simpa [Y, weight] using hprefixLp, ?_⟩
  have hprefixCubeInt : Integrable
      (fun history => sequentialPrefixSum Y i history ^ 3) reference := by
    have h := hprefixLp.integrable_norm_pow'
    apply h.congr
    filter_upwards with history
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold sequentialPrefixSum
      exact Finset.sum_nonneg fun j hj => hY0 j history)]
  have hsumCubeInt : Integrable
      (fun history => ∑ j ∈ Finset.range i, Y j history ^ 3) reference :=
    integrable_finsetSum _ fun j hj => (hY3 j (by
      have : j < i := Finset.mem_range.mp hj
      omega)).integrable_norm_pow'.congr (by
        filter_upwards with history
        rw [Real.norm_eq_abs, abs_of_nonneg (hY0 j history)])
  have hpoint : ∀ history,
      sequentialPrefixSum Y i history ^ 3 ≤
        (i : ℝ) ^ 2 * ∑ j ∈ Finset.range i, Y j history ^ 3 := by
    intro history
    have hpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.range i) (f := fun j => Y j history)
      (p := (3 : ℝ)) (by norm_num)
      (fun j _hj => hY0 j history)
    norm_num [Real.rpow_natCast] at hpow
    simpa [sequentialPrefixSum, Finset.card_range] using hpow
  calc
    (∫ history, sequentialPrefixSum Y i history ^ 3 ∂reference) ≤
        ∫ history, (i : ℝ) ^ 2 *
          (∑ j ∈ Finset.range i, Y j history ^ 3) ∂reference := by
      exact integral_mono hprefixCubeInt
        (hsumCubeInt.const_mul ((i : ℝ) ^ 2)) hpoint
    _ = (i : ℝ) ^ 2 *
          ∑ j ∈ Finset.range i, ∫ history, Y j history ^ 3 ∂reference := by
      rw [integral_const_mul, integral_finset_sum (s := Finset.range i)
        (fun j hj => (hY3 j (by
          have : j < i := Finset.mem_range.mp hj
          omega)).integrable_norm_pow'.congr (by
            filter_upwards with history
            rw [Real.norm_eq_abs, abs_of_nonneg (hY0 j history)]))]
    _ ≤ (i : ℝ) ^ 2 * ∑ _j ∈ Finset.range i, A ^ 3 := by
      gcongr with j hj
      exact hYcube j (by
        have : j < i := Finset.mem_range.mp hj
        omega)
    _ = ((i : ℝ) * A) ^ 3 := by
      simp [Finset.card_range]
      ring

#print axioms integral_retainedSampleObservation_cube_eq_gaussianThird_of_map_eq
#print axioms memLp_retainedSampleObservation_three_of_map_eq
#print axioms exactShadowHistory_prefix_thirdMoment_le

end

end ArlibCommunity.Algorithms.CV18
