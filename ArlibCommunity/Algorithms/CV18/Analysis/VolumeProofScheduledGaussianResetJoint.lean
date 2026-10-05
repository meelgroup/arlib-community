/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetAverageSecond
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetEventTransfer

/-!
# Joint Gaussian phase reset targets

The fixed-cost sample-history reference is mapped back to the public phase
result.  This keeps the empirical-average moment bounds and exposes, in the
same witness, the exact retained-state marginal needed to start the next
chronological phase.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Map a fixed-reset sample history to the public averaged phase result. -/
noncomputable def scheduledGaussianResetJointOutput
    (q : VolumeParams) (phase count : ℕ) :
    RetainedSampleHistory (AmbientSpace q.n) →
      Option (ℝ × AmbientSpace q.n) :=
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  balancedCoolingAverage count ∘ retainedSumOutput ∘
    retainedSampleHistoryToSum weight count

theorem measurable_scheduledGaussianResetJointOutput
    (q : VolumeParams) (phase count : ℕ) :
    Measurable (scheduledGaussianResetJointOutput q phase count) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  exact (measurable_balancedCoolingAverage count).comp <|
    measurable_retainedSumOutput.comp <|
      measurable_retainedSampleHistoryToSum
        (measurable_gaussianRatioWeight _ _) count

theorem map_initializedScheduledRetainedHistory_jointOutput
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : count = figureOnePhaseSampleCount q (scheduleValue q phase)) :
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1)).map
        (scheduledGaussianResetJointOutput q phase count) =
      figureOneScheduledGaussianPhaseTarget q I phase := by
  subst count
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight _ _
  have hsum := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K hK.1 hK.2 weight hweight exact (count - 1)
  have htail : count - 1 + 1 = count := by
    have hcountPos := figureOnePhaseSampleCount_pos q (scheduleValue q phase)
    omega
  rw [htail] at hsum
  rw [figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel]
  rw [← hsum]
  unfold scheduledGaussianResetJointOutput
  rw [Measure.map_map
    ((measurable_balancedCoolingAverage count).comp
      measurable_retainedSumOutput)
    (measurable_retainedSampleHistoryToSum hweight count)]
  rfl

/-- The joint output of an exact-state reset reference retains that exact
state marginal. -/
theorem map_scheduledGaussianResetJointOutput_optionSnd
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hstate : reference.map retainedSampleHistoryState =
      scheduledRetainedExactSome q I phase) :
    (reference.map (scheduledGaussianResetJointOutput q phase count)).map
        optionSnd = scheduledRetainedExactSome q I phase := by
  have hout := measurable_scheduledGaussianResetJointOutput q phase count
  rw [Measure.map_map measurable_optionSnd hout]
  calc
    reference.map (optionSnd ∘ scheduledGaussianResetJointOutput q phase count) =
        reference.map retainedSampleHistoryState := by
      apply Measure.map_congr
      filter_upwards with history
      change optionSnd (balancedCoolingAverage count
        (retainedSumOutput
          (retainedSampleHistoryToSum
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) count history))) = history.2
      rw [optionSnd_balancedCoolingAverage]
      unfold retainedSampleHistoryToSum
      cases history.2 <;> rfl
    _ = scheduledRetainedExactSome q I phase := hstate

/-- A Gaussian phase has one joint reset target carrying the exact retained
state and the reference Eq.(6) bounds for its live empirical average. -/
theorem exists_figureOneScheduledGaussianResetJointTarget
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : count = figureOnePhaseSampleCount q (scheduleValue q phase))
    (hcountPos : 0 < count)
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
    ∃ target : Measure (Option (ℝ × AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo (figureOneScheduledGaussianPhaseTarget q I phase)
        target (scheduledResetReferenceError q (count - 1)) ∧
      target.map optionSnd = scheduledRetainedExactSome q I phase ∧
      MemLp figureOneScheduledTraceLiveRawOutput 2 target ∧
      (∫ result, figureOneScheduledTraceLiveRawOutput result ∂target) =
        ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)) x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) ∧
      (∫ result, figureOneScheduledTraceLiveRawOutput result ^ 2 ∂target) ≤
        (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
          3 * (figureOneDependentEpsilon q +
              3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
                (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * A ^ 2 := by
  obtain ⟨reference, hreferenceProb, hcomparison, hstate, hmem,
      hmean, hsecond⟩ :=
    exists_scheduledRetainedResetReference_average_secondMoment_with_state
      q I phase count hcountPos hcountMax hA hmean0 hcoordinateMean
        hcoordinateSecond hcoordinateThird
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let output := scheduledGaussianResetJointOutput q phase count
  let target := reference.map output
  have houtput : Measurable output :=
    measurable_scheduledGaussianResetJointOutput q phase count
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  have hlive : ∀ᵐ history ∂reference,
      retainedSampleHistoryState history ≠ none := by
    have hset : MeasurableSet
        ({state : Option (AmbientSpace q.n) | state ≠ none}) :=
      measurableSet_option_none.compl
    have htarget : ∀ᵐ state ∂scheduledRetainedExactSome q I phase,
        state ≠ none := by
      unfold scheduledRetainedExactSome
      apply (ae_map_iff measurable_some.aemeasurable hset).2
      exact ae_of_all _ fun point => by simp
    rw [← hstate] at htarget
    exact (ae_map_iff measurable_snd.aemeasurable hset).1 htarget
  have hscore : ∀ᵐ history ∂reference,
      figureOneScheduledTraceLiveRawOutput (output history) =
        sequentialPrefixSum
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)))) count history /
            (count : ℝ) := by
    filter_upwards [hlive] with history hhistory
    rcases hstateValue : retainedSampleHistoryState history with _ | point
    · exact (hhistory hstateValue).elim
    · have hsum0 : 0 ≤ sequentialPrefixSum
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)))) count history := by
        unfold sequentialPrefixSum
        apply Finset.sum_nonneg
        intro i hi
        unfold retainedSampleObservation retainedOptionWeight
        cases history.1 i <;> simp [gaussianRatioWeight_nonnegative]
      have hcount0 : (0 : ℝ) ≤ count := by exact_mod_cast hcountPos.le
      change history.2 = some point at hstateValue
      simp [output, scheduledGaussianResetJointOutput, Function.comp_def,
        retainedSampleHistoryToSum, retainedSumOutput, balancedCoolingAverage,
        figureOneScheduledTraceLiveRawOutput, hstateValue,
        sequentialPrefixSum]
      exact div_nonneg hsum0 hcount0
  refine ⟨target, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · have hmapped := hcomparison.map houtput
    rw [map_initializedScheduledRetainedHistory_jointOutput
      q I phase count hcount] at hmapped
    simpa only [target, output] using hmapped
  · simpa only [target, output] using
      map_scheduledGaussianResetJointOutput_optionSnd
        q I phase count reference hstate
  · apply (memLp_map_measure_iff
      measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable
      houtput.aemeasurable).2
    exact (memLp_congr_ae hscore).2 hmem
  · rw [show target = reference.map output by rfl,
      integral_map houtput.aemeasurable
        measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable]
    rw [integral_congr_ae hscore]
    exact hmean
  · rw [show target = reference.map output by rfl,
      integral_map houtput.aemeasurable
        (measurable_figureOneScheduledTraceLiveRawOutput.pow_const 2).aestronglyMeasurable]
    have hscoreSq :
        (fun history =>
          (figureOneScheduledTraceLiveRawOutput (output history)) ^ 2) =ᵐ[reference]
        (fun history =>
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ)) ^ 2) :=
      hscore.mono fun history hh => congrArg (fun value : ℝ => value ^ 2) hh
    rw [integral_congr_ae hscoreSq]
    exact hsecond

#print axioms map_initializedScheduledRetainedHistory_jointOutput
#print axioms map_scheduledGaussianResetJointOutput_optionSnd
#print axioms exists_figureOneScheduledGaussianResetJointTarget

end

end ArlibCommunity.Algorithms.CV18
