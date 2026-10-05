/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableTransfer

/-!
# Bounded means under the scheduled accepted target

This file turns the scheduled accepted-target total-variation estimate into
the bounded-observable estimate needed in the first-moment half of CV18
equation (6).  In particular, it identifies the exact error budget used by
the executable schedule rather than leaving an abstract mixing hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- A bounded nonnegative observable has almost the same mean under the
scheduled accepted target and the exact truncated Gaussian target. -/
theorem integral_figureOneScheduledAcceptedTargetAt_sub_truncatedGaussian_abs_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {f : AmbientSpace q.n → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 < B) (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    |(∫ x, f x ∂figureOneScheduledAcceptedTargetAt q I phase) -
        ∫ x, f x ∂(truncatedGaussianProbability q I
          (scheduleValue q phase) (scheduleValue_pos q phase) :
            Measure (AmbientSpace q.n))| ≤
      B * (figureOneCorrectedTargetBudget q).toReal := by
  let _ : IsProbabilityMeasure
      (figureOneScheduledAcceptedTargetAt q I phase) :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) :=
    inferInstance
  have htv : TVLe
      (figureOneScheduledAcceptedTargetAt q I phase)
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
      (scheduledBalancedStationaryTargetError q) := by
    simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
        q I (scheduleValue_pos q phase)
  have htarget := scheduledBalancedStationaryTargetError_le_targetBudget q
  have htargetTop : figureOneCorrectedTargetBudget q ≠ ⊤ := by
    unfold figureOneCorrectedTargetBudget figureOneCorrectedTransitionBudget
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hstationaryTop : scheduledBalancedStationaryTargetError q ≠ ⊤ :=
    ne_top_of_le_ne_top htargetTop htarget
  calc
    |(∫ x, f x ∂figureOneScheduledAcceptedTargetAt q I phase) -
        ∫ x, f x ∂(truncatedGaussianProbability q I
          (scheduleValue q phase) (scheduleValue_pos q phase) :
            Measure (AmbientSpace q.n))| ≤
        B * (scheduledBalancedStationaryTargetError q).toReal :=
      Arlib.TVLe.integral_le_of_nonnegative_le
        htv hstationaryTop hf hB hf0 hfB
    _ ≤ B * (figureOneCorrectedTargetBudget q).toReal := by
      exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono htargetTop htarget) hB.le

#print axioms
  integral_figureOneScheduledAcceptedTargetAt_sub_truncatedGaussian_abs_le

end ArlibCommunity.Algorithms.CV18
