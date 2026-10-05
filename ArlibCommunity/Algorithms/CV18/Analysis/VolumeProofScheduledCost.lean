/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedTarget

/-! # Scheduled accuracy stride and its exact logarithmic cost

The scheduled KLS body is larger than the old fixed body, so its proposal is
smaller by the new accuracy logarithm.  These definitions thread that exact
proposal through the first-block and retry-block mixing deadlines.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- First proper block: accepted-state warmness followed by adjacent-phase
warmness, at the component error assigned to one block. -/
noncomputable def figureOneScheduledCorrectedFirstWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  figureOneScheduledWalkRequirement q sigma2
    (16 * speedyAdjacentWarmConstant q)
    (figureOneCorrectedBlockMixingError q attempts)

/-- Retry blocks start from the normalized rejected branch, which is
two-warm for the scheduled speedy stationary law. -/
noncomputable def figureOneScheduledCorrectedRetryWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  figureOneScheduledWalkRequirement q sigma2 2
    (figureOneCorrectedBlockMixingError q attempts)

/-- A single proper-step stride covering both block types at scheduled
geometry. -/
noncomputable def figureOneScheduledCorrectedProperStride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℕ :=
  Nat.ceil (max 1 (max
    (figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts)
    (figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts)))

theorem figureOneScheduledCorrectedFirstWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts ≤
      (figureOneScheduledCorrectedProperStride q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem figureOneScheduledCorrectedRetryWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts ≤
      (figureOneScheduledCorrectedProperStride q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem figureOneScheduledCorrectedProperStride_pos
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    0 < figureOneScheduledCorrectedProperStride q sigma2 attempts := by
  have hone : (1 : ℝ) ≤
      figureOneScheduledCorrectedProperStride q sigma2 attempts := by
    apply le_trans (le_max_left _ _)
    exact Nat.le_ceil _
  exact_mod_cast hone

/-- The new logarithm is not hidden in an abstract constant: after expansion
the proposal denominator contains exactly
`sqrt (n * figureOneScheduledAccuracyLog q)`. -/
theorem figureOneScheduledCorrectedFirstWalkRequirement_explicit
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts =
      4 * ((Real.log (16 * speedyAdjacentWarmConstant q) +
          2 * Real.log
            (1 / figureOneCorrectedBlockMixingError q attempts)) /
        (((min (Real.sqrt sigma2) 1 /
            (4096 * Real.sqrt
              ((q.n : ℝ) * figureOneScheduledAccuracyLog q))) * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2)) + 1 := by
  simp only [figureOneScheduledCorrectedFirstWalkRequirement,
    figureOneScheduledWalkRequirement, figureOneScheduledProposalRadius]

theorem figureOneScheduledCorrectedRetryWalkRequirement_explicit
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts =
      4 * ((Real.log 2 +
          2 * Real.log
            (1 / figureOneCorrectedBlockMixingError q attempts)) /
        (((min (Real.sqrt sigma2) 1 /
            (4096 * Real.sqrt
              ((q.n : ℝ) * figureOneScheduledAccuracyLog q))) * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2)) + 1 := by
  simp only [figureOneScheduledCorrectedRetryWalkRequirement,
    figureOneScheduledWalkRequirement, figureOneScheduledProposalRadius]

/-- Expanded budget dependence of the new logarithm.  This records that the
only new cost factor is logarithmic in the already-selected per-sample
exact-chance error, rather than a bounded-roundness parameter. -/
theorem figureOneScheduledAccuracyLog_eq_perSample
    (q : VolumeParams) :
    figureOneScheduledAccuracyLog q =
      max
        (protectedLog ((q.n : ℝ) /
          (figureOnePerSampleMixingError q / 768)))
        (protectedLog ((q.n : ℝ) /
          (figureOnePerSampleMixingError q / 8))) := by
  rfl

#print axioms figureOneScheduledCorrectedFirstWalkRequirement_le_stride
#print axioms figureOneScheduledCorrectedRetryWalkRequirement_le_stride
#print axioms figureOneScheduledAccuracyLog_eq_perSample

end ArlibCommunity.Algorithms.CV18
