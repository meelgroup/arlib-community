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

theorem firstWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    firstWalkRequirement q sigma2 attempts ≤
      (strideFor q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem retryWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    retryWalkRequirement q sigma2 attempts ≤
      (strideFor q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem strideFor_pos
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    0 < strideFor q sigma2 attempts := by
  have hone : (1 : ℝ) ≤
      strideFor q sigma2 attempts := by
    apply le_trans (le_max_left _ _)
    exact Nat.le_ceil _
  exact_mod_cast hone

/-- The new logarithm is not hidden in an abstract constant: after expansion
the proposal denominator contains exactly
`sqrt (n * accuracyLog q)`. -/
theorem firstWalkRequirement_explicit
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    firstWalkRequirement q sigma2 attempts =
      4 * ((Real.log (16 * warmConstant q) +
          2 * Real.log
            (1 / blockMixingError q attempts)) /
        (((min (Real.sqrt sigma2) 1 /
            (4096 * Real.sqrt
              ((q.n : ℝ) * accuracyLog q))) * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2)) + 1 := by
  simp only [firstWalkRequirement,
    walkRequirement, proposalRadius]

theorem retryWalkRequirement_explicit
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    retryWalkRequirement q sigma2 attempts =
      4 * ((Real.log 2 +
          2 * Real.log
            (1 / blockMixingError q attempts)) /
        (((min (Real.sqrt sigma2) 1 /
            (4096 * Real.sqrt
              ((q.n : ℝ) * accuracyLog q))) * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2)) + 1 := by
  simp only [retryWalkRequirement,
    walkRequirement, proposalRadius]

/-- Expanded budget dependence of the new logarithm.  This records that the
only new cost factor is logarithmic in the already-selected per-sample
exact-chance error, rather than a bounded-roundness parameter. -/
theorem accuracyLog_eq_perSample
    (q : VolumeParams) :
    accuracyLog q =
      max
        (protectedLog ((q.n : ℝ) /
          (sampleMixingError q / 768)))
        (protectedLog ((q.n : ℝ) /
          (sampleMixingError q / 8))) := by
  rfl

#print axioms firstWalkRequirement_le_stride
#print axioms retryWalkRequirement_le_stride
#print axioms accuracyLog_eq_perSample

end ArlibCommunity.Algorithms.CV18
