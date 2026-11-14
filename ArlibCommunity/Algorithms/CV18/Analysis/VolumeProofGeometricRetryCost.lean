/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost

/-!
# Finite geometric retry-cost arithmetic

The balanced rejection stage has stationary rejection mass at most `121/128`.
This module packages the exact finite retry recurrence and its uniform
`128/7` expectation multiplier.
-/

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal BigOperators

/-- Cost of at most `attempts` trials when each live trial costs at most
`trialCost` and leaves a retry branch of mass at most `rejectMass`. -/
noncomputable def finiteRetryExpectedCost
    (trialCost rejectMass : ENNReal) : ℕ → ENNReal
  | 0 => 0
  | attempts + 1 => trialCost + rejectMass *
      finiteRetryExpectedCost trialCost rejectMass attempts

private theorem one_add_mul_sum_range_pow (rejectMass : ENNReal) : ∀ attempts,
    1 + rejectMass * ∑ i ∈ Finset.range attempts, rejectMass ^ i =
      ∑ i ∈ Finset.range (attempts + 1), rejectMass ^ i := by
  intro attempts
  induction attempts with
  | zero => simp
  | succ attempts ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ, ← ih]
      ring

theorem finiteRetryExpectedCost_eq_sum
    (trialCost rejectMass : ENNReal) : ∀ attempts,
    finiteRetryExpectedCost trialCost rejectMass attempts =
      trialCost * ∑ i ∈ Finset.range attempts, rejectMass ^ i := by
  intro attempts
  induction attempts with
  | zero => simp [finiteRetryExpectedCost]
  | succ attempts ih =>
      rw [finiteRetryExpectedCost, ih]
      calc
        trialCost + rejectMass *
            (trialCost * ∑ i ∈ Finset.range attempts, rejectMass ^ i) =
          trialCost *
            (1 + rejectMass * ∑ i ∈ Finset.range attempts, rejectMass ^ i) := by
              ring
        _ = trialCost * ∑ i ∈ Finset.range (attempts + 1), rejectMass ^ i := by
          rw [one_add_mul_sum_range_pow]

theorem finiteRetryExpectedCost_mono_rejectMass
    {trialCost rejectMass bound : ENNReal} (hreject : rejectMass ≤ bound) :
    ∀ attempts,
      finiteRetryExpectedCost trialCost rejectMass attempts ≤
        finiteRetryExpectedCost trialCost bound attempts := by
  intro attempts
  induction attempts with
  | zero => simp [finiteRetryExpectedCost]
  | succ attempts ih =>
      simp only [finiteRetryExpectedCost]
      gcongr

theorem sum_range_balancedRejectMass_pow_le (attempts : ℕ) :
    ∑ i ∈ Finset.range attempts,
        ENNReal.ofReal (121 / 128 : ℝ) ^ i ≤
      ENNReal.ofReal (128 / 7 : ℝ) := by
  calc
    ∑ i ∈ Finset.range attempts,
        ENNReal.ofReal (121 / 128 : ℝ) ^ i ≤
      ∑' i : ℕ, ENNReal.ofReal (121 / 128 : ℝ) ^ i :=
        ENNReal.sum_le_tsum (Finset.range attempts)
    _ = (1 - ENNReal.ofReal (121 / 128 : ℝ))⁻¹ :=
      ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (128 / 7 : ℝ) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 121 / 128)]
      have hpos : (0 : ℝ) < 7 / 128 := by norm_num
      rw [show (1 - 121 / 128 : ℝ) = 7 / 128 by norm_num,
        ← ENNReal.ofReal_inv_of_pos hpos]
      congr 1
      norm_num

/-- The balanced retry loop costs at most `128/7` times one live trial,
uniformly in its finite retry limit. -/
theorem finiteRetryExpectedCost_balanced_le
    (trialCost : ENNReal) (attempts : ℕ) :
    finiteRetryExpectedCost trialCost
        (ENNReal.ofReal (121 / 128 : ℝ)) attempts ≤
      trialCost * ENNReal.ofReal (128 / 7 : ℝ) := by
  rw [finiteRetryExpectedCost_eq_sum]
  gcongr
  exact sum_range_balancedRejectMass_pow_le attempts

/-- Allowing one additional `1/128` mixing-error mass per rejection raises
the geometric multiplier only from `128/7` to `64/3`. -/
theorem sum_range_nearBalancedRejectMass_pow_le (attempts : ℕ) :
    ∑ i ∈ Finset.range attempts,
        ENNReal.ofReal (61 / 64 : ℝ) ^ i ≤
      ENNReal.ofReal (64 / 3 : ℝ) := by
  calc
    ∑ i ∈ Finset.range attempts,
        ENNReal.ofReal (61 / 64 : ℝ) ^ i ≤
      ∑' i : ℕ, ENNReal.ofReal (61 / 64 : ℝ) ^ i :=
        ENNReal.sum_le_tsum (Finset.range attempts)
    _ = (1 - ENNReal.ofReal (61 / 64 : ℝ))⁻¹ :=
      ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (64 / 3 : ℝ) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 61 / 64)]
      have hpos : (0 : ℝ) < 3 / 64 := by norm_num
      rw [show (1 - 61 / 64 : ℝ) = 3 / 64 by norm_num,
        ← ENNReal.ofReal_inv_of_pos hpos]
      congr 1
      norm_num

theorem finiteRetryExpectedCost_nearBalanced_le
    (trialCost : ENNReal) (attempts : ℕ) :
    finiteRetryExpectedCost trialCost
        (ENNReal.ofReal (61 / 64 : ℝ)) attempts ≤
      trialCost * ENNReal.ofReal (64 / 3 : ℝ) := by
  rw [finiteRetryExpectedCost_eq_sum]
  gcongr
  exact sum_range_nearBalancedRejectMass_pow_le attempts

/-- The exact arithmetic step used after adding at most `1/128` block error
to the stationary `121/128` rejection mass. -/
theorem balancedRejectMass_add_error_le_nearBalanced
    {rejectMass blockError : ENNReal}
    (hreject : rejectMass ≤ ENNReal.ofReal (121 / 128 : ℝ))
    (herror : blockError ≤ ENNReal.ofReal (1 / 128 : ℝ)) :
    rejectMass + blockError ≤ ENNReal.ofReal (61 / 64 : ℝ) := by
  calc
    rejectMass + blockError ≤
        ENNReal.ofReal (121 / 128 : ℝ) +
          ENNReal.ofReal (1 / 128 : ℝ) := add_le_add hreject herror
    _ = ENNReal.ofReal (61 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 121 / 128)] <;>
        norm_num

end ArlibCommunity.Algorithms.CV18
