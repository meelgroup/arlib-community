/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCoolingPrimitives

/-! # Exact work sum for the scheduled proper stride

This isolates the remaining rate question from the probabilistic expected-cost
proof: after the geometric retry multiplier is discharged, the raw proper-step
work is precisely the phase/sample sum below.
-/

namespace ArlibCommunity.Algorithms.CV18

open scoped BigOperators

/-- Exact soft-O rate of the schedule-targeted executable.  The two extra
factors are logarithmic: one selects the accuracy body/radius and the other
is the squared warm-start mixing deadline. -/
noncomputable def volumeScheduledBaseComplexityRate (q : VolumeParams) : ℝ :=
  volumeBaseComplexityRate q * figureOneScheduledAccuracyLog q *
    protectedLog (1 / figureOneCorrectedBlockMixingError q
      (figureOneSafeRetryCount q - 1)) ^ 2

theorem volumeScheduledBaseComplexityRate_pos (q : VolumeParams) :
    0 < volumeScheduledBaseComplexityRate q := by
  unfold volumeScheduledBaseComplexityRate
  have hbase : 0 < volumeBaseComplexityRate q :=
    volumeBaseComplexityRate_pos_balanced q
  have haccuracy : 0 < figureOneScheduledAccuracyLog q :=
    lt_of_lt_of_le zero_lt_one (figureOneScheduledAccuracyLog_one_le q)
  have hmix : 0 < protectedLog
      (1 / figureOneCorrectedBlockMixingError q
        (figureOneSafeRetryCount q - 1)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos (mul_pos hbase haccuracy) (sq_pos_of_pos hmix)

theorem volumeBaseComplexityRate_le_scheduled (q : VolumeParams) :
    volumeBaseComplexityRate q ≤ volumeScheduledBaseComplexityRate q := by
  unfold volumeScheduledBaseComplexityRate
  have hbase : 0 ≤ volumeBaseComplexityRate q :=
    (volumeBaseComplexityRate_pos_balanced q).le
  have hA : 1 ≤ figureOneScheduledAccuracyLog q :=
    figureOneScheduledAccuracyLog_one_le q
  have hB : 1 ≤ protectedLog
      (1 / figureOneCorrectedBlockMixingError q
        (figureOneSafeRetryCount q - 1)) := le_max_left _ _
  calc
    volumeBaseComplexityRate q = volumeBaseComplexityRate q * 1 * 1 := by ring
    _ ≤ volumeBaseComplexityRate q * figureOneScheduledAccuracyLog q *
        protectedLog (1 / figureOneCorrectedBlockMixingError q
          (figureOneSafeRetryCount q - 1)) ^ 2 := by
      gcongr
      nlinarith [sq_nonneg (protectedLog
        (1 / figureOneCorrectedBlockMixingError q
          (figureOneSafeRetryCount q - 1)) - 1)]

theorem volumeScheduledBaseComplexityRate_one_le (q : VolumeParams) :
    1 ≤ volumeScheduledBaseComplexityRate q := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let L : ℝ := protectedLog (n / q.eps)
  let Le : ℝ := protectedLog (1 / q.eps)
  let H : ℝ := protectedLog (volumeTerminalScale q)
  let R : ℝ := M * n ^ 3 / q.eps ^ 2 * Le ^ 2 * L ^ 2 * H ^ 2
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hL : 1 ≤ L := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hH : 1 ≤ H := le_max_left _ _
  have he2pos : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have he2le : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hR : 1 ≤ R := by
    have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ (le_trans (by norm_num) hn)
    have hfirst : 1 ≤ M * n ^ 3 / q.eps ^ 2 := by
      rw [le_div_iff₀ he2pos]
      simpa only [one_mul] using he2le.trans (hmul hM hn3)
    exact hmul (hmul (hmul hfirst (one_le_pow₀ hLe))
      (one_le_pow₀ hL)) (one_le_pow₀ hH)
  have hbase : volumeBaseComplexityRate q = R := by
    dsimp [volumeBaseComplexityRate, R, M, n, Le, L, H, terminalVariance]
  exact (hbase.symm ▸ hR).trans (volumeBaseComplexityRate_le_scheduled q)

/-- Exact expected-cost target consumed by the generalized capstone. -/
def FigureOneScheduledBalancedExpectedQueryCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (C : ℝ) : Prop :=
  ∫⁻ outcome, (outcome.2 : ENNReal)
      ∂((figureOneScheduledBalancedBaseProgram q).run oracle.query) ≤
    ENNReal.ofReal (C * volumeScheduledBaseComplexityRate q)

noncomputable def figureOneScheduledProperWork (q : VolumeParams) : ℕ :=
  (∑ k ∈ Finset.range (terminalPhaseSteps q),
      figureOnePhaseSampleCount q (scheduleValue q k) *
        figureOneScheduledBalancedParameters.properStride q
          (scheduleValue q k)) +
    figureOneSampleCount q *
      figureOneScheduledBalancedParameters.properStride q (terminalVariance q)

/-- Pointwise stride overhead lifts without loss through all phase and sample
counts.  This is the exact interface needed to reuse `figureOne_base_query_cost`.
-/
theorem figureOneScheduledProperWork_le_mul_old
    (q : VolumeParams) (overhead : ℕ)
    (hstride : ∀ sigma2,
      figureOneScheduledBalancedParameters.properStride q sigma2 ≤
        overhead * figureOneWalkSteps q sigma2) :
    figureOneScheduledProperWork q ≤
      overhead *
        (figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q)) := by
  rw [figureOneCoolingQueryBudget_explicit]
  unfold figureOneScheduledProperWork
  calc
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
        figureOnePhaseSampleCount q (scheduleValue q k) *
          figureOneScheduledBalancedParameters.properStride q
            (scheduleValue q k)) +
        figureOneSampleCount q *
          figureOneScheduledBalancedParameters.properStride q
            (terminalVariance q) ≤
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
        figureOnePhaseSampleCount q (scheduleValue q k) *
          (overhead * figureOneWalkSteps q (scheduleValue q k))) +
        figureOneSampleCount q *
          (overhead * figureOneWalkSteps q (terminalVariance q)) := by
      gcongr with k hk
      · exact hstride _
      · exact hstride _
    _ = overhead *
        ((∑ k ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q k) *
            figureOneWalkSteps q (scheduleValue q k)) +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q)) := by
      rw [Nat.mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro k hk
        simp [mul_assoc, mul_left_comm, mul_comm]
      · simp [mul_assoc, mul_left_comm, mul_comm]

/-- The old explicit rate theorem controls scheduled work exactly when the
scheduled stride has a uniform constant overhead.  The expanded scheduled
formula shows why proving such a constant is the remaining arithmetic issue.
-/
theorem figureOneScheduledProperWork_le_mul_ceil_rate
    (overhead : ℕ)
    (hstride : ∀ q sigma2,
      figureOneScheduledBalancedParameters.properStride q sigma2 ≤
        overhead * figureOneWalkSteps q sigma2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q,
      figureOneScheduledProperWork q ≤
        overhead * Nat.ceil (C * volumeBaseComplexityRate q) := by
  obtain ⟨C, hC, hbaseAll⟩ := figureOne_base_query_cost
  refine ⟨C, hC, ?_⟩
  intro q
  have hbase : figureOneCoolingQueryBudget q
          (explicitVolumeCoolingSchedule q).variances +
        figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q) ≤
      Nat.ceil (C * volumeBaseComplexityRate q) := by
    have hone := hbaseAll q
    omega
  exact (figureOneScheduledProperWork_le_mul_old q overhead (hstride q)).trans
    (Nat.mul_le_mul_left overhead hbase)

#print axioms figureOneScheduledProperWork_le_mul_old

end ArlibCommunity.Algorithms.CV18
