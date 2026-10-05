/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostChain
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortCost

/-! # Expected cost of the paper-faithful aborting scheduled executable -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Structural whole-program cost bound after interpreting the executable
cooling program by its chronological retained-state trace. -/
theorem figureOneFinalScheduledAbortBaseProgram_cost_le_retained
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query) ≤
      1 + (figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle) := by
  calc
    _ ≤ 1 + ∫⁻ point, countedQueryCost
          ((scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).run oracle.query)
        ∂(truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q)) :=
      figureOneFinalScheduledAbortBaseProgram_countedQueryCost_le_initial_add
        q I oracle
    _ = _ := by
      rw [lintegral_scheduledBalancedFigureOnePointContinuation_cost_eq
        q I oracle]

/-- The explicit upper envelope supplied by the warm/live plus retained-error
decomposition for one Gaussian phase. -/
noncomputable def figureOneFinalScheduledGaussianPhaseCostEnvelope
    (q : VolumeParams) (phase : ℕ) : ENNReal :=
  ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
    figureOneSafeRetryCount q *
    figureOneFinalScheduledBalancedParameters.properStride q
      (scheduleValue q phase)) : ℕ) : ENNReal) +
  ((figureOnePhaseSampleCount q (scheduleValue q phase) *
    figureOneSafeRetryCount q *
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (scheduleValue q phase) + 2) : ℕ) : ENNReal) *
    figureOneScheduledRetainedError q phase

/-- The analogous terminal Gaussian-to-uniform envelope. -/
noncomputable def figureOneFinalScheduledTerminalCostEnvelope
    (q : VolumeParams) : ENNReal :=
  ((384 * (figureOneSampleCount q * figureOneSafeRetryCount q *
    figureOneFinalScheduledBalancedParameters.properStride q
      (terminalVariance q)) : ℕ) : ENNReal) +
  ((figureOneSampleCount q * figureOneSafeRetryCount q *
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q) + 2) : ℕ) : ENNReal) *
    figureOneScheduledRetainedError q (terminalPhaseSteps q)

/-- The part of the explicit envelope charged to the accumulated retained-law
error.  This is the only numerical remainder after the standard warm-work
sum is extracted. -/
noncomputable def figureOneFinalScheduledRetainedErrorCost
    (q : VolumeParams) : ENNReal :=
  (∑ phase ∈ Finset.range (terminalPhaseSteps q),
    ((figureOnePhaseSampleCount q (scheduleValue q phase) *
      figureOneSafeRetryCount q *
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase) + 2) : ℕ) : ENNReal) *
      figureOneScheduledRetainedError q phase) +
  ((figureOneSampleCount q * figureOneSafeRetryCount q *
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q) + 2) : ℕ) : ENNReal) *
    figureOneScheduledRetainedError q (terminalPhaseSteps q)

/-- Exact separation of the finite cost envelope into the familiar scheduled
proper work and the retained-error charge. -/
theorem figureOneFinalScheduledCostEnvelopes_eq_warm_add_error
    (q : VolumeParams) :
    (∑ phase ∈ Finset.range (terminalPhaseSteps q),
        figureOneFinalScheduledGaussianPhaseCostEnvelope q phase) +
      figureOneFinalScheduledTerminalCostEnvelope q =
    ((384 * (figureOneSafeRetryCount q *
      figureOneScheduledProperWork q) : ℕ) : ENNReal) +
      figureOneFinalScheduledRetainedErrorCost q := by
  simp only [figureOneFinalScheduledGaussianPhaseCostEnvelope,
    figureOneFinalScheduledTerminalCostEnvelope,
    figureOneFinalScheduledRetainedErrorCost, Finset.sum_add_distrib,
    Nat.cast_add, Nat.cast_mul,
    figureOneScheduledProperWork,
    figureOneScheduledBalancedParameters_properStride,
    figureOneFinalScheduledBalancedParameters_properStride]
  push_cast
  simp only [mul_add, Finset.mul_sum]
  ring_nf
  ac_rfl

theorem figureOneFinalScheduledGaussianPhaseExpectedCost_le_envelope
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (hphase : phase < terminalPhaseSteps q) :
    figureOneFinalScheduledGaussianPhaseExpectedCost q I oracle phase ≤
      figureOneFinalScheduledGaussianPhaseCostEnvelope q phase := by
  simpa only [figureOneFinalScheduledGaussianPhaseCostEnvelope,
    figureOneFinalScheduledBalancedParameters_retryLimit] using
      figureOneFinalScheduledGaussianPhaseExpectedCost_le
        q I oracle phase hphase

theorem figureOneFinalScheduledTerminalExpectedCost_le_envelope
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    figureOneFinalScheduledTerminalExpectedCost q I oracle ≤
      figureOneFinalScheduledTerminalCostEnvelope q := by
  simpa only [figureOneFinalScheduledTerminalCostEnvelope,
    figureOneFinalScheduledBalancedParameters_retryLimit] using
      figureOneFinalScheduledTerminalExpectedCost_le q I oracle

/-- The recursive chronological cost sum is bounded by the finite sum of the
explicit phase envelopes. -/
theorem figureOneFinalScheduledGaussianPhaseCostTail_le_sum
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps, phase + steps ≤ terminalPhaseSteps q →
    figureOneFinalScheduledGaussianPhaseCostTail q I oracle phase steps ≤
      ∑ k ∈ Finset.range steps,
        figureOneFinalScheduledGaussianPhaseCostEnvelope q (phase + k) := by
  intro phase steps
  induction steps generalizing phase with
  | zero => simp [figureOneFinalScheduledGaussianPhaseCostTail]
  | succ steps ih =>
      intro hbound
      rw [figureOneFinalScheduledGaussianPhaseCostTail]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm (∑ k ∈ Finset.range steps,
        figureOneFinalScheduledGaussianPhaseCostEnvelope q (phase + (k + 1)))
        (figureOneFinalScheduledGaussianPhaseCostEnvelope q phase)]
      apply add_le_add
      · exact figureOneFinalScheduledGaussianPhaseExpectedCost_le_envelope
          q I oracle phase (by omega)
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (phase + 1) (by omega)

/-- Fully explicit finite-sum bound for the aborting base executable. -/
theorem figureOneFinalScheduledAbortBaseProgram_cost_le_envelopes
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query) ≤
      1 + ((∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOneFinalScheduledGaussianPhaseCostEnvelope q phase) +
        figureOneFinalScheduledTerminalCostEnvelope q) := by
  calc
    _ ≤ 1 + (figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle) :=
      figureOneFinalScheduledAbortBaseProgram_cost_le_retained q I oracle
    _ ≤ _ := by
      gcongr
      · simpa only [zero_add] using
          figureOneFinalScheduledGaussianPhaseCostTail_le_sum q I oracle 0
            (terminalPhaseSteps q) (by omega)
      · exact figureOneFinalScheduledTerminalExpectedCost_le_envelope q I oracle

/-- Rate-ready reduction: the live/warm portion is the already-bounded
scheduled work; all remaining arithmetic is isolated in one error charge. -/
theorem figureOneFinalScheduledAbortBaseProgram_cost_le_warm_add_error
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query) ≤
      1 + (((384 * (figureOneSafeRetryCount q *
          figureOneScheduledProperWork q) : ℕ) : ENNReal) +
        figureOneFinalScheduledRetainedErrorCost q) := by
  rw [← figureOneFinalScheduledCostEnvelopes_eq_warm_add_error q]
  exact figureOneFinalScheduledAbortBaseProgram_cost_le_envelopes q I oracle

/-- The extracted live/warm work occupies at most nine tenths of the selected
`10^30` scheduled-rate constant. -/
theorem figureOneFinalScheduledWarmCost_le_rate (q : VolumeParams) :
    ((384 * (figureOneSafeRetryCount q *
      figureOneScheduledProperWork q) : ℕ) : ENNReal) ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q) := by
  simpa only [ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (figureOneWarmShadowScheduledWork_cast_le q)

#print axioms figureOneFinalScheduledAbortBaseProgram_cost_le_retained
#print axioms figureOneFinalScheduledAbortBaseProgram_cost_le_envelopes
#print axioms figureOneFinalScheduledAbortBaseProgram_cost_le_warm_add_error
#print axioms figureOneFinalScheduledWarmCost_le_rate

end ArlibCommunity.Algorithms.CV18
