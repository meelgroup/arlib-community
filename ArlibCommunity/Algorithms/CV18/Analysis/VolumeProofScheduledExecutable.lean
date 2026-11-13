/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduleTargetedKLS
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram

/-! # Executable balanced sampler at schedule-targeted geometry -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

theorem scheduledAccuracyMetropolisMarkedProposalProgram_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).QueryBound
      1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem scheduledAccuracyMetropolisMarkedBallStep_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  exact scheduledAccuracyMetropolisMarkedProposalProgram_queryBound
    q sigma2 current proposal

theorem scheduledAccuracyZeroObservation_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

theorem cappedScheduledAccuracyProperBlockAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper current,
      (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
        rawCap remainingProper current).QueryBound rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper current
      rw [cappedScheduledAccuracyProperBlockAux]
      exact .pure _ 0
  | succ rawCap ih =>
      intro remainingProper current
      cases remainingProper with
      | zero =>
          simp only [cappedScheduledAccuracyProperBlockAux]
          simpa [Nat.add_comm] using
            (scheduledAccuracyZeroObservation_queryBound
              q sigma2 current).bind (fun observed => .pure _ rawCap)
      | succ remainingProper =>
          simp only [cappedScheduledAccuracyProperBlockAux]
          simpa [Nat.add_comm] using
            (scheduledAccuracyMetropolisMarkedBallStep_queryBound
              q sigma2 current).bind (fun result => by
                by_cases hmark : result.1 = true
                · simp only [hmark, if_true]
                  cases remainingProper with
                  | zero => exact ih 0 result.2
                  | succ nextRemaining => exact ih (nextRemaining + 1) result.2
                · have hfalse : result.1 = false :=
                    Bool.eq_false_of_not_eq_true hmark
                  simp only [hfalse, if_false]
                  exact ih (remainingProper + 1) result.2)

theorem cappedScheduledAccuracyProperBlock_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (rawCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    (cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride
      current).QueryBound rawCap :=
  cappedScheduledAccuracyProperBlockAux_queryBound q sigma2 properStride
    rawCap properStride current

theorem scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).QueryBound
      1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem scheduledBalancedAccuracyRetryCollectAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples total current,
      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
        properStride retryLimit attempts samples total current).QueryBound
          (balancedRetryQueryBudget proposalCap retryLimit attempts samples) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro total current
          rw [scheduledBalancedAccuracyRetryCollectAux]
          exact .pure _ _
      | succ future =>
          induction attempts with
          | zero =>
              intro total current
              rw [scheduledBalancedAccuracyRetryCollectAux]
              exact .pure _ _
          | succ attempts ihAttempts =>
              intro total current
              simp only [scheduledBalancedAccuracyRetryCollectAux]
              let block := cappedScheduledAccuracyProperBlock q sigma2
                (proposalCap + 1) properStride current
              let tail : Option (ℝ × AmbientSpace q.n) →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun value =>
                match value with
                | none => .pure none
                | some (_, mixed) =>
                    (scheduledBalancedAccuracyGaussianRejectionAttempt
                      q sigma2 mixed).bind fun result =>
                        if result.1 then
                          scheduledBalancedAccuracyRetryCollectAux q sigma2
                            weight proposalCap properStride retryLimit retryLimit
                            future (total + weight result.2) mixed
                        else
                          scheduledBalancedAccuracyRetryCollectAux q sigma2
                            weight proposalCap properStride retryLimit attempts
                            (future + 1) total mixed
              have hblock : block.QueryBound (proposalCap + 1) := by
                exact cappedScheduledAccuracyProperBlock_queryBound
                  q sigma2 (proposalCap + 1) properStride current
              have htail : ∀ value, (tail value).QueryBound
                  (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                    (future + 1)) := by
                intro value
                cases value with
                | none => exact .pure _ _
                | some value =>
                    rcases value with ⟨ignored, mixed⟩
                    dsimp only [tail]
                    apply MembershipOracleProgram.QueryBound.bind
                      (scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
                        q sigma2 mixed)
                    intro result
                    by_cases hresult : result.1 = true
                    · simp only [hresult, if_true]
                      have hrec := ihSamples future (by omega) retryLimit
                        (total + weight result.2) mixed
                      rw [balancedRetryQueryBudget_full] at hrec
                      exact hrec.mono <| Nat.mul_le_mul_right
                        (proposalCap + 2) (Nat.le_add_right _ attempts)
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hresult
                      simp only [hfalse, Bool.false_eq_true, if_false]
                      exact ihAttempts total mixed
              have hbound := hblock.bind htail
              change (block.bind tail).QueryBound
                (balancedRetryQueryBudget proposalCap retryLimit
                  (attempts + 1) (future + 1))
              rw [← balancedRetryQueryBudget_step]
              have heq : proposalCap + 1 +
                    (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1)) =
                  proposalCap + 2 +
                    balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1) := by omega
              rw [← heq]
              exact hbound

theorem scheduledBalancedAccuracyRetryCollect_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
      properStride retryLimit samples current).QueryBound
        (samples * retryLimit * (proposalCap + 2)) := by
  unfold scheduledBalancedAccuracyRetryCollect
  have h := scheduledBalancedAccuracyRetryCollectAux_queryBound q sigma2 weight
    proposalCap properStride retryLimit retryLimit samples 0 current
  rw [balancedRetryQueryBudget_full] at h
  exact h.bind fun result => .pure _ 0

#print axioms scheduledAccuracyMetropolisMarkedBallStep_queryBound
#print axioms scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
#print axioms scheduledBalancedAccuracyRetryCollect_queryBound

end ArlibCommunity.Algorithms.CV18
