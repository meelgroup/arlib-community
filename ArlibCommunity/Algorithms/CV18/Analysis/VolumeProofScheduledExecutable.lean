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

/-- Marked Metropolis proposal using the schedule-targeted radial test. -/
noncomputable def scheduledAccuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2 then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

noncomputable def scheduledAccuracyMetropolisMarkedBallStep
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current
      (figureOneScheduledProposalRadius q sigma2)) inferInstance fun proposal =>
      scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal

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

/-- The dummy endpoint observation retained by the proper-proposal clock. -/
noncomputable def scheduledAccuracyZeroObservation
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n ℝ :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  .query target fun _ => .pure 0

theorem scheduledAccuracyZeroObservation_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

/-- Capped proper-step block at the new body and proposal radius. -/
noncomputable def cappedScheduledAccuracyProperBlockAux
    (q : VolumeParams) (sigma2 : ℝ) (properStride : ℕ) :
    ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | 0, _, _ => .pure none
  | rawCap + 1, 0, current =>
      (scheduledAccuracyZeroObservation q sigma2 current).bind fun observed =>
        .pure (some (observed, current))
  | rawCap + 1, remainingProper + 1, current =>
      (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).bind
        fun result =>
          if result.1 then
            match remainingProper with
            | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                rawCap 0 result.2
            | nextRemaining + 1 =>
                cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap (nextRemaining + 1) result.2
          else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
            rawCap (remainingProper + 1) result.2
termination_by rawCap remainingProper current => rawCap

noncomputable def cappedScheduledAccuracyProperBlock
    (q : VolumeParams) (sigma2 : ℝ) (rawCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
    rawCap properStride current

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

/-- Schedule-targeted balanced KLS rejection. -/
noncomputable def scheduledBalancedAccuracyGaussianRejectionAttempt
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else .pure (false, target)

theorem scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).QueryBound
      1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

/-- Finite balanced retries whose proper blocks and rejection tests both use
the schedule-targeted geometry. -/
noncomputable def scheduledBalancedAccuracyRetryCollectAux
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, current => .pure (some (total, current))
  | 0, _ + 1, _, _ => .pure none
  | attempts + 1, samples + 1, total, current =>
      (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).bind fun block =>
        match block with
        | none => .pure none
        | some (_, mixed) =>
            (scheduledBalancedAccuracyGaussianRejectionAttempt
              q sigma2 mixed).bind fun result =>
                if result.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit retryLimit samples
                    (total + weight result.2) mixed
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit attempts
                    (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

noncomputable def scheduledBalancedAccuracyRetryCollect
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
    properStride retryLimit retryLimit samples 0 current).bind fun result =>
      .pure (balancedAccuracyRetryOutput q result)

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
