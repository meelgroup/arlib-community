/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProgramPrefix

/-!
# Prefix invisibility through the balanced retry stack

This strengthens local-cap equality to compositional `QueryPrefixEq`, so the
fact can be transported through balanced retries and cooling binds.
-/

namespace ArlibCommunity.Algorithms.CV18

open MembershipOracleProgram

theorem cappedAccuracyProperCollectWeightsAux_queryPrefixEq_of_lt
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ budget rawCap₁ rawCap₂ remainingProper samples total current,
      budget < rawCap₁ → budget < rawCap₂ →
      QueryPrefixEq budget
        (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap₁ remainingProper samples total current)
        (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap₂ remainingProper samples total current) := by
  intro budget
  induction budget with
  | zero =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux,
            cappedAccuracyProperCollectWeightsAux]
          exact .pure 0 _
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind]
              exact .queryZero _ _ _ _
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyMetropolisMarkedBallStep,
                accuracyMetropolisMarkedProposalProgram,
                MembershipOracleProgram.bind]
              apply QueryPrefixEq.randomPoint
              intro proposal
              exact .queryZero _ _ _ _
  | succ budget ih =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      have hcap₁' : budget < rawCap₁ := by omega
      have hcap₂' : budget < rawCap₂ := by omega
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux,
            cappedAccuracyProperCollectWeightsAux]
          exact .pure (budget + 1) _
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind]
              apply QueryPrefixEq.querySucc
              intro inside
              exact ih rawCap₁ rawCap₂ properStride samples _ current
                hcap₁' hcap₂'
          | succ remainingProper =>
              cases remainingProper with
              | zero =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind]
                  apply QueryPrefixEq.randomPoint
                  intro proposal
                  apply QueryPrefixEq.querySucc
                  intro inside
                  apply QueryPrefixEq.randomReal
                  intro coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption
              | succ nextRemaining =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind]
                  apply QueryPrefixEq.randomPoint
                  intro proposal
                  apply QueryPrefixEq.querySucc
                  intro inside
                  apply QueryPrefixEq.randomReal
                  intro coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption

theorem cappedAccuracyProperCollectWeights_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride samples : ℕ)
    (current : AmbientSpace q.n) {budget proposalCap₁ proposalCap₂ : ℕ}
    (hcap₁ : budget ≤ proposalCap₁) (hcap₂ : budget ≤ proposalCap₂) :
    QueryPrefixEq budget
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap₁ + 1) properStride samples current)
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap₂ + 1) properStride samples current) := by
  unfold cappedAccuracyProperCollectWeights
  apply cappedAccuracyProperCollectWeightsAux_queryPrefixEq_of_lt
  · omega
  · omega

/-- Changing the artificial local proposal cap above the outer budget is
invisible through all balanced retries. -/
theorem balancedAccuracyRetryCollectAux_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride retryLimit : ℕ) :
    ∀ samples attempts total current budget proposalCap₁ proposalCap₂,
      budget ≤ proposalCap₁ → budget ≤ proposalCap₂ →
      QueryPrefixEq budget
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap₁
          properStride retryLimit attempts samples total current)
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap₂
          properStride retryLimit attempts samples total current) := by
  intro samples
  induction samples using Nat.strong_induction_on with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro attempts total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
          rw [balancedAccuracyRetryCollectAux,
            balancedAccuracyRetryCollectAux]
          exact .pure budget _
      | succ future =>
          intro attempts
          induction attempts with
          | zero =>
              intro total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
              rw [balancedAccuracyRetryCollectAux,
                balancedAccuracyRetryCollectAux]
              exact .pure budget _
          | succ attempts ihAttempts =>
              intro total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
              simp only [balancedAccuracyRetryCollectAux]
              have hblock := cappedAccuracyProperCollectWeights_queryPrefixEq_of_le
                q sigma2 (fun _ => 0) properStride 1 current hcap₁ hcap₂
              apply hblock.bind
              intro block
              cases block with
              | none => exact .pure budget _
              | some value =>
                  rcases value with ⟨ignored, mixed⟩
                  apply (QueryPrefixEq.refl budget
                    (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed)).bind
                  intro result
                  by_cases hresult : result.1 = true
                  · simp only [hresult, if_true]
                    exact ihSamples future (by omega) retryLimit
                      (total + weight result.2) mixed budget proposalCap₁
                        proposalCap₂ hcap₁ hcap₂
                  · have hfalse : result.1 = false :=
                      Bool.eq_false_of_not_eq_true hresult
                    simp only [hfalse, Bool.false_eq_true, if_false]
                    exact ihAttempts total mixed budget proposalCap₁ proposalCap₂
                      hcap₁ hcap₂

theorem balancedAccuracyRetryCollect_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) {budget proposalCap₁ proposalCap₂ : ℕ}
    (hcap₁ : budget ≤ proposalCap₁) (hcap₂ : budget ≤ proposalCap₂) :
    QueryPrefixEq budget
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap₁
        properStride retryLimit samples current)
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap₂
        properStride retryLimit samples current) := by
  unfold balancedAccuracyRetryCollect
  apply (balancedAccuracyRetryCollectAux_queryPrefixEq_of_le
    q sigma2 weight properStride retryLimit samples retryLimit 0 current budget
      proposalCap₁ proposalCap₂ hcap₁ hcap₂).bind
  intro result
  exact .pure budget _

theorem balancedCoolingRatioEstimate_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (sigma2 tau2 : ℝ) (current : AmbientSpace q.n)
    (budget : ℕ)
    (hcap₁ : budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2) :
    QueryPrefixEq budget
      (balancedCoolingRatioEstimate parameters₁ q sigma2 tau2 current)
      (balancedCoolingRatioEstimate parameters₂ q sigma2 tau2 current) := by
  unfold balancedCoolingRatioEstimate
  rw [hstride, hretry]
  apply (balancedAccuracyRetryCollect_queryPrefixEq_of_le q sigma2
    (gaussianRatioWeight sigma2 tau2) (parameters₂.properStride q sigma2)
      (parameters₂.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current) hcap₁ hcap₂).bind
  intro result
  exact .pure budget _

theorem balancedCoolingUniformEstimateWithState_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n)
    (budget : ℕ)
    (hcap₁ : budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2) :
    QueryPrefixEq budget
      (balancedCoolingUniformEstimateWithState parameters₁ q sigma2 current)
      (balancedCoolingUniformEstimateWithState parameters₂ q sigma2 current) := by
  unfold balancedCoolingUniformEstimateWithState
  rw [hstride, hretry]
  apply (balancedAccuracyRetryCollect_queryPrefixEq_of_le q sigma2
    (uniformRatioWeight sigma2) (parameters₂.properStride q sigma2)
      (parameters₂.retryLimit q sigma2) (figureOneSampleCount q)
      (accuracyScaleFactor q • current) hcap₁ hcap₂).bind
  intro result
  exact .pure budget _

theorem balancedCoolingUniformRatioEstimate_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n)
    (budget : ℕ)
    (hcap₁ : budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2) :
    QueryPrefixEq budget
      (balancedCoolingUniformRatioEstimate parameters₁ q sigma2 current)
      (balancedCoolingUniformRatioEstimate parameters₂ q sigma2 current) := by
  unfold balancedCoolingUniformRatioEstimate
  apply (balancedCoolingUniformEstimateWithState_queryPrefixEq
    parameters₁ parameters₂ q sigma2 current budget hcap₁ hcap₂
      hstride hretry).bind
  intro result
  exact .pure budget _

/-- Prefix invisibility transported through every Gaussian cooling phase. -/
theorem balancedCoolingProduct_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (budget : ℕ)
    (hcap₁ : ∀ sigma2, budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : ∀ sigma2, budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : ∀ sigma2, parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : ∀ sigma2, parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2) :
    ∀ variances point,
      QueryPrefixEq budget
        (coolingProduct (balancedCoolingPrimitives parameters₁) q variances point)
        (coolingProduct (balancedCoolingPrimitives parameters₂) q variances point) := by
  intro variances
  induction variances with
  | nil =>
      intro point
      simpa only [coolingProduct] using
        (QueryPrefixEq.pure budget (some ((1 : ℝ), point)))
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro point
          simpa only [coolingProduct] using
            (QueryPrefixEq.pure budget (some ((1 : ℝ), point)))
      | cons tau2 rest =>
          intro point
          simp only [coolingProduct, balancedCoolingPrimitives]
          apply (balancedCoolingRatioEstimate_queryPrefixEq parameters₁ parameters₂
            q sigma2 tau2 point budget (hcap₁ sigma2) (hcap₂ sigma2)
              (hstride sigma2) (hretry sigma2)).bind
          intro phase
          cases phase with
          | none => exact .pure budget _
          | some value =>
              rcases value with ⟨ratio, nextPoint⟩
              apply (ih nextPoint).bind
              intro result
              exact .pure budget _

theorem balancedFigureOnePointContinuation_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (budget : ℕ)
    (hcap₁ : ∀ sigma2, budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : ∀ sigma2, budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : ∀ sigma2, parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : ∀ sigma2, parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2)
    (point : AmbientSpace q.n) :
    QueryPrefixEq budget
      (balancedFigureOnePointContinuation parameters₁ q point)
      (balancedFigureOnePointContinuation parameters₂ q point) := by
  unfold balancedFigureOnePointContinuation
  apply (balancedCoolingProduct_queryPrefixEq parameters₁ parameters₂ q budget
    hcap₁ hcap₂ hstride hretry
      (explicitVolumeCoolingSchedule q).variances point).bind
  intro product
  cases product with
  | none => exact .pure budget _
  | some value =>
      rcases value with ⟨gaussianProduct, lastPoint⟩
      change QueryPrefixEq budget
        ((balancedCoolingUniformRatioEstimate parameters₁ q
          (terminalVariance q) lastPoint).bind _)
        ((balancedCoolingUniformRatioEstimate parameters₂ q
          (terminalVariance q) lastPoint).bind _)
      apply (balancedCoolingUniformRatioEstimate_queryPrefixEq
        parameters₁ parameters₂ q (terminalVariance q) lastPoint budget
          (hcap₁ _) (hcap₂ _) (hstride _) (hretry _)).bind
      intro result
      exact .pure budget _

/-- Full base-program prefix invisibility, including initialization and the
terminal uniform-ratio phase. -/
theorem balancedFigureOneBaseVolumeCooling_queryPrefixEq
    (parameters₁ parameters₂ : BalancedCoolingParameters)
    (q : VolumeParams) (budget : ℕ)
    (hcap₁ : ∀ sigma2, budget ≤ parameters₁.proposalCap q sigma2)
    (hcap₂ : ∀ sigma2, budget ≤ parameters₂.proposalCap q sigma2)
    (hstride : ∀ sigma2, parameters₁.properStride q sigma2 =
      parameters₂.properStride q sigma2)
    (hretry : ∀ sigma2, parameters₁.retryLimit q sigma2 =
      parameters₂.retryLimit q sigma2) :
    QueryPrefixEq budget
      (baseVolumeCooling (balancedCoolingPrimitives parameters₁)
        explicitVolumeCoolingSchedule q)
      (baseVolumeCooling (balancedCoolingPrimitives parameters₂)
        explicitVolumeCoolingSchedule q) := by
  unfold baseVolumeCooling balancedCoolingPrimitives
  apply (QueryPrefixEq.refl budget (figureOneInitialSample q)).bind
  intro initialPoint
  cases initialPoint with
  | none => exact .pure budget _
  | some point =>
      exact balancedFigureOnePointContinuation_queryPrefixEq
        parameters₁ parameters₂ q budget hcap₁ hcap₂ hstride hretry point

/-- Increase only the artificial local raw-proposal caps. -/
noncomputable def BalancedCoolingParameters.addProposalCap
    (parameters : BalancedCoolingParameters) (extra : ℕ) :
    BalancedCoolingParameters where
  proposalCap := fun q sigma2 => parameters.proposalCap q sigma2 + extra
  properStride := parameters.properStride
  retryLimit := parameters.retryLimit

/-- The complete globally capped Figure-One base syntax is unchanged if all
local proposal caps are increased arbitrarily. -/
theorem figureOneGlobalBalancedBaseProgram_withQueryCap_addProposalCap
    (q : VolumeParams) (extra : ℕ) :
    (figureOneGlobalBalancedBaseProgram q).withQueryCap
        (figureOneGlobalQueryBudget q) =
      (baseVolumeCooling
        (balancedCoolingPrimitives
          (figureOneGlobalBalancedParameters.addProposalCap extra))
        explicitVolumeCoolingSchedule q).withQueryCap
          (figureOneGlobalQueryBudget q) := by
  apply QueryPrefixEq.withQueryCap_eq
  apply balancedFigureOneBaseVolumeCooling_queryPrefixEq
  · intro sigma2
    rfl
  · intro sigma2
    unfold BalancedCoolingParameters.addProposalCap
    dsimp only
    change figureOneGlobalQueryBudget q ≤
      figureOneGlobalQueryBudget q + extra
    omega
  · intro sigma2
    rfl
  · intro sigma2
    rfl

end ArlibCommunity.Algorithms.CV18
