/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryWarmCost

/-! # Expected cost of a fixed-length killed transition chain -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- Expected accumulated trial cost along at most `trials` transitions of a
possibly killed (subprobability) transition law. -/
noncomputable def finiteKilledChainExpectedCost
    {S : Type*} [MeasurableSpace S]
    (next : S → Measure S) (trialCost : S → ENNReal) : ℕ → S → ENNReal
  | 0, _ => 0
  | trials + 1, current => trialCost current +
      ∫⁻ nextState, finiteKilledChainExpectedCost next trialCost trials nextState
        ∂next current

theorem measurable_finiteKilledChainExpectedCost
    {S : Type*} [MeasurableSpace S]
    {next : S → Measure S} (hnext : Measurable next)
    {trialCost : S → ENNReal} (htrial : Measurable trialCost) :
    ∀ trials, Measurable (finiteKilledChainExpectedCost next trialCost trials) := by
  intro trials
  induction trials with
  | zero => exact measurable_const
  | succ trials ih =>
      simp only [finiteKilledChainExpectedCost]
      exact htrial.add ((Measure.measurable_lintegral ih).comp hnext)

/-- A fixed-length shadow execution costs linearly when every killed endpoint
law preserves the same warmness invariant.  This is the expectation argument
behind replacing the nested retry control flow by at most
`samples * retryLimit` live trials. -/
theorem lintegral_finiteKilledChainExpectedCost_le
    {S : Type*} [MeasurableSpace S]
    {next : S → Measure S} (hnext : Measurable next)
    {trialCost : S → ENNReal} (htrial : Measurable trialCost)
    {pi : Measure S} {M C : ENNReal}
    (hcost : ∀ mu : Measure S, _root_.Arlib.IsWarm M mu pi →
      ∫⁻ current, trialCost current ∂mu ≤ C)
    (hwarmNext : ∀ mu : Measure S, _root_.Arlib.IsWarm M mu pi →
      _root_.Arlib.IsWarm M (mu.bind next) pi) :
    ∀ (trials : ℕ) (mu : Measure S), _root_.Arlib.IsWarm M mu pi →
      ∫⁻ current, finiteKilledChainExpectedCost next trialCost trials current ∂mu ≤
        (trials : ENNReal) * C := by
  intro trials
  induction trials with
  | zero =>
      intro mu hwarm
      simp [finiteKilledChainExpectedCost]
  | succ trials ih =>
      intro mu hwarm
      have hmeas := measurable_finiteKilledChainExpectedCost hnext htrial trials
      calc
        (∫⁻ current,
            finiteKilledChainExpectedCost next trialCost (trials + 1) current
            ∂mu) =
            (∫⁻ current, trialCost current ∂mu) +
              ∫⁻ current,
                (∫⁻ nextState,
                  finiteKilledChainExpectedCost next trialCost trials nextState
                    ∂next current) ∂mu := by
              simp only [finiteKilledChainExpectedCost]
              rw [lintegral_add_left htrial]
        _ = (∫⁻ current, trialCost current ∂mu) +
              ∫⁻ nextState,
                finiteKilledChainExpectedCost next trialCost trials nextState
                  ∂(mu.bind next) := by
              congr 1
              rw [Measure.lintegral_bind hnext.aemeasurable hmeas.aemeasurable]
        _ ≤ C + (trials : ENNReal) * C :=
          add_le_add (hcost mu hwarm) (ih (mu.bind next) (hwarmNext mu hwarm))
        _ = (trials + 1 : ℕ) * C := by
          push_cast
          ring

/-! ## Scheduled-block specialization -/

/-- Successful endpoint transition of one capped scheduled proper block. -/
noncomputable def scheduledSuccessfulBlockEndpointLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    Measure (AmbientSpace q.n) :=
  successfulEndpointLaw
    (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
      properStride current)

theorem scheduledSuccessfulBlockEndpointLaw_measurable
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    Measurable (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
      properStride) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  unfold scheduledSuccessfulBlockEndpointLaw successfulEndpointLaw
  exact measurable_measure_bind_param_variable B.measurable
    (fun current => IsMarkovKernel.isProbabilityMeasure current)
    (measurable_successfulEndpointKernel.comp measurable_snd)

theorem bind_scheduledSuccessfulBlockEndpointLaw_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    _root_.Arlib.IsWarm M
      (mu.bind (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
        properStride))
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2) := by
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  have h :=
    successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_isWarm
      q I sigma2 proposalCap properStride hwarm
        (scheduledPhaseLazySpeedyPow_invariant q I sigma2 properStride)
  change _root_.Arlib.IsWarm M
    (mu.bind fun current => (B current).bind successfulEndpointKernel)
    (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  have heq : (mu.bind B).bind successfulEndpointKernel =
      mu.bind (fun current => (B current).bind successfulEndpointKernel) :=
    Measure.bind_bind B.aemeasurable
      measurable_successfulEndpointKernel.aemeasurable
  rw [← heq]
  exact h

/-- A padded trial charges the proper block plus one rejection query even if
the block is killed.  This dominates the executable retry step and makes the
fixed-shadow recurrence exact. -/
noncomputable def scheduledPaddedTrialCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n) : ENNReal :=
  countedQueryCost
    ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
      properStride current).run oracle.query) + 1

theorem measurable_scheduledPaddedTrialCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    Measurable (scheduledPaddedTrialCost q I oracle sigma2 proposalCap
      properStride) := by
  unfold scheduledPaddedTrialCost
  exact ((Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
    (cappedScheduledAccuracyProperBlock_countedMeasurable q I oracle hsigma2
      (proposalCap + 1) properStride).1).add measurable_const

theorem lintegral_scheduledPaddedTrialCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride : ℕ) :
    ∫⁻ current, scheduledPaddedTrialCost q I oracle sigma2 proposalCap
        properStride current ∂mu ≤
      (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by
  unfold scheduledPaddedTrialCost
  have hmeasCost : Measurable fun current => countedQueryCost
      ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      (cappedScheduledAccuracyProperBlock_countedMeasurable q I oracle hsigma2
        (proposalCap + 1) properStride).1
  rw [lintegral_add_left hmeasCost]
  simp only [lintegral_const, one_mul]
  calc
    _ ≤ ((properStride : ENNReal) * (M * 2) + mu Set.univ) +
        mu Set.univ := by
      gcongr
      exact lintegral_cappedScheduledAccuracyProperBlock_countedQueryCost_le_of_isWarm_submeasure
        q I oracle hsigma2 hwarm (proposalCap + 1) properStride
    _ = (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by ring

/-- The fixed-live-trial shadow for a warm scheduled phase has linear cost,
with no dependence on the local proposal cap. -/
theorem lintegral_scheduledFixedLiveTrialShadowCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride trials : ℕ) :
    let next := scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
      properStride
    let trialCost := fun current => countedQueryCost
      ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
        current).run oracle.query)
    ∫⁻ current, finiteKilledChainExpectedCost next trialCost trials current ∂mu ≤
      (trials : ENNReal) *
        ((properStride : ENNReal) * (M * 2) + 2 * M) := by
  dsimp only
  let pi := ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 := ellGaussianMeasure_univ_ne_zero
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledPhaseBody_convex q I sigma2)
    (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
    (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := ellGaussianMeasure_ne_top_cv18
    (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  let next := scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
    properStride
  let trialCost : AmbientSpace q.n → ENNReal := fun current => countedQueryCost
    ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
      current).run oracle.query)
  have hnext : Measurable next :=
    scheduledSuccessfulBlockEndpointLaw_measurable q I hsigma2 proposalCap
      properStride
  have htrial : Measurable trialCost :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      (scheduledBalancedAccuracyLiveTrial_run_measurable q I oracle hsigma2
        proposalCap properStride)
  apply lintegral_finiteKilledChainExpectedCost_le hnext htrial
  · intro nu hwarmNu
    have hmass : nu Set.univ ≤ M := by
      calc
        nu Set.univ ≤ M * pi Set.univ :=
          hwarmNu Set.univ MeasurableSet.univ
        _ = M := by rw [measure_univ, mul_one]
    exact
      (lintegral_scheduledBalancedAccuracyLiveTrial_countedQueryCost_le_of_isWarm
        q I oracle hsigma2 hwarmNu proposalCap properStride).trans
        (add_le_add le_rfl (by gcongr))
  · intro nu hwarmNu
    exact bind_scheduledSuccessfulBlockEndpointLaw_isWarm q I sigma2
      proposalCap properStride hwarmNu
  · exact hwarm

/-- Padded fixed-trial version used directly by the executable retry
domination theorem. -/
theorem lintegral_scheduledFixedPaddedTrialShadowCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride trials : ℕ) :
    ∫⁻ current, finiteKilledChainExpectedCost
        (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap properStride)
        (scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride)
        trials current ∂mu ≤
      (trials : ENNReal) *
        ((properStride : ENNReal) * (M * 2) + 2 * M) := by
  let pi := ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 := ellGaussianMeasure_univ_ne_zero
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledPhaseBody_convex q I sigma2)
    (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
    (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := ellGaussianMeasure_ne_top_cv18
    (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  apply lintegral_finiteKilledChainExpectedCost_le
    (scheduledSuccessfulBlockEndpointLaw_measurable q I hsigma2 proposalCap
      properStride)
    (measurable_scheduledPaddedTrialCost q I oracle hsigma2 proposalCap
      properStride)
  · intro nu hwarmNu
    have hmass : nu Set.univ ≤ M := by
      calc
        nu Set.univ ≤ M * pi Set.univ :=
          hwarmNu Set.univ MeasurableSet.univ
        _ = M := by rw [measure_univ, mul_one]
    exact (lintegral_scheduledPaddedTrialCost_le_of_isWarm q I oracle hsigma2
      hwarmNu proposalCap properStride).trans (add_le_add le_rfl (by gcongr))
  · intro nu hwarmNu
    exact bind_scheduledSuccessfulBlockEndpointLaw_isWarm q I sigma2
      proposalCap properStride hwarmNu
  · exact hwarm

end ArlibCommunity.Algorithms.CV18
