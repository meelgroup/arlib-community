/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledChainCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCostComposition

/-! # Domination of finite scheduled retries by a fixed-trial shadow -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- Number of live trials still possible in the lexicographic retry state. -/
def balancedRemainingTrials (retryLimit attempts samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | future + 1 => future * retryLimit + attempts

@[simp] theorem balancedRemainingTrials_zero
    (retryLimit attempts : ℕ) :
    balancedRemainingTrials retryLimit attempts 0 = 0 := rfl

@[simp] theorem balancedRemainingTrials_succ
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      future * retryLimit + attempts := rfl

theorem balancedRemainingTrials_accept
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit retryLimit future ≤
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  cases future with
  | zero => simp [balancedRemainingTrials]
  | succ future =>
      simp only [balancedRemainingTrials, Nat.succ_mul]
      omega

theorem balancedRemainingTrials_reject
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  simp [balancedRemainingTrials]

/-- Monotonicity of the numerical fixed-chain shadow in its horizon. -/
theorem finiteKilledChainExpectedCost_mono
    {S : Type*} [MeasurableSpace S]
    (next : S → Measure S) (trialCost : S → ENNReal) :
    Monotone fun trials => finiteKilledChainExpectedCost next trialCost trials := by
  intro first second hle
  intro current
  induction second generalizing first current with
  | zero =>
      have : first = 0 := Nat.eq_zero_of_le_zero hle
      subst first
      exact le_rfl
  | succ second ih =>
      cases first with
      | zero => exact bot_le
      | succ first =>
          simp only [finiteKilledChainExpectedCost]
          exact add_le_add le_rfl (lintegral_mono fun state =>
            ih (Nat.le_of_succ_le_succ hle) state)

/-- Integrating over successful endpoints is the same as integrating the
endpoint payload on successful optional outputs and zero on failure. -/
theorem lintegral_successfulEndpointLaw
    {S : Type*} [MeasurableSpace S]
    (law : Measure (Option (ℝ × S)))
    {f : S → ENNReal} (hf : Measurable f) :
    ∫⁻ state, f state ∂successfulEndpointLaw law =
      ∫⁻ output, match output with
        | none => 0
        | some value => f value.2 ∂law := by
  unfold successfulEndpointLaw
  rw [Measure.lintegral_bind measurable_successfulEndpointKernel.aemeasurable
    hf.aemeasurable]
  apply lintegral_congr
  intro output
  cases output with
  | none => simp [successfulEndpointKernel]
  | some value =>
      simp only [successfulEndpointKernel]
      rw [lintegral_dirac' _ hf]

/-- One executable scheduled retry step is bounded by its padded block cost
plus the successful-endpoint average of any uniform continuation envelope. -/
theorem scheduledRetryStep_countedQueryCost_le_padded
    {Result : Type} [MeasurableSpace Result]
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n)
    (failure : Result)
    (next : AmbientSpace q.n × (Bool × AmbientSpace q.n) →
      MembershipOracleProgram q.n Result)
    (hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query)
    (hnextRun : Measurable fun z => (next z).run oracle.query)
    (envelope : AmbientSpace q.n → ENNReal)
    (henvelope : Measurable envelope)
    (hbound : ∀ mixed result,
      countedQueryCost ((next (mixed, result)).run oracle.query) ≤
        envelope mixed) :
    countedQueryCost
        (((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
          properStride current).bind fun block =>
            match block with
            | none => .pure failure
            | some (_, mixed) =>
                (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                  mixed).bind fun result => next (mixed, result)).run
          oracle.query) ≤
      scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride
        current +
        ∫⁻ state, envelope state ∂scheduledSuccessfulBlockEndpointLaw q I
          sigma2 proposalCap properStride current := by
  let block := cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
    properStride current
  let tail : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n Result
    | none => .pure failure
    | some (_, mixed) =>
        (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
          fun result => next (mixed, result)
  have hblock := (cappedScheduledAccuracyProperBlock_countedMeasurable
    q I oracle hsigma2 (proposalCap + 1) properStride).2 current
  have htail : ∀ value, (tail value).CountedStronglyMeasurable oracle.query := by
    intro value
    cases value with
    | none => trivial
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        exact (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
          q I oracle sigma2 mixed).bind (fun result => hnext (mixed, result))
            (hnextRun.comp (measurable_const.prodMk measurable_id))
  have htailRun : Measurable fun value => (tail value).run oracle.query := by
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (tail (some value)).run oracle.query := by
      let rejection (value : ℝ × AmbientSpace q.n) :=
        scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 value.2
      let continuation (z : (ℝ × AmbientSpace q.n) ×
          (Bool × AmbientSpace q.n)) := next (z.1.2, z.2)
      apply MembershipOracleProgram.measurable_run_bind_param oracle.query
        rejection continuation
      · apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
          oracle.query rejection 1
        · intro value
          exact scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
            q sigma2 value.2
        · intro value
          exact scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
            q I oracle sigma2 value.2
        · rw [show (fun value => (rejection value).runEstimate oracle.query) =
              fun value => scheduledBalancedAccuracyGaussianRejectionKernel
                q I sigma2 value.2 by
              funext value
              exact runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
                q I oracle hsigma2 value.2]
          exact (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2).measurable.comp
            measurable_snd
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
          q I oracle sigma2 value.2
      · exact hnextRun.comp <|
          (measurable_snd.comp measurable_fst).prodMk measurable_snd
      · intro z
        exact hnext (z.1.2, z.2)
    convert Measurable.optionElim
      (Measure.dirac (failure, 0)) hsome using 1
    funext value
    cases value <;> rfl
  rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query block tail
    hblock htail htailRun]
  unfold scheduledPaddedTrialCost
  let law := block.runEstimate oracle.query
  have hlaw : law = scheduledBalancedAccuracyRetryBlockKernel q I sigma2
      proposalCap properStride current := by
    exact cappedScheduledAccuracyProperBlock_semantics q I oracle hsigma2
      proposalCap properStride current
  let payload : Option (ℝ × AmbientSpace q.n) → ENNReal
    | none => 0
    | some value => envelope value.2
  have hpayload : Measurable payload := by
    convert Measurable.optionElim 0 (henvelope.comp measurable_snd) using 1
    funext value
    cases value <;> rfl
  have htailCost : ∀ value,
      countedQueryCost ((tail value).run oracle.query) ≤ 1 + payload value := by
    intro value
    cases value with
    | none =>
        dsimp only [tail, payload]
        calc
          countedQueryCost
              ((MembershipOracleProgram.pure (n := q.n) failure).run
                oracle.query) ≤ 0 :=
            by simpa only [countedQueryCost, Nat.cast_zero] using
              (MembershipOracleProgram.QueryBound.pure failure 0).lintegral_queryCount_le
                (oracle := oracle.query) (by trivial)
          _ ≤ 1 + 0 := bot_le
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        dsimp only [tail, payload]
        rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
          (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed)
          (fun result => next (mixed, result))
          (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
            q I oracle sigma2 mixed)
          (fun result => hnext (mixed, result))
          (hnextRun.comp (measurable_const.prodMk measurable_id))]
        have hrejectionCost : countedQueryCost
            ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
              mixed).run oracle.query) ≤ 1 :=
          by simpa only [countedQueryCost, Nat.cast_one] using
            (scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
              q sigma2 mixed).lintegral_queryCount_le
                (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
                  q I oracle sigma2 mixed)
        apply add_le_add hrejectionCost
        let _ : IsProbabilityMeasure
            ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
              mixed).runEstimate oracle.query) :=
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
            (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
              q I oracle sigma2 mixed).estimateMeasurable
        calc
          (∫⁻ result, countedQueryCost ((next (mixed, result)).run oracle.query)
              ∂(scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                mixed).runEstimate oracle.query) ≤
              ∫⁻ _result, envelope mixed
                ∂(scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                  mixed).runEstimate oracle.query := lintegral_mono (hbound mixed)
          _ = envelope mixed := by simp
  have htailIntegral :
      (∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law) ≤
        1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by
    calc
      (∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law) ≤
        ∫⁻ value, (1 + payload value) ∂law := lintegral_mono htailCost
      _ = 1 + ∫⁻ value, payload value ∂law := by
        rw [lintegral_add_left measurable_const]
        let _ : IsProbabilityMeasure law :=
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query block
            hblock.stronglyMeasurable.estimateMeasurable
        simp
      _ = 1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by
        rw [hlaw]
        congr 1
        change
          (∫⁻ output, match output with
            | none => 0
            | some value => envelope value.2
            ∂scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
              properStride current) =
          ∫⁻ state, envelope state
            ∂successfulEndpointLaw
              (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
                properStride current)
        unfold successfulEndpointLaw
        rw [Measure.lintegral_bind measurable_successfulEndpointKernel.aemeasurable
          henvelope.aemeasurable]
        apply lintegral_congr
        intro output
        cases output with
        | none => simp [successfulEndpointKernel]
        | some value =>
            simp only [successfulEndpointKernel]
            rw [lintegral_dirac' _ henvelope]
  calc
    countedQueryCost (block.run oracle.query) +
        ∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law ≤
      countedQueryCost (block.run oracle.query) +
        (1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current) := add_le_add le_rfl htailIntegral
    _ = (countedQueryCost (block.run oracle.query) + 1) +
        ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by ring

/-- The actual nested finite-retry collector is pointwise dominated by the
fixed-trial killed-chain shadow with the exact number of live trials remaining
in its lexicographic `(samples, attempts)` state. -/
theorem scheduledBalancedAccuracyRetryCollectAux_countedQueryCost_le_shadow
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples total current,
      countedQueryCost
          ((scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
            properStride retryLimit attempts samples total current).run
              oracle.query) ≤
        finiteKilledChainExpectedCost
          (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap properStride)
          (scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride)
          (balancedRemainingTrials retryLimit attempts samples) current := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro total current
          simp [scheduledBalancedAccuracyRetryCollectAux,
            balancedRemainingTrials, finiteKilledChainExpectedCost,
            MembershipOracleProgram.countedQueryCost_pure]
      | succ future =>
          induction attempts with
          | zero =>
              intro total current
              rw [scheduledBalancedAccuracyRetryCollectAux]
              simp only [MembershipOracleProgram.countedQueryCost_pure]
              exact bot_le
          | succ attempts ihAttempts =>
              intro total current
              let nextLaw := scheduledSuccessfulBlockEndpointLaw q I sigma2
                proposalCap properStride
              let trialCost := scheduledPaddedTrialCost q I oracle sigma2
                proposalCap properStride
              let remaining := balancedRemainingTrials retryLimit (attempts + 1)
                (future + 1)
              let envelope := finiteKilledChainExpectedCost nextLaw trialCost
                (remaining - 1)
              let next (z : AmbientSpace q.n ×
                  (Bool × AmbientSpace q.n)) :=
                if z.2.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit retryLimit future
                      (total + weight z.2.2) z.1
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit attempts (future + 1)
                      total z.1
              have hnext : ∀ z, (next z).CountedStronglyMeasurable
                  oracle.query := by
                rintro ⟨mixed, mark, target⟩
                cases mark with
                | false =>
                    exact (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable
                      q I oracle hsigma2 hweight proposalCap properStride retryLimit
                        attempts (future + 1)).2 total mixed
                | true =>
                    exact (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable
                      q I oracle hsigma2 hweight proposalCap properStride retryLimit
                        retryLimit future).2 (total + weight target) mixed
              have hnextRun : Measurable fun z => (next z).run oracle.query := by
                dsimp only [next]
                rw [show (fun z : AmbientSpace q.n ×
                      (Bool × AmbientSpace q.n) =>
                      (if z.2.1 = true then
                        scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                          proposalCap properStride retryLimit retryLimit future
                            (total + weight z.2.2) z.1
                      else
                        scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                          proposalCap properStride retryLimit attempts (future + 1)
                            total z.1).run oracle.query) =
                    fun z => if z.2.1 = true then
                      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit retryLimit future
                          (total + weight z.2.2) z.1).run oracle.query
                    else
                      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit attempts (future + 1)
                          total z.1).run oracle.query by
                    funext z
                    split <;> rfl]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable
                    q I oracle hsigma2 hweight proposalCap properStride retryLimit
                      retryLimit future).1.comp <|
                      ((measurable_const.add
                        (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                          measurable_fst)
                · exact (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable
                    q I oracle hsigma2 hweight proposalCap properStride retryLimit
                      attempts (future + 1)).1.comp
                        (measurable_const.prodMk measurable_fst)
              have henvelope : Measurable envelope :=
                measurable_finiteKilledChainExpectedCost
                  (scheduledSuccessfulBlockEndpointLaw_measurable q I hsigma2
                    proposalCap properStride)
                  (measurable_scheduledPaddedTrialCost q I oracle hsigma2
                    proposalCap properStride) _
              have hbound : ∀ mixed result,
                  countedQueryCost ((next (mixed, result)).run oracle.query) ≤
                    envelope mixed := by
                intro mixed result
                rcases result with ⟨mark, target⟩
                cases mark with
                | false =>
                    dsimp only [next, Bool.false_eq_true, ↓reduceIte]
                    calc
                      countedQueryCost
                          ((scheduledBalancedAccuracyRetryCollectAux q sigma2
                            weight proposalCap properStride retryLimit attempts
                              (future + 1) total mixed).run oracle.query) ≤
                        finiteKilledChainExpectedCost nextLaw trialCost
                          (balancedRemainingTrials retryLimit attempts
                            (future + 1)) mixed := ihAttempts total mixed
                      _ ≤ envelope mixed :=
                        finiteKilledChainExpectedCost_mono nextLaw trialCost
                          (by rw [balancedRemainingTrials_reject]) mixed
                | true =>
                    dsimp only [next, ↓reduceIte]
                    calc
                      countedQueryCost
                          ((scheduledBalancedAccuracyRetryCollectAux q sigma2
                            weight proposalCap properStride retryLimit retryLimit
                              future (total + weight target) mixed).run
                                oracle.query) ≤
                        finiteKilledChainExpectedCost nextLaw trialCost
                          (balancedRemainingTrials retryLimit retryLimit future)
                            mixed :=
                              ihSamples future (by omega) retryLimit
                                (total + weight target) mixed
                      _ ≤ envelope mixed :=
                        finiteKilledChainExpectedCost_mono nextLaw trialCost
                          (balancedRemainingTrials_accept retryLimit attempts future)
                            mixed
              have hstep := scheduledRetryStep_countedQueryCost_le_padded
                q I oracle hsigma2 proposalCap properStride current
                  (none : Option (ℝ × AmbientSpace q.n)) next hnext hnextRun
                    envelope henvelope hbound
              have hremaining : remaining = remaining - 1 + 1 := by
                dsimp only [remaining, balancedRemainingTrials]
                omega
              calc
                countedQueryCost
                    ((scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                      proposalCap properStride retryLimit (attempts + 1)
                        (future + 1) total current).run oracle.query) ≤
                  trialCost current + ∫⁻ state, envelope state ∂nextLaw current := by
                    rw [scheduledBalancedAccuracyRetryCollectAux]
                    convert hstep using 1
                    simp only [next]
                    rfl
                _ = finiteKilledChainExpectedCost nextLaw trialCost remaining
                    current := by
                      rw [hremaining]
                      rfl

/-- The public scheduled collector's final output normalization is query-free,
so its cost is bounded by the `samples * retryLimit` fixed shadow. -/
theorem scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_shadow
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
          properStride retryLimit samples current).run oracle.query) ≤
      finiteKilledChainExpectedCost
        (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap properStride)
        (scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride)
        (samples * retryLimit) current := by
  unfold scheduledBalancedAccuracyRetryCollect
  rw [MembershipOracleProgram.countedQueryCost_bind_pure_eq oracle.query _
    (balancedAccuracyRetryOutput q) (measurable_balancedAccuracyRetryOutput q)
    ((scheduledBalancedAccuracyRetryCollectAux_countedMeasurable q I oracle
      hsigma2 hweight proposalCap properStride retryLimit retryLimit samples).2
        0 current)]
  cases samples with
  | zero =>
      simpa only [balancedRemainingTrials, Nat.zero_mul] using
        scheduledBalancedAccuracyRetryCollectAux_countedQueryCost_le_shadow
          q I oracle hsigma2 hweight proposalCap properStride retryLimit retryLimit
            0 0 current
  | succ future =>
      simpa only [balancedRemainingTrials, Nat.succ_mul] using
        scheduledBalancedAccuracyRetryCollectAux_countedQueryCost_le_shadow
          q I oracle hsigma2 hweight proposalCap properStride retryLimit retryLimit
            (future + 1) 0 current

/-- Warm-start expected query cost of a complete scheduled retry collector.
Crucially, the bound is independent of the local proposal cap. -/
theorem lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride retryLimit samples : ℕ) :
    ∫⁻ current,
        countedQueryCost
          ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
            properStride retryLimit samples current).run oracle.query) ∂mu ≤
      ((samples * retryLimit : ℕ) : ENNReal) *
        ((properStride : ENNReal) * (M * 2) + 2 * M) := by
  calc
    _ ≤ ∫⁻ current, finiteKilledChainExpectedCost
          (scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap properStride)
          (scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride)
          (samples * retryLimit) current ∂mu :=
      lintegral_mono fun current =>
        scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_shadow
          q I oracle hsigma2 hweight proposalCap properStride retryLimit samples
            current
    _ ≤ _ := lintegral_scheduledFixedPaddedTrialShadowCost_le_of_isWarm
      q I oracle hsigma2 hwarm proposalCap properStride (samples * retryLimit)



end ArlibCommunity.Algorithms.CV18
