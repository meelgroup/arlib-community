/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperExpectedCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetrySemantics

/-! # Counted measurability of the scheduled retry collector -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The scheduled rejection test always makes exactly one membership query. -/
theorem scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).FixedQueryCount 1 := by
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  apply MembershipOracleProgram.FixedQueryCount.randomReal
  intro coin
  split <;> exact .pure _

/-- Counted measurability of the scheduled rejection test. -/
theorem scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  (scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount q sigma2 current).countedStronglyMeasurable
    oracle.query
      (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
        q I oracle sigma2 current)

/-! ## Balanced retry loop -/

/-- The complete finite balanced retry state machine has measurable counted
semantics.  This composes the variable raw-proposal cost of each proper block
with the one-query rejection decision and both retry branches. -/
theorem scheduledBalancedAccuracyRetryCollectAux_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) : ∀ attempts samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
        properStride retryLimit attempts samples state.1 state.2).run
          oracle.query) ∧
    (∀ total current,
      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
        properStride retryLimit attempts samples total current).CountedStronglyMeasurable
          oracle.query) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          constructor
          · simp only [scheduledBalancedAccuracyRetryCollectAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <| measurable_fst.prodMk measurable_snd).prodMk
                measurable_const
          · intro total current
            rw [scheduledBalancedAccuracyRetryCollectAux]
            trivial
      | succ future =>
          induction attempts with
          | zero =>
              constructor
              · simp only [scheduledBalancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.run]
                exact Measure.measurable_dirac.comp <|
                  measurable_const.prodMk measurable_const
              · intro total current
                rw [scheduledBalancedAccuracyRetryCollectAux]
                trivial
          | succ attempts ihAttempts =>
              let block (state : ℝ × AmbientSpace q.n) :=
                cappedScheduledAccuracyProperBlock q sigma2
                  (proposalCap + 1) properStride state.2
              let decisionNext (z : ((ℝ × AmbientSpace q.n) ×
                  (ℝ × AmbientSpace q.n)) ×
                    (Bool × AmbientSpace q.n)) :=
                if z.2.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit retryLimit future
                      (z.1.1.1 + weight z.2.2) z.1.2.2
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit attempts (future + 1)
                      z.1.1.1 z.1.2.2
              let rejection (p : (ℝ × AmbientSpace q.n) ×
                  (ℝ × AmbientSpace q.n)) :=
                scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 p.2.2
              let someTail (p : (ℝ × AmbientSpace q.n) ×
                  (ℝ × AmbientSpace q.n)) :=
                (rejection p).bind fun result => decisionNext (p, result)
              let tail (z : (ℝ × AmbientSpace q.n) ×
                  Option (ℝ × AmbientSpace q.n)) :=
                match z.2 with
                | none => MembershipOracleProgram.pure none
                | some value => someTail (z.1, value)
              have hblockMeas : Measurable fun state =>
                  (block state).run oracle.query :=
                (cappedScheduledAccuracyProperBlock_countedMeasurable
                  q I oracle hsigma2 (proposalCap + 1) properStride).1.comp
                    measurable_snd
              have hblock : ∀ state,
                  (block state).CountedStronglyMeasurable oracle.query := by
                intro state
                exact (cappedScheduledAccuracyProperBlock_countedMeasurable
                  q I oracle hsigma2 (proposalCap + 1) properStride).2 state.2
              have hdecisionNext : ∀ z,
                  (decisionNext z).CountedStronglyMeasurable oracle.query := by
                rintro ⟨⟨⟨total, current⟩, ignored, mixed⟩, mark, target⟩
                cases mark with
                | false => exact ihAttempts.2 total mixed
                | true =>
                    exact (ihSamples future (by omega) retryLimit).2
                      (total + weight target) mixed
              have hdecisionNextMeas : Measurable fun z =>
                  (decisionNext z).run oracle.query := by
                dsimp only [decisionNext]
                rw [show (fun z : (((ℝ × AmbientSpace q.n) ×
                      (ℝ × AmbientSpace q.n)) ×
                        (Bool × AmbientSpace q.n)) =>
                      (if z.2.1 = true then
                        scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                          proposalCap properStride retryLimit retryLimit future
                            (z.1.1.1 + weight z.2.2) z.1.2.2
                      else scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit attempts (future + 1)
                          z.1.1.1 z.1.2.2).run oracle.query) =
                    fun z => if z.2.1 = true then
                      (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit retryLimit future
                          (z.1.1.1 + weight z.2.2) z.1.2.2).run oracle.query
                    else (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                      proposalCap properStride retryLimit attempts (future + 1)
                        z.1.1.1 z.1.2.2).run oracle.query by
                      funext z
                      split <;> rfl]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (ihSamples future (by omega) retryLimit).1.comp <|
                    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
                      (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
                · exact ihAttempts.1.comp <|
                    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
                      (measurable_snd.comp (measurable_snd.comp measurable_fst))
              have hrejectionMeas : Measurable fun p =>
                  (rejection p).run oracle.query := by
                apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
                  oracle.query rejection 1
                · intro p
                  exact scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
                    q sigma2 p.2.2
                · intro p
                  exact scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 p.2.2
                · rw [show (fun p => (rejection p).runEstimate oracle.query) =
                      fun p => scheduledBalancedAccuracyGaussianRejectionKernel
                        q I sigma2 p.2.2 by
                    funext p
                    exact runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
                      q I oracle hsigma2 p.2.2]
                  exact (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2).measurable.comp
                    (measurable_snd.comp measurable_snd)
              have hrejection : ∀ p,
                  (rejection p).CountedStronglyMeasurable oracle.query := by
                intro p
                exact scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
                  q I oracle sigma2 p.2.2
              have hsomeTailMeas : Measurable fun p =>
                  (someTail p).run oracle.query := by
                exact MembershipOracleProgram.measurable_run_bind_param
                  oracle.query rejection decisionNext hrejectionMeas hrejection
                    hdecisionNextMeas hdecisionNext
              have hsomeTail : ∀ p,
                  (someTail p).CountedStronglyMeasurable oracle.query := by
                intro p
                apply MembershipOracleProgram.CountedStronglyMeasurable.bind
                  (hrejection p) (fun result => hdecisionNext (p, result))
                exact hdecisionNextMeas.comp <|
                  measurable_const.prodMk measurable_id
              have htailMeas : Measurable fun z => (tail z).run oracle.query := by
                rw [show (fun z => (tail z).run oracle.query) = fun z =>
                    match z.2 with
                    | none => Measure.dirac
                        ((none : Option (ℝ × AmbientSpace q.n)), (0 : ℕ))
                    | some value => (someTail (z.1, value)).run oracle.query by
                      funext z
                      rcases z with ⟨state, value⟩
                      cases value <;> simp [tail, MembershipOracleProgram.run]]
                have hnone : Measurable fun _ : ℝ × AmbientSpace q.n =>
                    Measure.dirac
                      ((none : Option (ℝ × AmbientSpace q.n)), (0 : ℕ)) :=
                  measurable_const
                convert Measurable.optionElimParam hnone hsomeTailMeas using 1
                funext z
                rcases z with ⟨state, value⟩
                cases value <;> rfl
              have htail : ∀ z,
                  (tail z).CountedStronglyMeasurable oracle.query := by
                rintro ⟨state, value⟩
                cases value with
                | none => trivial
                | some blockValue => exact hsomeTail (state, blockValue)
              have hprogramEq : ∀ state : ℝ × AmbientSpace q.n,
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit (attempts + 1) (future + 1)
                      state.1 state.2 =
                    (block state).bind fun value => tail (state, value) := by
                intro state
                rw [Nat.add_one, Nat.add_one,
                  scheduledBalancedAccuracyRetryCollectAux]
                dsimp only [block]
                congr 1
                funext value
                cases value with
                | none => rfl
                | some value =>
                    rcases value with ⟨ignored, mixed⟩
                    rfl
              constructor
              · have hbind := MembershipOracleProgram.measurable_run_bind_param
                  oracle.query block tail hblockMeas hblock htailMeas htail
                rw [show (fun state =>
                    (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                      properStride retryLimit (attempts + 1) (future + 1)
                        state.1 state.2).run oracle.query) =
                    fun state => ((block state).bind fun value =>
                      tail (state, value)).run oracle.query by
                        funext state
                        rw [hprogramEq state]]
                exact hbind
              · intro total current
                rw [hprogramEq (total, current)]
                apply MembershipOracleProgram.CountedStronglyMeasurable.bind
                  (hblock (total, current))
                  (fun value => htail ((total, current), value))
                exact htailMeas.comp <| measurable_const.prodMk measurable_id

/-- Public balanced collector counted semantics, including the final retained
speedy-to-Gaussian output map. -/
theorem scheduledBalancedAccuracyRetryCollect_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ) :
    (Measurable fun current =>
      (scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
        retryLimit samples current).run oracle.query) ∧
    (∀ current,
      (scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
        retryLimit samples current).CountedStronglyMeasurable oracle.query) := by
  let aux (current : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
      retryLimit retryLimit samples 0 current
  let finish (z : AmbientSpace q.n × Option (ℝ × AmbientSpace q.n)) :=
    MembershipOracleProgram.pure (n := q.n) (balancedAccuracyRetryOutput q z.2)
  have hauxMeas : Measurable fun current => (aux current).run oracle.query :=
    (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable q I oracle hsigma2
      hweight proposalCap properStride retryLimit retryLimit samples).1.comp
        (measurable_const.prodMk measurable_id)
  have haux : ∀ current,
      (aux current).CountedStronglyMeasurable oracle.query := by
    intro current
    exact (scheduledBalancedAccuracyRetryCollectAux_countedMeasurable q I oracle hsigma2
      hweight proposalCap properStride retryLimit retryLimit samples).2 0 current
  have hfinishMeas : Measurable fun z => (finish z).run oracle.query := by
    simp only [finish, MembershipOracleProgram.run]
    exact Measure.measurable_dirac.comp <|
      (measurable_balancedAccuracyRetryOutput q).comp measurable_snd |>.prodMk
        measurable_const
  have hfinish : ∀ z, (finish z).CountedStronglyMeasurable oracle.query := by
    intro z
    trivial
  constructor
  · unfold scheduledBalancedAccuracyRetryCollect
    change Measurable fun current =>
      ((aux current).bind fun value => finish (current, value)).run oracle.query
    exact MembershipOracleProgram.measurable_run_bind_param
      oracle.query aux finish hauxMeas haux hfinishMeas hfinish
  · intro current
    unfold scheduledBalancedAccuracyRetryCollect
    apply MembershipOracleProgram.CountedStronglyMeasurable.bind (haux current)
      (fun value => hfinish (current, value))
    exact hfinishMeas.comp <| measurable_const.prodMk measurable_id

end ArlibCommunity.Algorithms.CV18

