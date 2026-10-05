/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalQueryCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives

/-!
# Fixed-count programs have measurable counted semantics

This module supplies the missing generic bridge between the estimate-only
measurability proofs used throughout the CV18 development and the interpreter
which retains the actual number of oracle queries.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- If every execution has the same syntactic query count, the counted law is
the estimate law paired with that count. -/
theorem MembershipOracleProgram.FixedQueryCount.run_eq_map_runEstimate
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {program : MembershipOracleProgram n Result} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (hmeas : program.StronglyMeasurable oracle) :
    program.run oracle =
      (program.runEstimate oracle).map (fun result => (result, count)) := by
  induction hcount with
  | pure result =>
      simp only [MembershipOracleProgram.run, MembershipOracleProgram.runEstimate]
      rw [Measure.map_dirac']
      fun_prop
  | query point next count hnext ih =>
      simp only [MembershipOracleProgram.run, MembershipOracleProgram.runEstimate]
      rw [ih (oracle point) hmeas]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
  | randomNat law next count hnext ih =>
      simp only [MembershipOracleProgram.run, MembershipOracleProgram.runEstimate]
      rw [show (fun seed => MembershipOracleProgram.run oracle (next seed)) =
          (fun seed => (MembershipOracleProgram.runEstimate oracle (next seed)).map
            fun result => (result, count)) by
        funext seed
        exact ih seed (hmeas.2 seed)]
      exact (measure_map_bind_eq_bind_map_ae _ hmeas.1.aemeasurable
        (by fun_prop)).symm
  | randomPoint law hprob next count hnext ih =>
      simp only [MembershipOracleProgram.run, MembershipOracleProgram.runEstimate]
      rw [show (fun point => MembershipOracleProgram.run oracle (next point)) =
          (fun point => (MembershipOracleProgram.runEstimate oracle (next point)).map
            fun result => (result, count)) by
        funext point
        exact ih point (hmeas.2 point)]
      exact (measure_map_bind_eq_bind_map_ae _ hmeas.1.aemeasurable
        (by fun_prop)).symm
  | randomReal law hprob next count hnext ih =>
      simp only [MembershipOracleProgram.run, MembershipOracleProgram.runEstimate]
      rw [show (fun value => MembershipOracleProgram.run oracle (next value)) =
          (fun value => (MembershipOracleProgram.runEstimate oracle (next value)).map
            fun result => (result, count)) by
        funext value
        exact ih value (hmeas.2 value)]
      exact (measure_map_bind_eq_bind_map_ae _ hmeas.1.aemeasurable
        (by fun_prop)).symm

/-- Fixed-count estimate measurability is enough for pointwise counted
measurability.  This packages the preceding exact-law identity into the
recursive predicate needed by the global cutoff. -/
theorem MembershipOracleProgram.FixedQueryCount.countedStronglyMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {program : MembershipOracleProgram n Result} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (hmeas : program.StronglyMeasurable oracle) :
    program.CountedStronglyMeasurable oracle := by
  induction hcount with
  | pure result => trivial
  | query point next count hnext ih =>
      exact ih (oracle point) hmeas
  | randomNat law next count hnext ih =>
      constructor
      · rw [show (fun seed => MembershipOracleProgram.run oracle (next seed)) =
            (fun seed => (MembershipOracleProgram.runEstimate oracle (next seed)).map
              fun result => (result, count)) by
          funext seed
          exact (hnext seed).run_eq_map_runEstimate oracle (hmeas.2 seed)]
        exact measurable_measure_map_param_variable hmeas.1
          (fun seed => MembershipOracleProgram.runEstimate_isProbabilityMeasure
            oracle (next seed) (hmeas.2 seed).estimateMeasurable)
          (by fun_prop)
      · exact fun seed => ih seed (hmeas.2 seed)
  | randomPoint law hprob next count hnext ih =>
      constructor
      · rw [show (fun point => MembershipOracleProgram.run oracle (next point)) =
            (fun point => (MembershipOracleProgram.runEstimate oracle (next point)).map
              fun result => (result, count)) by
          funext point
          exact (hnext point).run_eq_map_runEstimate oracle (hmeas.2 point)]
        exact measurable_measure_map_param_variable hmeas.1
          (fun point => MembershipOracleProgram.runEstimate_isProbabilityMeasure
            oracle (next point) (hmeas.2 point).estimateMeasurable)
          (by fun_prop)
      · exact fun point => ih point (hmeas.2 point)
  | randomReal law hprob next count hnext ih =>
      constructor
      · rw [show (fun value => MembershipOracleProgram.run oracle (next value)) =
            (fun value => (MembershipOracleProgram.runEstimate oracle (next value)).map
              fun result => (result, count)) by
          funext value
          exact (hnext value).run_eq_map_runEstimate oracle (hmeas.2 value)]
        exact measurable_measure_map_param_variable hmeas.1
          (fun value => MembershipOracleProgram.runEstimate_isProbabilityMeasure
            oracle (next value) (hmeas.2 value).estimateMeasurable)
          (by fun_prop)
      · exact fun value => ih value (hmeas.2 value)

/-- Parameterized version of the fixed-count bridge. -/
theorem MembershipOracleProgram.measurable_run_of_fixedQueryCount
    {n : ℕ} {P : Type*} {Result : Type} [MeasurableSpace P]
    [MeasurableSpace Result] (oracle : AmbientSpace n → Bool)
    (program : P → MembershipOracleProgram n Result) (count : ℕ)
    (hcount : ∀ p, (program p).FixedQueryCount count)
    (hstrong : ∀ p, (program p).StronglyMeasurable oracle)
    (hestimate : Measurable fun p => (program p).runEstimate oracle) :
    Measurable fun p => (program p).run oracle := by
  rw [show (fun p => (program p).run oracle) =
      fun p => ((program p).runEstimate oracle).map
        (fun result => (result, count)) by
    funext p
    exact (hcount p).run_eq_map_runEstimate oracle (hstrong p)]
  exact measurable_measure_map_param_variable hestimate
    (fun p => MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle _
      (hstrong p).estimateMeasurable)
    (by fun_prop)

/-- Parameterized counted interpreter law for a syntactic bind.  This is the
workhorse for variable-cost loops: both the source program and its
continuation may depend measurably on an external state. -/
theorem MembershipOracleProgram.measurable_run_bind_param
    {n : ℕ} {P : Type*} {A B : Type} [MeasurableSpace P] [MeasurableSpace A]
    [MeasurableSpace B] (oracle : AmbientSpace n → Bool)
    (program : P → MembershipOracleProgram n A)
    (next : P × A → MembershipOracleProgram n B)
    (hprogramMeas : Measurable fun p => (program p).run oracle)
    (hprogram : ∀ p, (program p).CountedStronglyMeasurable oracle)
    (hnextMeas : Measurable fun z => (next z).run oracle)
    (hnext : ∀ z, (next z).CountedStronglyMeasurable oracle) :
    Measurable fun p => ((program p).bind fun a => next (p, a)).run oracle := by
  let continuation : P × (A × ℕ) → Measure (B × ℕ) := fun z =>
    ((next (z.1, z.2.1)).run oracle).map fun second =>
      (second.1, z.2.2 + second.2)
  have hcontinuation : Measurable continuation := by
    exact measurable_measure_map_param_variable
      (hnextMeas.comp <|
        measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      (fun z => MembershipOracleProgram.run_isProbabilityMeasure oracle _
        (hnext (z.1, z.2.1)).executionMeasurable)
      ((measurable_fst.comp measurable_snd).prodMk <|
        (measurable_snd.comp (measurable_snd.comp measurable_fst)).add
          (measurable_snd.comp measurable_snd)
      )
  rw [show (fun p => ((program p).bind fun a => next (p, a)).run oracle) =
      fun p => ((program p).run oracle).bind fun first => continuation (p, first) by
    funext p
    rw [MembershipOracleProgram.run_bind_counted oracle (program p)
      (fun a => next (p, a)) (hprogram p) (fun a => hnext (p, a))]
    · rfl
    · exact hnextMeas.comp (measurable_const.prodMk measurable_id)]
  exact measurable_measure_bind_param_variable hprogramMeas
    (fun p => MembershipOracleProgram.run_isProbabilityMeasure oracle _
      (hprogram p).executionMeasurable)
    hcontinuation

/-! ## Fixed-cost CV18 leaves -/

theorem accuracyImportanceObservation_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (current : AmbientSpace q.n) :
    (accuracyImportanceObservation q sigma2 weight current).FixedQueryCount 1 := by
  unfold accuracyImportanceObservation
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  exact .pure _

theorem accuracyImportanceObservation_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) :
    (accuracyImportanceObservation q sigma2 weight current).CountedStronglyMeasurable
      oracle.query :=
  MembershipOracleProgram.FixedQueryCount.countedStronglyMeasurable
    (accuracyImportanceObservation_fixedQueryCount q sigma2 weight current) oracle.query
      (accuracyImportanceObservation_stronglyMeasurable
        q I oracle sigma2 weight current)

theorem accuracyMetropolisMarkedProposalProgram_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).FixedQueryCount 1 := by
  unfold accuracyMetropolisMarkedProposalProgram
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  apply MembershipOracleProgram.FixedQueryCount.randomReal
  intro coin
  split <;> exact .pure _

theorem accuracyMetropolisMarkedBallStep_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).FixedQueryCount 1 := by
  unfold accuracyMetropolisMarkedBallStep
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro proposal
  exact accuracyMetropolisMarkedProposalProgram_fixedQueryCount
    q sigma2 current proposal

theorem accuracyMetropolisMarkedBallStep_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  MembershipOracleProgram.FixedQueryCount.countedStronglyMeasurable
    (accuracyMetropolisMarkedBallStep_fixedQueryCount q sigma2 current) oracle.query
      (accuracyMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current)

theorem balancedAccuracyGaussianRejectionAttempt_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionAttempt q sigma2 current).FixedQueryCount 1 := by
  unfold balancedAccuracyGaussianRejectionAttempt
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  apply MembershipOracleProgram.FixedQueryCount.randomReal
  intro coin
  split <;> exact .pure _

theorem balancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionAttempt q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  MembershipOracleProgram.FixedQueryCount.countedStronglyMeasurable
    (balancedAccuracyGaussianRejectionAttempt_fixedQueryCount q sigma2 current)
      oracle.query
      (balancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
        q I oracle sigma2 current)

theorem figureOneInitialSample_fixedQueryCount (q : VolumeParams) :
    (figureOneInitialSample q).FixedQueryCount 1 := by
  unfold figureOneInitialSample
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro point
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  split <;> exact .pure _

theorem figureOneInitialSample_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneInitialSample q).CountedStronglyMeasurable oracle.query :=
  (figureOneInitialSample_fixedQueryCount q).countedStronglyMeasurable
    oracle.query (figureOneInitialSample_stronglyMeasurable q I oracle)

/-! ## Variable-cost capped proper collector -/

/-- The capped raw-proposal collector has a jointly measurable counted law
in its accumulator and retained state, and is pointwise counted-measurable.
Unlike the estimate-only semantics theorem, this records early exits and the
actual raw-query total. -/
theorem cappedAccuracyProperCollectWeightsAux_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples state.1 state.2).run oracle.query) ∧
    (∀ total current,
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).CountedStronglyMeasurable
          oracle.query) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
    (accuracyPhaseTruncatedBody q I sigma2)
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let f := accuracyImportanceWeight q I sigma2 weight
  have hf : Measurable f := measurable_accuracyImportanceWeight q I sigma2 hweight
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <| measurable_fst.prodMk measurable_snd).prodMk
                measurable_const
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
      | succ samples =>
          constructor
          · simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              measurable_const.prodMk measurable_const
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <| measurable_fst.prodMk measurable_snd).prodMk
                measurable_const
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
      | succ samples =>
          cases remainingProper with
          | zero =>
              let observation (state : ℝ × AmbientSpace q.n) :=
                accuracyImportanceObservation q sigma2 weight state.2
              let next (z : (ℝ × AmbientSpace q.n) × ℝ) :=
                cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
                  rawCap properStride samples (z.1.1 + z.2) z.1.2
              have hobservationMeas : Measurable fun state =>
                  (observation state).run oracle.query := by
                apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
                  oracle.query observation 1
                · intro state
                  exact accuracyImportanceObservation_fixedQueryCount
                    q sigma2 weight state.2
                · intro state
                  exact accuracyImportanceObservation_stronglyMeasurable
                    q I oracle sigma2 weight state.2
                · rw [show (fun state =>
                      (observation state).runEstimate oracle.query) =
                    fun state => Measure.dirac (f state.2) by
                      funext state
                      exact runEstimate_accuracyImportanceObservation
                        q I oracle sigma2 weight state.2]
                  exact Measure.measurable_dirac.comp (hf.comp measurable_snd)
              have hnextMeas : Measurable fun z => (next z).run oracle.query :=
                (ih properStride samples).1.comp <|
                  ((measurable_fst.comp measurable_fst).add measurable_snd).prodMk
                    (measurable_snd.comp measurable_fst)
              have hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query := by
                intro z
                exact (ih properStride samples).2 _ _
              constructor
              · simpa only [observation, next,
                  cappedAccuracyProperCollectWeightsAux] using
                  MembershipOracleProgram.measurable_run_bind_param
                    oracle.query observation next hobservationMeas
                    (fun state =>
                      accuracyImportanceObservation_countedStronglyMeasurable
                        q I oracle sigma2 weight state.2)
                    hnextMeas hnext
              · intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                apply MembershipOracleProgram.CountedStronglyMeasurable.bind
                  (accuracyImportanceObservation_countedStronglyMeasurable
                    q I oracle sigma2 weight current)
                  (fun observed => (ih properStride samples).2 _ _)
                exact hnextMeas.comp <|
                  (measurable_const : Measurable fun _ : ℝ => (total, current)).prodMk
                    measurable_id
          | succ remainingProper =>
              let step (state : ℝ × AmbientSpace q.n) :=
                accuracyMetropolisMarkedBallStep q sigma2 state.2
              let next (z : (ℝ × AmbientSpace q.n) ×
                  (Bool × AmbientSpace q.n)) :=
                if z.2.1 then
                  match remainingProper with
                  | 0 =>
                      cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap 0 (samples + 1) z.1.1 z.2.2
                  | nextRemaining + 1 =>
                      cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap (nextRemaining + 1) (samples + 1)
                          z.1.1 z.2.2
                else
                  cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride rawCap (remainingProper + 1) (samples + 1)
                      z.1.1 z.2.2
              have hstepMeas : Measurable fun state =>
                  (step state).run oracle.query := by
                apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
                  oracle.query step 1
                · intro state
                  exact accuracyMetropolisMarkedBallStep_fixedQueryCount
                    q sigma2 state.2
                · intro state
                  exact accuracyMetropolisMarkedBallStep_stronglyMeasurable
                    q I oracle sigma2 state.2
                · rw [show (fun state =>
                      (step state).runEstimate oracle.query) =
                    fun state => Q state.2 by
                      funext state
                      exact runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
                        q I oracle hsigma2 state.2]
                  exact Q.measurable.comp measurable_snd
              have hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query := by
                rintro ⟨state, mark, point⟩
                cases mark with
                | false => exact (ih (remainingProper + 1) (samples + 1)).2 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih 0 (samples + 1)).2 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1) (samples + 1)).2 _ _
              have hnextMeas : Measurable fun z => (next z).run oracle.query := by
                dsimp only [next]
                rw [show (fun z : (ℝ × AmbientSpace q.n) ×
                      (Bool × AmbientSpace q.n) =>
                      (if z.2.1 = true then
                        match remainingProper with
                        | 0 => cappedAccuracyProperCollectWeightsAux q sigma2
                            weight properStride rawCap 0 (samples + 1)
                              z.1.1 z.2.2
                        | nextRemaining + 1 =>
                            cappedAccuracyProperCollectWeightsAux q sigma2
                              weight properStride rawCap (nextRemaining + 1)
                                (samples + 1) z.1.1 z.2.2
                      else cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap (remainingProper + 1) (samples + 1)
                          z.1.1 z.2.2).run oracle.query) =
                    fun z => if z.2.1 = true then
                      (match remainingProper with
                      | 0 => cappedAccuracyProperCollectWeightsAux q sigma2
                          weight properStride rawCap 0 (samples + 1)
                            z.1.1 z.2.2
                      | nextRemaining + 1 =>
                          cappedAccuracyProperCollectWeightsAux q sigma2 weight
                            properStride rawCap (nextRemaining + 1) (samples + 1)
                              z.1.1 z.2.2).run oracle.query
                    else (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                      properStride rawCap (remainingProper + 1) (samples + 1)
                        z.1.1 z.2.2).run oracle.query by
                      funext z
                      split <;> rfl]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (ih 0 (samples + 1)).1.comp <|
                        (measurable_fst.comp measurable_fst).prodMk
                          (measurable_snd.comp measurable_snd)
                  | succ nextRemaining =>
                      exact (ih (nextRemaining + 1) (samples + 1)).1.comp <|
                        (measurable_fst.comp measurable_fst).prodMk
                          (measurable_snd.comp measurable_snd)
                · exact (ih (remainingProper + 1) (samples + 1)).1.comp <|
                    (measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp measurable_snd)
              constructor
              · simp only [cappedAccuracyProperCollectWeightsAux]
                change Measurable fun state =>
                  ((step state).bind fun result => next (state, result)).run
                    oracle.query
                exact MembershipOracleProgram.measurable_run_bind_param
                  oracle.query step next hstepMeas
                  (fun state =>
                    accuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                      q I oracle sigma2 state.2)
                  hnextMeas hnext
              · intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                apply MembershipOracleProgram.CountedStronglyMeasurable.bind
                  (accuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                    q I oracle sigma2 current)
                  (fun result => hnext ((total, current), result))
                exact hnextMeas.comp <| measurable_const.prodMk measurable_id

theorem cappedAccuracyProperCollectWeights_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) :
    (Measurable fun current =>
      (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
        samples current).run oracle.query) ∧
    (∀ current,
      (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
        samples current).CountedStronglyMeasurable oracle.query) := by
  have h := cappedAccuracyProperCollectWeightsAux_countedMeasurable
    q I oracle hsigma2 hweight properStride rawCap properStride samples
  exact ⟨h.1.comp (measurable_const.prodMk measurable_id), fun current => h.2 0 current⟩

/-! ## Balanced retry loop -/

/-- The complete finite balanced retry state machine has measurable counted
semantics.  This composes the variable raw-proposal cost of each proper block
with the one-query rejection decision and both retry branches. -/
theorem balancedAccuracyRetryCollectAux_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) : ∀ attempts samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
        properStride retryLimit attempts samples state.1 state.2).run
          oracle.query) ∧
    (∀ total current,
      (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
        properStride retryLimit attempts samples total current).CountedStronglyMeasurable
          oracle.query) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          constructor
          · simp only [balancedAccuracyRetryCollectAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <| measurable_fst.prodMk measurable_snd).prodMk
                measurable_const
          · intro total current
            rw [balancedAccuracyRetryCollectAux]
            trivial
      | succ future =>
          induction attempts with
          | zero =>
              constructor
              · simp only [balancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.run]
                exact Measure.measurable_dirac.comp <|
                  measurable_const.prodMk measurable_const
              · intro total current
                rw [balancedAccuracyRetryCollectAux]
                trivial
          | succ attempts ihAttempts =>
              let block (state : ℝ × AmbientSpace q.n) :=
                cappedAccuracyProperCollectWeights q sigma2 (fun _ => 0)
                  (proposalCap + 1) properStride 1 state.2
              let decisionNext (z : ((ℝ × AmbientSpace q.n) ×
                  (ℝ × AmbientSpace q.n)) ×
                    (Bool × AmbientSpace q.n)) :=
                if z.2.1 then
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit retryLimit future
                      (z.1.1.1 + weight z.2.2) z.1.2.2
                else
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit attempts (future + 1)
                      z.1.1.1 z.1.2.2
              let rejection (p : (ℝ × AmbientSpace q.n) ×
                  (ℝ × AmbientSpace q.n)) :=
                balancedAccuracyGaussianRejectionAttempt q sigma2 p.2.2
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
                (cappedAccuracyProperCollectWeights_countedMeasurable
                  q I oracle hsigma2 measurable_const (proposalCap + 1)
                    properStride 1).1.comp measurable_snd
              have hblock : ∀ state,
                  (block state).CountedStronglyMeasurable oracle.query := by
                intro state
                exact (cappedAccuracyProperCollectWeights_countedMeasurable
                  q I oracle hsigma2 measurable_const (proposalCap + 1)
                    properStride 1).2 state.2
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
                        balancedAccuracyRetryCollectAux q sigma2 weight
                          proposalCap properStride retryLimit retryLimit future
                            (z.1.1.1 + weight z.2.2) z.1.2.2
                      else balancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit attempts (future + 1)
                          z.1.1.1 z.1.2.2).run oracle.query) =
                    fun z => if z.2.1 = true then
                      (balancedAccuracyRetryCollectAux q sigma2 weight
                        proposalCap properStride retryLimit retryLimit future
                          (z.1.1.1 + weight z.2.2) z.1.2.2).run oracle.query
                    else (balancedAccuracyRetryCollectAux q sigma2 weight
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
                  exact balancedAccuracyGaussianRejectionAttempt_fixedQueryCount
                    q sigma2 p.2.2
                · intro p
                  exact balancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 p.2.2
                · rw [show (fun p => (rejection p).runEstimate oracle.query) =
                      fun p => balancedAccuracyGaussianRejectionKernel
                        q I sigma2 p.2.2 by
                    funext p
                    exact runEstimate_balancedAccuracyGaussianRejectionAttempt
                      q I oracle hsigma2 p.2.2]
                  exact (balancedAccuracyGaussianRejectionKernel q I sigma2).measurable.comp
                    (measurable_snd.comp measurable_snd)
              have hrejection : ∀ p,
                  (rejection p).CountedStronglyMeasurable oracle.query := by
                intro p
                exact balancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
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
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit (attempts + 1) (future + 1)
                      state.1 state.2 =
                    (block state).bind fun value => tail (state, value) := by
                intro state
                rw [Nat.add_one, Nat.add_one,
                  balancedAccuracyRetryCollectAux]
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
                    (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
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
theorem balancedAccuracyRetryCollect_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ) :
    (Measurable fun current =>
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
        retryLimit samples current).run oracle.query) ∧
    (∀ current,
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
        retryLimit samples current).CountedStronglyMeasurable oracle.query) := by
  let aux (current : AmbientSpace q.n) :=
    balancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
      retryLimit retryLimit samples 0 current
  let finish (z : AmbientSpace q.n × Option (ℝ × AmbientSpace q.n)) :=
    MembershipOracleProgram.pure (n := q.n) (balancedAccuracyRetryOutput q z.2)
  have hauxMeas : Measurable fun current => (aux current).run oracle.query :=
    (balancedAccuracyRetryCollectAux_countedMeasurable q I oracle hsigma2
      hweight proposalCap properStride retryLimit retryLimit samples).1.comp
        (measurable_const.prodMk measurable_id)
  have haux : ∀ current,
      (aux current).CountedStronglyMeasurable oracle.query := by
    intro current
    exact (balancedAccuracyRetryCollectAux_countedMeasurable q I oracle hsigma2
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
  · unfold balancedAccuracyRetryCollect
    change Measurable fun current =>
      ((aux current).bind fun value => finish (current, value)).run oracle.query
    exact MembershipOracleProgram.measurable_run_bind_param
      oracle.query aux finish hauxMeas haux hfinishMeas hfinish
  · intro current
    unfold balancedAccuracyRetryCollect
    apply MembershipOracleProgram.CountedStronglyMeasurable.bind (haux current)
      (fun value => hfinish (current, value))
    exact hfinishMeas.comp <| measurable_const.prodMk measurable_id

end ArlibCommunity.Algorithms.CV18
