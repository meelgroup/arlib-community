/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperSemantics

/-! # Exact executable semantics of scheduled balanced retries -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

theorem scheduledBalancedAccuracyRetryCollectAux_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples,
      (∀ total current,
        (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
          properStride retryLimit attempts samples total current).StronglyMeasurable
            oracle.query) ∧
      (∀ total current,
        (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
          properStride retryLimit attempts samples total current).runEstimate
            oracle.query =
          balancedRetryCollectLawAux
            (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
              properStride)
            (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2)
            weight retryLimit attempts samples total current) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  let R := scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          constructor
          · intro total current
            simp only [scheduledBalancedAccuracyRetryCollectAux,
              MembershipOracleProgram.StronglyMeasurable]
          · intro total current
            simp only [scheduledBalancedAccuracyRetryCollectAux,
              MembershipOracleProgram.runEstimate, balancedRetryCollectLawAux]
      | succ future =>
          induction attempts with
          | zero =>
              constructor
              · intro total current
                simp only [scheduledBalancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.StronglyMeasurable]
              · intro total current
                simp only [scheduledBalancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.runEstimate, balancedRetryCollectLawAux]
          | succ attempts ihAttempts =>
              let next (total : ℝ) (mixed : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n → MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit retryLimit future
                    (total + weight result.2) mixed
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit attempts (future + 1)
                    total mixed
              let nextLaw (total : ℝ) (mixed : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  balancedRetryCollectLawAux B R weight retryLimit retryLimit
                    future (total + weight result.2) mixed
                else
                  balancedRetryCollectLawAux B R weight retryLimit attempts
                    (future + 1) total mixed
              have hnextStrong : ∀ total mixed result,
                  (next total mixed result).StronglyMeasurable oracle.query := by
                intro total mixed
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact ihAttempts.1 total mixed
                | true =>
                    exact (ihSamples future (by omega) retryLimit).1
                      (total + weight target) mixed
              have hnextEq : ∀ total mixed result,
                  (next total mixed result).runEstimate oracle.query =
                    nextLaw total mixed result := by
                intro total mixed
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact ihAttempts.2 total mixed
                | true =>
                    exact (ihSamples future (by omega) retryLimit).2
                      (total + weight target) mixed
              have hnextLawMeasurable : ∀ total mixed,
                  Measurable (nextLaw total mixed) := by
                intro total mixed
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (balancedRetryCollectLawAux_measurable_and_probability
                    B R hweight retryLimit retryLimit future).1.comp <|
                      (measurable_const.add (hweight.comp measurable_snd)).prodMk
                        measurable_const
                · exact (balancedRetryCollectLawAux_measurable_and_probability
                    B R hweight retryLimit attempts (future + 1)).1.comp <|
                      measurable_const.prodMk measurable_const
              have hnextRun : ∀ total mixed, Measurable fun result =>
                  (next total mixed result).runEstimate oracle.query := by
                intro total mixed
                rw [show (fun result =>
                    (next total mixed result).runEstimate oracle.query) =
                  nextLaw total mixed by
                    funext result
                    exact hnextEq total mixed result]
                exact hnextLawMeasurable total mixed
              let someTail (total : ℝ) (block : ℝ × AmbientSpace q.n) :=
                (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                  block.2).bind (next total block.2)
              let someTailLaw (total : ℝ) (block : ℝ × AmbientSpace q.n) :
                  Measure (Option (ℝ × AmbientSpace q.n)) :=
                (R block.2).bind (nextLaw total block.2)
              have hsomeTailStrong : ∀ total block,
                  (someTail total block).StronglyMeasurable oracle.query := by
                intro total block
                exact
                  (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 block.2).bind
                    (hnextStrong total block.2) (hnextRun total block.2)
              have hsomeTailEq : ∀ total block,
                  (someTail total block).runEstimate oracle.query =
                    someTailLaw total block := by
                intro total block
                dsimp only [someTail, someTailLaw]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total block.2)
                  (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 block.2)
                  (hnextStrong total block.2) (hnextRun total block.2)]
                rw [runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
                  q I oracle hsigma2 block.2]
                apply Measure.bind_congr_right
                filter_upwards with result
                exact hnextEq total block.2 result
              have hsomeTailLawMeasurable : ∀ total,
                  Measurable (someTailLaw total) := by
                intro total
                dsimp only [someTailLaw]
                exact measurable_measure_bind_param_variable
                  (R.measurable.comp measurable_snd)
                  (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
                  (by
                    let joint : (ℝ × AmbientSpace q.n) ×
                        (Bool × AmbientSpace q.n) →
                          Measure (Option (ℝ × AmbientSpace q.n)) := fun value =>
                      nextLaw total value.1.2 value.2
                    have hjoint : Measurable joint := by
                      dsimp only [joint, nextLaw]
                      apply Measurable.ite
                      · exact (measurable_fst.comp measurable_snd)
                          (measurableSet_singleton true)
                      · exact
                          (balancedRetryCollectLawAux_measurable_and_probability
                            B R hweight retryLimit retryLimit future).1.comp <|
                            ((measurable_const.add
                              (hweight.comp
                                (measurable_snd.comp measurable_snd))).prodMk
                              (measurable_snd.comp measurable_fst))
                      · exact
                          (balancedRetryCollectLawAux_measurable_and_probability
                            B R hweight retryLimit attempts (future + 1)).1.comp <|
                            measurable_const.prodMk
                              (measurable_snd.comp measurable_fst)
                    exact hjoint)
              let tail (total : ℝ) : Option (ℝ × AmbientSpace q.n) →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun block =>
                match block with
                | none => .pure none
                | some block => someTail total block
              let tailLaw (total : ℝ) : Option (ℝ × AmbientSpace q.n) →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun block =>
                match block with
                | none => Measure.dirac none
                | some block => someTailLaw total block
              have htailStrong : ∀ total block,
                  (tail total block).StronglyMeasurable oracle.query := by
                intro total block
                cases block with
                | none =>
                    simp only [tail, MembershipOracleProgram.StronglyMeasurable]
                | some block => exact hsomeTailStrong total block
              have htailEq : ∀ total block,
                  (tail total block).runEstimate oracle.query =
                    tailLaw total block := by
                intro total block
                cases block with
                | none =>
                    simp only [tail, tailLaw,
                      MembershipOracleProgram.runEstimate]
                | some block => exact hsomeTailEq total block
              have htailLawMeasurable : ∀ total,
                  Measurable (tailLaw total) := by
                intro total
                dsimp only [tailLaw]
                convert Measurable.optionElim
                  (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                  (hsomeTailLawMeasurable total) using 1
                ext block
                cases block <;> rfl
              have htailRun : ∀ total, Measurable fun block =>
                  (tail total block).runEstimate oracle.query := by
                intro total
                rw [show (fun block =>
                    (tail total block).runEstimate oracle.query) =
                  tailLaw total by
                    funext block
                    exact htailEq total block]
                exact htailLawMeasurable total
              have htailDef : ∀ total,
                  (fun block =>
                    match block with
                    | none => MembershipOracleProgram.pure none
                    | some (_, mixed) =>
                        (scheduledBalancedAccuracyGaussianRejectionAttempt
                          q sigma2 mixed).bind (next total mixed)) =
                    tail total := by
                intro total
                funext block
                cases block with
                | none => rfl
                | some block => rcases block with ⟨ignored, mixed⟩; rfl
              have hprogram : ∀ total current,
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                      proposalCap properStride retryLimit (attempts + 1)
                      (future + 1) total current =
                    (cappedScheduledAccuracyProperBlock q sigma2
                      (proposalCap + 1) properStride current).bind
                        (tail total) := by
                intro total current
                rw [scheduledBalancedAccuracyRetryCollectAux]
                congr 1
                exact htailDef total
              have hsemantic : ∀ total current,
                  (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit (attempts + 1)
                    (future + 1) total current).runEstimate oracle.query =
                  balancedRetryCollectLawAux B R weight retryLimit
                    (attempts + 1) (future + 1) total current := by
                intro total current
                rw [hprogram total current]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (tail total)
                  (cappedScheduledAccuracyProperBlock_stronglyMeasurable
                    q I oracle hsigma2 proposalCap properStride current)
                  (htailStrong total) (htailRun total)]
                rw [cappedScheduledAccuracyProperBlock_semantics
                  q I oracle hsigma2 proposalCap properStride current]
                rw [balancedRetryCollectLawAux]
                apply Measure.bind_congr_right
                filter_upwards with block
                cases block with
                | none => exact htailEq total none
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    exact htailEq total (some (ignored, mixed))
              constructor
              · intro total current
                rw [hprogram total current]
                exact
                  (cappedScheduledAccuracyProperBlock_stronglyMeasurable
                    q I oracle hsigma2 proposalCap properStride current).bind
                    (htailStrong total) (htailRun total)
              · exact hsemantic

theorem scheduledBalancedAccuracyRetryCollect_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
      properStride retryLimit samples current).runEstimate oracle.query =
        scheduledBalancedAccuracyRetryCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples current := by
  let raw := scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
    properStride retryLimit retryLimit samples 0 current
  let output : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
    fun result => .pure (balancedAccuracyRetryOutput q result)
  have hraw := scheduledBalancedAccuracyRetryCollectAux_semantics
    q I oracle hsigma2 hweight proposalCap properStride retryLimit retryLimit
      samples
  have houtputStrong : ∀ result,
      (output result).StronglyMeasurable oracle.query := fun _ => by trivial
  have houtputRun : Measurable fun result =>
      (output result).runEstimate oracle.query := by
    simp only [output, MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp
      (measurable_balancedAccuracyRetryOutput q)
  unfold scheduledBalancedAccuracyRetryCollect
    scheduledBalancedAccuracyRetryCollectLaw
  change (raw.bind output).runEstimate oracle.query = _
  rw [MembershipOracleProgram.runEstimate_bind oracle.query raw output
    (hraw.1 0 current) houtputStrong houtputRun]
  rw [hraw.2 0 current]
  exact Measure.bind_dirac_eq_map _ (measurable_balancedAccuracyRetryOutput q)

#print axioms scheduledBalancedAccuracyRetryCollect_semantics

end ArlibCommunity.Algorithms.CV18
