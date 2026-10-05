/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceProgram

/-! # Law of the capped CV18 importance collector -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Abstract law of the importance collector.  Unlike
`cappedProperCollectLawAux`, recording an observable consumes one unit of the
shared raw budget, matching the membership query needed by the executable
KLS observation. -/
noncomputable def cappedImportanceCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) (f : S → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → S → Measure (Option (ℝ × S))
  | _, _, 0, total, current => Measure.dirac (some (total, current))
  | 0, _, _ + 1, _, _ => Measure.dirac none
  | rawCap + 1, 0, samples + 1, total, current =>
      cappedImportanceCollectLawAux Q f properStride rawCap properStride
        samples (total + f current) current
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (Q current).bind fun result =>
        if result.1 then
          match remainingProper with
          | 0 =>
              cappedImportanceCollectLawAux Q f properStride rawCap 0
                (samples + 1) total result.2
          | nextRemaining + 1 =>
              cappedImportanceCollectLawAux Q f properStride rawCap
                (nextRemaining + 1) (samples + 1) total result.2
        else
          cappedImportanceCollectLawAux Q f properStride rawCap
            (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedImportanceCollectLaw
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) (f : S → ℝ)
    (rawCap properStride samples : ℕ) (current : S) :
    Measure (Option (ℝ × S)) :=
  cappedImportanceCollectLawAux Q f properStride rawCap properStride
    samples 0 current

/-- The importance collector is a measurable probability kernel in its
running sum and current speedy state. -/
theorem cappedImportanceCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    {f : S → ℝ} (hf : Measurable f) (properStride : ℕ) :
    ∀ rawCap remainingProper samples,
      Measurable (fun p : ℝ × S =>
        cappedImportanceCollectLawAux Q f properStride rawCap remainingProper
          samples p.1 p.2) ∧
      ∀ total current, IsProbabilityMeasure
        (cappedImportanceCollectLawAux Q f properStride rawCap remainingProper
          samples total current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      cases samples with
      | zero =>
          simp only [cappedImportanceCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            infer_instance
      | succ samples =>
          simp only [cappedImportanceCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp measurable_const
          · intro total current
            infer_instance
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          simp only [cappedImportanceCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            infer_instance
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedImportanceCollectLawAux]
              constructor
              · exact (ih properStride samples).1.comp <|
                  (measurable_fst.add (hf.comp measurable_snd)).prodMk
                    measurable_snd
              · intro total current
                exact (ih properStride samples).2 (total + f current) current
          | succ remainingProper =>
              let tail : (ℝ × S) → (Bool × S) →
                  Measure (Option (ℝ × S)) := fun state result =>
                if result.1 then
                  match remainingProper with
                  | 0 =>
                      cappedImportanceCollectLawAux Q f properStride rawCap 0
                        (samples + 1) state.1 result.2
                  | nextRemaining + 1 =>
                      cappedImportanceCollectLawAux Q f properStride rawCap
                        (nextRemaining + 1) (samples + 1) state.1 result.2
                else
                  cappedImportanceCollectLawAux Q f properStride rawCap
                    (remainingProper + 1) (samples + 1) state.1 result.2
              have htail : Measurable fun p : (ℝ × S) × (Bool × S) =>
                  tail p.1 p.2 := by
                dsimp only [tail]
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
              have htailProb : ∀ state result,
                  IsProbabilityMeasure (tail state result) := by
                intro state result
                dsimp only [tail]
                split_ifs
                · cases remainingProper with
                  | zero => exact (ih 0 (samples + 1)).2 _ _
                  | succ nextRemaining =>
                      exact (ih (nextRemaining + 1) (samples + 1)).2 _ _
                · exact (ih (remainingProper + 1) (samples + 1)).2 _ _
              simp only [cappedImportanceCollectLawAux]
              constructor
              · change Measurable fun state : ℝ × S =>
                  (Q state.2).bind (tail state)
                exact measurable_measure_bind_param_variable
                  (Q.measurable.comp measurable_snd)
                  (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
                  htail
              · intro total current
                change IsProbabilityMeasure ((Q current).bind (tail (total, current)))
                exact MeasureTheory.isProbabilityMeasure_bind
                  (htail.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable <|
                  ae_of_all _ (htailProb (total, current))

/-- Fewer raw operations than remaining observations forces failure, since
each observation itself consumes one operation even before proposal costs. -/
theorem cappedImportanceCollectLawAux_eq_dirac_none_of_lt_samples
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    (f : S → ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
      rawCap < samples →
      cappedImportanceCollectLawAux Q f properStride rawCap remainingProper
        samples total current = Measure.dirac none := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples total current hlt
      cases samples with
      | zero => simp at hlt
      | succ samples => simp only [cappedImportanceCollectLawAux]
  | succ rawCap ih =>
      intro remainingProper samples total current hlt
      cases samples with
      | zero => simp at hlt
      | succ samples =>
          have hlt' : rawCap < samples + 1 := by omega
          cases remainingProper with
          | zero =>
              simp only [cappedImportanceCollectLawAux]
              exact ih properStride samples (total + f current) current (by omega)
          | succ remainingProper =>
              simp only [cappedImportanceCollectLawAux]
              have hbranch : ∀ result : Bool × S,
                  (if result.1 then
                    match remainingProper with
                    | 0 => cappedImportanceCollectLawAux Q f properStride
                        rawCap 0 (samples + 1) total result.2
                    | nextRemaining + 1 =>
                        cappedImportanceCollectLawAux Q f properStride rawCap
                          (nextRemaining + 1) (samples + 1) total result.2
                  else cappedImportanceCollectLawAux Q f properStride rawCap
                    (remainingProper + 1) (samples + 1) total result.2) =
                    Measure.dirac none := by
                rintro ⟨mark, state⟩
                cases mark <;> simp only [Bool.false_eq_true, if_false, if_true]
                · exact ih (remainingProper + 1) (samples + 1) total state hlt'
                · cases remainingProper with
                  | zero => exact ih 0 (samples + 1) total state hlt'
                  | succ nextRemaining =>
                      exact ih (nextRemaining + 1) (samples + 1) total state hlt'
              simp_rw [hbranch]
              rw [Measure.bind_const, measure_univ, one_smul]

/-- Reserving exactly one raw operation for every requested observation
makes the importance collector identical to the established proper collector
with the remaining budget available for marked proposals. -/
theorem cappedImportanceCollectLawAux_add_samples_eq_cappedProperCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    (f : S → ℝ) (properStride : ℕ) :
    ∀ proposalCap remainingProper samples total current,
      cappedImportanceCollectLawAux Q f properStride
          (proposalCap + samples) remainingProper samples total current =
        cappedProperCollectLawAux Q f properStride proposalCap
          remainingProper samples total current := by
  intro proposalCap
  induction proposalCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          simp only [Nat.add_zero, cappedImportanceCollectLawAux,
            cappedProperCollectLawAux]
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              rw [show 0 + (samples + 1) = samples + 1 by omega]
              simp only [cappedImportanceCollectLawAux,
                cappedProperCollectLawAux]
              simpa only [Nat.zero_add] using
                ihSamples properStride (total + f current) current
          | succ remainingProper =>
              rw [show 0 + (samples + 1) = samples + 1 by omega]
              simp only [cappedImportanceCollectLawAux,
                cappedProperCollectLawAux]
              have hbranch : ∀ result : Bool × S,
                  (if result.1 then
                    match remainingProper with
                    | 0 => cappedImportanceCollectLawAux Q f properStride
                        samples 0 (samples + 1) total result.2
                    | nextRemaining + 1 =>
                        cappedImportanceCollectLawAux Q f properStride samples
                          (nextRemaining + 1) (samples + 1) total result.2
                  else cappedImportanceCollectLawAux Q f properStride samples
                    (remainingProper + 1) (samples + 1) total result.2) =
                    Measure.dirac none := by
                rintro ⟨mark, state⟩
                cases mark <;>
                  simp only [Bool.false_eq_true, if_false, if_true]
                · apply cappedImportanceCollectLawAux_eq_dirac_none_of_lt_samples
                  omega
                · cases remainingProper with
                  | zero =>
                      apply cappedImportanceCollectLawAux_eq_dirac_none_of_lt_samples
                      omega
                  | succ nextRemaining =>
                      apply cappedImportanceCollectLawAux_eq_dirac_none_of_lt_samples
                      omega
              simp_rw [hbranch]
              rw [Measure.bind_const, measure_univ, one_smul]
  | succ proposalCap ih =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          simp only [Nat.add_zero, cappedImportanceCollectLawAux,
            cappedProperCollectLawAux]
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              rw [show proposalCap + 1 + (samples + 1) =
                (proposalCap + 1 + samples) + 1 by omega]
              rw [cappedImportanceCollectLawAux, cappedProperCollectLawAux]
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ihSamples properStride (total + f current) current
          | succ remainingProper =>
              rw [show proposalCap + 1 + (samples + 1) =
                (proposalCap + samples + 1) + 1 by omega]
              rw [cappedImportanceCollectLawAux, cappedProperCollectLawAux]
              apply Measure.bind_congr_right
              filter_upwards with result
              by_cases hmark : result.1 = true
              · simp only [hmark, if_true]
                cases remainingProper with
                | zero =>
                    change cappedImportanceCollectLawAux Q f properStride
                        (proposalCap + samples + 1) 0 (samples + 1) total result.2 =
                      cappedProperCollectLawAux Q f properStride proposalCap
                        properStride samples (total + f result.2) result.2
                    rw [show proposalCap + samples + 1 =
                      proposalCap + (samples + 1) by omega]
                    rw [ih 0 (samples + 1) total result.2]
                    rw [cappedProperCollectLawAux]
                | succ nextRemaining =>
                    simpa only [Nat.add_assoc] using
                      ih (nextRemaining + 1) (samples + 1) total result.2
              · have hfalse : result.1 = false :=
                  Bool.eq_false_of_not_eq_true hmark
                simp only [hfalse, Bool.false_eq_true, if_false]
                simpa only [Nat.add_assoc] using
                  ih (remainingProper + 1) (samples + 1) total result.2

theorem cappedImportanceCollectLaw_add_samples_eq_cappedProperCollectLaw
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    (f : S → ℝ) (proposalCap properStride samples : ℕ) (current : S) :
    cappedImportanceCollectLaw Q f (proposalCap + samples) properStride
        samples current =
      cappedProperCollectLaw Q f proposalCap properStride samples current :=
  cappedImportanceCollectLawAux_add_samples_eq_cappedProperCollectLawAux
    Q f properStride proposalCap properStride samples 0 current

/-- Exact semantics of the executable importance collector. -/
theorem cappedAccuracyProperCollectWeightsAux_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples state.1 state.2).runEstimate oracle.query) ∧
    (∀ total current,
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).StronglyMeasurable
          oracle.query) ∧
    (∀ total current,
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).runEstimate oracle.query =
      cappedImportanceCollectLawAux
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyImportanceWeight q I sigma2 weight) properStride rawCap
          remainingProper samples total current) := by
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
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedImportanceCollectLawAux]
      | succ samples =>
          constructor
          · simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp measurable_const
          constructor
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedImportanceCollectLawAux]
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedImportanceCollectLawAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              let next (total : ℝ) (current : AmbientSpace q.n) (observed : ℝ) :=
                cappedAccuracyProperCollectWeightsAux q sigma2 weight
                  properStride rawCap properStride samples (total + observed) current
              let nextLaw (total : ℝ) (current : AmbientSpace q.n) (observed : ℝ) :=
                cappedImportanceCollectLawAux Q f properStride rawCap
                  properStride samples (total + observed) current
              have hnextStrong : ∀ total current observed,
                  (next total current observed).StronglyMeasurable oracle.query := by
                intro total current observed
                exact (ih properStride samples).2.1 _ _
              have hnextEq : ∀ total current observed,
                  (next total current observed).runEstimate oracle.query =
                    nextLaw total current observed := by
                intro total current observed
                exact (ih properStride samples).2.2 _ _
              have hnextLawMeasurable : ∀ total current,
                  Measurable (nextLaw total current) := by
                intro total current
                exact (cappedImportanceCollectLawAux_measurable_and_probability
                  Q hf properStride rawCap properStride samples).1.comp <|
                    (measurable_const.add measurable_id).prodMk measurable_const
              have hnextRun : ∀ total current,
                  Measurable fun observed =>
                    (next total current observed).runEstimate oracle.query := by
                intro total current
                rw [show (fun observed =>
                    (next total current observed).runEstimate oracle.query) =
                  nextLaw total current by
                    funext observed
                    exact hnextEq total current observed]
                exact hnextLawMeasurable total current
              have hsemantic : ∀ total current,
                  (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride (rawCap + 1) 0 (samples + 1)
                    total current).runEstimate oracle.query =
                  cappedImportanceCollectLawAux Q f properStride
                    (rawCap + 1) 0 (samples + 1) total current := by
                intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total current)
                  (accuracyImportanceObservation_stronglyMeasurable
                    q I oracle sigma2 weight current)
                  (hnextStrong total current) (hnextRun total current)]
                rw [runEstimate_accuracyImportanceObservation
                  q I oracle sigma2 weight current]
                simp_rw [hnextEq total current]
                rw [Measure.dirac_bind (hnextLawMeasurable total current)]
                rw [cappedImportanceCollectLawAux]
              constructor
              · rw [show (fun state : ℝ × AmbientSpace q.n =>
                    (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                      properStride (rawCap + 1) 0 (samples + 1)
                      state.1 state.2).runEstimate oracle.query) =
                  fun state => cappedImportanceCollectLawAux Q f properStride
                    (rawCap + 1) 0 (samples + 1) state.1 state.2 by
                    funext state
                    exact hsemantic state.1 state.2]
                exact (cappedImportanceCollectLawAux_measurable_and_probability
                  Q hf properStride (rawCap + 1) 0 (samples + 1)).1
              constructor
              · intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                exact (accuracyImportanceObservation_stronglyMeasurable
                  q I oracle sigma2 weight current).bind
                    (hnextStrong total current) (hnextRun total current)
              · exact hsemantic
          | succ remainingProper =>
              let next (total : ℝ) : Bool × AmbientSpace q.n →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 =>
                      cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap 0 (samples + 1) total result.2
                  | nextRemaining + 1 =>
                      cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap (nextRemaining + 1) (samples + 1)
                          total result.2
                else
                  cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride rawCap (remainingProper + 1) (samples + 1)
                      total result.2
              let nextLaw (total : ℝ) : Bool × AmbientSpace q.n →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 =>
                      cappedImportanceCollectLawAux Q f properStride rawCap 0
                        (samples + 1) total result.2
                  | nextRemaining + 1 =>
                      cappedImportanceCollectLawAux Q f properStride rawCap
                        (nextRemaining + 1) (samples + 1) total result.2
                else
                  cappedImportanceCollectLawAux Q f properStride rawCap
                    (remainingProper + 1) (samples + 1) total result.2
              have hnextStrong : ∀ total result,
                  (next total result).StronglyMeasurable oracle.query := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1)
                    (samples + 1)).2.1 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih 0 (samples + 1)).2.1 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1)
                          (samples + 1)).2.1 _ _
              have hnextEq : ∀ total result,
                  (next total result).runEstimate oracle.query =
                    nextLaw total result := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1)
                    (samples + 1)).2.2 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih 0 (samples + 1)).2.2 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1)
                          (samples + 1)).2.2 _ _
              have hnextLawMeasurable : ∀ total,
                  Measurable (nextLaw total) := by
                intro total
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (cappedImportanceCollectLawAux_measurable_and_probability
                        Q hf properStride rawCap 0 (samples + 1)).1.comp <|
                          measurable_const.prodMk measurable_snd
                  | succ nextRemaining =>
                      exact (cappedImportanceCollectLawAux_measurable_and_probability
                        Q hf properStride rawCap (nextRemaining + 1)
                          (samples + 1)).1.comp <|
                            measurable_const.prodMk measurable_snd
                · exact (cappedImportanceCollectLawAux_measurable_and_probability
                    Q hf properStride rawCap (remainingProper + 1)
                      (samples + 1)).1.comp <|
                        measurable_const.prodMk measurable_snd
              have hnextRun : ∀ total, Measurable fun result =>
                  (next total result).runEstimate oracle.query := by
                intro total
                rw [show (fun result =>
                    (next total result).runEstimate oracle.query) =
                  nextLaw total by
                    funext result
                    exact hnextEq total result]
                exact hnextLawMeasurable total
              have hsemantic : ∀ total current,
                  (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1) total current).runEstimate oracle.query =
                  cappedImportanceCollectLawAux Q f properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                      total current := by
                intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                change ((accuracyMetropolisMarkedBallStep q sigma2 current).bind
                    (next total)).runEstimate oracle.query = _
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total)
                  (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                    q I oracle sigma2 current)
                  (hnextStrong total) (hnextRun total)]
                rw [runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
                  q I oracle hsigma2 current]
                simp_rw [hnextEq total]
                change (Q current).bind (nextLaw total) = _
                rw [cappedImportanceCollectLawAux]
              constructor
              · rw [show (fun state : ℝ × AmbientSpace q.n =>
                    (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                      properStride (rawCap + 1) (remainingProper + 1)
                      (samples + 1) state.1 state.2).runEstimate oracle.query) =
                  fun state => cappedImportanceCollectLawAux Q f properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                      state.1 state.2 by
                    funext state
                    exact hsemantic state.1 state.2]
                exact (cappedImportanceCollectLawAux_measurable_and_probability
                  Q hf properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1)).1
              constructor
              · intro total current
                simp only [cappedAccuracyProperCollectWeightsAux]
                exact (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                  q I oracle sigma2 current).bind
                    (hnextStrong total) (hnextRun total)
              · exact hsemantic

/-- Public zero-initialized executable-law identity. -/
theorem cappedAccuracyProperCollectWeights_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) :
    (Measurable fun current =>
      (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
        samples current).runEstimate oracle.query) ∧
    (∀ current,
      (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
        samples current).StronglyMeasurable oracle.query) ∧
    (∀ current,
      (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
        samples current).runEstimate oracle.query =
      cappedImportanceCollectLaw
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyImportanceWeight q I sigma2 weight) rawCap properStride
          samples current) := by
  have h := cappedAccuracyProperCollectWeightsAux_semantics
    q I oracle hsigma2 hweight properStride rawCap properStride samples
  constructor
  · exact h.1.comp (measurable_const.prodMk measurable_id)
  constructor
  · intro current
    exact h.2.1 0 current
  · intro current
    exact h.2.2 0 current

/-- With one query reserved per observation, the executable phase has exactly
the previously analyzed capped proper-speedy law. -/
theorem cappedAccuracyProperCollectWeights_add_samples_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap + samples) properStride samples current).runEstimate
          oracle.query =
      cappedProperCollectLaw
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyImportanceWeight q I sigma2 weight) proposalCap properStride
          samples current := by
  rw [(cappedAccuracyProperCollectWeights_semantics q I oracle hsigma2 hweight
    (proposalCap + samples) properStride samples).2.2 current]
  exact cappedImportanceCollectLaw_add_samples_eq_cappedProperCollectLaw
    _ _ proposalCap properStride samples current

/-- Accuracy-phase specialization of the paper's one-half average-local-
conductance cutoff bound. -/
theorem half_mul_natCast_mul_bind_accuracyCappedProperCollectLaw_none_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ℝ≥0∞} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properStride samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (rawCap : ℝ≥0∞) *
        (mu.bind fun current => cappedProperCollectLaw
          (Arlib.MarkovChains.lazyProperProposalGaussianAux
            (accuracyPhaseTruncatedBody q I sigma2)
            (accuracyPhaseTruncatedBody_measurable q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2)
          weight rawCap properStride samples current) {none} ≤
      ((properStride * samples : ℕ) : ℝ≥0∞) * M := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux K
    (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
  have hK : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hKc : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKcompact : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have hKb : Bornology.IsBounded K := hKcompact.isBounded
  have hK0 : volume K ≠ 0 :=
    accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hZ0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      hK hKc hKb hK0 hdelta sigma2
  have hZtop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  have hlambda : ENNReal.ofReal (1 / 2) *
      (∫⁻ x in K, Arlib.MarkovChains.gaussianWeight sigma2 x) ≤
        Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ := by
    simpa [K, delta] using
      half_mul_gaussianWeight_le_accuracyPhaseEllGaussian q I hsigma2
  have hcollect : Measurable fun current =>
      cappedProperCollectLaw Q weight rawCap properStride samples current := by
    unfold cappedProperCollectLaw
    exact (cappedProperCollectLawAux_measurable_and_probability
      Q hweight properStride rawCap properStride samples).1.comp
        (measurable_const.prodMk measurable_id)
  have hmarked : Measurable fun current =>
      cappedProperMarkedLaw Q rawCap (properStride * samples) current :=
    measurable_cappedProperMarkedLaw Q rawCap (properStride * samples)
  have hfailure : (mu.bind fun current =>
        cappedProperCollectLaw Q weight rawCap properStride samples current) {none} =
      (mu.bind fun current =>
        cappedProperMarkedLaw Q rawCap (properStride * samples) current) {none} := by
    rw [Measure.bind_apply measurableSet_option_none hcollect.aemeasurable,
      Measure.bind_apply measurableSet_option_none hmarked.aemeasurable]
    apply lintegral_congr
    intro current
    exact cappedProperCollectLaw_none_eq_cappedProperMarkedLaw_none
      Q hweight rawCap properStride samples current
  change ENNReal.ofReal (1 / 2) * (rawCap : ℝ≥0∞) *
      (mu.bind fun current => cappedProperCollectLaw Q weight rawCap
        properStride samples current) {none} ≤ _
  rw [hfailure]
  exact Arlib.MarkovChains.mul_natCast_mul_bind_cappedLazyProperMarkedLaw_none_le
    K hK hKc hKb hK0 hdelta sigma2 hZ0 hZtop hlambda hwarm rawCap
      (properStride * samples)

/-- The same cutoff inequality for the actual oracle program, after accounting
for its one observation query per sample. -/
theorem half_mul_natCast_mul_bind_accuracyImportanceProgram_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ℝ≥0∞} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (proposalCap properStride samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (proposalCap : ℝ≥0∞) *
        (mu.bind fun current =>
          (cappedAccuracyProperCollectWeights q sigma2 weight
            (proposalCap + samples) properStride samples current).runEstimate
              oracle.query) {none} ≤
      ((properStride * samples : ℕ) : ℝ≥0∞) * M := by
  have hlaw : (fun current =>
        (cappedAccuracyProperCollectWeights q sigma2 weight
          (proposalCap + samples) properStride samples current).runEstimate
            oracle.query) =
      fun current => cappedProperCollectLaw
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyImportanceWeight q I sigma2 weight) proposalCap properStride
          samples current := by
    funext current
    exact cappedAccuracyProperCollectWeights_add_samples_semantics
      q I oracle hsigma2 hweight proposalCap properStride samples current
  rw [hlaw]
  exact half_mul_natCast_mul_bind_accuracyCappedProperCollectLaw_none_le
    q I hsigma2 (measurable_accuracyImportanceWeight q I sigma2 hweight)
      hwarm proposalCap properStride samples

end ArlibCommunity.Algorithms.CV18
