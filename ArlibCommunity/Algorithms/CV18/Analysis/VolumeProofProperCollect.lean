/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperFailure

/-! # A globally capped proper-step collector for CV18 Figure 1 -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Consume one shared raw-proposal budget while recording a weight after
every `properStride` proper proposals.  This is the finite executable shape
of Figure 1, which specifies its mixing deadline in proper steps and applies
one global raw-step cutoff. -/
noncomputable def cappedProperCollectWeightsAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, _, 0, total, current => .pure (some (total, current))
  | rawCap, 0, samples + 1, total, current =>
      cappedProperCollectWeightsAux q sigma2 weight properStride
        rawCap properStride samples (total + weight current) current
  | 0, _ + 1, _ + 1, _, _ => .pure none
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (truncatedMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        if result.1 then
          match remainingProper with
          | 0 =>
              cappedProperCollectWeightsAux q sigma2 weight properStride
                rawCap properStride samples (total + weight result.2) result.2
          | nextRemaining + 1 =>
              cappedProperCollectWeightsAux q sigma2 weight properStride
                rawCap (nextRemaining + 1) (samples + 1) total result.2
        else
          cappedProperCollectWeightsAux q sigma2 weight properStride
            rawCap (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

/-- Public zero-initialized proper-step collector. -/
noncomputable def cappedProperCollectWeights (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedProperCollectWeightsAux q sigma2 weight properStride
    rawCap properStride samples 0 current

/-- Measure-level counterpart of the globally capped collector. -/
noncomputable def cappedProperCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) (f : S → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → S → Measure (Option (ℝ × S))
  | _, _, 0, total, current => Measure.dirac (some (total, current))
  | rawCap, 0, samples + 1, total, current =>
      cappedProperCollectLawAux Q f properStride rawCap properStride samples
        (total + f current) current
  | 0, _ + 1, _ + 1, _, _ => Measure.dirac none
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (Q current).bind fun result =>
        if result.1 then
          match remainingProper with
          | 0 =>
              cappedProperCollectLawAux Q f properStride rawCap properStride samples
                (total + f result.2) result.2
          | nextRemaining + 1 =>
              cappedProperCollectLawAux Q f properStride rawCap (nextRemaining + 1)
                (samples + 1) total result.2
        else
          cappedProperCollectLawAux Q f properStride rawCap (remainingProper + 1)
            (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedProperCollectLaw
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) (f : S → ℝ)
    (rawCap properStride samples : ℕ) (current : S) :
    Measure (Option (ℝ × S)) :=
  cappedProperCollectLawAux Q f properStride
    rawCap properStride samples 0 current

/-- Number of further proper proposals requested by a collector state. -/
def properProposalsNeeded (properStride remainingProper samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | samples + 1 => remainingProper + properStride * samples

/-- The abstract capped collector is a measurable probability kernel in its
running sum and current state. -/
theorem cappedProperCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    {f : S → ℝ} (hf : Measurable f) (properStride : ℕ) :
    ∀ rawCap remainingProper samples,
      Measurable (fun p : ℝ × S =>
        cappedProperCollectLawAux Q f properStride rawCap remainingProper samples
          p.1 p.2) ∧
      ∀ total current, IsProbabilityMeasure
        (cappedProperCollectLawAux Q f properStride rawCap remainingProper samples
          total current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          simp only [cappedProperCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            change IsProbabilityMeasure (Measure.dirac (some (total, current)))
            infer_instance
      | succ samples ihSamples =>
          cases remainingProper with
          | zero =>
              have ih := ihSamples properStride
              simp only [cappedProperCollectLawAux]
              constructor
              · exact ih.1.comp <|
                  (measurable_fst.add (hf.comp measurable_snd)).prodMk measurable_snd
              · intro total current
                exact ih.2 (total + f current) current
          | succ remainingProper =>
              simp only [cappedProperCollectLawAux]
              constructor
              · exact Measure.measurable_dirac.comp measurable_const
              · intro total current
                change IsProbabilityMeasure (Measure.dirac none)
                infer_instance
  | succ rawCap ih =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          simp only [cappedProperCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            change IsProbabilityMeasure (Measure.dirac (some (total, current)))
            infer_instance
      | succ samples ihSamples =>
          cases remainingProper with
          | zero =>
              have ih' := ihSamples properStride
              simp only [cappedProperCollectLawAux]
              constructor
              · exact ih'.1.comp <|
                  (measurable_fst.add (hf.comp measurable_snd)).prodMk measurable_snd
              · intro total current
                exact ih'.2 (total + f current) current
          | succ remainingProper =>
              let tail : (ℝ × S) → (Bool × S) →
                  Measure (Option (ℝ × S)) := fun state result =>
                if result.1 then
                  match remainingProper with
                  | 0 =>
                      cappedProperCollectLawAux Q f properStride rawCap properStride
                        samples (state.1 + f result.2) result.2
                  | nextRemaining + 1 =>
                      cappedProperCollectLawAux Q f properStride rawCap
                        (nextRemaining + 1) (samples + 1) state.1 result.2
                else
                  cappedProperCollectLawAux Q f properStride rawCap
                    (remainingProper + 1) (samples + 1) state.1 result.2
              have htail : Measurable fun p : (ℝ × S) × (Bool × S) =>
                  tail p.1 p.2 := by
                dsimp only [tail]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (ih properStride samples).1.comp <|
                        ((measurable_fst.comp measurable_fst).add
                          (hf.comp (measurable_snd.comp measurable_snd))).prodMk
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
                split_ifs with hmark
                · cases remainingProper with
                  | zero => exact (ih properStride samples).2 _ _
                  | succ nextRemaining =>
                      exact (ih (nextRemaining + 1) (samples + 1)).2 _ _
                · exact (ih (remainingProper + 1) (samples + 1)).2 _ _
              simp only [cappedProperCollectLawAux]
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

theorem properProposalsNeeded_self (properStride samples : ℕ) :
    properProposalsNeeded properStride properStride samples =
      properStride * samples := by
  cases samples <;>
    simp [properProposalsNeeded, Nat.mul_succ, Nat.add_comm]

/-- Exhausting the shared collector cap is exactly the same event as failing
to complete the corresponding total number of proper proposals. -/
theorem cappedProperCollectLawAux_none_eq_cappedProperMarkedLaw_none
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    {f : S → ℝ} (hf : Measurable f) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
    cappedProperCollectLawAux Q f properStride rawCap remainingProper samples
        total current {none} =
      cappedProperMarkedLaw Q rawCap
        (properProposalsNeeded properStride remainingProper samples) current {none} := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          simp only [cappedProperCollectLawAux, properProposalsNeeded,
            cappedProperMarkedLaw]
          rw [Measure.dirac_apply' _ measurableSet_option_none,
            Measure.dirac_apply' _ measurableSet_option_none]
          simp
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              have h := ihSamples properStride (total + f current) current
              rw [properProposalsNeeded_self] at h
              simpa only [cappedProperCollectLawAux, properProposalsNeeded,
                zero_add] using h
          | succ remainingProper =>
              rw [cappedProperCollectLawAux]
              rw [show properProposalsNeeded properStride (remainingProper + 1)
                    (samples + 1) =
                  (remainingProper + properStride * samples) + 1 by
                simp [properProposalsNeeded]; omega]
              rw [cappedProperMarkedLaw]
              rw [Measure.dirac_apply' _ measurableSet_option_none,
                Measure.dirac_apply' _ measurableSet_option_none]
              simp
  | succ rawCap ih =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          simp only [cappedProperCollectLawAux, properProposalsNeeded,
            cappedProperMarkedLaw]
          rw [Measure.dirac_apply' _ measurableSet_option_none,
            Measure.dirac_apply' _ measurableSet_option_none]
          simp
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              have h := ihSamples properStride (total + f current) current
              rw [properProposalsNeeded_self] at h
              simpa only [cappedProperCollectLawAux, properProposalsNeeded,
                zero_add] using h
          | succ remainingProper =>
              rw [cappedProperCollectLawAux]
              rw [show properProposalsNeeded properStride (remainingProper + 1)
                    (samples + 1) =
                  (remainingProper + properStride * samples) + 1 by
                simp [properProposalsNeeded]; omega]
              rw [cappedProperMarkedLaw]
              let L : Bool × S → Measure (Option (ℝ × S)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 => cappedProperCollectLawAux Q f properStride rawCap
                      properStride samples (total + f result.2) result.2
                  | nextRemaining + 1 => cappedProperCollectLawAux Q f properStride
                      rawCap (nextRemaining + 1) (samples + 1) total result.2
                else cappedProperCollectLawAux Q f properStride rawCap
                    (remainingProper + 1) (samples + 1) total result.2
              let R : Bool × S → Measure (Option S) := fun result =>
                cappedProperMarkedLaw Q rawCap
                  (if result.1 then remainingProper + properStride * samples
                    else remainingProper + properStride * samples + 1) result.2
              have hL : Measurable L := by
                dsimp only [L]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        Q hf properStride rawCap properStride samples).1.comp <|
                          (measurable_const.add (hf.comp measurable_snd)).prodMk
                            measurable_snd
                  | succ nextRemaining =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        Q hf properStride rawCap (nextRemaining + 1)
                          (samples + 1)).1.comp <|
                            measurable_const.prodMk measurable_snd
                · exact (cappedProperCollectLawAux_measurable_and_probability
                    Q hf properStride rawCap (remainingProper + 1)
                      (samples + 1)).1.comp <|
                        measurable_const.prodMk measurable_snd
              have hR : Measurable R := by
                rw [show R = fun result => if result.1 = true then
                    cappedProperMarkedLaw Q rawCap
                      (remainingProper + properStride * samples) result.2 else
                    cappedProperMarkedLaw Q rawCap
                      (remainingProper + properStride * samples + 1) result.2 by
                  funext result
                  rcases result with ⟨mark, state⟩
                  cases mark <;> rfl]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (measurable_cappedProperMarkedLaw Q rawCap
                    (remainingProper + properStride * samples)).comp measurable_snd
                · exact (measurable_cappedProperMarkedLaw Q rawCap
                    (remainingProper + properStride * samples + 1)).comp measurable_snd
              change (Q current).bind L {none} = (Q current).bind R {none}
              rw [Measure.bind_apply measurableSet_option_none hL.aemeasurable,
                Measure.bind_apply measurableSet_option_none hR.aemeasurable]
              apply lintegral_congr
              intro result
              dsimp only [L, R]
              by_cases hmark : result.1 = true
              · simp only [hmark, if_true]
                cases remainingProper with
                | zero =>
                    have h := ih properStride samples
                      (total + f result.2) result.2
                    rw [properProposalsNeeded_self] at h
                    simpa only [zero_add] using h
                | succ nextRemaining =>
                    simpa [properProposalsNeeded, Nat.add_assoc] using
                      ih (nextRemaining + 1) (samples + 1) total result.2
              · have hfalse : result.1 = false :=
                  Bool.eq_false_of_not_eq_true hmark
                simp only [hfalse]
                simpa [properProposalsNeeded, Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using
                  ih (remainingProper + 1) (samples + 1) total result.2

theorem cappedProperCollectLaw_none_eq_cappedProperMarkedLaw_none
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    {f : S → ℝ} (hf : Measurable f)
    (rawCap properStride samples : ℕ) (current : S) :
    cappedProperCollectLaw Q f rawCap properStride samples current {none} =
      cappedProperMarkedLaw Q rawCap (properStride * samples) current {none} := by
  unfold cappedProperCollectLaw
  rw [cappedProperCollectLawAux_none_eq_cappedProperMarkedLaw_none
    Q hf properStride, properProposalsNeeded_self]

/-- The paper's one-half average-conductance cutoff bound applies directly
to the shared collector cap, with the total requested proper steps equal to
`properStride * samples`. -/
theorem half_mul_natCast_mul_bind_cappedProperCollectLaw_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ℝ≥0∞} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properStride samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (rawCap : ℝ≥0∞) *
        (mu.bind fun current => cappedProperCollectLaw
          (Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
            (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
            sigma2)
          weight rawCap properStride samples current) {none} ≤
      ((properStride * samples : ℕ) : ℝ≥0∞) * M := by
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
    (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2) sigma2
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
      (mu.bind fun current => cappedProperCollectLaw Q weight rawCap properStride
        samples current) {none} ≤ _
  rw [hfailure]
  have hcap := half_mul_natCast_mul_cappedProperMetropolisBallWalk_none_le
    q I oracle hsigma2 hwarm rawCap (properStride * samples)
  have hlaw : (fun current =>
        (cappedProperMetropolisBallWalk q sigma2 rawCap
          (properStride * samples) current).runEstimate oracle.query) =
      fun current => cappedProperMarkedLaw Q rawCap
        (properStride * samples) current := by
    funext current
    exact (cappedProperMetropolisBallWalk_semantics
      q I oracle hsigma2 rawCap (properStride * samples)).2.2 current
  rw [hlaw] at hcap
  exact hcap

/-- The executable shared-cap collector realizes exactly its abstract marked
kernel law.  The measurability conjuncts make the result usable inside later
membership-oracle programs. -/
theorem cappedProperCollectWeightsAux_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (cappedProperCollectWeightsAux q sigma2 weight properStride rawCap
        remainingProper samples state.1 state.2).runEstimate oracle.query) ∧
    (∀ total current,
      (cappedProperCollectWeightsAux q sigma2 weight properStride rawCap
        remainingProper samples total current).StronglyMeasurable oracle.query) ∧
    (∀ total current,
      (cappedProperCollectWeightsAux q sigma2 weight properStride rawCap
        remainingProper samples total current).runEstimate oracle.query =
      cappedProperCollectLawAux
        (Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
          (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
          sigma2)
        weight properStride rawCap remainingProper samples total current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          constructor
          · simp only [cappedProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedProperCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate, cappedProperCollectLawAux]
      | succ samples ihSamples =>
          cases remainingProper with
          | zero =>
              have ih' := ihSamples properStride
              constructor
              · simp only [cappedProperCollectWeightsAux]
                exact ih'.1.comp <|
                  (measurable_fst.add (hweight.comp measurable_snd)).prodMk
                    measurable_snd
              constructor
              · intro total current
                simpa only [cappedProperCollectWeightsAux] using
                  ih'.2.1 (total + weight current) current
              · intro total current
                simpa only [cappedProperCollectWeightsAux,
                  cappedProperCollectLawAux] using
                    ih'.2.2 (total + weight current) current
          | succ remainingProper =>
              constructor
              · simp only [cappedProperCollectWeightsAux,
                  MembershipOracleProgram.runEstimate]
                exact Measure.measurable_dirac.comp measurable_const
              constructor
              · intro total current
                rw [cappedProperCollectWeightsAux]
                trivial
              · intro total current
                simp only [cappedProperCollectWeightsAux,
                  MembershipOracleProgram.runEstimate, cappedProperCollectLawAux]
  | succ rawCap ih =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          constructor
          · simp only [cappedProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedProperCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedProperCollectWeightsAux,
              MembershipOracleProgram.runEstimate, cappedProperCollectLawAux]
      | succ samples ihSamples =>
          cases remainingProper with
          | zero =>
              have ih' := ihSamples properStride
              constructor
              · simp only [cappedProperCollectWeightsAux]
                exact ih'.1.comp <|
                  (measurable_fst.add (hweight.comp measurable_snd)).prodMk
                    measurable_snd
              constructor
              · intro total current
                simpa only [cappedProperCollectWeightsAux] using
                  ih'.2.1 (total + weight current) current
              · intro total current
                simpa only [cappedProperCollectWeightsAux,
                  cappedProperCollectLawAux] using
                    ih'.2.2 (total + weight current) current
          | succ remainingProper =>
              let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
                (truncatedBody q I) (truncatedBody_measurable q I)
                (figureOneProposalRadius q sigma2) sigma2
              let next (total : ℝ) : Bool × AmbientSpace q.n →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 => cappedProperCollectWeightsAux q sigma2 weight properStride
                      rawCap properStride samples (total + weight result.2) result.2
                  | nextRemaining + 1 =>
                      cappedProperCollectWeightsAux q sigma2 weight properStride
                        rawCap (nextRemaining + 1) (samples + 1) total result.2
                else cappedProperCollectWeightsAux q sigma2 weight properStride
                  rawCap (remainingProper + 1) (samples + 1) total result.2
              let nextLaw (total : ℝ) : Bool × AmbientSpace q.n →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 => cappedProperCollectLawAux Q weight properStride rawCap
                      properStride samples (total + weight result.2) result.2
                  | nextRemaining + 1 =>
                      cappedProperCollectLawAux Q weight properStride rawCap
                        (nextRemaining + 1) (samples + 1) total result.2
                else cappedProperCollectLawAux Q weight properStride rawCap
                  (remainingProper + 1) (samples + 1) total result.2
              have hnextStrong : ∀ total result,
                  (next total result).StronglyMeasurable oracle.query := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1) (samples + 1)).2.1 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih properStride samples).2.1 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1) (samples + 1)).2.1 _ _
              have hnextEq : ∀ total result,
                  (next total result).runEstimate oracle.query =
                    nextLaw total result := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1) (samples + 1)).2.2 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih properStride samples).2.2 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1) (samples + 1)).2.2 _ _
              have hnextLawMeasurable : ∀ total,
                  Measurable (nextLaw total) := by
                intro total
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        Q hweight properStride rawCap properStride samples).1.comp <|
                          ((measurable_const.add
                            (hweight.comp measurable_snd)).prodMk measurable_snd)
                  | succ nextRemaining =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        Q hweight properStride rawCap (nextRemaining + 1)
                          (samples + 1)).1.comp <|
                            measurable_const.prodMk measurable_snd
                · exact (cappedProperCollectLawAux_measurable_and_probability
                    Q hweight properStride rawCap (remainingProper + 1)
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
                  (cappedProperCollectWeightsAux q sigma2 weight properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                    total current).runEstimate oracle.query =
                  cappedProperCollectLawAux Q weight properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                    total current := by
                intro total current
                have hstepStrong :=
                  truncatedMetropolisMarkedBallStep_stronglyMeasurable
                    q I oracle sigma2 current
                simp only [cappedProperCollectWeightsAux]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _ (next total)
                  hstepStrong (hnextStrong total) (hnextRun total)]
                rw [runEstimate_truncatedMetropolisMarkedBallStep_eq_lazyProperAux
                  q I oracle hsigma2 current]
                simp_rw [hnextEq total]
                change (Q current).bind (nextLaw total) = _
                rw [cappedProperCollectLawAux]
              constructor
              · have heq : (fun state : ℝ × AmbientSpace q.n =>
                    (cappedProperCollectWeightsAux q sigma2 weight properStride
                      (rawCap + 1) (remainingProper + 1) (samples + 1)
                      state.1 state.2).runEstimate oracle.query) =
                  fun state => cappedProperCollectLawAux Q weight properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                    state.1 state.2 := by
                    funext state
                    exact hsemantic state.1 state.2
                rw [heq]
                exact (cappedProperCollectLawAux_measurable_and_probability
                  Q hweight properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1)).1
              constructor
              · intro total current
                simp only [cappedProperCollectWeightsAux]
                exact (truncatedMetropolisMarkedBallStep_stronglyMeasurable
                  q I oracle sigma2 current).bind
                    (hnextStrong total) (hnextRun total)
              · exact hsemantic

/-- Public semantics theorem for the zero-initialized collector. -/
theorem cappedProperCollectWeights_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) :
    (Measurable fun current =>
      (cappedProperCollectWeights q sigma2 weight rawCap properStride samples
        current).runEstimate oracle.query) ∧
    (∀ current,
      (cappedProperCollectWeights q sigma2 weight rawCap properStride samples
        current).StronglyMeasurable oracle.query) ∧
    (∀ current,
      (cappedProperCollectWeights q sigma2 weight rawCap properStride samples
        current).runEstimate oracle.query =
      cappedProperCollectLaw
        (Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
          (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
          sigma2)
        weight rawCap properStride samples current) := by
  have h := cappedProperCollectWeightsAux_semantics q I oracle hsigma2 hweight
    properStride rawCap properStride samples
  constructor
  · exact h.1.comp (measurable_const.prodMk measurable_id)
  constructor
  · intro current
    exact h.2.1 0 current
  · intro current
    exact h.2.2 0 current

/-- The paper's cutoff estimate now holds for the failure output of the
actual shared-cap membership-oracle collector. -/
theorem half_mul_natCast_mul_bind_cappedProperCollectWeights_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ℝ≥0∞} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properStride samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          (cappedProperCollectWeights q sigma2 weight rawCap properStride samples
            current).runEstimate oracle.query) {none} ≤
      ((properStride * samples : ℕ) : ℝ≥0∞) * M := by
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
    (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2) sigma2
  have hlaw : (fun current =>
        (cappedProperCollectWeights q sigma2 weight rawCap properStride samples
          current).runEstimate oracle.query) =
      fun current => cappedProperCollectLaw Q weight rawCap properStride samples
        current := by
    funext current
    exact (cappedProperCollectWeights_semantics q I oracle hsigma2 hweight
      rawCap properStride samples).2.2 current
  rw [hlaw]
  exact half_mul_natCast_mul_bind_cappedProperCollectLaw_none_le
    q I oracle hsigma2 hweight hwarm rawCap properStride samples

/-- The shared cutoff is a genuine deterministic membership-query bound,
independent of how many improper proposals occur. -/
theorem cappedProperCollectWeightsAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
    (cappedProperCollectWeightsAux q sigma2 weight properStride
      rawCap remainingProper samples total current).QueryBound rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          rw [cappedProperCollectWeightsAux]
          exact .pure _ 0
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              simpa only [cappedProperCollectWeightsAux] using
                ihSamples properStride (total + weight current) current
          | succ remainingProper =>
              rw [cappedProperCollectWeightsAux]
              exact .pure _ 0
  | succ rawCap ih =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current
          rw [cappedProperCollectWeightsAux]
          exact .pure _ (rawCap + 1)
      | succ samples ihSamples =>
          intro total current
          cases remainingProper with
          | zero =>
              simpa only [cappedProperCollectWeightsAux] using
                ihSamples properStride (total + weight current) current
          | succ remainingProper =>
              simp only [cappedProperCollectWeightsAux]
              simpa [Nat.add_comm] using
                (truncatedMetropolisMarkedBallStep_queryBound
                  q sigma2 current).bind (fun result => by
                    by_cases hmark : result.1 = true
                    · simp only [hmark, if_true]
                      cases remainingProper with
                      | zero =>
                          exact ih properStride samples
                            (total + weight result.2) result.2
                      | succ nextRemaining =>
                          exact ih (nextRemaining + 1) (samples + 1) total result.2
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hmark
                      simp only [hfalse, if_false]
                      exact ih (remainingProper + 1) (samples + 1) total result.2)

theorem cappedProperCollectWeights_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (cappedProperCollectWeights q sigma2 weight rawCap properStride samples current).QueryBound
      rawCap :=
  cappedProperCollectWeightsAux_queryBound q sigma2 weight properStride
    rawCap properStride samples 0 current

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.cappedProperCollectWeights_queryBound
