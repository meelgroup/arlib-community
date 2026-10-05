/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedBaseCounted

/-!
# Local proposal caps are invisible below the global cutoff

The finite balanced syntax uses a local raw-proposal counter solely to make
each retry structurally finite.  CV18 instead stops the complete execution at
one global query budget.  This file records the basic operational prefix fact:
two local caps larger than the remaining outer budget give exactly the same
globally capped proper collector.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Counted pointwise measurability also supplies the estimate-only
pointwise measurability needed by the ordinary interpreter laws. -/
theorem MembershipOracleProgram.CountedStronglyMeasurable.stronglyMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {oracle : AmbientSpace n → Bool}
    {program : MembershipOracleProgram n Result}
    (h : program.CountedStronglyMeasurable oracle) :
    program.StronglyMeasurable oracle := by
  induction program with
  | pure => trivial
  | query point next ih => exact ih (oracle point) h
  | randomNat law next ih =>
      constructor
      · rw [show (fun seed => (next seed).runEstimate oracle) =
            fun seed => ((next seed).run oracle).map Prod.fst by
          funext seed
          exact MembershipOracleProgram.runEstimate_eq_map_fst_run
            oracle (next seed) (h.2 seed).executionMeasurable]
        exact (Measure.measurable_map _ measurable_fst).comp h.1
      · exact fun seed => ih seed (h.2 seed)
  | randomPoint law hprob next ih =>
      constructor
      · rw [show (fun point => (next point).runEstimate oracle) =
            fun point => ((next point).run oracle).map Prod.fst by
          funext point
          exact MembershipOracleProgram.runEstimate_eq_map_fst_run
            oracle (next point) (h.2 point).executionMeasurable]
        exact (Measure.measurable_map _ measurable_fst).comp h.1
      · exact fun point => ih point (h.2 point)
  | randomReal law hprob next ih =>
      constructor
      · rw [show (fun value => (next value).runEstimate oracle) =
            fun value => ((next value).run oracle).map Prod.fst by
          funext value
          exact MembershipOracleProgram.runEstimate_eq_map_fst_run
            oracle (next value) (h.2 value).executionMeasurable]
        exact (Measure.measurable_map _ measurable_fst).comp h.1
      · exact fun value => ih value (h.2 value)

/-- A counted-measurable program remains estimate-measurable after installing
an arbitrary global query cutoff. -/
theorem MembershipOracleProgram.CountedStronglyMeasurable.withQueryCap_stronglyMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {oracle : AmbientSpace n → Bool}
    {program : MembershipOracleProgram n Result}
    (h : program.CountedStronglyMeasurable oracle) (budget : ℕ) :
    (program.withQueryCap budget).StronglyMeasurable oracle := by
  induction program generalizing budget with
  | pure => trivial
  | query point next ih =>
      cases budget with
      | zero => trivial
      | succ budget => exact ih (oracle point) h budget
  | randomNat law next ih =>
      constructor
      · rw [show (fun seed => (next seed).withQueryCap budget |>.runEstimate oracle) =
            fun seed => ((next seed).run oracle).map (queryCapOutcome budget) by
          funext seed
          exact MembershipOracleProgram.runEstimate_withQueryCap oracle
            (next seed) budget (h.2 seed).executionMeasurable]
        exact (Measure.measurable_map _ (measurable_queryCapOutcome budget)).comp h.1
      · exact fun seed => ih seed (h.2 seed) budget
  | randomPoint law hprob next ih =>
      constructor
      · rw [show (fun point => (next point).withQueryCap budget |>.runEstimate oracle) =
            fun point => ((next point).run oracle).map (queryCapOutcome budget) by
          funext point
          exact MembershipOracleProgram.runEstimate_withQueryCap oracle
            (next point) budget (h.2 point).executionMeasurable]
        exact (Measure.measurable_map _ (measurable_queryCapOutcome budget)).comp h.1
      · exact fun point => ih point (h.2 point) budget
  | randomReal law hprob next ih =>
      constructor
      · rw [show (fun value => (next value).withQueryCap budget |>.runEstimate oracle) =
            fun value => ((next value).run oracle).map (queryCapOutcome budget) by
          funext value
          exact MembershipOracleProgram.runEstimate_withQueryCap oracle
            (next value) budget (h.2 value).executionMeasurable]
        exact (Measure.measurable_map _ (measurable_queryCapOutcome budget)).comp h.1
      · exact fun value => ih value (h.2 value) budget

/-- A syntax-level query bound is exactly strong enough for the outer cap to
leave every execution branch intact. -/
theorem MembershipOracleProgram.QueryBound.withQueryCap_eq
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {budget : ℕ} (h : program.QueryBound budget) :
    program.withQueryCap budget =
      program.bind fun result => .pure (some result) := by
  induction h with
  | pure result budget => rfl
  | query point next budget hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.bind]
      congr 1
      funext answer
      exact ih answer
  | randomNat law next budget hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.bind]
      congr 1
      funext seed
      exact ih seed
  | randomPoint law hprob next budget hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.bind]
      congr 1
      funext point
      exact ih point
  | randomReal law hprob next budget hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.bind]
      congr 1
      funext value
      exact ih value

/-- A structural query bound also bounds the expectation of the interpreter's
actual query counter. -/
theorem MembershipOracleProgram.QueryBound.lintegral_queryCount_le
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {oracle : AmbientSpace n → Bool}
    {program : MembershipOracleProgram n Result} {budget : ℕ}
    (hbound : program.QueryBound budget)
    (hmeas : program.CountedStronglyMeasurable oracle) :
    ∫⁻ outcome, (outcome.2 : ENNReal) ∂(program.run oracle) ≤
      (budget : ENNReal) := by
  have hstrong := hmeas.stronglyMeasurable
  have hnone : (program.withQueryCap budget).runEstimate oracle {none} = 0 := by
    rw [hbound.withQueryCap_eq]
    rw [MembershipOracleProgram.runEstimate_bind oracle program _ hstrong
      (fun _ => by trivial)]
    · simp only [MembershipOracleProgram.runEstimate]
      rw [Measure.bind_dirac_eq_map _ measurable_some,
        Measure.map_apply measurable_some measurableSet_queryCap_none]
      rw [show some ⁻¹' ({none} : Set (Option Result)) = ∅ by
        ext result
        simp]
      exact measure_empty
    · simp only [MembershipOracleProgram.runEstimate]
      exact Measure.measurable_dirac.comp measurable_some
  have hlarge : program.run oracle {outcome | budget < outcome.2} = 0 := by
    rw [← MembershipOracleProgram.runEstimate_withQueryCap_apply_none
      oracle program budget hmeas.executionMeasurable]
    exact hnone
  have hae : ∀ᵐ outcome ∂(program.run oracle), outcome.2 ≤ budget := by
    rw [ae_iff]
    simpa only [not_le] using hlarge
  have hae' : ∀ᵐ outcome ∂(program.run oracle),
      (outcome.2 : ENNReal) ≤ (budget : ENNReal) :=
    hae.mono fun outcome hout => by exact_mod_cast hout
  calc
    ∫⁻ outcome, (outcome.2 : ENNReal) ∂(program.run oracle) ≤
        ∫⁻ _outcome, (budget : ENNReal) ∂(program.run oracle) :=
      lintegral_mono_ae hae'
    _ = (budget : ENNReal) := by
      let _ : IsProbabilityMeasure (program.run oracle) :=
        MembershipOracleProgram.run_isProbabilityMeasure oracle program
          hmeas.executionMeasurable
      simp

/-- An outer query cutoff cannot observe the precise value of a larger local
raw-proposal cap. -/
theorem cappedAccuracyProperCollectWeightsAux_withQueryCap_eq_of_lt
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ budget rawCap₁ rawCap₂ remainingProper samples total current,
      budget < rawCap₁ → budget < rawCap₂ →
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap₁ remainingProper samples total current).withQueryCap budget =
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap₂ remainingProper samples total current).withQueryCap budget := by
  intro budget
  induction budget with
  | zero =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      cases samples with
      | zero =>
          simp only [cappedAccuracyProperCollectWeightsAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind,
                MembershipOracleProgram.withQueryCap]
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyMetropolisMarkedBallStep,
                accuracyMetropolisMarkedProposalProgram,
                MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
  | succ budget ih =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      have hcap₁' : budget < rawCap₁ := by omega
      have hcap₂' : budget < rawCap₂ := by omega
      cases samples with
      | zero =>
          simp only [cappedAccuracyProperCollectWeightsAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind,
                MembershipOracleProgram.withQueryCap]
              congr 1
              funext inside
              exact ih rawCap₁ rawCap₂ properStride samples
                (total + if inside = true ∧
                    ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
                      Real.sqrt (terminalVariance q) ∧
                    ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
                      accuracyPhaseRadius q sigma2 then
                    (Arlib.MarkovChains.gaussianScaleAcceptance sigma2
                      (accuracyScaleFactor q)
                      ((accuracyScaleFactor q)⁻¹ • current)).toReal *
                        weight ((accuracyScaleFactor q)⁻¹ • current)
                  else 0) current hcap₁' hcap₂'
          | succ remainingProper =>
              cases remainingProper with
              | zero =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind,
                    MembershipOracleProgram.withQueryCap]
                  congr 1
                  funext proposal
                  congr 1
                  funext inside
                  congr 1
                  funext coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption
              | succ nextRemaining =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind,
                    MembershipOracleProgram.withQueryCap]
                  congr 1
                  funext proposal
                  congr 1
                  funext inside
                  congr 1
                  funext coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption

/-- In particular, the concrete local cap `B + 1` is indistinguishable from
any still larger cap under the one outer budget `B`. -/
theorem cappedAccuracyProperCollectWeightsAux_globalPrefix
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride budget extra : ℕ)
    (remainingProper samples : ℕ) (total : ℝ)
    (current : AmbientSpace q.n) :
    (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
      (budget + 1) remainingProper samples total current).withQueryCap budget =
    (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
      (budget + 1 + extra) remainingProper samples total current).withQueryCap
        budget := by
  apply cappedAccuracyProperCollectWeightsAux_withQueryCap_eq_of_lt
  · omega
  · omega

/-- The concrete finite base syntax inherits the generic structural expected
cost bound.  This bound is deliberately not used for CV18's final rate: its
local finiteness cap contains the global budget and must first be erased by
the prefix theorem above. -/
theorem figureOneGlobalBalancedBaseProgram_lintegral_queryCount_le_structural
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∫⁻ outcome, (outcome.2 : ENNReal)
        ∂((figureOneGlobalBalancedBaseProgram q).run oracle.query) ≤
      (balancedFigureOneBaseQueryBudget figureOneGlobalBalancedParameters q :
        ENNReal) := by
  apply MembershipOracleProgram.QueryBound.lintegral_queryCount_le
  · exact balancedFigureOneBaseVolumeCooling_queryBound
      figureOneGlobalBalancedParameters q
  · exact figureOneGlobalBalancedBaseProgram_countedStronglyMeasurable
      q I oracle

/-- Real-valued base program used by the generic median amplifier: a global
cutoff failure is represented by the harmless default value zero. -/
noncomputable def figureOneGloballyCappedBalancedBaseValueProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  (figureOneGloballyCappedBalancedBaseProgram q).bind fun estimate =>
    .pure (estimate.getD 0)

theorem measurable_optionGetD_zero :
    Measurable fun estimate : Option ℝ => estimate.getD 0 := by
  convert Measurable.optionElim (0 : ℝ) measurable_id using 1
  funext estimate
  cases estimate <;> rfl

theorem figureOneGloballyCappedBalancedBaseValueProgram_queryBound
    (q : VolumeParams) :
    (figureOneGloballyCappedBalancedBaseValueProgram q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  unfold figureOneGloballyCappedBalancedBaseValueProgram
  exact (figureOneGloballyCappedBalancedBaseProgram_queryBound q).bind
    fun _ => .pure _ 0

theorem figureOneGloballyCappedBalancedBaseValueProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneGloballyCappedBalancedBaseValueProgram q).StronglyMeasurable
      oracle.query := by
  have hcapped :=
    (figureOneGlobalBalancedBaseProgram_countedStronglyMeasurable
      q I oracle).withQueryCap_stronglyMeasurable
        (figureOneGlobalQueryBudget q)
  unfold figureOneGloballyCappedBalancedBaseValueProgram
  apply hcapped.bind (fun _ => by trivial)
  simp only [MembershipOracleProgram.runEstimate]
  exact Measure.measurable_dirac.comp measurable_optionGetD_zero

end ArlibCommunity.Algorithms.CV18
