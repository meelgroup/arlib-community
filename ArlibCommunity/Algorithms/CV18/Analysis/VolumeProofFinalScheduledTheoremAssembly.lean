/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedHybridCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCheapAbortCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGenericRateAmplification

/-! # Final assembly for the counted-reference scheduled executable

This file isolates the last soft-O amplification step for the final scheduled
CV18 program.  Unlike the older capstone, its cap-failure premise may be
discharged by a counted reference law rather than an unrestricted expected
cost bound for the actual program.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- The final scheduled aborting base program, guarded by the shared global
query cutoff and with cutoff failure represented by the harmless value zero. -/
noncomputable def figureOneFinalScheduledCappedValueProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
      (figureOneFinalScheduledQueryBudget q)).bind
    fun estimate => .pure (estimate.getD 0)

theorem figureOneFinalScheduledCappedValueProgram_queryBound
    (q : VolumeParams) :
    (figureOneFinalScheduledCappedValueProgram q).QueryBound
      (figureOneFinalScheduledQueryBudget q) := by
  unfold figureOneFinalScheduledCappedValueProgram
  exact ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap_queryBound
    (figureOneFinalScheduledQueryBudget q)).bind fun _ => .pure _ 0

theorem figureOneFinalScheduledCappedValueProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneFinalScheduledCappedValueProgram q).StronglyMeasurable
      oracle.query := by
  have hcapped :=
    (figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
      q I oracle).withQueryCap_stronglyMeasurable
        (figureOneFinalScheduledQueryBudget q)
  unfold figureOneFinalScheduledCappedValueProgram
  apply hcapped.bind (fun _ => by trivial)
  simp only [MembershipOracleProgram.runEstimate]
  exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem runEstimate_figureOneFinalScheduledCappedValueProgram
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneFinalScheduledCappedValueProgram q).runEstimate oracle.query =
      (((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
        (figureOneFinalScheduledQueryBudget q)).runEstimate oracle.query).map
          (fun result => result.getD 0) := by
  let capped := (figureOneFinalScheduledAbortBaseProgram q).withQueryCap
    (figureOneFinalScheduledQueryBudget q)
  have hcapped : capped.StronglyMeasurable oracle.query :=
    (figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
      q I oracle).withQueryCap_stronglyMeasurable
        (figureOneFinalScheduledQueryBudget q)
  unfold figureOneFinalScheduledCappedValueProgram
  change ((capped.bind fun estimate => .pure (estimate.getD 0)).runEstimate
    oracle.query) = (capped.runEstimate oracle.query).map
      (fun result => result.getD 0)
  rw [MembershipOracleProgram.runEstimate_bind oracle.query capped _ hcapped]
  · exact Measure.bind_dirac_eq_map _ measurable_optionGetD_zero
  · intro result
    trivial
  · simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp measurable_optionGetD_zero

/-- The two independently proved failure budgets for the uncapped estimator
and the counted-reference cutoff combine to the three-quarter base success
probability required by amplification. -/
theorem figureOneFinalScheduledCappedValueProgram_failure_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hbase : (figureOneFinalScheduledAbortBaseProgram q).runEstimate
      oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ))
    (hcap : ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
      (figureOneFinalScheduledQueryBudget q)).runEstimate oracle.query {none} ≤
        ENNReal.ofReal (1 / 64 : ℝ)) :
    (figureOneFinalScheduledCappedValueProgram q).runEstimate oracle.query
      (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let capped := (figureOneFinalScheduledAbortBaseProgram q).withQueryCap
    (figureOneFinalScheduledQueryBudget q)
  let bad := (accurateOutcome q I)ᶜ
  have hbad : MeasurableSet bad := (accurateOutcome_measurable q I).compl
  have hsubset : (fun result : Option ℝ => result.getD 0) ⁻¹' bad ⊆
      optionSomeEvent bad ∪ ({none} : Set (Option ℝ)) := by
    intro result hresult
    cases result with
    | none => simp
    | some value => simpa [optionSomeEvent] using hresult
  rw [runEstimate_figureOneFinalScheduledCappedValueProgram q I oracle,
    Measure.map_apply measurable_optionGetD_zero hbad]
  calc
    capped.runEstimate oracle.query
        ((fun result : Option ℝ => result.getD 0) ⁻¹' bad) ≤
      capped.runEstimate oracle.query
        (optionSomeEvent bad ∪ ({none} : Set (Option ℝ))) := measure_mono hsubset
    _ ≤ capped.runEstimate oracle.query (optionSomeEvent bad) +
        capped.runEstimate oracle.query {none} := measure_union_le _ _
    _ ≤ (figureOneFinalScheduledAbortBaseProgram q).runEstimate
          oracle.query bad + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add
        (MembershipOracleProgram.runEstimate_withQueryCap_optionSomeEvent_le
          oracle.query (figureOneFinalScheduledAbortBaseProgram q)
          (figureOneFinalScheduledQueryBudget q)
          (figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
            q I oracle).executionMeasurable bad hbad)
        hcap
    _ ≤ ENNReal.ofReal (13 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hbase le_rfl
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 13 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Direct counted-reference entry point for the final capped base.  This is
the interface used by the chronological cost construction: no expected-cost
bound for the actual (approximate) execution is required. -/
theorem figureOneFinalScheduledCappedValueProgram_failure_le_of_countedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (reference : Measure (ℝ × ℕ)) {delta : ENNReal}
    (hbase : (figureOneFinalScheduledAbortBaseProgram q).runEstimate
      oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ))
    (hdom : MeasureLeUpTo
      ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query)
      reference delta)
    (href : ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q))
    (hdelta : delta ≤ ENNReal.ofReal (1 / 640 : ℝ)) :
    (figureOneFinalScheduledCappedValueProgram q).runEstimate oracle.query
      (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  apply figureOneFinalScheduledCappedValueProgram_failure_le q I oracle hbase
  exact figureOneFinalScheduledAbortQueryCap_failure_le_of_countedReference
    q I oracle reference hdom href hdelta

/-- Final amplification for the scheduled executable, conditional only on
the two local conclusions that the analytic and counted-reference lanes are
designed to supply. -/
theorem volumeTheorem_finalScheduled_of_baseFailure_and_capFailure
    (hbase : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
        (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ))
    (hcap : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
        ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
          (figureOneFinalScheduledQueryBudget q)).runEstimate oracle.query
            {none} ≤ ENNReal.ofReal (1 / 64 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram figureOneFinalScheduledCappedValueProgram)
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              figureOneFinalScheduledCappedValueProgram q).QueryBound calls ∧
            calls ≤ Nat.ceil
              (C * (volumeScheduledBaseComplexityRate q *
                protectedLog (1 / q.p))) := by
  obtain ⟨C, hC, hamp⟩ := oracleProgram_proof_amplification_of_rate
    volumeScheduledBaseComplexityRate
    volumeScheduledBaseComplexityRate_one_le
    (64 * figureOneFinalScheduledExpectedCostConstant)
    (mul_pos (by norm_num) figureOneFinalScheduledExpectedCostConstant_pos)
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  apply hamp figureOneFinalScheduledCappedValueProgram q I oracle
  · let μ := (figureOneFinalScheduledCappedValueProgram q).runEstimate
      oracle.query
    let _ : IsProbabilityMeasure μ :=
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        (figureOneFinalScheduledCappedValueProgram_stronglyMeasurable
          q I oracle).estimateMeasurable
    apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
    exact figureOneFinalScheduledCappedValueProgram_failure_le q I oracle
      (hbase q I oracle hrounded) (hcap q I oracle)
  · exact figureOneFinalScheduledCappedValueProgram_stronglyMeasurable
      q I oracle
  · refine ⟨figureOneFinalScheduledQueryBudget q,
      figureOneFinalScheduledCappedValueProgram_queryBound q, ?_⟩
    exact le_rfl

/-- Final scheduled amplification after the counted runtime lane has been
closed unconditionally.  The sole remaining premise is the analytic accuracy
bound for the uncapped executable base estimator. -/
theorem volumeTheorem_finalScheduled_of_baseFailure
    (hbase : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
        (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram figureOneFinalScheduledCappedValueProgram)
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              figureOneFinalScheduledCappedValueProgram q).QueryBound calls ∧
            calls ≤ Nat.ceil
              (C * (volumeScheduledBaseComplexityRate q *
                protectedLog (1 / q.p))) := by
  apply volumeTheorem_finalScheduled_of_baseFailure_and_capFailure hbase
  intro q I oracle
  exact figureOneFinalScheduledAbortQueryCap_failure_le q I oracle

#print axioms figureOneFinalScheduledCappedValueProgram_failure_le
#print axioms
  figureOneFinalScheduledCappedValueProgram_failure_le_of_countedReference
#print axioms volumeTheorem_finalScheduled_of_baseFailure_and_capFailure
#print axioms volumeTheorem_finalScheduled_of_baseFailure

end ArlibCommunity.Algorithms.CV18
