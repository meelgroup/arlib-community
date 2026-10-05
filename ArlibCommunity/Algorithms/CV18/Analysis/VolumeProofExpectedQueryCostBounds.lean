/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost

/-! # Inequality interface for compositional expected query cost -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Expected cost of a bind is the source cost plus the output-law average
of the continuation cost.  Unlike the fixed-count variant, this applies to
the variable-cost proper clocks and retry loops. -/
theorem MembershipOracleProgram.countedQueryCost_bind_eq_add
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (hprogram : program.CountedStronglyMeasurable oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).run oracle) :
    countedQueryCost ((program.bind next).run oracle) =
      countedQueryCost (program.run oracle) +
        ∫⁻ result, countedQueryCost ((next result).run oracle)
          ∂(program.runEstimate oracle) := by
  rw [MembershipOracleProgram.countedQueryCost_bind oracle program next
    hprogram hnext hnextRun]
  have hcost : Measurable fun result =>
      countedQueryCost ((next result).run oracle) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hnextRun
  rw [lintegral_add_left measurable_countedQueryCost_integrand]
  congr 1
  rw [program.runEstimate_eq_map_fst_run oracle
    hprogram.executionMeasurable, lintegral_map]
  · exact hcost
  · fun_prop

/-- A uniform continuation-cost bound adds only once after a bind. -/
theorem MembershipOracleProgram.countedQueryCost_bind_le_add
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (hprogram : program.CountedStronglyMeasurable oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (C : ENNReal)
    (hC : ∀ result, countedQueryCost ((next result).run oracle) ≤ C) :
    countedQueryCost ((program.bind next).run oracle) ≤
      countedQueryCost (program.run oracle) + C := by
  rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle program next
    hprogram hnext hnextRun]
  gcongr
  let _ : IsProbabilityMeasure (program.run oracle) :=
    MembershipOracleProgram.run_isProbabilityMeasure oracle program
      hprogram.executionMeasurable
  have hprob : IsProbabilityMeasure (program.runEstimate oracle) := by
    rw [program.runEstimate_eq_map_fst_run oracle hprogram.executionMeasurable]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let _ : IsProbabilityMeasure (program.runEstimate oracle) := hprob
  calc
    (∫⁻ result, countedQueryCost ((next result).run oracle)
        ∂(program.runEstimate oracle)) ≤
      ∫⁻ _result, C ∂(program.runEstimate oracle) := lintegral_mono hC
    _ = C := by simp

/-- A pointwise source-cost bound and a uniform continuation bound compose
without introducing a structural query cap. -/
theorem MembershipOracleProgram.countedQueryCost_bind_le
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (hprogram : program.CountedStronglyMeasurable oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (sourceCost continuationCost : ENNReal)
    (hsource : countedQueryCost (program.run oracle) ≤ sourceCost)
    (hcontinuation : ∀ result,
      countedQueryCost ((next result).run oracle) ≤ continuationCost) :
    countedQueryCost ((program.bind next).run oracle) ≤
      sourceCost + continuationCost := by
  exact (MembershipOracleProgram.countedQueryCost_bind_le_add oracle program next
    hprogram hnext hnextRun continuationCost hcontinuation).trans
      (add_le_add hsource le_rfl)

#print axioms MembershipOracleProgram.countedQueryCost_bind_eq_add
#print axioms MembershipOracleProgram.countedQueryCost_bind_le_add

end ArlibCommunity.Algorithms.CV18
