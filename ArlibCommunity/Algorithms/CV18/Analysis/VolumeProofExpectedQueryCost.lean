/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedMeasurability

/-!
# Compositional expected membership-query cost

This module records the exact expectation law for the counted interpreter's
Kleisli bind.  It is the measure-theoretic bookkeeping layer used to sum the
proper-proposal and rejection-query costs through the balanced retry loop.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Expected membership-query count of a counted execution law. -/
noncomputable def countedQueryCost {A : Type*} [MeasurableSpace A]
    (mu : Measure (A × ℕ)) : ENNReal :=
  ∫⁻ outcome, (outcome.2 : ENNReal) ∂mu

theorem measurable_countedQueryCost_integrand {A : Type*} [MeasurableSpace A] :
    Measurable (fun outcome : A × ℕ => (outcome.2 : ENNReal)) := by
  fun_prop

/-- Exact cost of a counted continuation: the incoming count plus the cost
of the continuation program. -/
theorem lintegral_countedContinuation_queryCount
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (next : A → MembershipOracleProgram n B)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (first : A × ℕ) :
    ∫⁻ outcome, (outcome.2 : ENNReal)
        ∂(countedContinuation oracle next first) =
      (first.2 : ENNReal) +
        ∫⁻ outcome, (outcome.2 : ENNReal) ∂((next first.1).run oracle) := by
  let _ : IsProbabilityMeasure ((next first.1).run oracle) :=
    MembershipOracleProgram.run_isProbabilityMeasure oracle _
      (hnext first.1).executionMeasurable
  simp only [countedContinuation]
  rw [lintegral_map]
  · change (∫⁻ outcome, ((first.2 + outcome.2 : ℕ) : ENNReal)
        ∂((next first.1).run oracle)) = _
    simp only [Nat.cast_add]
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
  · fun_prop
  · fun_prop

/-- Exact expected-cost law for a syntactic bind. -/
theorem MembershipOracleProgram.countedQueryCost_bind
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (hprogram : program.CountedStronglyMeasurable oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).run oracle) :
    countedQueryCost ((program.bind next).run oracle) =
      ∫⁻ first, (first.2 : ENNReal) +
        countedQueryCost ((next first.1).run oracle) ∂(program.run oracle) := by
  rw [MembershipOracleProgram.run_bind_counted oracle program next
    hprogram hnext hnextRun]
  unfold countedQueryCost
  rw [Measure.lintegral_bind
    (measurable_countedContinuation oracle next hnextRun hnext).aemeasurable
    measurable_countedQueryCost_integrand.aemeasurable]
  apply lintegral_congr
  intro first
  exact lintegral_countedContinuation_queryCount oracle next hnext first

/-- When the source has a fixed query count, the bind law separates that
constant from the expected continuation cost. -/
theorem MembershipOracleProgram.FixedQueryCount.countedQueryCost_bind
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {program : MembershipOracleProgram n A} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (next : A → MembershipOracleProgram n B)
    (hstrong : program.StronglyMeasurable oracle)
    (hprogram : program.CountedStronglyMeasurable oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).run oracle) :
    countedQueryCost ((program.bind next).run oracle) =
      (count : ENNReal) +
        ∫⁻ result, countedQueryCost ((next result).run oracle)
          ∂(program.runEstimate oracle) := by
  rw [MembershipOracleProgram.countedQueryCost_bind oracle program next
    hprogram hnext hnextRun,
    hcount.run_eq_map_runEstimate oracle hstrong]
  have hcost : Measurable fun result =>
      countedQueryCost ((next result).run oracle) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp hnextRun
  rw [lintegral_map]
  · change (∫⁻ result, (count : ENNReal) +
        countedQueryCost ((next result).run oracle)
          ∂(program.runEstimate oracle)) = _
    rw [lintegral_add_left measurable_const]
    let _ : IsProbabilityMeasure (program.runEstimate oracle) :=
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle program
        hstrong.estimateMeasurable
    simp only [lintegral_const, measure_univ, mul_one]
  · exact measurable_countedQueryCost_integrand.add
      (hcost.comp measurable_fst)
  · fun_prop

end ArlibCommunity.Algorithms.CV18
