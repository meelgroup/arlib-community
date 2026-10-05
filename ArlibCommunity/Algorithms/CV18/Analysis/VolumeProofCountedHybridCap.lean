/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalQueryCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortCost

/-! # Transferring a global query cutoff through a counted hybrid

The CV18 exact-chance replacements are an accuracy argument, not an
unrestricted-runtime argument.  A replacement error must therefore be
charged as probability mass before applying Markov's inequality to the
reference execution.  Charging it at a local syntactic proposal cap loses
the advertised rate.

This file supplies the generic counted-law interface for the paper-faithful
argument.  It deliberately compares full result-and-query-count laws.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- If a counted execution law is dominated by a reference counted law up to
`delta`, global-cap exhaustion is bounded by the reference Markov term plus
`delta`.  In multiplicative form no division or finiteness side condition is
needed. -/
theorem MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_of_run_leUpTo
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure (Result × ℕ)) {delta R : ENNReal}
    (hdom : MeasureLeUpTo (program.run oracle) reference delta)
    (href : ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference ≤ R) :
    (budget + 1 : ENNReal) *
        (program.withQueryCap budget).runEstimate oracle {none} ≤
      R + (budget + 1 : ENNReal) * delta := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  let expensive : Set (Result × ℕ) := {outcome | budget < outcome.2}
  have hevent := hdom.event_le expensive
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun outcome : Result × ℕ =>
      (outcome.2 : ENNReal) by fun_prop)
    (budget + 1 : ENNReal) (μ := reference)
  have hexpensive : expensive = {outcome : Result × ℕ |
      (budget + 1 : ENNReal) ≤ (outcome.2 : ENNReal)} := by
    ext outcome
    simp only [expensive, Set.mem_ofPred_eq]
    exact_mod_cast Nat.add_one_le_iff
  rw [← hexpensive] at hmarkov
  calc
    (budget + 1 : ENNReal) * (program.run oracle) expensive ≤
        (budget + 1 : ENNReal) * (reference expensive + delta) := by
      gcongr
    _ = (budget + 1 : ENNReal) * reference expensive +
        (budget + 1 : ENNReal) * delta := by ring
    _ ≤ (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) +
        (budget + 1 : ENNReal) * delta := by gcongr
    _ ≤ R + (budget + 1 : ENNReal) * delta := by gcongr

/-- Event form of the counted-hybrid cutoff estimate. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap_none_le_reference_tail
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure (Result × ℕ)) {delta : ENNReal}
    (hdom : MeasureLeUpTo (program.run oracle) reference delta) :
    (program.withQueryCap budget).runEstimate oracle {none} ≤
      reference {outcome | budget < outcome.2} + delta := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  exact hdom.event_le _

/-- The cutoff event only depends on the query-count marginal, so a reference
measure on counts is sufficient; numerical result coordinates need not be
coupled. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap_none_le_countReference_tail
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure ℕ) {delta : ENNReal}
    (hdom : MeasureLeUpTo ((program.run oracle).map Prod.snd)
      reference delta) :
    (program.withQueryCap budget).runEstimate oracle {none} ≤
      reference {count | budget < count} + delta := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  have hevent := hdom.event_le {count | budget < count}
  have hset : MeasurableSet {count : ℕ | budget < count} :=
    measurableSet_lt measurable_const measurable_id
  rw [Measure.map_apply measurable_snd hset] at hevent
  exact hevent

/-- Numerical final-schedule cutoff estimate stated only in terms of a
query-count reference marginal. -/
theorem figureOneFinalScheduledQueryCap_failure_le_of_countReference
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (q : VolumeParams) (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure ℕ) {delta : ENNReal}
    (hdom : MeasureLeUpTo ((program.run oracle).map Prod.snd)
      reference delta)
    (href : ∫⁻ count, (count : ENNReal) ∂reference ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q))
    (hdelta : delta ≤ ENNReal.ofReal (1 / 640 : ℝ)) :
    (program.withQueryCap (figureOneFinalScheduledQueryBudget q)).runEstimate
        oracle {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let budget := figureOneFinalScheduledQueryBudget q
  let tail := reference {count | budget < count}
  let base := ENNReal.ofReal
    (figureOneFinalScheduledExpectedCostConstant *
      volumeScheduledBaseComplexityRate q)
  have hbase0 : base ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr <|
      mul_pos figureOneFinalScheduledExpectedCostConstant_pos
        (volumeScheduledBaseComplexityRate_pos q)
  have hbaseTop : base ≠ ∞ := ENNReal.ofReal_ne_top
  have hbudget : ENNReal.ofReal (64 : ℝ) * base ≤
      (budget + 1 : ENNReal) := by
    have hceil : 64 * figureOneFinalScheduledExpectedCostConstant *
        volumeScheduledBaseComplexityRate q ≤ (budget : ℝ) := by
      simpa [budget, figureOneFinalScheduledQueryBudget,
        globalQueryBudgetOfRate] using Nat.le_ceil
          (64 * figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q)
    have h := ENNReal.ofReal_le_ofReal hceil
    rw [ENNReal.ofReal_natCast] at h
    calc
      ENNReal.ofReal (64 : ℝ) * base =
          ENNReal.ofReal (64 *
            (figureOneFinalScheduledExpectedCostConstant *
              volumeScheduledBaseComplexityRate q)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      _ = ENNReal.ofReal (64 *
          figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q) := by ring_nf
      _ ≤ (budget : ENNReal) := h
      _ ≤ (budget + 1 : ENNReal) := by
        exact_mod_cast Nat.le_add_right budget 1
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun count : ℕ => (count : ENNReal) by fun_prop)
    (budget + 1 : ENNReal) (μ := reference)
  have hevent : ({count : ℕ | budget < count}) =
      {count : ℕ | (budget + 1 : ENNReal) ≤ (count : ENNReal)} := by
    ext count
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast Nat.add_one_le_iff
  rw [← hevent] at hmarkov
  have hwarmEq : ENNReal.ofReal ((9 * 10 ^ 29) *
      volumeScheduledBaseComplexityRate q) =
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    rw [← ENNReal.ofReal_mul
      (by positivity [figureOneFinalScheduledExpectedCostConstant_pos,
        volumeScheduledBaseComplexityRate_pos q] :
        0 ≤ figureOneFinalScheduledExpectedCostConstant *
          volumeScheduledBaseComplexityRate q)]
    congr 1
    simp only [figureOneFinalScheduledExpectedCostConstant]
    ring
  have hscaled : base * (tail * ENNReal.ofReal (64 : ℝ)) ≤
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    calc
      base * (tail * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * base) * tail := by ring
      _ ≤ (budget + 1 : ENNReal) * tail := by gcongr
      _ ≤ ∫⁻ count, (count : ENNReal) ∂reference := hmarkov
      _ ≤ ENNReal.ofReal ((9 * 10 ^ 29) *
          volumeScheduledBaseComplexityRate q) := href
      _ = base * ENNReal.ofReal (9 / 10 : ℝ) := hwarmEq
  have htailScaled : tail * ENNReal.ofReal (64 : ℝ) ≤
      ENNReal.ofReal (9 / 10 : ℝ) := by
    have hdiv : tail * ENNReal.ofReal (64 : ℝ) ≤
        (base * ENNReal.ofReal (9 / 10 : ℝ)) / base :=
      (ENNReal.le_div_iff_mul_le (Or.inl hbase0)
        (Or.inl hbaseTop)).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hcancel : (base * ENNReal.ofReal (9 / 10 : ℝ)) / base =
        ENNReal.ofReal (9 / 10 : ℝ) := by
      rw [ENNReal.div_eq_inv_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hbase0 hbaseTop, one_mul]
    simpa only [hcancel] using hdiv
  have htail : tail ≤ ENNReal.ofReal (9 / 640 : ℝ) := by
    have h := (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 htailScaled
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)] at h
    norm_num at h
    exact h
  calc
    (program.withQueryCap budget).runEstimate oracle {none} ≤
        tail + delta := by
      simpa only [budget, tail] using
        program.runEstimate_withQueryCap_none_le_countReference_tail
          oracle budget hmeas reference hdom
    _ ≤ ENNReal.ofReal (9 / 640 : ℝ) +
        ENNReal.ofReal (1 / 640 : ℝ) := add_le_add htail hdelta
    _ = ENNReal.ofReal (1 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 9 / 640)
        (by norm_num : (0 : ℝ) ≤ 1 / 640)]
      congr 1
      norm_num

/-- Numerical final-schedule specialization.  A counted reference using at
most nine tenths of the selected expected-cost constant and a hybrid loss of
at most `1/640` makes the shared global cutoff fail with probability at most
`1/64`.  This is the exact replacement for the invalid attempt to bound the
unrestricted bad branch by every local syntactic cap. -/
theorem figureOneFinalScheduledQueryCap_failure_le_of_countedReference
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (q : VolumeParams) (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure (Result × ℕ)) {delta : ENNReal}
    (hdom : MeasureLeUpTo (program.run oracle) reference delta)
    (href : ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q))
    (hdelta : delta ≤ ENNReal.ofReal (1 / 640 : ℝ)) :
    (program.withQueryCap (figureOneFinalScheduledQueryBudget q)).runEstimate
        oracle {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let budget := figureOneFinalScheduledQueryBudget q
  let tail := reference {outcome | budget < outcome.2}
  let base := ENNReal.ofReal
    (figureOneFinalScheduledExpectedCostConstant *
      volumeScheduledBaseComplexityRate q)
  have hbase0 : base ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr <|
      mul_pos figureOneFinalScheduledExpectedCostConstant_pos
        (volumeScheduledBaseComplexityRate_pos q)
  have hbaseTop : base ≠ ∞ := ENNReal.ofReal_ne_top
  have hbudget : ENNReal.ofReal (64 : ℝ) * base ≤
      (budget + 1 : ENNReal) := by
    have hceil : 64 * figureOneFinalScheduledExpectedCostConstant *
        volumeScheduledBaseComplexityRate q ≤ (budget : ℝ) := by
      simpa [budget, figureOneFinalScheduledQueryBudget,
        globalQueryBudgetOfRate] using Nat.le_ceil
          (64 * figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q)
    have h := ENNReal.ofReal_le_ofReal hceil
    rw [ENNReal.ofReal_natCast] at h
    calc
      ENNReal.ofReal (64 : ℝ) * base =
          ENNReal.ofReal (64 *
            (figureOneFinalScheduledExpectedCostConstant *
              volumeScheduledBaseComplexityRate q)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      _ = ENNReal.ofReal (64 *
          figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q) := by ring_nf
      _ ≤ (budget : ENNReal) := h
      _ ≤ (budget + 1 : ENNReal) := by
        exact_mod_cast Nat.le_add_right budget 1
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun outcome : Result × ℕ =>
      (outcome.2 : ENNReal) by fun_prop)
    (budget + 1 : ENNReal) (μ := reference)
  have hevent : ({outcome : Result × ℕ | budget < outcome.2}) =
      {outcome : Result × ℕ |
        (budget + 1 : ENNReal) ≤ (outcome.2 : ENNReal)} := by
    ext outcome
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast Nat.add_one_le_iff
  rw [← hevent] at hmarkov
  have hwarmEq : ENNReal.ofReal ((9 * 10 ^ 29) *
      volumeScheduledBaseComplexityRate q) =
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    rw [← ENNReal.ofReal_mul
      (by positivity [figureOneFinalScheduledExpectedCostConstant_pos,
        volumeScheduledBaseComplexityRate_pos q] :
        0 ≤ figureOneFinalScheduledExpectedCostConstant *
          volumeScheduledBaseComplexityRate q)]
    congr 1
    simp only [figureOneFinalScheduledExpectedCostConstant]
    ring
  have hscaled : base * (tail * ENNReal.ofReal (64 : ℝ)) ≤
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    calc
      base * (tail * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * base) * tail := by ring
      _ ≤ (budget + 1 : ENNReal) * tail := by gcongr
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference := hmarkov
      _ ≤ ENNReal.ofReal ((9 * 10 ^ 29) *
          volumeScheduledBaseComplexityRate q) := href
      _ = base * ENNReal.ofReal (9 / 10 : ℝ) := hwarmEq
  have htailScaled : tail * ENNReal.ofReal (64 : ℝ) ≤
      ENNReal.ofReal (9 / 10 : ℝ) := by
    have hdiv : tail * ENNReal.ofReal (64 : ℝ) ≤
        (base * ENNReal.ofReal (9 / 10 : ℝ)) / base :=
      (ENNReal.le_div_iff_mul_le (Or.inl hbase0)
        (Or.inl hbaseTop)).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hcancel : (base * ENNReal.ofReal (9 / 10 : ℝ)) / base =
        ENNReal.ofReal (9 / 10 : ℝ) := by
      rw [ENNReal.div_eq_inv_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hbase0 hbaseTop, one_mul]
    simpa only [hcancel] using hdiv
  have htail : tail ≤ ENNReal.ofReal (9 / 640 : ℝ) := by
    have h := (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 htailScaled
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)] at h
    norm_num at h
    exact h
  calc
    (program.withQueryCap budget).runEstimate oracle {none} ≤
        tail + delta := by
      simpa only [budget, tail] using
        program.runEstimate_withQueryCap_none_le_reference_tail oracle budget
          hmeas reference hdom
    _ ≤ ENNReal.ofReal (9 / 640 : ℝ) +
        ENNReal.ofReal (1 / 640 : ℝ) := add_le_add htail hdelta
    _ = ENNReal.ofReal (1 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 9 / 640)
        (by norm_num : (0 : ℝ) ≤ 1 / 640)]
      congr 1
      norm_num

/-- Exact final-program wrapper: after a counted chronological reference is
constructed, only its domination, expected-count, and total replacement-loss
bounds remain. -/
theorem figureOneFinalScheduledAbortQueryCap_failure_le_of_countedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (reference : Measure (ℝ × ℕ)) {delta : ENNReal}
    (hdom : MeasureLeUpTo
      ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query)
      reference delta)
    (href : ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q))
    (hdelta : delta ≤ ENNReal.ofReal (1 / 640 : ℝ)) :
    ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
        (figureOneFinalScheduledQueryBudget q)).runEstimate oracle.query
          {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  exact figureOneFinalScheduledQueryCap_failure_le_of_countedReference
    q oracle.query (figureOneFinalScheduledAbortBaseProgram q)
      (figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
        q I oracle).executionMeasurable
      reference hdom href hdelta

#print axioms
  MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_of_run_leUpTo
#print axioms
  MembershipOracleProgram.runEstimate_withQueryCap_none_le_reference_tail
#print axioms
  MembershipOracleProgram.runEstimate_withQueryCap_none_le_countReference_tail
#print axioms figureOneFinalScheduledQueryCap_failure_le_of_countedReference
#print axioms figureOneFinalScheduledQueryCap_failure_le_of_countReference
#print axioms
  figureOneFinalScheduledAbortQueryCap_failure_le_of_countedReference

end ArlibCommunity.Algorithms.CV18
