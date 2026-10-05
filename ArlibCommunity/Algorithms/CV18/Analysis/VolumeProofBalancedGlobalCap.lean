/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedFullHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedPhaseInstantiation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalQueryCap

/-!
# One global query cutoff for the balanced CV18 program

The paper charges the proper-proposal tail once, over the complete cooling
execution.  It does not allocate a tiny failure probability to every sample.
This module therefore uses a local syntactic cutoff only beyond the global
budget and wraps the entire base run in `withQueryCap`.

The operational global-cap theorem below reduces its failure probability to
one expected-query-cost integral.  Proving that integral at the advertised
rate is deliberately exposed as the remaining compositional cost interface.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Positivity of the exact unrestricted base-complexity rate. -/
theorem volumeBaseComplexityRate_pos_balanced (q : VolumeParams) :
    0 < volumeBaseComplexityRate q := by
  unfold volumeBaseComplexityRate
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have heps : 0 < q.eps := q.heps.1
  have hround : 0 < max 1 q.roundness :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlogEps : 0 < protectedLog (1 / q.eps) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlogNEps : 0 < protectedLog ((q.n : ℝ) / q.eps) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlogTerminal : 0 < protectedLog (volumeTerminalScale q) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

/-- The warm-start mixing expression for the first block of an adjacent
cooling phase. -/
noncomputable def figureOneGlobalFirstWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  let M := speedyAdjacentWarmConstant q
  4 * ((Real.log (2 * M) +
      2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
    (figureOneProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

/-- The stationary-rejection mixing expression for later retries. -/
noncomputable def figureOneGlobalRetryWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  4 * ((Real.log 2 +
      2 * Real.log (1 / (figureOnePerSampleMixingError q / 2))) /
    (figureOneProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

/-- A concrete stride satisfying both speedy-mixing deadlines. -/
noncomputable def figureOneGlobalProperStride
    (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  Nat.ceil (max 1 (max
    (figureOneGlobalFirstWalkRequirement q sigma2)
    (figureOneGlobalRetryWalkRequirement q sigma2)))

theorem figureOneGlobalFirstWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneGlobalFirstWalkRequirement q sigma2 ≤
      (figureOneGlobalProperStride q sigma2 : ℝ) := by
  apply le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem figureOneGlobalRetryWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOneGlobalRetryWalkRequirement q sigma2 ≤
      (figureOneGlobalProperStride q sigma2 : ℝ) := by
  apply le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem figureOneGlobalProperStride_pos
    (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOneGlobalProperStride q sigma2 := by
  have h : (1 : ℝ) ≤ (figureOneGlobalProperStride q sigma2 : ℝ) := by
    apply le_trans (le_max_left _ _)
    exact Nat.le_ceil _
  exact_mod_cast h

/-- Absolute base-run cost constant already used by the explicit Figure-One
complexity arithmetic in `VolumeProofCost`. -/
noncomputable def figureOneGlobalExpectedCostConstant : ℝ := 10 ^ 25

theorem figureOneGlobalExpectedCostConstant_pos :
    0 < figureOneGlobalExpectedCostConstant := by
  norm_num [figureOneGlobalExpectedCostConstant]

/-- A constant-factor global cutoff.  The outer factor `64` assigns at most
`1/64` failure probability to exhausting the complete-run budget. -/
noncomputable def figureOneGlobalQueryBudget (q : VolumeParams) : ℕ :=
  Nat.ceil (64 * figureOneGlobalExpectedCostConstant *
    volumeBaseComplexityRate q)

theorem figureOneGlobalQueryBudget_pos (q : VolumeParams) :
    0 < figureOneGlobalQueryBudget q := by
  apply Nat.ceil_pos.mpr
  positivity [figureOneGlobalExpectedCostConstant_pos,
    volumeBaseComplexityRate_pos_balanced q]

/-- Finite local syntax parameters.  Each one-block collector internally
uses `proposalCap + 1` raw proposals.  This places its intended exhaustion
threshold just beyond the outer global budget; the exact prefix-invisibility
lemma connecting this finite syntax to the costed proper kernel is part of
the remaining whole-run expected-cost interface described below. -/
noncomputable def figureOneGlobalBalancedParameters :
    BalancedCoolingParameters where
  proposalCap := fun q _ => figureOneGlobalQueryBudget q
  properStride := figureOneGlobalProperStride
  retryLimit := fun q _ =>
    figureOneDependentMaxSampleCount q * figureOneDependentPhaseCount q

/-- The finite base syntax before installing the one shared cutoff. -/
noncomputable def figureOneGlobalBalancedBaseProgram (q : VolumeParams) :
    MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling (balancedCoolingPrimitives figureOneGlobalBalancedParameters)
    explicitVolumeCoolingSchedule q

/-- The paper-faithful outer cutoff.  Its failure is represented by `none`. -/
noncomputable def figureOneGloballyCappedBalancedBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n (Option ℝ) :=
  (figureOneGlobalBalancedBaseProgram q).withQueryCap
    (figureOneGlobalQueryBudget q)

theorem figureOneGloballyCappedBalancedBaseProgram_queryBound
    (q : VolumeParams) :
    (figureOneGloballyCappedBalancedBaseProgram q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  exact MembershipOracleProgram.withQueryCap_queryBound _ _

/-- A global cutoff does not increase the mass of any measurable event among
successful outputs.  Only the new `none` branch has to be charged. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap_optionSomeEvent_le
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (A : Set Result) (hA : MeasurableSet A) :
    (program.withQueryCap budget).runEstimate oracle (optionSomeEvent A) ≤
      program.runEstimate oracle A := by
  rw [program.runEstimate_withQueryCap oracle budget hmeas,
    Measure.map_apply (measurable_queryCapOutcome budget)
      (measurableSet_optionSomeEvent hA),
    program.runEstimate_eq_map_fst_run oracle hmeas,
    Measure.map_apply measurable_fst hA]
  apply measure_mono
  intro outcome hout
  simp only [Set.mem_preimage] at hout ⊢
  unfold queryCapOutcome at hout
  split at hout
  · simpa [optionSomeEvent] using hout
  · simp [optionSomeEvent] at hout

/-- Specialized successful-event transfer for the balanced base run. -/
theorem figureOneGloballyCappedBalancedBaseProgram_success_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (figureOneGlobalBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query) (A : Set ℝ) (hA : MeasurableSet A) :
    (figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query
        (optionSomeEvent A) ≤
      (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query A := by
  exact MembershipOracleProgram.runEstimate_withQueryCap_optionSomeEvent_le
    oracle.query (figureOneGlobalBalancedBaseProgram q)
      (figureOneGlobalQueryBudget q) hmeas.executionMeasurable A hA

/-- The exact whole-program expected-cost statement needed by the global
Markov argument.  This is the smallest missing bridge from phasewise proper
proposal cost bounds to the executable cooling program. -/
def FigureOneBalancedExpectedQueryCost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Prop :=
  ∫⁻ outcome, (outcome.2 : ENNReal)
      ∂((figureOneGlobalBalancedBaseProgram q).run oracle.query) ≤
    ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
      volumeBaseComplexityRate q)

/-- The global cutoff failure satisfies the raw multiplicative Markov bound.
No phase count or sample count is paid in its probability budget. -/
theorem figureOneGloballyCappedBalancedBaseProgram_mul_failure_le_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (figureOneGlobalBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query) :
    (figureOneGlobalQueryBudget q + 1 : ENNReal) *
        (figureOneGloballyCappedBalancedBaseProgram q).runEstimate
          oracle.query {none} ≤
      ∫⁻ outcome, (outcome.2 : ENNReal)
        ∂((figureOneGlobalBalancedBaseProgram q).run oracle.query) := by
  exact MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_cost
    oracle.query (figureOneGlobalBalancedBaseProgram q)
      (figureOneGlobalQueryBudget q) hmeas.executionMeasurable

theorem figureOneGlobalQueryBudget_rate_lower (q : VolumeParams) :
    ENNReal.ofReal (64 * figureOneGlobalExpectedCostConstant *
      volumeBaseComplexityRate q) ≤
      (figureOneGlobalQueryBudget q + 1 : ENNReal) := by
  have hceil : 64 * figureOneGlobalExpectedCostConstant *
      volumeBaseComplexityRate q ≤
      (figureOneGlobalQueryBudget q : ℝ) := Nat.le_ceil _
  have h := ENNReal.ofReal_le_ofReal hceil
  rw [ENNReal.ofReal_natCast] at h
  have hn : figureOneGlobalQueryBudget q ≤
      figureOneGlobalQueryBudget q + 1 := Nat.le_add_right _ _
  have hn' : (figureOneGlobalQueryBudget q : ENNReal) ≤
      (figureOneGlobalQueryBudget q + 1 : ENNReal) := by exact_mod_cast hn
  exact h.trans hn'

/-- Once the one expected-cost integral is supplied, exhaustion of the
single global cutoff costs at most `1/64`. -/
theorem figureOneGloballyCappedBalancedBaseProgram_failure_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (figureOneGlobalBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query)
    (hcost : FigureOneBalancedExpectedQueryCost q I oracle) :
    (figureOneGloballyCappedBalancedBaseProgram q).runEstimate
        oracle.query {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let R := ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
    volumeBaseComplexityRate q)
  let failure := (figureOneGloballyCappedBalancedBaseProgram q).runEstimate
    oracle.query {none}
  have hR0 : R ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos figureOneGlobalExpectedCostConstant_pos
        (volumeBaseComplexityRate_pos_balanced q))
  have hRtop : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbudget : ENNReal.ofReal (64 : ℝ) * R ≤
      (figureOneGlobalQueryBudget q + 1 : ENNReal) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    simpa [mul_assoc] using figureOneGlobalQueryBudget_rate_lower q
  have hmarkov := figureOneGloballyCappedBalancedBaseProgram_mul_failure_le_cost
    q I oracle hmeas
  have hcost' : (∫⁻ outcome, (outcome.2 : ENNReal)
        ∂((figureOneGlobalBalancedBaseProgram q).run oracle.query)) ≤ R := hcost
  have hscaled : R * (failure * ENNReal.ofReal (64 : ℝ)) ≤ R := by
    calc
      R * (failure * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * R) * failure := by ring
      _ ≤ (figureOneGlobalQueryBudget q + 1 : ENNReal) * failure := by
        gcongr
      _ ≤ (∫⁻ outcome, (outcome.2 : ENNReal)
          ∂((figureOneGlobalBalancedBaseProgram q).run oracle.query)) := hmarkov
      _ ≤ R := hcost'
  have hcancel : failure * ENNReal.ofReal (64 : ℝ) ≤ 1 := by
    have hdiv : failure * ENNReal.ofReal (64 : ℝ) ≤ R / R :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hR0) (Or.inl hRtop)).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    simpa [ENNReal.div_self hR0 hRtop] using hdiv
  have hfailure : failure ≤ 1 / ENNReal.ofReal (64 : ℝ) :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 hcancel
  simpa [failure] using hfailure

/-- Event-transfer form used by an accuracy proof: a measurable bad event
among successful outputs plus global exhaustion is bounded by the original
bad-event mass plus `1/64`. -/
theorem figureOneGloballyCappedBalancedBaseProgram_bad_add_failure_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (figureOneGlobalBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query)
    (hcost : FigureOneBalancedExpectedQueryCost q I oracle)
    (bad : Set ℝ) (hbad : MeasurableSet bad) :
    (figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query
          (optionSomeEvent bad) +
        (figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query
          {none} ≤
      (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query bad +
        ENNReal.ofReal (1 / 64 : ℝ) := by
  exact add_le_add
    (figureOneGloballyCappedBalancedBaseProgram_success_le
      q I oracle hmeas bad hbad)
    (figureOneGloballyCappedBalancedBaseProgram_failure_le
      q I oracle hmeas hcost)

#print axioms figureOneGloballyCappedBalancedBaseProgram_queryBound
#print axioms figureOneGloballyCappedBalancedBaseProgram_failure_le

end ArlibCommunity.Algorithms.CV18
