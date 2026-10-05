import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProgramCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGenericRateAmplification

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable def globalQueryBudgetOfRate
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (q : VolumeParams) : ℕ :=
  Nat.ceil (64 * costConstant * rate q)

noncomputable def globallyCappedValueProgramOfRate
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  ((base q).withQueryCap (globalQueryBudgetOfRate costConstant rate q)).bind
    fun estimate => .pure (estimate.getD 0)

theorem globallyCappedValueProgramOfRate_queryBound
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) :
    (globallyCappedValueProgramOfRate costConstant rate base q).QueryBound
      (globalQueryBudgetOfRate costConstant rate q) := by
  unfold globallyCappedValueProgramOfRate
  exact ((base q).withQueryCap_queryBound
    (globalQueryBudgetOfRate costConstant rate q)).bind fun _ => .pure _ 0

theorem globallyCappedValueProgramOfRate_stronglyMeasurable
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query) :
    (globallyCappedValueProgramOfRate costConstant rate base q).StronglyMeasurable
      oracle.query := by
  unfold globallyCappedValueProgramOfRate
  apply (hmeas.withQueryCap_stronglyMeasurable
    (globalQueryBudgetOfRate costConstant rate q)).bind (fun _ => by trivial)
  simp only [MembershipOracleProgram.runEstimate]
  exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem runEstimate_globallyCappedValueProgramOfRate
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query) :
    (globallyCappedValueProgramOfRate costConstant rate base q).runEstimate
        oracle.query =
      (((base q).withQueryCap
        (globalQueryBudgetOfRate costConstant rate q)).runEstimate
          oracle.query).map (fun result => result.getD 0) := by
  let capP := (base q).withQueryCap
    (globalQueryBudgetOfRate costConstant rate q)
  have hcap : capP.StronglyMeasurable oracle.query :=
    hmeas.withQueryCap_stronglyMeasurable
      (globalQueryBudgetOfRate costConstant rate q)
  unfold globallyCappedValueProgramOfRate
  change ((capP.bind fun estimate => .pure (estimate.getD 0)).runEstimate
    oracle.query) = (capP.runEstimate oracle.query).map fun result => result.getD 0
  rw [MembershipOracleProgram.runEstimate_bind oracle.query capP _ hcap]
  · exact Measure.bind_dirac_eq_map _ measurable_optionGetD_zero
  · intro result
    trivial
  · simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem globallyCappedValueProgramOfRate_failure_le
    (costConstant : ℝ) (hcostConstant : 0 < costConstant)
    (rate : VolumeParams → ℝ) (hrate : ∀ q, 1 ≤ rate q)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query)
    (hcost : ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) ≤
      ENNReal.ofReal (costConstant * rate q))
    (hbase : (base q).runEstimate oracle.query (accurateOutcome q I)ᶜ ≤
      ENNReal.ofReal (13 / 64 : ℝ)) :
    (globallyCappedValueProgramOfRate costConstant rate base q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let budget := globalQueryBudgetOfRate costConstant rate q
  let capped := (base q).withQueryCap budget
  let bad := (accurateOutcome q I)ᶜ
  let R := ENNReal.ofReal (costConstant * rate q)
  let failure := capped.runEstimate oracle.query {none}
  have hbad : MeasurableSet bad := (accurateOutcome_measurable q I).compl
  have hsubset : (fun result : Option ℝ => result.getD 0) ⁻¹' bad ⊆
      optionSomeEvent bad ∪ ({none} : Set (Option ℝ)) := by
    intro result hresult
    cases result with
    | none => simp
    | some value => simpa [optionSomeEvent] using hresult
  have hR0 : R ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr <|
    mul_pos hcostConstant (lt_of_lt_of_le zero_lt_one (hrate q))
  have hbudget : ENNReal.ofReal (64 : ℝ) * R ≤ (budget + 1 : ENNReal) := by
    have hceil : 64 * costConstant * rate q ≤ (budget : ℝ) := Nat.le_ceil _
    have h := ENNReal.ofReal_le_ofReal hceil
    rw [ENNReal.ofReal_natCast] at h
    calc
      ENNReal.ofReal (64 : ℝ) * R =
          ENNReal.ofReal (64 * (costConstant * rate q)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      _ = ENNReal.ofReal (64 * costConstant * rate q) := by ring_nf
      _ ≤ (budget : ENNReal) := h
      _ ≤ (budget + 1 : ENNReal) := by exact_mod_cast Nat.le_add_right budget 1
  have hmarkov : (budget + 1 : ENNReal) * failure ≤
      ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) := by
    exact MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_cost
      oracle.query (base q) budget hmeas.executionMeasurable
  have hscaled : R * (failure * ENNReal.ofReal (64 : ℝ)) ≤ R := by
    calc
      R * (failure * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * R) * failure := by ring
      _ ≤ (budget + 1 : ENNReal) * failure := by gcongr
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) := hmarkov
      _ ≤ R := hcost
  have hcancel : failure * ENNReal.ofReal (64 : ℝ) ≤ 1 := by
    have hdiv : failure * ENNReal.ofReal (64 : ℝ) ≤ R / R :=
      (ENNReal.le_div_iff_mul_le (Or.inl hR0)
        (Or.inl ENNReal.ofReal_ne_top)).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    simpa [ENNReal.div_self hR0 ENNReal.ofReal_ne_top] using hdiv
  have hcapFailure : failure ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
    have := (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 hcancel
    simpa using this
  rw [runEstimate_globallyCappedValueProgramOfRate
    costConstant rate base q I oracle hmeas,
    Measure.map_apply measurable_optionGetD_zero hbad]
  calc
    capped.runEstimate oracle.query ((fun result : Option ℝ => result.getD 0) ⁻¹' bad) ≤
      capped.runEstimate oracle.query
        (optionSomeEvent bad ∪ ({none} : Set (Option ℝ))) := measure_mono hsubset
    _ ≤ capped.runEstimate oracle.query (optionSomeEvent bad) + failure :=
      measure_union_le _ _
    _ ≤ (base q).runEstimate oracle.query bad + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add
        (MembershipOracleProgram.runEstimate_withQueryCap_optionSomeEvent_le
          oracle.query (base q) budget hmeas.executionMeasurable bad hbad)
        hcapFailure
    _ ≤ ENNReal.ofReal (13 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hbase le_rfl
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 13 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem volumeTheorem_of_baseProgram_and_rate
    (costConstant : ℝ) (hcostConstant : 0 < costConstant)
    (rate : VolumeParams → ℝ) (hrate : ∀ q, 1 ≤ rate q)
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (hmeas : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
      (base q).CountedStronglyMeasurable oracle.query)
    (hbase : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
      (base q).runEstimate oracle.query (accurateOutcome q I)ᶜ ≤
        ENNReal.ofReal (13 / 64 : ℝ))
    (hcost : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
      ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) ≤
        ENNReal.ofReal (costConstant * rate q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram
                (globallyCappedValueProgramOfRate costConstant rate base))
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              (globallyCappedValueProgramOfRate costConstant rate base) q).QueryBound calls ∧
            calls ≤ Nat.ceil
              (C * (rate q * protectedLog (1 / q.p))) := by
  obtain ⟨C, hC, hamp⟩ := oracleProgram_proof_amplification_of_rate
    rate hrate (64 * costConstant) (mul_pos (by norm_num) hcostConstant)
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  apply hamp (globallyCappedValueProgramOfRate costConstant rate base) q I oracle
  · let μ := (globallyCappedValueProgramOfRate costConstant rate base q).runEstimate
      oracle.query
    let _ : IsProbabilityMeasure μ :=
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        (globallyCappedValueProgramOfRate_stronglyMeasurable
          costConstant rate base q I oracle (hmeas q I oracle)).estimateMeasurable
    apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
    exact globallyCappedValueProgramOfRate_failure_le
      costConstant hcostConstant rate hrate base q I oracle
        (hmeas q I oracle) (hcost q I oracle) (hbase q I oracle hrounded)
  · exact globallyCappedValueProgramOfRate_stronglyMeasurable
      costConstant rate base q I oracle (hmeas q I oracle)
  · refine ⟨globalQueryBudgetOfRate costConstant rate q,
      globallyCappedValueProgramOfRate_queryBound costConstant rate base q, ?_⟩
    exact le_rfl

end ArlibCommunity.Algorithms.CV18
