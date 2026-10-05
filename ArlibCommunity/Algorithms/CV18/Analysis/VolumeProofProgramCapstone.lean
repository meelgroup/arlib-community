import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofParameterizedCapstone

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-! The final cutoff/amplification layer depends only on a measurable base
program, its expected cost, and its base failure probability.  It is
therefore independent of the particular cooling primitives. -/

noncomputable def globallyCappedValueProgram
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  ((base q).withQueryCap (figureOneGlobalQueryBudget q)).bind
    fun estimate => .pure (estimate.getD 0)

theorem globallyCappedValueProgram_queryBound
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) :
    (globallyCappedValueProgram base q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  unfold globallyCappedValueProgram
  exact ((base q).withQueryCap_queryBound
    (figureOneGlobalQueryBudget q)).bind fun _ => .pure _ 0

theorem globallyCappedValueProgram_stronglyMeasurable
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query) :
    (globallyCappedValueProgram base q).StronglyMeasurable oracle.query := by
  unfold globallyCappedValueProgram
  apply (hmeas.withQueryCap_stronglyMeasurable
    (figureOneGlobalQueryBudget q)).bind (fun _ => by trivial)
  simp only [MembershipOracleProgram.runEstimate]
  exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem runEstimate_globallyCappedValueProgram
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query) :
    (globallyCappedValueProgram base q).runEstimate oracle.query =
      (((base q).withQueryCap (figureOneGlobalQueryBudget q)).runEstimate
        oracle.query).map (fun result => result.getD 0) := by
  let capP := (base q).withQueryCap (figureOneGlobalQueryBudget q)
  have hcap : capP.StronglyMeasurable oracle.query :=
    hmeas.withQueryCap_stronglyMeasurable (figureOneGlobalQueryBudget q)
  unfold globallyCappedValueProgram
  change ((capP.bind fun estimate => .pure (estimate.getD 0)).runEstimate
    oracle.query) = (capP.runEstimate oracle.query).map fun result => result.getD 0
  rw [MembershipOracleProgram.runEstimate_bind oracle.query capP _ hcap]
  · exact Measure.bind_dirac_eq_map _ measurable_optionGetD_zero
  · intro result
    trivial
  · simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem globallyCappedValueProgram_failure_le
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hmeas : (base q).CountedStronglyMeasurable oracle.query)
    (hcost : ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) ≤
      ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
        volumeBaseComplexityRate q))
    (hbase : (base q).runEstimate oracle.query (accurateOutcome q I)ᶜ ≤
      ENNReal.ofReal (13 / 64 : ℝ)) :
    (globallyCappedValueProgram base q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let capped := (base q).withQueryCap (figureOneGlobalQueryBudget q)
  let bad := (accurateOutcome q I)ᶜ
  let R := ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
    volumeBaseComplexityRate q)
  let failure := capped.runEstimate oracle.query {none}
  have hbad : MeasurableSet bad := (accurateOutcome_measurable q I).compl
  have hsubset : (fun result : Option ℝ => result.getD 0) ⁻¹' bad ⊆
      optionSomeEvent bad ∪ ({none} : Set (Option ℝ)) := by
    intro result hresult
    cases result with
    | none => simp
    | some value => simpa [optionSomeEvent] using hresult
  have hR0 : R ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr <|
    mul_pos figureOneGlobalExpectedCostConstant_pos
      (volumeBaseComplexityRate_pos_balanced q)
  have hbudget : ENNReal.ofReal (64 : ℝ) * R ≤
      (figureOneGlobalQueryBudget q + 1 : ENNReal) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    simpa [R, mul_assoc] using figureOneGlobalQueryBudget_rate_lower q
  have hmarkov : (figureOneGlobalQueryBudget q + 1 : ENNReal) * failure ≤
      ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) := by
    exact MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_cost
      oracle.query (base q) (figureOneGlobalQueryBudget q)
        hmeas.executionMeasurable
  have hscaled : R * (failure * ENNReal.ofReal (64 : ℝ)) ≤ R := by
    calc
      R * (failure * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * R) * failure := by ring
      _ ≤ (figureOneGlobalQueryBudget q + 1 : ENNReal) * failure := by gcongr
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂((base q).run oracle.query) :=
        hmarkov
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
  rw [runEstimate_globallyCappedValueProgram base q I oracle hmeas,
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
          oracle.query (base q) (figureOneGlobalQueryBudget q)
            hmeas.executionMeasurable bad hbad) hcapFailure
    _ ≤ ENNReal.ofReal (13 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hbase le_rfl
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 13 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem volumeTheorem_of_baseProgram
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
        ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
          volumeBaseComplexityRate q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram (globallyCappedValueProgram base))
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram (globallyCappedValueProgram base) q).QueryBound calls ∧
            calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  let C₀ := 64 * figureOneGlobalExpectedCostConstant
  obtain ⟨C, hC, hamp⟩ := oracleProgram_proof_amplification C₀ (by
    dsimp [C₀]
    positivity [figureOneGlobalExpectedCostConstant_pos])
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  apply hamp (globallyCappedValueProgram base) q I oracle
  · let μ := (globallyCappedValueProgram base q).runEstimate oracle.query
    let _ : IsProbabilityMeasure μ :=
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        (globallyCappedValueProgram_stronglyMeasurable base q I oracle
          (hmeas q I oracle)).estimateMeasurable
    apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
    exact globallyCappedValueProgram_failure_le base q I oracle
      (hmeas q I oracle) (hcost q I oracle) (hbase q I oracle hrounded)
  · exact globallyCappedValueProgram_stronglyMeasurable base q I oracle
      (hmeas q I oracle)
  · refine ⟨figureOneGlobalQueryBudget q,
      globallyCappedValueProgram_queryBound base q, ?_⟩
    simp [figureOneGlobalQueryBudget, C₀]

end ArlibCommunity.Algorithms.CV18
