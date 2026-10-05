import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedCapstone

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-! A parameter-generic version of the globally capped Figure-One capstone.
This lets the final theorem use the scheduled retry count and walk stride
proved by the executable KLS analysis, rather than the earlier provisional
parameter record. -/

noncomputable def figureOneBalancedBaseProgramFor
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling (balancedCoolingPrimitives parameters)
    explicitVolumeCoolingSchedule q

noncomputable def figureOneGloballyCappedBalancedBaseProgramFor
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (figureOneBalancedBaseProgramFor parameters q).withQueryCap
    (figureOneGlobalQueryBudget q)

noncomputable def figureOneGloballyCappedBalancedBaseValueProgramFor
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    MembershipOracleProgram q.n ℝ :=
  (figureOneGloballyCappedBalancedBaseProgramFor parameters q).bind
    fun estimate => .pure (estimate.getD 0)

def FigureOneBalancedExpectedQueryCostFor
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Prop :=
  ∫⁻ outcome, (outcome.2 : ENNReal)
      ∂((figureOneBalancedBaseProgramFor parameters q).run oracle.query) ≤
    ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
      volumeBaseComplexityRate q)

theorem figureOneBalancedBaseProgramFor_countedStronglyMeasurable
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneBalancedBaseProgramFor parameters q).CountedStronglyMeasurable
      oracle.query := by
  exact balancedFigureOneBaseVolumeCooling_countedStronglyMeasurable
    parameters q I oracle

theorem figureOneGloballyCappedBalancedBaseProgramFor_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    (figureOneGloballyCappedBalancedBaseProgramFor parameters q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  exact MembershipOracleProgram.withQueryCap_queryBound _ _

theorem figureOneGloballyCappedBalancedBaseValueProgramFor_stronglyMeasurable
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneGloballyCappedBalancedBaseValueProgramFor parameters q).StronglyMeasurable
      oracle.query := by
  have hcapped :=
    (figureOneBalancedBaseProgramFor_countedStronglyMeasurable
      parameters q I oracle).withQueryCap_stronglyMeasurable
        (figureOneGlobalQueryBudget q)
  unfold figureOneGloballyCappedBalancedBaseValueProgramFor
  apply hcapped.bind (fun _ => by trivial)
  simp only [MembershipOracleProgram.runEstimate]
  exact Measure.measurable_dirac.comp measurable_optionGetD_zero

theorem figureOneGloballyCappedBalancedBaseValueProgramFor_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    (figureOneGloballyCappedBalancedBaseValueProgramFor parameters q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  unfold figureOneGloballyCappedBalancedBaseValueProgramFor
  exact (figureOneGloballyCappedBalancedBaseProgramFor_queryBound parameters q).bind
    fun _ => .pure _ 0

theorem runEstimate_figureOneGloballyCappedBalancedBaseValueProgramFor
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneGloballyCappedBalancedBaseValueProgramFor parameters q).runEstimate
        oracle.query =
      ((figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
        oracle.query).map (fun result => result.getD 0) := by
  let capP := figureOneGloballyCappedBalancedBaseProgramFor parameters q
  have hcap : capP.StronglyMeasurable oracle.query :=
    (figureOneBalancedBaseProgramFor_countedStronglyMeasurable
      parameters q I oracle).withQueryCap_stronglyMeasurable
        (figureOneGlobalQueryBudget q)
  unfold figureOneGloballyCappedBalancedBaseValueProgramFor
  change ((capP.bind fun estimate => .pure (estimate.getD 0)).runEstimate
    oracle.query) = (capP.runEstimate oracle.query).map fun result => result.getD 0
  rw [MembershipOracleProgram.runEstimate_bind oracle.query capP _ hcap]
  · exact Measure.bind_dirac_eq_map _ (measurable_optionGetD 0)
  · intro result
    trivial
  · simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp (measurable_optionGetD 0)

theorem figureOneGloballyCappedBalancedBaseProgramFor_failure_le
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hcost : FigureOneBalancedExpectedQueryCostFor parameters q I oracle) :
    (figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
        oracle.query {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let base := figureOneBalancedBaseProgramFor parameters q
  let capped := figureOneGloballyCappedBalancedBaseProgramFor parameters q
  let R := ENNReal.ofReal (figureOneGlobalExpectedCostConstant *
    volumeBaseComplexityRate q)
  let failure := capped.runEstimate oracle.query {none}
  have hmeas := figureOneBalancedBaseProgramFor_countedStronglyMeasurable
    parameters q I oracle
  have hR0 : R ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos figureOneGlobalExpectedCostConstant_pos
        (volumeBaseComplexityRate_pos_balanced q))
  have hRtop : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbudget : ENNReal.ofReal (64 : ℝ) * R ≤
      (figureOneGlobalQueryBudget q + 1 : ENNReal) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    simpa [R, mul_assoc] using figureOneGlobalQueryBudget_rate_lower q
  have hmarkov : (figureOneGlobalQueryBudget q + 1 : ENNReal) * failure ≤
      ∫⁻ outcome, (outcome.2 : ENNReal) ∂(base.run oracle.query) := by
    exact MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_cost
      oracle.query base (figureOneGlobalQueryBudget q)
        hmeas.executionMeasurable
  have hscaled : R * (failure * ENNReal.ofReal (64 : ℝ)) ≤ R := by
    calc
      R * (failure * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * R) * failure := by ring
      _ ≤ (figureOneGlobalQueryBudget q + 1 : ENNReal) * failure := by
        gcongr
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂(base.run oracle.query) := hmarkov
      _ ≤ R := hcost
  have hcancel : failure * ENNReal.ofReal (64 : ℝ) ≤ 1 := by
    have hdiv : failure * ENNReal.ofReal (64 : ℝ) ≤ R / R :=
      (ENNReal.le_div_iff_mul_le (Or.inl hR0) (Or.inl hRtop)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    simpa [ENNReal.div_self hR0 hRtop] using hdiv
  have hfailure : failure ≤ 1 / ENNReal.ofReal (64 : ℝ) :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 hcancel
  simpa [failure, capped] using hfailure

theorem figureOneGloballyCappedBalancedBaseValueProgramFor_failure_le
    (parameters : BalancedCoolingParameters)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hcost : FigureOneBalancedExpectedQueryCostFor parameters q I oracle)
    (hbase : (figureOneBalancedBaseProgramFor parameters q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ)) :
    (figureOneGloballyCappedBalancedBaseValueProgramFor parameters q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let bad := (accurateOutcome q I)ᶜ
  have hbad : MeasurableSet bad := (accurateOutcome_measurable q I).compl
  have hsubset : (fun result : Option ℝ => result.getD 0) ⁻¹' bad ⊆
      optionSomeEvent bad ∪ ({none} : Set (Option ℝ)) := by
    intro result hresult
    cases result with
    | none => simp
    | some value => simpa [optionSomeEvent] using hresult
  rw [runEstimate_figureOneGloballyCappedBalancedBaseValueProgramFor
    parameters q I oracle, Measure.map_apply measurable_optionGetD_zero hbad]
  calc
    ((figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
        oracle.query) ((fun result : Option ℝ => result.getD 0) ⁻¹' bad) ≤
      ((figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
        oracle.query) (optionSomeEvent bad ∪ ({none} : Set (Option ℝ))) :=
        measure_mono hsubset
    _ ≤
      (figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
          oracle.query (optionSomeEvent bad) +
        (figureOneGloballyCappedBalancedBaseProgramFor parameters q).runEstimate
          oracle.query {none} := measure_union_le _ _
    _ ≤
      (figureOneBalancedBaseProgramFor parameters q).runEstimate oracle.query bad +
        ENNReal.ofReal (1 / 64 : ℝ) := add_le_add
      (MembershipOracleProgram.runEstimate_withQueryCap_optionSomeEvent_le
        oracle.query (figureOneBalancedBaseProgramFor parameters q)
          (figureOneGlobalQueryBudget q)
          (figureOneBalancedBaseProgramFor_countedStronglyMeasurable
            parameters q I oracle).executionMeasurable bad hbad)
      (figureOneGloballyCappedBalancedBaseProgramFor_failure_le
        parameters q I oracle hcost)
    _ ≤ ENNReal.ofReal (13 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hbase le_rfl
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 13 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem volumeTheorem_balancedFor_of_baseFailure_and_expectedCost
    (parameters : BalancedCoolingParameters)
    (hbase : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
      (figureOneBalancedBaseProgramFor parameters q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ))
    (hcost : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
      FigureOneBalancedExpectedQueryCostFor parameters q I oracle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram
                (figureOneGloballyCappedBalancedBaseValueProgramFor parameters))
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              (figureOneGloballyCappedBalancedBaseValueProgramFor parameters) q).QueryBound calls ∧
            calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  let C₀ := 64 * figureOneGlobalExpectedCostConstant
  obtain ⟨C, hC, hamp⟩ := oracleProgram_proof_amplification C₀ (by
    dsimp [C₀]
    positivity [figureOneGlobalExpectedCostConstant_pos])
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  apply hamp (figureOneGloballyCappedBalancedBaseValueProgramFor parameters)
  · let μ := (figureOneGloballyCappedBalancedBaseValueProgramFor parameters q).runEstimate
      oracle.query
    have hstrong :=
      figureOneGloballyCappedBalancedBaseValueProgramFor_stronglyMeasurable
        parameters q I oracle
    let _ : IsProbabilityMeasure μ :=
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        hstrong.estimateMeasurable
    apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
    exact figureOneGloballyCappedBalancedBaseValueProgramFor_failure_le
      parameters q I oracle (hcost q I oracle) (hbase q I oracle hrounded)
  · exact
      figureOneGloballyCappedBalancedBaseValueProgramFor_stronglyMeasurable
        parameters q I oracle
  · refine ⟨figureOneGlobalQueryBudget q,
      ?_, by simp [figureOneGlobalQueryBudget, C₀]⟩
    exact figureOneGloballyCappedBalancedBaseValueProgramFor_queryBound
      parameters q

end ArlibCommunity.Algorithms.CV18
