import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGenericAmplification
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLocalCapPrefix
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalKernelInstantiation

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

theorem runEstimate_figureOneGloballyCappedBalancedBaseValueProgram
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    :
    (figureOneGloballyCappedBalancedBaseValueProgram q).runEstimate
        oracle.query =
      ((figureOneGloballyCappedBalancedBaseProgram q).runEstimate
        oracle.query).map (fun result => result.getD 0) := by
  let capP := figureOneGloballyCappedBalancedBaseProgram q
  have hcap : capP.StronglyMeasurable oracle.query :=
    (figureOneGlobalBalancedBaseProgram_countedStronglyMeasurable
      q I oracle).withQueryCap_stronglyMeasurable
        (figureOneGlobalQueryBudget q)
  unfold figureOneGloballyCappedBalancedBaseValueProgram
  change ((capP.bind fun estimate => .pure (estimate.getD 0)).runEstimate
    oracle.query) = (capP.runEstimate oracle.query).map fun result => result.getD 0
  rw [MembershipOracleProgram.runEstimate_bind oracle.query capP _ hcap]
  · exact Measure.bind_dirac_eq_map _ (measurable_optionGetD 0)
  · intro result
    trivial
  · simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp (measurable_optionGetD 0)

theorem figureOneGloballyCappedBalancedBaseValueProgram_failure_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hcost : FigureOneBalancedExpectedQueryCost q I oracle)
    (hbase : (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ)) :
    (figureOneGloballyCappedBalancedBaseValueProgram q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let bad := (accurateOutcome q I)ᶜ
  have hbad : MeasurableSet bad := (accurateOutcome_measurable q I).compl
  have hsubset : (fun result : Option ℝ => result.getD 0) ⁻¹' bad ⊆
      optionSomeEvent bad ∪ ({none} : Set (Option ℝ)) := by
    intro result hresult
    cases result with
    | none => simp
    | some value => simpa [optionSomeEvent] using hresult
  have hcapBound :=
    figureOneGloballyCappedBalancedBaseProgram_bad_add_failure_le
      q I oracle
        (figureOneGlobalBalancedBaseProgram_countedStronglyMeasurable q I oracle)
        hcost bad hbad
  rw [runEstimate_figureOneGloballyCappedBalancedBaseValueProgram q I oracle,
    Measure.map_apply measurable_optionGetD_zero hbad]
  calc
    ((figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query)
        ((fun result : Option ℝ => result.getD 0) ⁻¹' bad) ≤
      ((figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query)
        (optionSomeEvent bad ∪ ({none} : Set (Option ℝ))) := measure_mono hsubset
    _ ≤
      (figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query
          (optionSomeEvent bad) +
        (figureOneGloballyCappedBalancedBaseProgram q).runEstimate oracle.query
          {none} := measure_union_le _ _
    _ ≤
      (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query bad +
        ENNReal.ofReal (1 / 64 : ℝ) := hcapBound
    _ ≤ ENNReal.ofReal (13 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hbase le_rfl
    _ = ENNReal.ofReal (7 / 32 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 13 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)

theorem figureOneGloballyCappedBalancedBaseValueProgram_accuracy_of_baseFailure
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hcost : FigureOneBalancedExpectedQueryCost q I oracle)
    (hbase : (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query
      (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ)) :
    3 / 4 ≤ outcomeProbability
      (volumeAlgorithmLaw figureOneGloballyCappedBalancedBaseValueProgram
        q I oracle) (accurateOutcome q I) := by
  let μ := (figureOneGloballyCappedBalancedBaseValueProgram q).runEstimate
    oracle.query
  have hstrong :=
    figureOneGloballyCappedBalancedBaseValueProgram_stronglyMeasurable q I oracle
  let _ : IsProbabilityMeasure μ :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      hstrong.estimateMeasurable
  apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
  exact figureOneGloballyCappedBalancedBaseValueProgram_failure_le
    q I oracle hcost hbase

theorem figureOneGloballyCappedBalancedBaseValueProgram_accuracy_of_mappedLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hcost : FigureOneBalancedExpectedQueryCost q I oracle)
    (htransfer : MeasureLeUpTo
      ((balancedFigureOnePostInitialHistoryLaw figureOneGlobalBalancedParameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ))) :
    3 / 4 ≤ outcomeProbability
      (volumeAlgorithmLaw figureOneGloballyCappedBalancedBaseValueProgram
        q I oracle) (accurateOutcome q I) := by
  exact figureOneGloballyCappedBalancedBaseValueProgram_accuracy_of_baseFailure
    q I oracle hcost (balancedFigureOneBase_failure_le_of_mappedLaw
      figureOneGlobalBalancedParameters q I oracle hrounded htransfer)

theorem volumeTheorem_balanced_of_baseFailure_and_expectedCost
    (hbase : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
      (figureOneGlobalBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ))
    (hcost : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
      FigureOneBalancedExpectedQueryCost q I oracle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I),
        WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram
                figureOneGloballyCappedBalancedBaseValueProgram)
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              figureOneGloballyCappedBalancedBaseValueProgram q).QueryBound calls ∧
            calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  let C₀ := 64 * figureOneGlobalExpectedCostConstant
  obtain ⟨C, hC, hamp⟩ := oracleProgram_proof_amplification C₀ (by
    dsimp [C₀]
    positivity [figureOneGlobalExpectedCostConstant_pos])
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  exact hamp figureOneGloballyCappedBalancedBaseValueProgram q I oracle
    (figureOneGloballyCappedBalancedBaseValueProgram_accuracy_of_baseFailure
      q I oracle (hcost q I oracle) (hbase q I oracle hrounded))
    (figureOneGloballyCappedBalancedBaseValueProgram_stronglyMeasurable
      q I oracle)
    ⟨figureOneGlobalQueryBudget q,
      figureOneGloballyCappedBalancedBaseValueProgram_queryBound q,
      by simp [figureOneGlobalQueryBudget, C₀]⟩

/-- Final Theorem-1.1 assembly for the globally capped balanced implementation.
The two quantified premises are exactly the remaining walk-law and global
expected-cost bridges; all probability bookkeeping, cutoff handling, and
confidence amplification are discharged. -/
theorem volumeTheorem_balanced_of_mappedLaw_and_expectedCost
    (htransfer : ∀ (q : VolumeParams) (I : VolumeInput q.n),
      WellRounded q I → MeasureLeUpTo
        ((balancedFigureOnePostInitialHistoryLaw
          figureOneGlobalBalancedParameters q I).map
          (fun history => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (balancedCoolingChronologicalPhaseVariable q)
              (figureOneDependentPhaseCount q) history))
        ((figureOneIdealExperimentLaw q I).map
          (fun samples => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (figureOneChronologicalIdealCoordinate q)
              (figureOneDependentPhaseCount q) samples))
        (ENNReal.ofReal (1 / 64 : ℝ)))
    (hcost : ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I),
      FigureOneBalancedExpectedQueryCost q I oracle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I),
        WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram
                figureOneGloballyCappedBalancedBaseValueProgram)
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              figureOneGloballyCappedBalancedBaseValueProgram q).QueryBound calls ∧
            calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  apply volumeTheorem_balanced_of_baseFailure_and_expectedCost
    (hcost := hcost)
  intro q I oracle hrounded
  exact balancedFigureOneBase_failure_le_of_mappedLaw
    figureOneGlobalBalancedParameters q I oracle hrounded
      (htransfer q I hrounded)

end ArlibCommunity.Algorithms.CV18
