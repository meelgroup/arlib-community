/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalKernelInstantiation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCorrectedErrorAllocation

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- Uniform envelope for one complete Figure-One phase. -/
noncomputable def figureOnePhaseReplacementBudget (q : VolumeParams) : ENNReal :=
  figureOneDependentMaxSampleCount q •
    ENNReal.ofReal (figureOnePerSampleMixingError q)

/-- The corrected per-sample theorem, enlarged only from the actual phase
sample count to the uniform Figure-One maximum. -/
theorem MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_max
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (q : VolumeParams)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    {totalBudget : ENNReal}
    (hstep : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealK initial i).bind (actualK i))
      (iteratedKernelLaw idealK initial (i + 1)) totalBudget)
    (hbudget : totalBudget ≤
      ENNReal.ofReal (figureOnePerSampleMixingError q))
    (k : ℕ) (hk : k ≤ figureOneDependentMaxSampleCount q)
    (average : State → Output) (haverage : Measurable average) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK initial k).map average)
      ((iteratedKernelLaw idealK initial k).map average)
      (figureOnePhaseReplacementBudget q) := by
  have h := MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_budget
    q actualK idealK initial hactualMeas hactualProb hstep hbudget
      k average haverage
  exact h.mono_error <| nsmul_le_nsmul_left (show
    0 ≤ ENNReal.ofReal (figureOnePerSampleMixingError q) from bot_le) hk

/-- Summing the uniform complete-phase envelope over the finite cooling
horizon occupies exactly the `1/64` final event-transfer slot. -/
theorem figureOnePhaseReplacementBudget_sum_le (q : VolumeParams) :
    figureOneDependentPhaseCount q • figureOnePhaseReplacementBudget q ≤
      ENNReal.ofReal (1 / 64 : ℝ) := by
  unfold figureOnePhaseReplacementBudget
  calc
    figureOneDependentPhaseCount q •
        (figureOneDependentMaxSampleCount q •
          ENNReal.ofReal (figureOnePerSampleMixingError q)) =
      (figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q) •
          ENNReal.ofReal (figureOnePerSampleMixingError q) := by
        simp [nsmul_eq_mul, Nat.cast_mul]
        ring
    _ ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
      figureOne_exactChance_event_budget_le q

/-- Outer chronological replacement: a complete-phase domination at every
step yields the mapped scalar-law `1/64` premise consumed by the balanced
base-run theorem. -/
theorem MeasureLeUpTo.map_figureOnePhaseIteration
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (q : VolumeParams)
    (actualPhase idealPhase : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualPhase i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualPhase i state))
    (hphase : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealPhase initial i).bind (actualPhase i))
      (iteratedKernelLaw idealPhase initial (i + 1))
      (figureOnePhaseReplacementBudget q))
    (output : State → Output) (houtput : Measurable output) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualPhase initial
        (figureOneDependentPhaseCount q)).map output)
      ((iteratedKernelLaw idealPhase initial
        (figureOneDependentPhaseCount q)).map output)
      (ENNReal.ofReal (1 / 64 : ℝ)) := by
  have h := MeasureLeUpTo.map_iteratedKernelLaw_exactChance
    actualPhase idealPhase initial hactualMeas hactualProb hphase
      (figureOneDependentPhaseCount q) output houtput
  exact h.mono_error (figureOnePhaseReplacementBudget_sum_le q)

/-- Final schedule adapter.  A concrete chronological phase construction
only has to identify its two terminal mapped laws and prove the per-phase
replacement premise; the complete analytic and base-run assembly is then
automatic. -/
theorem balancedFigureOneBase_failure_le_of_phaseIteration
    {State : Type*} [MeasurableSpace State]
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (actualPhase idealPhase : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualPhase i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualPhase i state))
    (hphase : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealPhase initial i).bind (actualPhase i))
      (iteratedKernelLaw idealPhase initial (i + 1))
      (figureOnePhaseReplacementBudget q))
    (output : State → ℝ) (houtput : Measurable output)
    (hactualLaw :
      (iteratedKernelLaw actualPhase initial
          (figureOneDependentPhaseCount q)).map output =
        (balancedFigureOnePostInitialHistoryLaw parameters q I).map
          (fun history => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (balancedCoolingChronologicalPhaseVariable q)
              (figureOneDependentPhaseCount q) history))
    (hidealLaw :
      (iteratedKernelLaw idealPhase initial
          (figureOneDependentPhaseCount q)).map output =
        (figureOneIdealExperimentLaw q I).map
          (fun samples => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (figureOneChronologicalIdealCoordinate q)
              (figureOneDependentPhaseCount q) samples)) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have htransfer := MeasureLeUpTo.map_figureOnePhaseIteration q
    actualPhase idealPhase initial hactualMeas hactualProb hphase output houtput
  rw [hactualLaw, hidealLaw] at htransfer
  exact balancedFigureOneBase_failure_le_of_mappedLaw
    parameters q I oracle hrounded htransfer

/-! ## Paper-faithful Lemma 7.15 specialization

The exact-chance route above is useful when a full-history replacement is
available.  The following theorem records the alternative route taken in
CV18 itself: apply Lemma 7.15 directly to the chronological phase averages
stored by the executable history.  All structural obligations (ordering,
measurability, product identity, continuation-law identity, finite schedule
arithmetic, truncation, and the `13/64` base budget) are discharged here.

The remaining hypotheses are deliberately only the substantive statements
of Lemma 7.17(b,c): first/second moments of the executable phase averages and
approximate independence of the accumulated truncated product from the next
truncated phase average. -/

/-- Direct balanced-base assembly from the paper's finite chronological
moment and Lemma 7.17(c) premises.  This avoids the stronger full-history TV
replacement required by `balancedFigureOneBase_failure_le_of_phaseIteration`.
-/
theorem balancedFigureOneBase_failure_le_of_actualChronologicalMoments
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hW0 : ∀ j history,
      0 ≤ balancedCoolingChronologicalPhaseVariable q j history)
    (hWmem : ∀ j, MemLp
      (balancedCoolingChronologicalPhaseVariable q j) 2
      (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hWmean : ∀ j,
      (∫ history, balancedCoolingChronologicalPhaseVariable q j history
        ∂balancedFigureOnePostInitialHistoryLaw parameters q I) =
          figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j,
      (∫ history,
          balancedCoolingChronologicalPhaseVariable q j history ^ 2
        ∂balancedFigureOnePostInitialHistoryLaw parameters q I) ≤
          figureOneChronologicalMomentFactor q j *
            figureOneChronologicalRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I
            (balancedFigureOnePostInitialHistoryLaw parameters q I)
            (balancedCoolingChronologicalPhaseVariable q))
          (figureOneChronologicalTruncatedPhase q I
            (balancedCoolingChronologicalPhaseVariable q)) i)
        (figureOneChronologicalTruncatedPhase q I
          (balancedCoolingChronologicalPhaseVariable q) (i + 1))
        (balancedFigureOnePostInitialHistoryLaw parameters q I)) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let mu := balancedFigureOnePostInitialHistoryLaw parameters q I
  let W := balancedCoolingChronologicalPhaseVariable q
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    balancedFigureOnePostInitialHistoryLaw_isProbabilityMeasure parameters q I
  have hWmeas : ∀ j, Measurable (W j) :=
    fun j => measurable_balancedCoolingChronologicalPhaseVariable q j
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I mu W hWmeas hW0 hWmem hWmean hWsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I mu W hWmeas hW0 hWmem hWmean hWsecond
  have htransfer : MeasureLeUpTo
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (ENNReal.ofReal (1 / 64 : ℝ)) :=
    (MeasureLeUpTo.refl _).mono_error bot_le
  have hpost :=
    balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
      parameters q I oracle (figureOneRadialTruncationBound q I hrounded)
      mu (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      (by
        unfold dependentPhaseSampleProduct
        exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
          fun j _ => hWmeas (j + 1))
      mean hmeanApprox htail
      (balancedFigureOnePostInitialHistoryLaw_ae_hasProduct parameters q I)
      htransfer
  exact balancedFigureOneBase_failure_le_of_directPostInitial
    parameters q I oracle hpost

/- The next four definitions use the executable history's own moments.  In
particular they do not assert that a finite walk has the exact stationary
mean; that quantitative comparison is kept visible in the final
`RelativeApprox` premise below. -/

noncomputable def balancedFigureOneActualRawMean
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history, balancedCoolingChronologicalPhaseVariable q j history
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

noncomputable def balancedFigureOneActualTruncatedPhase
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ℕ → Option (BalancedCoolingHistory q.n) → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (balancedFigureOneActualRawMean parameters q I)
    (balancedCoolingChronologicalPhaseVariable q)

noncomputable def balancedFigureOneActualTruncatedMean
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history, balancedFigureOneActualTruncatedPhase parameters q I j history
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

noncomputable def balancedFigureOneActualTruncatedSecond
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history,
      balancedFigureOneActualTruncatedPhase parameters q I j history ^ 2
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

/-- Fully law-correct specialization of Lemma 7.15.  Unlike the preceding
stationary-moment convenience theorem, the raw and truncated means here are
defined from the finite executable history law itself.  Thus all integral
identities are discharged by reflexivity.  The remaining hypotheses are
exactly the quantitative content needed from the paper's Lemma 7.17(b,c):
moment/truncation comparisons, product-center transfer, and adjacent-phase
approximate independence. -/
theorem balancedFigureOneBase_failure_le_of_lemma717bc
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hW0 : ∀ j history,
      0 ≤ balancedCoolingChronologicalPhaseVariable q j history)
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (balancedCoolingChronologicalPhaseVariable q j)
        (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hmeanPos : ∀ j,
      0 < balancedFigureOneActualTruncatedMean parameters q I j)
    (hrawMeanPos : ∀ j,
      0 < balancedFigureOneActualRawMean parameters q I j)
    (hrawMean_le : ∀ j,
      balancedFigureOneActualRawMean parameters q I j ≤
        2 * balancedFigureOneActualTruncatedMean parameters q I j)
    (hmeanSecond : ∀ j,
      balancedFigureOneActualTruncatedMean parameters q I j ^ 2 ≤
        balancedFigureOneActualTruncatedSecond parameters q I j)
    (hrawSecond : ∀ j,
      balancedFigureOneActualRawMean parameters q I j ^ 2 ≤
        2 * balancedFigureOneActualTruncatedSecond parameters q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (balancedFigureOneActualTruncatedMean parameters q I)
          (balancedFigureOneActualTruncatedPhase parameters q I) i)
        (balancedFigureOneActualTruncatedPhase parameters q I (i + 1))
        (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedSecond parameters q I) i ≤
        2 * dependentPhaseMeanProduct
          (balancedFigureOneActualTruncatedMean parameters q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedSecond parameters q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedMean parameters q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (balancedFigureOneActualTruncatedMean parameters q I)
        (figureOneDependentPhaseCount q))) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let mu := balancedFigureOnePostInitialHistoryLaw parameters q I
  let W := balancedCoolingChronologicalPhaseVariable q
  let rawMean := balancedFigureOneActualRawMean parameters q I
  let V := balancedFigureOneActualTruncatedPhase parameters q I
  let mean := balancedFigureOneActualTruncatedMean parameters q I
  let second := balancedFigureOneActualTruncatedSecond parameters q I
  let _ : IsProbabilityMeasure mu :=
    balancedFigureOnePostInitialHistoryLaw_isProbabilityMeasure parameters q I
  have hWmeas : ∀ j, Measurable (W j) :=
    fun j => measurable_balancedCoolingChronologicalPhaseVariable q j
  have hVmeas : ∀ j, Measurable (V j) := by
    intro j
    exact (hWmeas j).min measurable_const
  have hV0 : ∀ j history, 0 ≤ V j history := by
    intro j history
    exact le_min (hW0 j history)
      (mul_nonneg (figureOneDependentAlpha_pos q).le
        (hrawMeanPos j).le)
  have hVcap : ∀ j history,
      V j history ≤ figureOneDependentAlpha q * rawMean j := by
    intro j history
    exact min_le_right _ _
  have htail := measure_dependentPhaseSampleProduct_figureOne_le
    q mu mean rawMean second V W
      (fun j => (hmeanPos j).le) hmeanPos
      (fun j => (hrawMeanPos j).le) hrawMeanPos hrawMean_le
      (fun j => (sq_nonneg (mean j)).trans (hmeanSecond j))
      hmeanSecond hrawSecond hVmeas hV0 hVcap
      (fun _ => rfl) (fun _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun j _ _ => hWmeas j) (fun j _ _ => hW0 j)
      hWint (fun _ _ _ => rfl) hind hrelative htailSecond
  have htransfer : MeasureLeUpTo
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (ENNReal.ofReal (1 / 64 : ℝ)) :=
    (MeasureLeUpTo.refl _).mono_error bot_le
  have hpost :=
    balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
      parameters q I oracle (figureOneRadialTruncationBound q I hrounded)
      mu (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      (by
        unfold dependentPhaseSampleProduct
        exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
          fun j _ => hWmeas (j + 1))
      (dependentPhaseMeanProduct mean (figureOneDependentPhaseCount q))
      hmeanApprox htail
      (balancedFigureOnePostInitialHistoryLaw_ae_hasProduct parameters q I)
      htransfer
  exact balancedFigureOneBase_failure_le_of_directPostInitial
    parameters q I oracle hpost

/-! ## Complete-phase lift of the first retained transition

For Lemma 7.17(c), it is unnecessary (and generally too strong) to compare
every within-phase transition with an independent draw.  After replacing the
first transition, the remaining collector is the same probability kernel on
both sides, so `MeasureLeUpTo.bind_same` preserves the first-transition error
through the entire phase. -/

/-- A first accepted-target replacement lifts, with no additional loss, to
the complete accumulated phase law.  The comparison phase starts from the
fixed `target` law and then runs exactly the same remaining collector. -/
theorem MeasureLeUpTo.bind_balancedAccuracyTransitionCollectLaw_of_first
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (mu : Measure (AmbientSpace q.n))
    (target : Measure (Option (AmbientSpace q.n)))
    {delta : ENNReal}
    (hfirst : MeasureLeUpTo
      (mu.bind (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit)) target delta) :
    MeasureLeUpTo
      (mu.bind fun current =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit (samples + 1) 0 current)
      (target.bind fun result =>
        match result with
        | none => Measure.dirac none
        | some point =>
            balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples (weight point)
                (accuracyScaleFactor q • point))
      delta := by
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point)
  have hcollect :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit samples
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point) := by
      exact hcollect.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
        infer_instance
    | some point => exact hcollect.2 _ _
  have htransition :=
    balancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  have hsource :
      (mu.bind fun current =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit (samples + 1) 0 current) =
        (mu.bind (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride retryLimit)).bind tail := by
    calc
      _ = mu.bind fun current =>
          (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit current).bind tail := by
        apply Measure.bind_congr_right
        filter_upwards with current
        simp [balancedAccuracyTransitionCollectLaw, tail]
        rfl
      _ = _ :=
        (Measure.bind_bind htransition.1.aemeasurable htail.aemeasurable).symm
  change MeasureLeUpTo _ (target.bind tail) delta
  rw [hsource]
  exact hfirst.bind_same htail htailProb

/-- Paper-level complete-phase form of Lemma 7.17(b,c).  A uniform
first-transition replacement for every `2`-warm conditioning of the retained
history is lifted through all remaining samples, and arbitrary measurable
past-product and phase-estimator postprocessing then gives the required
approximate independence. -/
theorem approxIndepFun_balancedCompletePhase_of_warm_first
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (target : Measure (Option (AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hfirst : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu (history.map state) →
      MeasureLeUpTo
        (mu.bind (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride retryLimit)) target delta)
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget : (delta + delta).toReal ≤
      3 * (k : ℝ) * (m : ℝ) * nu) :
    let phaseTarget := target.bind fun result =>
      match result with
      | none => Measure.dirac none
      | some point =>
          balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit samples (weight point)
              (accuracyScaleFactor q • point)
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit (samples + 1) 0 current) ∘ state)) := by
  dsimp only
  let phaseKernel : AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun current =>
    balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
      properStride retryLimit (samples + 1) 0 current
  let phaseTarget : Measure (Option (ℝ × AmbientSpace q.n)) :=
    target.bind fun result =>
      match result with
      | none => Measure.dirac none
      | some point =>
          balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit samples (weight point)
              (accuracyScaleFactor q • point)
  have hphase :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit (samples + 1)
  have htail :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit samples
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point)
  have htailMeas : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point) := by
      exact htail.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none => infer_instance
    | some point => exact htail.2 _ _
  let _ : IsProbabilityMeasure phaseTarget :=
    MeasureTheory.isProbabilityMeasure_bind htailMeas.aemeasurable
      (ae_of_all _ htailProb)
  apply approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo
    history state hstate
      (hphase.1.comp (measurable_const.prodMk measurable_id))
      (fun current => hphase.2 0 current) phaseTarget hdelta ?_
      (pastProduct := pastProduct) (nextEstimator := nextEstimator)
      hpastProduct hnextEstimator k m nu hbudget
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  exact MeasureLeUpTo.bind_balancedAccuracyTransitionCollectLaw_of_first
    q I hsigma2 hweight proposalCap properStride retryLimit samples mu target
      (hfirst mu hmu hwarm)

/-- Complete-phase counterpart of
`approxIndepFun_balancedTransition_history_of_warm_blocks`.  The same KLS
first/retry block premises are paid only for the first retained transition;
the remaining `samples` transitions form common postprocessing. -/
theorem approxIndepFun_balancedCompletePhase_history_of_warm_blocks
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride attempts samples : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hfirstError : firstError ≠ ⊤) (hretryError : retryError ≠ ⊤)
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu (history.map state) →
      MeasureLeUpTo
        ((mu.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) firstError)
    (hretryBlock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError)
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget :
      let rejectMass :=
        balancedRejectedStateMeasure q I sigma2 pi Set.univ
      let error := firstError + rejectMass *
        balancedRetryError retryError rejectMass attempts
      (error + error).toReal ≤ 3 * (k : ℝ) * (m : ℝ) * nu) :
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
            properStride (attempts + 1) (samples + 1) 0 current) ∘ state)) := by
  let rejectMass :=
    balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let error := firstError + rejectMass *
    balancedRetryError retryError rejectMass attempts
  let target :=
    (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map some
  have hrejectedTop : rejectMass ≠ ⊤ := by
    dsimp only [rejectMass]
    have hle := balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  have hretryFinite :
      balancedRetryError retryError rejectMass attempts ≠ ⊤ :=
    balancedRetryError_ne_top hretryError hrejectedTop attempts
  have herror : error ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨hfirstError, ENNReal.mul_ne_top hrejectedTop hretryFinite⟩
  let _ : IsProbabilityMeasure
      (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi) :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply approxIndepFun_balancedCompletePhase_of_warm_first
    q I hsigma2 hweight proposalCap properStride (attempts + 1) samples
      history state hstate target herror ?_
      (pastProduct := pastProduct) (nextEstimator := nextEstimator)
      hpastProduct hnextEstimator k m nu
  · simpa [error, rejectMass] using hbudget
  · intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    simpa [target, error, rejectMass] using
      (bind_balancedTransition_leUpTo_acceptedTarget
        q I hsigma2 proposalCap properStride attempts mu pi
          hacceptedLower hrejectedLower
          (hfirstBlock mu hmu hwarm) hretryBlock)

#print axioms MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_max
#print axioms figureOnePhaseReplacementBudget_sum_le
#print axioms MeasureLeUpTo.map_figureOnePhaseIteration
#print axioms balancedFigureOneBase_failure_le_of_phaseIteration
#print axioms balancedFigureOneBase_failure_le_of_actualChronologicalMoments
#print axioms balancedFigureOneBase_failure_le_of_lemma717bc
#print axioms MeasureLeUpTo.bind_balancedAccuracyTransitionCollectLaw_of_first
#print axioms approxIndepFun_balancedCompletePhase_of_warm_first
#print axioms approxIndepFun_balancedCompletePhase_history_of_warm_blocks

end

end ArlibCommunity.Algorithms.CV18
