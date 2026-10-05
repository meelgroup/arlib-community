/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalPhase

/-!
# Randomized ideal chronological history laws

The chronological comparison state used earlier in the development carries a
complete ideal experiment beside the visible history.  That representation is
convenient for proving the final product identity, but it is too strong for a
one-phase replacement theorem: the next ideal history is visibly correlated
with the carried experiment, whereas the executable phase uses fresh
randomness.

This file projects away the carried experiment before every replacement.  The
resulting sequence of history laws is exactly the law of successively appending
fresh independent ideal phase blocks.  Exact-chance induction only needs this
sequence of measures and its one-step replacement estimates; no pointwise
ideal kernel on a state containing future randomness is required.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Exact-chance induction against an explicitly supplied sequence of ideal
prefix laws.  This is the law-sequence form of
`MeasureLeUpTo.iteratedKernelLaw_exactChance`. -/
theorem MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (actualInitial : Measure S)
    (idealLaw : ℕ → Measure S) {nu : ENNReal}
    (hinitial : MeasureLeUpTo actualInitial (idealLaw 0) 0)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t →
      MeasureLeUpTo ((idealLaw i).bind (actualK i)) (idealLaw (i + 1)) nu) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t) (idealLaw t) (t • nu) := by
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      have ih' := ih fun i hi => hstep i (hi.trans (Nat.lt_succ_self t))
      have hnext := MeasureLeUpTo.bind_then_replace ih' (actualK t)
        (hactualMeas t) (hactualProb t) (hstep t (Nat.lt_succ_self t))
      simpa only [iteratedKernelLaw_succ, succ_nsmul] using hnext

/-- Independent fresh randomness can be exposed as a bind from the prefix
law.  This is the generic identity used to turn a latent product experiment
into a genuinely randomized next-history kernel. -/
theorem bind_map_fresh_eq_map_append_of_indepFun
    {Omega H B T : Type*} [MeasurableSpace Omega] [MeasurableSpace H]
    [MeasurableSpace B] [MeasurableSpace T]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (past : Omega → H) (fresh : Omega → B)
    (append : H → B → T)
    (hpast : Measurable past) (hfresh : Measurable fresh)
    (happend : Measurable (Function.uncurry append))
    (hind : IndepFun past fresh mu) :
    (mu.map past).bind (fun history =>
        (mu.map fresh).map (append history)) =
      mu.map (fun omega => append (past omega) (fresh omega)) := by
  have hleft :
      ((mu.map past).prod (mu.map fresh)).map
          (Function.uncurry append) =
        (mu.map past).bind (fun history =>
          (mu.map fresh).map (append history)) := by
    have hprodKernel : Measurable fun history : H =>
        (mu.map fresh).map (Prod.mk history) :=
      Measurable.map_prodMk_left
    rw [Measure.prod]
    rw [map_bind_eq_bind_map_of_measurable
      (mu.map past) hprodKernel happend]
    apply Measure.bind_congr_right
    filter_upwards with history
    calc
      ((mu.map fresh).map (Prod.mk history)).map
          (Function.uncurry append) =
        (mu.map fresh).map
          (Function.uncurry append ∘ Prod.mk history) :=
        Measure.map_map happend (measurable_const.prodMk measurable_id)
      _ = (mu.map fresh).map (append history) := by rfl
  rw [← hleft, ← hind.map_prod_eq_prod_map_map
    hpast.aemeasurable hfresh.aemeasurable]
  rw [Measure.map_map happend (hpast.prodMk hfresh)]
  rfl

/-- The ideal chronological prefix after future ideal randomness has been
projected away.  Distributionally, this is the history obtained by drawing a
fresh independent ideal block at each completed phase. -/
noncomputable def figureOneRandomizedIdealHistoryLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phases : ℕ) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (iteratedKernelLaw (figureOneIdealChronologicalPhaseKernel q)
    (scheduledChronologicalCommonInitial q I) phases).map Prod.snd

/-- Append one freshly drawn ideal phase block to a visible history. -/
noncomputable def figureOneRandomizedIdealHistoryAppend
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    Option (BalancedCoolingHistory q.n) →
      FigureOneIdealPhaseSampleSpace q
        (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩) →
      Option (BalancedCoolingHistory q.n) :=
  fun history samples => match history with
    | none => none
    | some history => balancedCoolingHistorySnocTerminal history <| some
        (figureOneIdealPhaseEstimator q
          (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩) samples,
        figureOneIdealPhaseRetainedPoint q
          (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩) samples)

theorem measurable_uncurry_figureOneRandomizedIdealHistoryAppend
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    Measurable (Function.uncurry
      (figureOneRandomizedIdealHistoryAppend q phase hphase)) := by
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  have hresult : Measurable fun samples : FigureOneIdealPhaseSampleSpace q p =>
      (figureOneIdealPhaseEstimator q p samples,
        figureOneIdealPhaseRetainedPoint q p samples) :=
    (figureOneIdealPhaseEstimator_measurable q p).prodMk
      (measurable_figureOneIdealPhaseRetainedPoint q p)
  have hsome : Measurable fun state :
      FigureOneIdealPhaseSampleSpace q p × BalancedCoolingHistory q.n =>
      balancedCoolingHistorySnocTerminal state.2 (some
        (figureOneIdealPhaseEstimator q p state.1,
          figureOneIdealPhaseRetainedPoint q p state.1)) :=
    measurable_balancedCoolingHistorySnocTerminal.comp <|
      measurable_snd.prodMk (measurable_some.comp (hresult.comp measurable_fst))
  have hordered : Measurable fun state :
      FigureOneIdealPhaseSampleSpace q p ×
        Option (BalancedCoolingHistory q.n) =>
      figureOneRandomizedIdealHistoryAppend q phase hphase state.2 state.1 := by
    convert Measurable.optionCases
      ((fun _ => 0), 0, (1 : ℝ), (0 : AmbientSpace q.n))
      (noneValue := fun _ : FigureOneIdealPhaseSampleSpace q p =>
        (none : Option (BalancedCoolingHistory q.n)))
      (someValue := fun state =>
        balancedCoolingHistorySnocTerminal state.2 (some
          (figureOneIdealPhaseEstimator q p state.1,
            figureOneIdealPhaseRetainedPoint q p state.1)))
      measurable_const hsome using 1
    funext state
    cases state.2 <;> rfl
  exact hordered.comp (measurable_snd.prodMk measurable_fst)

/-- The freshly randomized ideal phase kernel on visible history alone. -/
noncomputable def figureOneRandomizedIdealHistoryKernel
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) :=
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  fun history => (figureOneIdealPhaseLaw q I p).map
    (figureOneRandomizedIdealHistoryAppend q phase hphase history)

theorem figureOneRandomizedIdealHistoryKernel_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    Measurable (figureOneRandomizedIdealHistoryKernel q I phase hphase) ∧
    ∀ history, IsProbabilityMeasure
      (figureOneRandomizedIdealHistoryKernel q I phase hphase history) := by
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  let block := figureOneIdealPhaseLaw q I p
  let append := figureOneRandomizedIdealHistoryAppend q phase hphase
  have happend := measurable_uncurry_figureOneRandomizedIdealHistoryAppend
    q phase hphase
  constructor
  · exact measurable_measure_map_param_variable measurable_const
      (fun _ => figureOneIdealPhaseLaw_isProbabilityMeasure q I p)
      happend
  · intro history
    let _ : IsProbabilityMeasure block :=
      figureOneIdealPhaseLaw_isProbabilityMeasure q I p
    exact Measure.isProbabilityMeasure_map
      (happend.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- If the visible ideal prefix is independent of the next latent phase
block, then projecting the old deterministic construction is exactly one
step of the genuinely randomized history kernel. -/
theorem figureOneRandomizedIdealHistoryLaw_succ_of_indepFun
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (hind : IndepFun
      (fun state => (figureOneIdealChronologicalState q phase state).2)
      (fun state => state.1
        (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩))
      (scheduledChronologicalCommonInitial q I)) :
    (figureOneRandomizedIdealHistoryLaw q I phase).bind
        (figureOneRandomizedIdealHistoryKernel q I phase hphase) =
      figureOneRandomizedIdealHistoryLaw q I (phase + 1) := by
  let common := scheduledChronologicalCommonInitial q I
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  let past := fun state : FigureOneIdealExperimentSpace q ×
      Option (BalancedCoolingHistory q.n) =>
    (figureOneIdealChronologicalState q phase state).2
  let fresh := fun state : FigureOneIdealExperimentSpace q ×
      Option (BalancedCoolingHistory q.n) => state.1 p
  let append := figureOneRandomizedIdealHistoryAppend q phase hphase
  let _ (i : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I i) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I i
  let initialHistory :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory
  let _ : IsProbabilityMeasure initialHistory :=
    Measure.isProbabilityMeasure_map
      measurable_balancedCoolingInitialHistory.aemeasurable
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  let _ : IsProbabilityMeasure common := by
    dsimp [common, scheduledChronologicalCommonInitial]
    infer_instance
  have hpast : Measurable past :=
    measurable_snd.comp (measurable_figureOneIdealChronologicalState q phase)
  have hfresh : Measurable fresh :=
    (measurable_pi_apply p).comp measurable_fst
  have hfreshLaw : common.map fresh = figureOneIdealPhaseLaw q I p := by
    rw [show common.map fresh = (common.map Prod.fst).map (fun samples =>
        samples p) by
      exact (Measure.map_map (measurable_pi_apply p) measurable_fst).symm]
    have hfst : common.map Prod.fst = figureOneIdealExperimentLaw q I := by
      dsimp only [common, scheduledChronologicalCommonInitial]
      let initialHistory :=
        (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
            balancedCoolingInitialHistory
      let _ : IsProbabilityMeasure initialHistory :=
        Measure.isProbabilityMeasure_map
          measurable_balancedCoolingInitialHistory.aemeasurable
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [hfst]
    exact (measurePreserving_eval (figureOneIdealPhaseLaw q I) p).map_eq
  have hbind := bind_map_fresh_eq_map_append_of_indepFun
    common past fresh append hpast hfresh
      (measurable_uncurry_figureOneRandomizedIdealHistoryAppend
        q phase hphase)
      (by simpa [past, fresh] using hind)
  rw [hfreshLaw] at hbind
  have hpastLaw :
      figureOneRandomizedIdealHistoryLaw q I phase = common.map past := by
    rw [figureOneRandomizedIdealHistoryLaw,
      iteratedKernelLaw_figureOneIdealChronologicalPhaseKernel]
    exact Measure.map_map measurable_snd
      (measurable_figureOneIdealChronologicalState q phase)
  rw [hpastLaw]
  rw [show figureOneRandomizedIdealHistoryKernel q I phase hphase =
      fun history => (figureOneIdealPhaseLaw q I p).map (append history) by
    rfl]
  rw [hbind]
  rw [figureOneRandomizedIdealHistoryLaw,
    iteratedKernelLaw_figureOneIdealChronologicalPhaseKernel,
    Measure.map_map measurable_snd
      (measurable_figureOneIdealChronologicalState q (phase + 1))]
  apply Measure.map_congr
  filter_upwards with state
  simp only [Function.comp_apply, figureOneIdealChronologicalState]
  rw [dif_pos hphase]
  dsimp only [append, past, fresh,
    figureOneRandomizedIdealHistoryAppend,
    figureOneIdealChronologicalAppend]
  rw [figureOneIdealChronologicalState_fst q phase state]
  cases (figureOneIdealChronologicalState q phase state).2 <;> rfl

theorem figureOneRandomizedIdealHistoryLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phases : ℕ) :
    IsProbabilityMeasure (figureOneRandomizedIdealHistoryLaw q I phases) := by
  let idealInitial := scheduledChronologicalCommonInitial q I
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  let initialHistory :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory
  let _ : IsProbabilityMeasure initialHistory :=
    Measure.isProbabilityMeasure_map
      measurable_balancedCoolingInitialHistory.aemeasurable
  let _ : IsProbabilityMeasure idealInitial := by
    dsimp [idealInitial, scheduledChronologicalCommonInitial]
    infer_instance
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw (figureOneIdealChronologicalPhaseKernel q)
        idealInitial phases) :=
    iteratedKernelLaw_isProbabilityMeasure
      (figureOneIdealChronologicalPhaseKernel q) idealInitial inferInstance
      (fun phase =>
        (figureOneIdealChronologicalPhaseKernel_measurable_and_probability
          q phase).1)
      (fun phase state =>
        (figureOneIdealChronologicalPhaseKernel_measurable_and_probability
          q phase).2 state)
      phases
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

theorem figureOneRandomizedIdealHistoryLaw_zero
    (q : VolumeParams) (I : VolumeInput q.n) :
    figureOneRandomizedIdealHistoryLaw q I 0 =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
          balancedCoolingInitialHistory := by
  simpa [figureOneRandomizedIdealHistoryLaw] using
    scheduledChronologicalCommonInitial_map_snd q I

/-- Projecting away the latent ideal experiment retains the already-proved
ideal scalar product law. -/
theorem figureOneRandomizedIdealHistoryLaw_map_output
    (q : VolumeParams) (I : VolumeInput q.n) :
    (figureOneRandomizedIdealHistoryLaw q I
      (figureOneDependentPhaseCount q)).map
        (balancedFigureOneHistoryEstimate q) =
      (figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples) := by
  rw [figureOneRandomizedIdealHistoryLaw, Measure.map_map
    (measurable_balancedFigureOneHistoryEstimate q) measurable_snd]
  exact figureOneIdealChronologicalIteration_map_output q I

/-- Correct outer exact-chance transfer on history alone.  Its premise is a
complete-phase replacement integrated against the randomized ideal prefix,
so it cannot inspect or correlate with unused future ideal samples. -/
theorem MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n)
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel parameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    MeasureLeUpTo
      ((scheduledBalancedForwardHistoryLaw parameters q I
        (figureOneDependentPhaseCount q)).map
          (balancedFigureOneHistoryEstimate q))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ)) := by
  let actualK := scheduledBalancedForwardPhaseKernel parameters q I
  let actualInitial :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory
  let idealLaw := figureOneRandomizedIdealHistoryLaw q I
  have hhistory := MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
    actualK actualInitial idealLaw
      (by
        rw [show idealLaw 0 = actualInitial by
          simpa [idealLaw, actualInitial] using
            figureOneRandomizedIdealHistoryLaw_zero q I]
        exact MeasureLeUpTo.refl actualInitial)
      (fun phase =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phase).1)
      (fun phase history =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phase).2 history)
      (figureOneDependentPhaseCount q)
      (fun phase hp => by simpa [idealLaw, actualK] using hphase phase hp)
  have hmapped := hhistory.map
    (measurable_balancedFigureOneHistoryEstimate q)
  have hbudget := figureOnePhaseReplacementBudget_sum_le q
  rw [show iteratedKernelLaw actualK actualInitial
        (figureOneDependentPhaseCount q) =
      scheduledBalancedForwardHistoryLaw parameters q I
        (figureOneDependentPhaseCount q) by rfl,
    figureOneRandomizedIdealHistoryLaw_map_output q I] at hmapped
  exact hmapped.mono_error hbudget

/-- Post-initial accuracy capstone with the corrected, history-only ideal
prefix premise. -/
theorem scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (hrounded : WellRounded q I)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        (scheduledBalancedForwardHistoryLaw parameters q I
          (figureOneDependentPhaseCount q)).map
            (balancedFigureOneHistoryEstimate q))
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel parameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  have htransfer := MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
    parameters q I hphase
  let W := figureOneChronologicalIdealCoordinate q
  let mu := figureOneIdealExperimentLaw q I
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  have hmeas : ∀ j, Measurable (W j) :=
    fun j => figureOneChronologicalIdealCoordinate_measurable q j
  have hnonneg : ∀ j samples, 0 ≤ W j samples :=
    fun j samples => figureOneChronologicalIdealCoordinate_nonneg q j samples
  have hmem : ∀ j, MemLp (W j) 2 mu :=
    fun j => figureOneChronologicalIdealCoordinate_memLp q I j 2
  have hsharp := figureOneSharpAcceleratedMoments q I
  have hmean : ∀ j, (∫ samples, W j samples ∂mu) =
      figureOneChronologicalRawMean q I j :=
    fun j => figureOneChronologicalIdealCoordinate_mean q I hsharp j
  have hsecond : ∀ j, (∫ samples, W j samples ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2 :=
    fun j => figureOneChronologicalIdealCoordinate_secondMoment_le
      q I hsharp j
  have hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I mu W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) mu := by
    intro i hi
    exact (figureOneChronologicalIdeal_exactIndependence q I i hi).mono
      (figureOneDependentEpsilon_nonneg q)
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I mu W hmeas hnonneg hmem hmean hsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I mu W hmeas hnonneg hmem hmean hsecond
  have hestimate : balancedFigureOneHistoryEstimate q = fun history =>
      initialGaussianIntegral q * balancedCoolingHistoryProduct q history := by
    funext history
    cases history <;>
      simp [balancedFigureOneHistoryEstimate, balancedCoolingHistoryProduct]
  rw [hestimate] at htransfer hlaw
  apply figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
    q I continuation (figureOneRadialTruncationBound q I hrounded)
    (scheduledBalancedForwardHistoryLaw parameters q I
      (figureOneDependentPhaseCount q)) mu
    (balancedCoolingHistoryProduct q)
    (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
    (measurable_balancedCoolingHistoryProduct q)
    (by
      unfold dependentPhaseSampleProduct
      exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
        fun j _ => hmeas (j + 1))
    mean hmeanApprox htail
  · simpa [W, mu] using htransfer
  · exact hlaw

/-- Final balanced-base wrapper for the corrected randomized ideal-prefix
route.  Once the history-only phase replacement is supplied, no executable
raw second-moment premise remains. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_postHistory_randomizedIdeal
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hpostLaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          (fun point =>
            (scheduledBalancedFigureOnePointContinuation
              figureOneFinalScheduledBalancedParameters q point).runEstimate
                oracle.query) =
        (scheduledBalancedForwardHistoryLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
            (balancedFigureOneHistoryEstimate q))
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel
            figureOneFinalScheduledBalancedParameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have hpost :=
    scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
      figureOneFinalScheduledBalancedParameters q I hrounded
      (fun point =>
        (scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point).runEstimate
            oracle.query)
      hpostLaw hphase
  exact figureOneFinalScheduledBalancedBase_failure_le_of_directPostInitial
    q I oracle hpost

#print axioms MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
#print axioms bind_map_fresh_eq_map_append_of_indepFun
#print axioms measurable_uncurry_figureOneRandomizedIdealHistoryAppend
#print axioms figureOneRandomizedIdealHistoryKernel_measurable_and_probability
#print axioms figureOneRandomizedIdealHistoryLaw_succ_of_indepFun
#print axioms figureOneRandomizedIdealHistoryLaw_isProbabilityMeasure
#print axioms figureOneRandomizedIdealHistoryLaw_zero
#print axioms figureOneRandomizedIdealHistoryLaw_map_output
#print axioms MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
#print axioms
  scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
#print axioms
  figureOneFinalScheduledBalancedBase_failure_le_of_postHistory_randomizedIdeal

end

end ArlibCommunity.Algorithms.CV18
