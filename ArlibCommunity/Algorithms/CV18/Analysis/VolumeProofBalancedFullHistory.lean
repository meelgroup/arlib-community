/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedCoolingHistory

/-!
# Full balanced Figure-One history and structural cost

This file extends the Gaussian cooling history through the terminal
Gaussian-to-uniform estimate.  The richer law retains the terminal target
point even though `baseVolumeCooling` intentionally forgets it.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Syntax-level associativity used to expose the retained terminal state
behind the public state-forgetting primitive. -/
theorem MembershipOracleProgram.bind_assoc_balanced
    {n : ℕ} {A B C : Type}
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (last : B → MembershipOracleProgram n C) :
    (program.bind next).bind last =
      program.bind (fun value => (next value).bind last) := by
  induction program with
  | pure value => rfl
  | query point branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext answer
      exact ih answer
  | randomNat law branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext seed
      exact ih seed
  | randomPoint law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext point
      exact ih point
  | randomReal law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext value
      exact ih value

/-- Exact retained-state law of the terminal averaged uniform-ratio phase. -/
noncomputable def balancedCoolingUniformLawWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (balancedAccuracyTransitionCollectLaw q I sigma2
      (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) 0
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOneSampleCount q))

theorem balancedCoolingUniformEstimateWithState_measurable_strong_and_law
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable (fun current =>
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
        oracle.query) ∧
    (∀ current,
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).StronglyMeasurable
        oracle.query) ∧
    ∀ current,
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
          oracle.query =
        balancedCoolingUniformLawWithState parameters q I sigma2 current := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOneSampleCount q
  let weight : AmbientSpace q.n → ℝ := uniformRatioWeight sigma2
  let scalePoint : AmbientSpace q.n → AmbientSpace q.n :=
    fun current => accuracyScaleFactor q • current
  have hweight : Measurable weight := measurable_uniformRatioWeight sigma2
  have htransition :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight cap stride retries samples
  have hscale : Measurable scalePoint :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (scalePoint current) :=
    htransition.1.comp (measurable_const.prodMk hscale)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  have hlaw : Measurable fun current =>
      balancedCoolingUniformLawWithState parameters q I sigma2 current := by
    unfold balancedCoolingUniformLawWithState
    exact (Measure.measurable_map _ havg).comp hsource
  have hcollectorStrong : ∀ current,
      (balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
        (scalePoint current)).StronglyMeasurable oracle.query := by
    intro current
    have haux := balancedAccuracyRetryCollectAux_semantics q I oracle hsigma2
      hweight cap stride retries retries samples
    let output : Option (ℝ × AmbientSpace q.n) →
        MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
      fun result => .pure (balancedAccuracyRetryOutput q result)
    have houtputRun : Measurable fun result =>
        (output result).runEstimate oracle.query := by
      simp only [output, MembershipOracleProgram.runEstimate]
      exact Measure.measurable_dirac.comp
        (measurable_balancedAccuracyRetryOutput q)
    unfold balancedAccuracyRetryCollect
    exact (haux.1 0 (scalePoint current)).bind (fun _ => by trivial) houtputRun
  have havgRun : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (.pure (balancedCoolingAverage samples result) :
        MembershipOracleProgram q.n
          (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp havg
  have hstrong : ∀ current,
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).StronglyMeasurable
        oracle.query := by
    intro current
    unfold balancedCoolingUniformEstimateWithState
    change (balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
      (scalePoint current)).bind _ |>.StronglyMeasurable oracle.query
    exact (hcollectorStrong current).bind (fun _ => by trivial) havgRun
  have hrun : ∀ current,
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
          oracle.query =
        balancedCoolingUniformLawWithState parameters q I sigma2 current := by
    intro current
    unfold balancedCoolingUniformEstimateWithState
      balancedCoolingUniformLawWithState
    change ((balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
      (scalePoint current)).bind fun result =>
        .pure (balancedCoolingAverage samples result)).runEstimate oracle.query = _
    rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
      (hcollectorStrong current) (fun _ => by trivial) havgRun]
    rw [balancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
      q I oracle hsigma2 hweight]
    exact Measure.bind_dirac_eq_map _ havg
  refine ⟨?_, hstrong, hrun⟩
  simpa only [hrun] using hlaw

theorem balancedCoolingUniformLawWithState_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable (balancedCoolingUniformLawWithState parameters q I sigma2) ∧
    ∀ current, IsProbabilityMeasure
      (balancedCoolingUniformLawWithState parameters q I sigma2 current) := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOneSampleCount q
  let weight : AmbientSpace q.n → ℝ := uniformRatioWeight sigma2
  have htransition :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 (measurable_uniformRatioWeight sigma2)
        cap stride retries samples
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (accuracyScaleFactor q • current) :=
    htransition.1.comp (measurable_const.prodMk hscale)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  constructor
  · unfold balancedCoolingUniformLawWithState
    exact (Measure.measurable_map _ havg).comp hsource
  · intro current
    unfold balancedCoolingUniformLawWithState
    let _ : IsProbabilityMeasure
        (balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
          samples 0 (accuracyScaleFactor q • current)) :=
      htransition.2 0 (accuracyScaleFactor q • current)
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- Append the terminal phase to a successful Gaussian history. -/
noncomputable def balancedCoolingHistorySnocTerminal
    (history : BalancedCoolingHistory n) :
    Option (ℝ × AmbientSpace n) → Option (BalancedCoolingHistory n)
  | none => none
  | some (ratio, terminalPoint) =>
      some ((fun k => if k = history.2.1 then ratio else history.1 k),
        history.2.1 + 1, history.2.2.1 * ratio, terminalPoint)

theorem measurable_balancedCoolingHistorySnocTerminal :
    Measurable fun value : BalancedCoolingHistory n ×
        Option (ℝ × AmbientSpace n) =>
      balancedCoolingHistorySnocTerminal value.1 value.2 := by
  have hnone : Measurable fun _ : BalancedCoolingHistory n =>
      (none : Option (BalancedCoolingHistory n)) := measurable_const
  have hsome : Measurable fun value : BalancedCoolingHistory n ×
      (ℝ × AmbientSpace n) =>
      some ((fun k => if k = value.1.2.1 then value.2.1 else value.1.1 k),
        value.1.2.1 + 1, value.1.2.2.1 * value.2.1, value.2.2) := by
    apply measurable_some.comp
    have hsequence : Measurable fun value : BalancedCoolingHistory n ×
        (ℝ × AmbientSpace n) =>
        fun k => if k = value.1.2.1 then value.2.1 else value.1.1 k := by
      refine measurable_pi_lambda _ fun k => ?_
      apply Measurable.ite
      · exact measurableSet_eq_fun measurable_const
          (measurable_fst.comp (measurable_snd.comp measurable_fst))
      · exact measurable_fst.comp measurable_snd
      · exact (measurable_pi_apply k).comp
          (measurable_fst.comp measurable_fst)
    exact hsequence.prodMk (by fun_prop)
  convert Measurable.optionCases
    ((0 : ℝ), (0 : AmbientSpace n)) hnone hsome using 1
  funext value
  cases value.2 <;> rfl

/-- Joint history law through the terminal Gaussian-to-uniform phase. -/
noncomputable def balancedFigureOneFullHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (balancedFigureOneCoolingHistoryLaw parameters q I point).bind fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)

theorem balancedFigureOneFullHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (balancedFigureOneFullHistoryLaw parameters q I) ∧
    ∀ point, IsProbabilityMeasure
      (balancedFigureOneFullHistoryLaw parameters q I point) := by
  have hcooling :=
    balancedFigureOneCoolingHistoryLaw_measurable_and_probability
      parameters q I
  have hterminal := balancedCoolingUniformLawWithState_measurable_and_probability
    parameters q I (terminalVariance_pos' q)
  let continuation : Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)
  have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
      (balancedCoolingUniformLawWithState parameters q I
        (terminalVariance q) value.2.2.2).map
          (balancedCoolingHistorySnocTerminal value) := by
    apply measurable_measure_map_param_variable
    · exact hterminal.1.comp <|
        measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    · intro value
      exact hterminal.2 value.2.2.2
    · exact measurable_balancedCoolingHistorySnocTerminal.comp <|
        measurable_fst.prodMk measurable_snd
  have hcontinuation : Measurable continuation := by
    dsimp only [continuation]
    convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext history
    cases history <;> rfl
  have hcontinuationProb : ∀ history,
      IsProbabilityMeasure (continuation history) := by
    intro history
    cases history with
    | none =>
        dsimp only [continuation]
        infer_instance
    | some value =>
        dsimp only [continuation]
        let _ : IsProbabilityMeasure
            (balancedCoolingUniformLawWithState parameters q I
              (terminalVariance q) value.2.2.2) := hterminal.2 value.2.2.2
        exact Measure.isProbabilityMeasure_map <|
          (measurable_balancedCoolingHistorySnocTerminal.comp
            (measurable_const.prodMk measurable_id)).aemeasurable
  constructor
  · unfold balancedFigureOneFullHistoryLaw
    exact (Measure.measurable_bind' hcontinuation).comp hcooling.1
  · intro point
    unfold balancedFigureOneFullHistoryLaw
    let _ : IsProbabilityMeasure
        (balancedFigureOneCoolingHistoryLaw parameters q I point) :=
      hcooling.2 point
    exact MeasureTheory.isProbabilityMeasure_bind hcontinuation.aemeasurable
      (ae_of_all _ hcontinuationProb)

/-- The scalar returned after initial-integral scaling. -/
noncomputable def balancedFigureOneHistoryEstimate (q : VolumeParams) :
    Option (BalancedCoolingHistory q.n) → ℝ
  | none => 0
  | some value => initialGaussianIntegral q * value.2.2.1

theorem measurable_balancedFigureOneHistoryEstimate (q : VolumeParams) :
    Measurable (balancedFigureOneHistoryEstimate q) := by
  have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
      initialGaussianIntegral q * value.2.2.1 :=
    measurable_const.mul <|
      measurable_fst.comp (measurable_snd.comp measurable_snd)
  convert Measurable.optionElim (0 : ℝ) hsome using 1
  funext value
  cases value <;> rfl

/-- Scalar terminal output when the Gaussian product is already known. -/
noncomputable def balancedFigureOneTerminalScalar (q : VolumeParams)
    (gaussianProduct : ℝ) : Option (ℝ × AmbientSpace q.n) → ℝ
  | none => 0
  | some (uniformRatio, _) =>
      initialGaussianIntegral q * gaussianProduct * uniformRatio

theorem measurable_balancedFigureOneTerminalScalar (q : VolumeParams) :
    Measurable fun value : ℝ × Option (ℝ × AmbientSpace q.n) =>
      balancedFigureOneTerminalScalar q value.1 value.2 := by
  have hnone : Measurable fun _ : ℝ => (0 : ℝ) := measurable_const
  have hsome : Measurable fun value : ℝ × (ℝ × AmbientSpace q.n) =>
      initialGaussianIntegral q * value.1 * value.2.1 := by fun_prop
  convert Measurable.optionCases
    ((0 : ℝ), (0 : AmbientSpace q.n)) hnone hsome using 1
  funext value
  cases value.2 <;> rfl

theorem balancedFigureOneHistoryEstimate_snocTerminal
    (q : VolumeParams) (history : BalancedCoolingHistory q.n)
    (terminal : Option (ℝ × AmbientSpace q.n)) :
    balancedFigureOneHistoryEstimate q
        (balancedCoolingHistorySnocTerminal history terminal) =
      balancedFigureOneTerminalScalar q history.2.2.1 terminal := by
  cases terminal with
  | none => rfl
  | some value =>
      rcases value with ⟨ratio, terminalPoint⟩
      unfold balancedCoolingHistorySnocTerminal
        balancedFigureOneHistoryEstimate balancedFigureOneTerminalScalar
      simp only
      ring

/-- Post-initial Figure-One program retaining the terminal state internally.
It has the same scalar output as the public primitive package. -/
noncomputable def balancedFigureOneRetainedPointContinuation
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) : MembershipOracleProgram q.n ℝ :=
  (coolingProduct (balancedCoolingPrimitives parameters) q
    (explicitVolumeCoolingSchedule q).variances point).bind fun product =>
      match product with
      | none => .pure 0
      | some (gaussianProduct, lastPoint) =>
          (balancedCoolingUniformEstimateWithState parameters q
            (terminalVariance q) lastPoint).bind fun terminal =>
              .pure (balancedFigureOneTerminalScalar q gaussianProduct terminal)

theorem balancedFigureOneRetainedPointContinuation_stronglyMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (balancedFigureOneRetainedPointContinuation parameters q point).StronglyMeasurable
      oracle.query := by
  have hcooling := balancedCoolingProduct_measurable_and_strong
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hterminal :=
    balancedCoolingUniformEstimateWithState_measurable_strong_and_law
      parameters q I oracle (terminalVariance_pos' q)
  let tail : Option (ℝ × AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (balancedCoolingUniformEstimateWithState parameters q
          (terminalVariance q) lastPoint).bind fun terminal =>
            .pure (balancedFigureOneTerminalScalar q gaussianProduct terminal)
  have hpureRun : ∀ gaussianProduct, Measurable fun terminal =>
      (.pure (balancedFigureOneTerminalScalar q gaussianProduct terminal) :
        MembershipOracleProgram q.n ℝ).runEstimate oracle.query := by
    intro gaussianProduct
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp <|
      (measurable_balancedFigureOneTerminalScalar q).comp
        (measurable_const.prodMk measurable_id)
  have htailStrong : ∀ product, (tail product).StronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value =>
        exact (hterminal.2.1 value.2).bind (fun _ => by trivial)
          (hpureRun value.1)
  have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
      (tail (some value)).runEstimate oracle.query := by
    have hlaw : (fun value : ℝ × AmbientSpace q.n =>
        (tail (some value)).runEstimate oracle.query) = fun value =>
          (balancedCoolingUniformLawWithState parameters q I
            (terminalVariance q) value.2).map
              (balancedFigureOneTerminalScalar q value.1) := by
      funext value
      unfold tail
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (hterminal.2.1 value.2) (fun _ => by trivial) (hpureRun value.1)]
      rw [hterminal.2.2 value.2]
      exact Measure.bind_dirac_eq_map _ <|
        (measurable_balancedFigureOneTerminalScalar q).comp
          (measurable_const.prodMk measurable_id)
    rw [hlaw]
    apply measurable_measure_map_param_variable
    · exact (balancedCoolingUniformLawWithState_measurable_and_probability
        parameters q I (terminalVariance_pos' q)).1.comp measurable_snd
    · intro value
      exact (balancedCoolingUniformLawWithState_measurable_and_probability
        parameters q I (terminalVariance_pos' q)).2 value.2
    · exact (measurable_balancedFigureOneTerminalScalar q).comp <|
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have htailRun : Measurable fun product =>
      (tail product).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsomeRun using 1
    funext product
    cases product <;> rfl
  unfold balancedFigureOneRetainedPointContinuation
  exact (hcooling.2 point).bind htailStrong htailRun

theorem balancedFigureOneRetainedPointContinuation_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (balancedFigureOneRetainedPointContinuation parameters q point).runEstimate
        oracle.query =
      (balancedFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) := by
  have hcooling := balancedCoolingProduct_measurable_and_strong
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hcoolingLaw :=
    balancedFigureOneCoolingProduct_runEstimate_eq_history_map
      parameters q I oracle point
  have hhistory :=
    balancedFigureOneCoolingHistoryLaw_measurable_and_probability
      parameters q I
  have hterminal :=
    balancedCoolingUniformEstimateWithState_measurable_strong_and_law
      parameters q I oracle (terminalVariance_pos' q)
  have hterminalLaw :=
    balancedCoolingUniformLawWithState_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  let tail : Option (ℝ × AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (balancedCoolingUniformEstimateWithState parameters q
          (terminalVariance q) lastPoint).bind fun terminal =>
            .pure (balancedFigureOneTerminalScalar q gaussianProduct terminal)
  have hpureRun : ∀ gaussianProduct, Measurable fun terminal =>
      (.pure (balancedFigureOneTerminalScalar q gaussianProduct terminal) :
        MembershipOracleProgram q.n ℝ).runEstimate oracle.query := by
    intro gaussianProduct
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp <|
      (measurable_balancedFigureOneTerminalScalar q).comp
        (measurable_const.prodMk measurable_id)
  have htailStrong : ∀ product, (tail product).StronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value =>
        exact (hterminal.2.1 value.2).bind (fun _ => by trivial)
          (hpureRun value.1)
  have htailLaw : ∀ product,
      (tail product).runEstimate oracle.query =
        match product with
        | none => Measure.dirac 0
        | some (gaussianProduct, lastPoint) =>
            (balancedCoolingUniformLawWithState parameters q I
              (terminalVariance q) lastPoint).map
                (balancedFigureOneTerminalScalar q gaussianProduct) := by
    intro product
    cases product with
    | none => rfl
    | some value =>
        unfold tail
        rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
          (hterminal.2.1 value.2) (fun _ => by trivial) (hpureRun value.1)]
        rw [hterminal.2.2 value.2]
        exact Measure.bind_dirac_eq_map _ <|
          (measurable_balancedFigureOneTerminalScalar q).comp
            (measurable_const.prodMk measurable_id)
  have htailRun : Measurable fun product =>
      (tail product).runEstimate oracle.query := by
    rw [show (fun product => (tail product).runEstimate oracle.query) =
        fun product => match product with
        | none => Measure.dirac 0
        | some (gaussianProduct, lastPoint) =>
            (balancedCoolingUniformLawWithState parameters q I
              (terminalVariance q) lastPoint).map
                (balancedFigureOneTerminalScalar q gaussianProduct) by
      funext product
      exact htailLaw product]
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2).map
            (balancedFigureOneTerminalScalar q value.1) := by
      apply measurable_measure_map_param_variable
        (hterminalLaw.1.comp measurable_snd)
        (fun value => hterminalLaw.2 value.2)
      exact (measurable_balancedFigureOneTerminalScalar q).comp <|
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsome using 1
    funext product
    cases product <;> rfl
  let extension : Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)
  have hextension : Measurable extension := by
    have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value) := by
      apply measurable_measure_map_param_variable
      · exact hterminalLaw.1.comp <|
          measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
      · intro value
        exact hterminalLaw.2 value.2.2.2
      · exact measurable_balancedCoolingHistorySnocTerminal.comp <|
          measurable_fst.prodMk measurable_snd
    dsimp only [extension]
    convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext history
    cases history <;> rfl
  unfold balancedFigureOneRetainedPointContinuation
  rw [MembershipOracleProgram.runEstimate_bind oracle.query _ tail
    (hcooling.2 point) htailStrong htailRun]
  rw [hcoolingLaw]
  rw [Measure.map_bind_eq_bind_comp _
    measurable_balancedCoolingHistoryOutput htailRun]
  unfold balancedFigureOneFullHistoryLaw
  rw [map_bind_eq_bind_map_of_measurable _ hextension
    (measurable_balancedFigureOneHistoryEstimate q)]
  apply Measure.bind_congr_right
  filter_upwards with history
  cases history with
  | none =>
      rw [htailLaw]
      rw [Measure.map_dirac' (measurable_balancedFigureOneHistoryEstimate q)]
      rfl
  | some value =>
      rw [htailLaw]
      change
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedFigureOneTerminalScalar q value.2.2.1) =
          ((balancedCoolingUniformLawWithState parameters q I
            (terminalVariance q) value.2.2.2).map
              (balancedCoolingHistorySnocTerminal value)).map
                (balancedFigureOneHistoryEstimate q)
      let mu := balancedCoolingUniformLawWithState parameters q I
        (terminalVariance q) value.2.2.2
      have hsnoc : Measurable
          (balancedCoolingHistorySnocTerminal value) :=
        measurable_balancedCoolingHistorySnocTerminal.comp
          (measurable_const.prodMk measurable_id)
      calc
        mu.map (balancedFigureOneTerminalScalar q value.2.2.1) =
            mu.map (balancedFigureOneHistoryEstimate q ∘
              balancedCoolingHistorySnocTerminal value) := by
          apply Measure.map_congr
          filter_upwards with terminal
          exact (balancedFigureOneHistoryEstimate_snocTerminal
            q value terminal).symm
        _ = (mu.map (balancedCoolingHistorySnocTerminal value)).map
            (balancedFigureOneHistoryEstimate q) :=
          (Measure.map_map
            (measurable_balancedFigureOneHistoryEstimate q) hsnoc).symm

/-- The public post-initial continuation, using the terminal field of the
`VolumeCoolingPrimitives` package exactly as `baseVolumeCooling` does. -/
noncomputable def balancedFigureOnePointContinuation
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) : MembershipOracleProgram q.n ℝ :=
  (coolingProduct (balancedCoolingPrimitives parameters) q
    (explicitVolumeCoolingSchedule q).variances point).bind fun product =>
      match product with
      | none => .pure 0
      | some (gaussianProduct, lastPoint) =>
          ((balancedCoolingPrimitives parameters).uniformRatioEstimate q
            (terminalVariance q) lastPoint).bind fun finalRatio =>
              .pure <| match finalRatio with
              | some uniformRatio =>
                  initialGaussianIntegral q * gaussianProduct * uniformRatio
              | none => 0

theorem balancedFigureOnePointContinuation_eq_retained
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) :
    balancedFigureOnePointContinuation parameters q point =
      balancedFigureOneRetainedPointContinuation parameters q point := by
  unfold balancedFigureOnePointContinuation
    balancedFigureOneRetainedPointContinuation
  congr 1
  funext product
  cases product with
  | none => rfl
  | some value =>
      rcases value with ⟨gaussianProduct, lastPoint⟩
      change
        ((balancedCoolingUniformRatioEstimate parameters q
          (terminalVariance q) lastPoint).bind fun finalRatio =>
            .pure <| match finalRatio with
            | some uniformRatio =>
                initialGaussianIntegral q * gaussianProduct * uniformRatio
            | none => 0) = _
      unfold balancedCoolingUniformRatioEstimate
      rw [MembershipOracleProgram.bind_assoc_balanced]
      congr 1
      funext terminal
      cases terminal with
      | none => rfl
      | some terminal => cases terminal; rfl

theorem balancedFigureOnePointContinuation_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (balancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query =
      (balancedFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) := by
  rw [balancedFigureOnePointContinuation_eq_retained]
  exact balancedFigureOneRetainedPointContinuation_runEstimate_eq_history_map
    parameters q I oracle point

/-- One joint history law including initialization, all Gaussian phases, and
the terminal ratio phase. -/
noncomputable def balancedFigureOneBaseHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : Measure (Option (BalancedCoolingHistory q.n)) :=
  (initialGaussianSamplingMeasure q).bind fun proposal =>
    balancedFigureOneFullHistoryLaw parameters q I
      (initialTruncatedFallback q I proposal)

theorem balancedFigureOneBaseHistoryLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    IsProbabilityMeasure (balancedFigureOneBaseHistoryLaw parameters q I) := by
  have hfull := balancedFigureOneFullHistoryLaw_measurable_and_probability
    parameters q I
  unfold balancedFigureOneBaseHistoryLaw
  exact MeasureTheory.isProbabilityMeasure_bind
    (hfull.1.comp (measurable_initialTruncatedFallback q I)).aemeasurable
      (ae_of_all _ fun proposal => hfull.2
        (initialTruncatedFallback q I proposal))

theorem balancedFigureOneBaseVolumeCooling_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q).runEstimate oracle.query =
        (balancedFigureOneBaseHistoryLaw parameters q I).map
          (balancedFigureOneHistoryEstimate q) := by
  have hfull := balancedFigureOneFullHistoryLaw_measurable_and_probability
    parameters q I
  have hpointStrong : ∀ point,
      (balancedFigureOnePointContinuation parameters q point).StronglyMeasurable
        oracle.query := by
    intro point
    rw [balancedFigureOnePointContinuation_eq_retained]
    exact balancedFigureOneRetainedPointContinuation_stronglyMeasurable
      parameters q I oracle point
  have hpointRun : Measurable fun point =>
      (balancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query := by
    rw [show (fun point =>
        (balancedFigureOnePointContinuation parameters q point).runEstimate
          oracle.query) = fun point =>
        (balancedFigureOneFullHistoryLaw parameters q I point).map
          (balancedFigureOneHistoryEstimate q) by
      funext point
      exact balancedFigureOnePointContinuation_runEstimate_eq_history_map
        parameters q I oracle point]
    exact (Measure.measurable_map _
      (measurable_balancedFigureOneHistoryEstimate q)).comp hfull.1
  let initialTail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => balancedFigureOnePointContinuation parameters q point
  have hinitialTailStrong : ∀ initialPoint,
      (initialTail initialPoint).StronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hpointStrong point
  have hinitialTailRun : Measurable fun initialPoint =>
      (initialTail initialPoint).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hpointRun using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have hbase : baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q =
      (figureOneInitialSample q).bind initialTail := by
    unfold baseVolumeCooling
    congr 1
  rw [hbase]
  rw [MembershipOracleProgram.runEstimate_bind oracle.query _ initialTail
    (figureOneInitialSample_stronglyMeasurable q I oracle)
      hinitialTailStrong hinitialTailRun]
  rw [runEstimate_figureOneInitialSample q I oracle]
  rw [Measure.map_bind_eq_bind_comp _
    (measurable_some.comp (measurable_initialTruncatedFallback q I))
      hinitialTailRun]
  unfold balancedFigureOneBaseHistoryLaw
  rw [show (fun proposal =>
      (initialTail ((some ∘ initialTruncatedFallback q I) proposal)).runEstimate
        oracle.query) = fun proposal =>
      (balancedFigureOneFullHistoryLaw parameters q I
        (initialTruncatedFallback q I proposal)).map
          (balancedFigureOneHistoryEstimate q) by
    funext proposal
    exact balancedFigureOnePointContinuation_runEstimate_eq_history_map
      parameters q I oracle (initialTruncatedFallback q I proposal)]
  exact (map_bind_eq_bind_map_of_measurable _
    (hfull.1.comp (measurable_initialTruncatedFallback q I))
      (measurable_balancedFigureOneHistoryEstimate q)).symm

/-! ## Structural query cost -/

noncomputable def balancedCoolingPhaseQueryBudget
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) : ℕ :=
  figureOnePhaseSampleCount q sigma2 * parameters.retryLimit q sigma2 *
    (parameters.proposalCap q sigma2 + 2)

noncomputable def balancedCoolingTerminalQueryBudget
    (parameters : BalancedCoolingParameters) (q : VolumeParams) : ℕ :=
  figureOneSampleCount q * parameters.retryLimit q (terminalVariance q) *
    (parameters.proposalCap q (terminalVariance q) + 2)

noncomputable def balancedCoolingQueryBudget
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | sigma2 :: tau2 :: rest =>
      balancedCoolingPhaseQueryBudget parameters q sigma2 +
        balancedCoolingQueryBudget parameters q (tau2 :: rest)
termination_by variances => variances.length

theorem balancedCoolingRatioEstimate_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).QueryBound
      (balancedCoolingPhaseQueryBudget parameters q sigma2) := by
  unfold balancedCoolingRatioEstimate balancedCoolingPhaseQueryBudget
  exact (balancedAccuracyRetryCollect_queryBound q sigma2
    (gaussianRatioWeight sigma2 tau2)
    (parameters.proposalCap q sigma2)
    (parameters.properStride q sigma2)
    (parameters.retryLimit q sigma2)
    (figureOnePhaseSampleCount q sigma2)
    (accuracyScaleFactor q • current)).bind fun _ => .pure _ 0

theorem balancedCoolingUniformEstimateWithState_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedCoolingUniformEstimateWithState parameters q sigma2 current).QueryBound
      (figureOneSampleCount q * parameters.retryLimit q sigma2 *
        (parameters.proposalCap q sigma2 + 2)) := by
  unfold balancedCoolingUniformEstimateWithState
  exact (balancedAccuracyRetryCollect_queryBound q sigma2
    (uniformRatioWeight sigma2)
    (parameters.proposalCap q sigma2)
    (parameters.properStride q sigma2)
    (parameters.retryLimit q sigma2)
    (figureOneSampleCount q)
    (accuracyScaleFactor q • current)).bind fun _ => .pure _ 0

theorem balancedCoolingUniformRatioEstimate_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedCoolingUniformRatioEstimate parameters q sigma2 current).QueryBound
      (figureOneSampleCount q * parameters.retryLimit q sigma2 *
        (parameters.proposalCap q sigma2 + 2)) := by
  unfold balancedCoolingUniformRatioEstimate
  exact (balancedCoolingUniformEstimateWithState_queryBound
    parameters q sigma2 current).bind fun _ => .pure _ 0

theorem balancedCoolingProduct_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    ∀ variances point,
      (coolingProduct (balancedCoolingPrimitives parameters) q variances point).QueryBound
        (balancedCoolingQueryBudget parameters q variances) := by
  intro variances
  induction variances with
  | nil =>
      intro point
      simpa [coolingProduct, balancedCoolingQueryBudget] using
        (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro point
          simpa [coolingProduct, balancedCoolingQueryBudget] using
            (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
      | cons tau2 rest =>
          intro point
          simp only [coolingProduct]
          have htail : ∀ phase,
              ((match phase with
                | none => .pure none
                | some (ratio, nextPoint) =>
                    (coolingProduct (balancedCoolingPrimitives parameters) q
                      (tau2 :: rest) nextPoint).bind fun tail =>
                        .pure <| match tail with
                        | some (product, lastPoint) =>
                            some (ratio * product, lastPoint)
                        | none => none) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).QueryBound
                    (balancedCoolingQueryBudget parameters q
                      (tau2 :: rest)) := by
            intro phase
            cases phase with
            | none => exact .pure _ _
            | some value =>
                exact (ih value.2).bind fun _ => .pure _ 0
          have h := (balancedCoolingRatioEstimate_queryBound
            parameters q sigma2 tau2 point).bind htail
          convert h using 1
          · rfl
          · rw [balancedCoolingQueryBudget]

noncomputable def balancedFigureOneBaseQueryBudget
    (parameters : BalancedCoolingParameters) (q : VolumeParams) : ℕ :=
  1 + (balancedCoolingQueryBudget parameters q
      (explicitVolumeCoolingSchedule q).variances +
    balancedCoolingTerminalQueryBudget parameters q)

theorem balancedFigureOneBaseVolumeCooling_queryBound
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q).QueryBound
        (balancedFigureOneBaseQueryBudget parameters q) := by
  have hproduct : ∀ initialPoint,
      ((match initialPoint with
        | none => .pure 0
        | some point =>
            (coolingProduct (balancedCoolingPrimitives parameters) q
              (explicitVolumeCoolingSchedule q).variances point).bind
                fun product => match product with
                | none => .pure 0
                | some (gaussianProduct, lastPoint) =>
                    ((balancedCoolingPrimitives parameters).uniformRatioEstimate q
                      (terminalVariance q) lastPoint).bind fun finalRatio =>
                        .pure <| match finalRatio with
                        | some uniformRatio =>
                            initialGaussianIntegral q * gaussianProduct * uniformRatio
                        | none => 0) : MembershipOracleProgram q.n ℝ).QueryBound
          (balancedCoolingQueryBudget parameters q
              (explicitVolumeCoolingSchedule q).variances +
            balancedCoolingTerminalQueryBudget parameters q) := by
    intro initialPoint
    cases initialPoint with
    | none => exact .pure _ _
    | some point =>
        apply (balancedCoolingProduct_queryBound parameters q
          (explicitVolumeCoolingSchedule q).variances point).bind
        intro product
        cases product with
        | none => exact .pure _ _
        | some value =>
            exact (balancedCoolingUniformRatioEstimate_queryBound parameters q
              (terminalVariance q) value.2).bind fun _ => .pure _ 0
  unfold baseVolumeCooling balancedFigureOneBaseQueryBudget
  exact (figureOneInitialSample_queryBound q).bind hproduct

/-- Exact residual arithmetic condition for an explicit
`volumeBaseComplexityRate` cap.  It cannot be removed for an arbitrary
`BalancedCoolingParameters`, since its caps and retry limits are unrestricted. -/
theorem balancedFigureOneBaseVolumeCooling_queryBound_rate
    (parameters : BalancedCoolingParameters) (q : VolumeParams) (C : ℝ)
    (hcost : (balancedFigureOneBaseQueryBudget parameters q : ℝ) ≤
      C * volumeBaseComplexityRate q) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q).QueryBound
        (Nat.ceil (C * volumeBaseComplexityRate q)) := by
  apply (balancedFigureOneBaseVolumeCooling_queryBound parameters q).mono
  exact_mod_cast hcost.trans (Nat.le_ceil _)

#print axioms balancedFigureOneRetainedPointContinuation_runEstimate_eq_history_map
#print axioms balancedFigureOneFullHistoryLaw_measurable_and_probability
#print axioms balancedFigureOneBaseVolumeCooling_runEstimate_eq_history_map
#print axioms balancedFigureOneBaseVolumeCooling_queryBound
#print axioms balancedFigureOneBaseVolumeCooling_queryBound_rate

end ArlibCommunity.Algorithms.CV18
