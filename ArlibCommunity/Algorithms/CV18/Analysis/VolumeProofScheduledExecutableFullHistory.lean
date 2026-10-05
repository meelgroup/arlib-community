
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutableCoolingHistory

/-! # Exact full scheduled Figure-One history law -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Joint history law through the terminal Gaussian-to-uniform phase. -/
noncomputable def scheduledExecutableFigureOneFullHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).bind fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)

theorem scheduledExecutableFigureOneFullHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (scheduledExecutableFigureOneFullHistoryLaw parameters q I) ∧
    ∀ point, IsProbabilityMeasure
      (scheduledExecutableFigureOneFullHistoryLaw parameters q I point) := by
  have hcooling :=
    scheduledExecutableFigureOneCoolingHistoryLaw_measurable_and_probability
      parameters q I
  have hterminal := scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
    parameters q I (terminalVariance_pos' q)
  let continuation : Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)
  have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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
            (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
              (terminalVariance q) value.2.2.2) := hterminal.2 value.2.2.2
        exact Measure.isProbabilityMeasure_map <|
          (measurable_balancedCoolingHistorySnocTerminal.comp
            (measurable_const.prodMk measurable_id)).aemeasurable
  constructor
  · unfold scheduledExecutableFigureOneFullHistoryLaw
    exact (Measure.measurable_bind' hcontinuation).comp hcooling.1
  · intro point
    unfold scheduledExecutableFigureOneFullHistoryLaw
    let _ : IsProbabilityMeasure
        (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point) :=
      hcooling.2 point
    exact MeasureTheory.isProbabilityMeasure_bind hcontinuation.aemeasurable
      (ae_of_all _ hcontinuationProb)

/-- Post-initial Figure-One program retaining the terminal state internally.
It has the same scalar output as the public primitive package. -/
noncomputable def scheduledExecutableFigureOneRetainedPointContinuation
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) : MembershipOracleProgram q.n ℝ :=
  (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
    (explicitVolumeCoolingSchedule q).variances point).bind fun product =>
      match product with
      | none => .pure 0
      | some (gaussianProduct, lastPoint) =>
          (scheduledBalancedCoolingUniformEstimateWithState parameters q
            (terminalVariance q) lastPoint).bind fun terminal =>
              .pure (balancedFigureOneTerminalScalar q gaussianProduct terminal)

theorem scheduledExecutableFigureOneRetainedPointContinuation_stronglyMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (scheduledExecutableFigureOneRetainedPointContinuation parameters q point).StronglyMeasurable
      oracle.query := by
  have hcooling := scheduledExecutableCoolingProduct_measurable_and_strong
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hterminal :=
    scheduledBalancedCoolingUniformEstimateWithState_measurable_strong_and_law
      parameters q I oracle (terminalVariance_pos' q)
  let tail : Option (ℝ × AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (scheduledBalancedCoolingUniformEstimateWithState parameters q
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
          (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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
    · exact (scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
        parameters q I (terminalVariance_pos' q)).1.comp measurable_snd
    · intro value
      exact (scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
        parameters q I (terminalVariance_pos' q)).2 value.2
    · exact (measurable_balancedFigureOneTerminalScalar q).comp <|
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have htailRun : Measurable fun product =>
      (tail product).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsomeRun using 1
    funext product
    cases product <;> rfl
  unfold scheduledExecutableFigureOneRetainedPointContinuation
  exact (hcooling.2 point).bind htailStrong htailRun

theorem scheduledExecutableFigureOneRetainedPointContinuation_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (scheduledExecutableFigureOneRetainedPointContinuation parameters q point).runEstimate
        oracle.query =
      (scheduledExecutableFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) := by
  have hcooling := scheduledExecutableCoolingProduct_measurable_and_strong
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hcoolingLaw :=
    scheduledExecutableFigureOneCoolingProduct_runEstimate_eq_history_map
      parameters q I oracle point
  have hhistory :=
    scheduledExecutableFigureOneCoolingHistoryLaw_measurable_and_probability
      parameters q I
  have hterminal :=
    scheduledBalancedCoolingUniformEstimateWithState_measurable_strong_and_law
      parameters q I oracle (terminalVariance_pos' q)
  have hterminalLaw :=
    scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  let tail : Option (ℝ × AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (scheduledBalancedCoolingUniformEstimateWithState parameters q
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
            (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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
            (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
              (terminalVariance q) lastPoint).map
                (balancedFigureOneTerminalScalar q gaussianProduct) by
      funext product
      exact htailLaw product]
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)
  have hextension : Measurable extension := by
    have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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
  unfold scheduledExecutableFigureOneRetainedPointContinuation
  rw [MembershipOracleProgram.runEstimate_bind oracle.query _ tail
    (hcooling.2 point) htailStrong htailRun]
  rw [hcoolingLaw]
  rw [Measure.map_bind_eq_bind_comp _
    measurable_balancedCoolingHistoryOutput htailRun]
  unfold scheduledExecutableFigureOneFullHistoryLaw
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
        (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedFigureOneTerminalScalar q value.2.2.1) =
          ((scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
            (terminalVariance q) value.2.2.2).map
              (balancedCoolingHistorySnocTerminal value)).map
                (balancedFigureOneHistoryEstimate q)
      let mu := scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
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

theorem scheduledBalancedFigureOnePointContinuation_eq_retained
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) :
    scheduledBalancedFigureOnePointContinuation parameters q point =
      scheduledExecutableFigureOneRetainedPointContinuation parameters q point := by
  unfold scheduledBalancedFigureOnePointContinuation
    scheduledExecutableFigureOneRetainedPointContinuation
  congr 1
  funext product
  cases product with
  | none => rfl
  | some value =>
      rcases value with ⟨gaussianProduct, lastPoint⟩
      change
        ((scheduledBalancedCoolingUniformRatioEstimate parameters q
          (terminalVariance q) lastPoint).bind fun finalRatio =>
            .pure <| match finalRatio with
            | some uniformRatio =>
                initialGaussianIntegral q * gaussianProduct * uniformRatio
            | none => 0) = _
      unfold scheduledBalancedCoolingUniformRatioEstimate
      rw [MembershipOracleProgram.bind_assoc_balanced]
      congr 1
      funext terminal
      cases terminal with
      | none => rfl
      | some terminal => cases terminal; rfl

theorem scheduledBalancedFigureOnePointContinuation_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (scheduledBalancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query =
      (scheduledExecutableFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) := by
  rw [scheduledBalancedFigureOnePointContinuation_eq_retained]
  exact scheduledExecutableFigureOneRetainedPointContinuation_runEstimate_eq_history_map
    parameters q I oracle point

#print axioms scheduledExecutableFigureOneFullHistoryLaw_measurable_and_probability
#print axioms scheduledExecutableFigureOneRetainedPointContinuation_runEstimate_eq_history_map
#print axioms scheduledBalancedFigureOnePointContinuation_runEstimate_eq_history_map

end ArlibCommunity.Algorithms.CV18
