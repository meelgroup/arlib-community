/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedMappedLawAssembly

/-!
# Chronological prefix laws for the balanced CV18 cooling program

The executable history was originally defined by recursion on the remaining
variance list.  Lemma 7.17(b,c), however, is naturally stated for prefixes in
chronological order.  This module gives the corresponding forward kernels,
using the already-defined history snoc operation.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- The zero-phase history retaining only the initial target-space point. -/
noncomputable def balancedCoolingInitialHistory (point : AmbientSpace n) :
    Option (BalancedCoolingHistory n) :=
  some ((fun _ => 0), 0, 1, point)

theorem measurable_balancedCoolingInitialHistory :
    Measurable (balancedCoolingInitialHistory (n := n)) := by
  exact measurable_some.comp <| measurable_const.prodMk <|
    measurable_const.prodMk <| measurable_const.prodMk measurable_id

/-- Extract the averaged phase value from the collector output, using zero
on its explicit failure branch. -/
noncomputable def balancedCoolingPhaseAverageValue (samples : ℕ) :
    Option (ℝ × AmbientSpace n) → ℝ
  | none => 0
  | some (total, _) => total / (samples : ℝ)

theorem measurable_balancedCoolingPhaseAverageValue (samples : ℕ) :
    Measurable (balancedCoolingPhaseAverageValue (n := n) samples) := by
  have hsome : Measurable fun value : ℝ × AmbientSpace n =>
      value.1 / (samples : ℝ) := measurable_fst.div_const _
  convert Measurable.optionElim (0 : ℝ) hsome using 1
  funext result
  cases result <;> rfl

theorem balancedCoolingHistorySnocTerminal_average_coordinate
    (q : VolumeParams) (m samples : ℕ)
    (history : BalancedCoolingHistory q.n) (hcount : history.2.1 = m)
    (result : Option (ℝ × AmbientSpace q.n))
    (hm : m < figureOneDependentPhaseCount q) :
    balancedCoolingChronologicalPhaseVariable q (m + 1)
        (balancedCoolingHistorySnocTerminal history
          (balancedCoolingAverage samples result)) =
      balancedCoolingPhaseAverageValue samples result := by
  cases result with
  | none => rfl
  | some value =>
      rcases value with ⟨total, point⟩
      rw [balancedCoolingChronologicalPhaseVariable_apply_succ q m hm]
      simp [balancedCoolingHistorySnocTerminal, balancedCoolingAverage,
        balancedCoolingPhaseAverageValue, hcount]

/-- The coordinate appended at chronological position `m + 1` is exactly the
scalar carried by the successful phase result. -/
theorem balancedCoolingHistorySnocTerminal_coordinate
    (q : VolumeParams) (m : ℕ)
    (history : BalancedCoolingHistory q.n) (hcount : history.2.1 = m)
    (value : ℝ × AmbientSpace q.n)
    (hm : m < figureOneDependentPhaseCount q) :
    balancedCoolingChronologicalPhaseVariable q (m + 1)
        (balancedCoolingHistorySnocTerminal history (some value)) =
      value.1 := by
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q m hm]
  simp [balancedCoolingHistorySnocTerminal, hcount]

/-- A successful chronological append retains precisely the phase endpoint. -/
theorem balancedCoolingHistoryRetainedState_snocTerminal
    (q : VolumeParams) (history : BalancedCoolingHistory q.n)
    (value : ℝ × AmbientSpace q.n) :
    balancedCoolingHistoryRetainedState q
        (balancedCoolingHistorySnocTerminal history (some value)) = value.2 := by
  rfl

theorem balancedCoolingHistorySnocTerminal_average_count
    (samples : ℕ) (history : BalancedCoolingHistory n)
    (result : Option (ℝ × AmbientSpace n)) :
    match balancedCoolingHistorySnocTerminal history
        (balancedCoolingAverage samples result) with
    | none => True
    | some next => next.2.1 = history.2.1 + 1 := by
  cases result <;> simp [balancedCoolingAverage,
    balancedCoolingHistorySnocTerminal]

/-- One chronological Gaussian-ratio phase, appending its average and
retained point to an already-completed prefix. -/
noncomputable def balancedCoolingForwardGaussianPhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n))
  | none => Measure.dirac none
  | some history =>
      (balancedCoolingRatioLaw parameters q I
        (scheduleValue q phase) (scheduleValue q (phase + 1))
        history.2.2.2).map (balancedCoolingHistorySnocTerminal history)

theorem balancedCoolingForwardGaussianPhaseKernel_measurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable
      (balancedCoolingForwardGaussianPhaseKernel parameters q I phase) := by
  have hphase := balancedCoolingRatioLaw_measurable_and_probability
    parameters q I (scheduleValue_pos q phase) (scheduleValue q (phase + 1))
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      (balancedCoolingRatioLaw parameters q I
        (scheduleValue q phase) (scheduleValue q (phase + 1))
        history.2.2.2).map (balancedCoolingHistorySnocTerminal history) := by
    apply measurable_measure_map_param_variable
    · exact hphase.1.comp <|
        measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    · intro history
      exact hphase.2 history.2.2.2
    · exact measurable_balancedCoolingHistorySnocTerminal.comp
        (measurable_fst.prodMk measurable_snd)
  convert Measurable.optionElim
    (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
  funext history
  cases history <;> rfl

theorem balancedCoolingForwardGaussianPhaseKernel_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (history : Option (BalancedCoolingHistory q.n)) :
    IsProbabilityMeasure
      (balancedCoolingForwardGaussianPhaseKernel parameters q I phase history) := by
  cases history with
  | none =>
      change IsProbabilityMeasure
        (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
      infer_instance
  | some history =>
      let _ : IsProbabilityMeasure
          (balancedCoolingRatioLaw parameters q I
            (scheduleValue q phase) (scheduleValue q (phase + 1))
            history.2.2.2) :=
        (balancedCoolingRatioLaw_measurable_and_probability parameters q I
          (scheduleValue_pos q phase) (scheduleValue q (phase + 1))).2 _
      exact Measure.isProbabilityMeasure_map
        ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
          (measurable_const.prodMk measurable_id)).aemeasurable

/-- The final Gaussian-to-uniform phase in chronological append form. -/
noncomputable def balancedCoolingForwardTerminalPhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n))
  | none => Measure.dirac none
  | some history =>
      (balancedCoolingUniformLawWithState parameters q I
        (terminalVariance q) history.2.2.2).map
          (balancedCoolingHistorySnocTerminal history)

theorem balancedCoolingForwardTerminalPhaseKernel_measurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable
      (balancedCoolingForwardTerminalPhaseKernel parameters q I) := by
  have hphase := balancedCoolingUniformLawWithState_measurable_and_probability
    parameters q I (terminalVariance_pos' q)
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      (balancedCoolingUniformLawWithState parameters q I
        (terminalVariance q) history.2.2.2).map
          (balancedCoolingHistorySnocTerminal history) := by
    apply measurable_measure_map_param_variable
    · exact hphase.1.comp <|
        measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    · intro history
      exact hphase.2 history.2.2.2
    · exact measurable_balancedCoolingHistorySnocTerminal.comp
        (measurable_fst.prodMk measurable_snd)
  convert Measurable.optionElim
    (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
  funext history
  cases history <;> rfl

theorem balancedCoolingForwardTerminalPhaseKernel_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n)
    (history : Option (BalancedCoolingHistory q.n)) :
    IsProbabilityMeasure
      (balancedCoolingForwardTerminalPhaseKernel parameters q I history) := by
  cases history with
  | none =>
      change IsProbabilityMeasure
        (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
      infer_instance
  | some history =>
      let _ : IsProbabilityMeasure
          (balancedCoolingUniformLawWithState parameters q I
            (terminalVariance q) history.2.2.2) :=
        (balancedCoolingUniformLawWithState_measurable_and_probability
          parameters q I (terminalVariance_pos' q)).2 _
      exact Measure.isProbabilityMeasure_map
        ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
          (measurable_const.prodMk measurable_id)).aemeasurable

/-- The finite chronological phase kernel: Gaussian-ratio phases precede the
single terminal Gaussian-to-uniform phase. -/
noncomputable def balancedFigureOneForwardPhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ℕ → Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
  if phase < terminalPhaseSteps q then
    balancedCoolingForwardGaussianPhaseKernel parameters q I phase
  else
    balancedCoolingForwardTerminalPhaseKernel parameters q I

theorem balancedFigureOneForwardPhaseKernel_measurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (balancedFigureOneForwardPhaseKernel parameters q I phase) := by
  unfold balancedFigureOneForwardPhaseKernel
  split_ifs
  · exact balancedCoolingForwardGaussianPhaseKernel_measurable
      parameters q I phase
  · exact balancedCoolingForwardTerminalPhaseKernel_measurable parameters q I

theorem balancedFigureOneForwardPhaseKernel_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (history : Option (BalancedCoolingHistory q.n)) :
    IsProbabilityMeasure
      (balancedFigureOneForwardPhaseKernel parameters q I phase history) := by
  unfold balancedFigureOneForwardPhaseKernel
  split_ifs
  · exact balancedCoolingForwardGaussianPhaseKernel_isProbabilityMeasure
      parameters q I phase history
  · exact balancedCoolingForwardTerminalPhaseKernel_isProbabilityMeasure
      parameters q I history

/-- Post-initial chronological prefix law after `phases` complete phases. -/
noncomputable def balancedFigureOneForwardHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  iteratedKernelLaw (balancedFigureOneForwardPhaseKernel parameters q I)
    ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory) phases

theorem balancedFigureOneForwardHistoryLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    IsProbabilityMeasure
      (balancedFigureOneForwardHistoryLaw parameters q I phases) := by
  unfold balancedFigureOneForwardHistoryLaw
  apply iteratedKernelLaw_isProbabilityMeasure
  · exact Measure.isProbabilityMeasure_map
      measurable_balancedCoolingInitialHistory.aemeasurable
  · exact balancedFigureOneForwardPhaseKernel_measurable parameters q I
  · exact balancedFigureOneForwardPhaseKernel_isProbabilityMeasure parameters q I

/-- Appending any complete phase preserves the exact stored-product
invariant, independently of whether that phase succeeds or takes its explicit
failure branch. -/
theorem balancedFigureOneForwardPhaseKernel_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (history : Option (BalancedCoolingHistory q.n))
    (hproduct : BalancedCoolingHistoryHasProduct m history) :
    ∀ᵐ next ∂balancedFigureOneForwardPhaseKernel parameters q I phase history,
      BalancedCoolingHistoryHasProduct (m + 1) next := by
  cases history with
  | none =>
      unfold balancedFigureOneForwardPhaseKernel
      split_ifs <;>
        apply (ae_dirac_iff
          (measurableSet_balancedCoolingHistoryHasProduct _)).2 <;>
        simp [BalancedCoolingHistoryHasProduct]
  | some history =>
      unfold balancedFigureOneForwardPhaseKernel
      split_ifs with hphase
      · unfold balancedCoolingForwardGaussianPhaseKernel
        apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasProduct _)).2
        filter_upwards with result
        exact hproduct.snocTerminal result
      · unfold balancedCoolingForwardTerminalPhaseKernel
        apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasProduct _)).2
        filter_upwards with result
        exact hproduct.snocTerminal result

/-- The forward prefix law contains exactly `phases` stored factors and their
stored product is their chronological product. -/
theorem balancedFigureOneForwardHistoryLaw_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ history ∂balancedFigureOneForwardHistoryLaw parameters q I phases,
      BalancedCoolingHistoryHasProduct phases history := by
  intro phases
  induction phases with
  | zero =>
      unfold balancedFigureOneForwardHistoryLaw
      apply (ae_map_iff measurable_balancedCoolingInitialHistory.aemeasurable
        (measurableSet_balancedCoolingHistoryHasProduct 0)).2
      filter_upwards with point
      simp [balancedCoolingInitialHistory, BalancedCoolingHistoryHasProduct]
  | succ phases ih =>
      let prefixLaw := balancedFigureOneForwardHistoryLaw parameters q I phases
      let kernel := balancedFigureOneForwardPhaseKernel parameters q I phases
      let good : Set (Option (BalancedCoolingHistory q.n)) :=
        {history | BalancedCoolingHistoryHasProduct (phases + 1) history}
      have hgood : MeasurableSet good :=
        measurableSet_balancedCoolingHistoryHasProduct _
      have hkernel : Measurable kernel :=
        balancedFigureOneForwardPhaseKernel_measurable parameters q I phases
      change ∀ᵐ history ∂prefixLaw.bind kernel,
        BalancedCoolingHistoryHasProduct (phases + 1) history
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with history hhistory
      exact MeasureTheory.mem_ae_iff.mp
        (balancedFigureOneForwardPhaseKernel_ae_hasProduct
          parameters q I phases phases history hhistory)

theorem balancedFigureOneForwardHistoryLaw_zero_retainedState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    (balancedFigureOneForwardHistoryLaw parameters q I 0).map
        (balancedCoolingHistoryRetainedState q) =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)) := by
  change ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory).map
      (balancedCoolingHistoryRetainedState q) = _
  rw [Measure.map_map (measurable_balancedCoolingHistoryRetainedState q)
    measurable_balancedCoolingInitialHistory]
  calc
    Measure.map (balancedCoolingHistoryRetainedState q ∘
        balancedCoolingInitialHistory)
        (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)) =
        Measure.map id
          (truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q) : Measure (AmbientSpace q.n)) := by
      apply Measure.map_congr
      filter_upwards with point
      rfl
    _ = _ := Measure.map_id

#print axioms balancedCoolingHistorySnocTerminal_average_coordinate
#print axioms balancedCoolingHistorySnocTerminal_coordinate
#print axioms balancedCoolingHistoryRetainedState_snocTerminal
#print axioms balancedCoolingForwardGaussianPhaseKernel_measurable
#print axioms balancedCoolingForwardTerminalPhaseKernel_measurable
#print axioms balancedFigureOneForwardHistoryLaw_isProbabilityMeasure
#print axioms balancedFigureOneForwardHistoryLaw_ae_hasProduct
#print axioms balancedFigureOneForwardHistoryLaw_zero_retainedState

end

end ArlibCommunity.Algorithms.CV18
