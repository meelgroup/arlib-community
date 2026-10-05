/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalResetDeviation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetEventTransfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceBoundaryMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledPhaseMeanBridge

/-!
# Terminal deviation through collector completion and the final trace

This module carries the terminal equation-(6) event estimate from the
coordinate-recording retained history through the all-or-nothing collector
and then through the final chronological trace comparison.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The terminal initialized-history deviation event is exactly the raw
retained-sum deviation event. -/
theorem initializedScheduledRetainedHistory_terminal_deviation_eq_retainedSum
    (q : VolumeParams) (I : VolumeInput q.n) (target eps : ℝ) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (initializedScheduledRetainedHistoryLaw q I
      (terminalPhaseSteps q) (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum (retainedSampleObservation weight) count history /
              (count : ℝ) - target|} =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1))
        {state | eps * target ≤ |state.1 / (count : ℝ) - target|} := by
  dsimp only
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q)
  let toSum := retainedSampleHistoryToSum weight count
  let deviation : Set (ℝ × Option (AmbientSpace q.n)) :=
    {state | eps * target ≤ |state.1 / (count : ℝ) - target|}
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (terminalVariance_pos' q)
  have hdeviation : MeasurableSet deviation := by
    apply measurableSet_le measurable_const
    exact (((measurable_fst.div_const (count : ℝ)).sub_const target).abs)
  have hmap := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K hK.1 hK.2 weight hweight exact (count - 1)
  have happly := congrArg
    (fun mu : Measure (ℝ × Option (AmbientSpace q.n)) => mu deviation) hmap
  rw [Measure.map_apply
    (measurable_retainedSampleHistoryToSum hweight ((count - 1) + 1))
    hdeviation] at happly
  have hcountEq : count - 1 + 1 = count :=
    Nat.sub_add_cancel (figureOneSampleCount_pos q)
  simpa [initializedScheduledRetainedHistoryLaw, exact, K, weight, toSum,
    deviation, retainedSampleHistoryToSum, sequentialPrefixSum, hcountEq,
    scheduleValue_terminalPhaseSteps] using happly

/-- The public terminal target's ratio-deviation event is the retained-sum
shadow's completed live-average event. -/
theorem figureOneScheduledTerminalPhaseTarget_deviation_eq_retainedSum
    (q : VolumeParams) (I : VolumeInput q.n) (target eps : ℝ) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    figureOneScheduledTerminalPhaseTarget q I
        {result | eps * target ≤
          |scheduledBalancedPhaseRatio result - target|} =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1))
        {state | eps * target ≤
          |retainedLiveTotal state / (count : ℝ) - target|} := by
  dsimp only
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let deviation : Set (Option (ℝ × AmbientSpace q.n)) :=
    {result | eps * target ≤
      |scheduledBalancedPhaseRatio result - target|}
  have hdeviation : MeasurableSet deviation := by
    apply measurableSet_le measurable_const
    exact (measurable_scheduledBalancedPhaseRatio.sub_const target).abs
  rw [figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel]
  rw [Measure.map_apply
    ((measurable_balancedCoolingAverage count).comp
      measurable_retainedSumOutput) hdeviation]
  congr 1
  ext state
  rcases state with ⟨total, result⟩
  cases result <;>
    simp [deviation, count, Function.comp_def, retainedSumOutput,
      balancedCoolingAverage, scheduledBalancedPhaseRatio, retainedLiveTotal]

/-- An initialized terminal-history deviation bound becomes a completed
terminal-target bound after charging only the retained shadow's death event. -/
theorem figureOneScheduledTerminalPhaseTarget_deviation_le_of_initializedHistory
    (q : VolumeParams) (I : VolumeInput q.n)
    (target eps : ℝ) (bound : ENNReal)
    (hhistory :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      (initializedScheduledRetainedHistoryLaw q I
        (terminalPhaseSteps q) (count - 1))
          {history | eps * target ≤
            |sequentialPrefixSum (retainedSampleObservation weight) count history /
                (count : ℝ) - target|} ≤ bound) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)
    figureOneScheduledTerminalPhaseTarget q I
        {result | eps * target ≤
          |scheduledBalancedPhaseRatio result - target|} ≤
      bound + shadow {state | state.2 = none} := by
  dsimp only at hhistory ⊢
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  rw [figureOneScheduledTerminalPhaseTarget_deviation_eq_retainedSum]
  have hsplit := measure_retainedLiveAverage_deviation_le_raw_add_dead
    shadow count target eps
  calc
    shadow {state | eps * target ≤
        |retainedLiveTotal state / (count : ℝ) - target|} ≤
      shadow {state | eps * target ≤
          |state.1 / (count : ℝ) - target|} +
        shadow {state | state.2 = none} := hsplit
    _ = (initializedScheduledRetainedHistoryLaw q I
          (terminalPhaseSteps q) (count - 1))
          {history | eps * target ≤
            |sequentialPrefixSum (retainedSampleObservation weight) count history /
                (count : ℝ) - target|} +
        shadow {state | state.2 = none} := by
      rw [initializedScheduledRetainedHistory_terminal_deviation_eq_retainedSum]
    _ ≤ bound + shadow {state | state.2 = none} := by
      gcongr

/-- The terminal retained-sum shadow death mass is the optional retained-chain
death mass, hence is controlled by the existing finite-retry endpoint bound. -/
theorem figureOneScheduledTerminalShadow_dead_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)) {state | state.2 = none} ≤
      scheduledBalancedStationaryTargetError q +
        (count - 1) • figureOneCorrectedTransitionBudget q := by
  dsimp only
  let count := figureOneSampleCount q
  let steps := count - 1
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let endpoint := iteratedKernelLaw (fun _ => K)
    (initial.map retainedSumState) steps
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (terminalVariance_pos' q)
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  have hinitialState : initial.map retainedSumState =
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some := by
    calc
      initial.map retainedSumState =
          (truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
              (retainedSumState ∘ fun x => (weight x, some x)) :=
        Measure.map_map measurable_snd
          (hweight.prodMk measurable_some)
      _ = _ := by rfl
  have hshadowMap : shadow.map retainedSumState = endpoint := by
    simpa [shadow, endpoint] using
      map_iterated_retainedSumKernel_state K hK.1 hK.2 weight hweight
        initial steps
  have hdead : shadow {state | state.2 = none} = endpoint {none} := by
    calc
      shadow {state | state.2 = none} =
          (shadow.map retainedSumState) {none} := by
        rw [Measure.map_apply
          (show Measurable (retainedSumState
            (S := AmbientSpace q.n)) from measurable_snd)
          measurableSet_option_none]
        rfl
      _ = endpoint {none} := by rw [hshadowMap]
  rw [hdead]
  dsimp only [endpoint]
  rw [hinitialState]
  simpa [K, steps, scheduleValue_terminalPhaseSteps] using
    iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_none_le
      q I (terminalPhaseSteps q) steps

/-- The terminal equation-(6) estimate after all-or-nothing collector
completion.  The only new charge is the explicit terminal shadow death mass. -/
theorem figureOneScheduledTerminalPhaseTarget_relativeDeviation_le_final
    (q : VolumeParams) (I : VolumeInput q.n) {eps : ℝ} (heps : 0 < eps) :
    let count := figureOneSampleCount q
    let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
      figureOneExecutableMomentSlack q / 8
    figureOneScheduledTerminalPhaseTarget q I
        {result | eps * figureOneIdealPhaseMean q I .terminal ≤
          |scheduledBalancedPhaseRatio result -
            figureOneIdealPhaseMean q I .terminal|} ≤
      (ENNReal.ofReal (delta / eps ^ 2) +
          scheduledResetReferenceError q (count - 1)) +
        (scheduledBalancedStationaryTargetError q +
          (count - 1) • figureOneCorrectedTransitionBudget q) := by
  dsimp only
  let count := figureOneSampleCount q
  let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
    figureOneExecutableMomentSlack q / 8
  let bound := ENNReal.ofReal (delta / eps ^ 2) +
    scheduledResetReferenceError q (count - 1)
  have hhistory :=
    initializedScheduledRetainedHistory_terminal_relativeDeviation_le_final
      q I heps
  have htarget :=
    figureOneScheduledTerminalPhaseTarget_deviation_le_of_initializedHistory
      q I (figureOneIdealPhaseMean q I .terminal) eps bound (by
        simpa [count, delta, bound] using hhistory)
  have hdead := figureOneScheduledTerminalShadow_dead_le q I
  exact htarget.trans (by
    dsimp [count, bound] at htarget ⊢
    gcongr)

/-- On the terminal target, clamped raw output and the ordinary phase ratio
have the same scalar law. -/
theorem map_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_ratio
    (q : VolumeParams) (I : VolumeInput q.n) :
    (figureOneScheduledTerminalPhaseTarget q I).map
        figureOneScheduledTraceLiveRawOutput =
      (figureOneScheduledTerminalPhaseTarget q I).map
        scheduledBalancedPhaseRatio := by
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map initialMap
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  let output := balancedCoolingAverage count ∘
    (retainedSumOutput (S := AmbientSpace q.n))
  have hcount : 0 < count := figureOneSampleCount_pos q
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  have hweight0 : ∀ x, 0 ≤ weight x :=
    uniformRatioWeight_nonnegative _
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (terminalVariance_pos' q)
  have hinitialMap : Measurable initialMap :=
    hweight.prodMk measurable_some
  have hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1 := by
    apply (ae_map_iff hinitialMap.aemeasurable
      (measurableSet_le measurable_const measurable_fst)).2
    filter_upwards with x
    exact hweight0 x
  have hshadow0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 :=
    iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight hweight0 initial hinitial0 (count - 1)
  have houtput : Measurable output :=
    (measurable_balancedCoolingAverage count).comp measurable_retainedSumOutput
  rw [figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel]
  rw [Measure.map_map
      measurable_figureOneScheduledTraceLiveRawOutput houtput,
    Measure.map_map measurable_scheduledBalancedPhaseRatio houtput]
  apply Measure.map_congr
  filter_upwards [hshadow0] with state hstate0
  rcases state with ⟨total, state⟩
  cases state with
  | none =>
      simp [output, Function.comp_def, retainedSumOutput,
        balancedCoolingAverage, figureOneScheduledTraceLiveRawOutput,
        scheduledBalancedPhaseRatio]
  | some point =>
      have havg0 : 0 ≤ total / (count : ℝ) :=
        div_nonneg hstate0 hcountReal.le
      simp [output, Function.comp_def, retainedSumOutput,
        balancedCoolingAverage, figureOneScheduledTraceLiveRawOutput,
        scheduledBalancedPhaseRatio, max_eq_right havg0]

/-- The final terminal equation-(6) deviation estimate at chronological trace
coordinate `terminalPhaseSteps q + 1`.  Besides the reference/event charge,
the right side lists exactly the collector-death and terminal boundary MLU
charges. -/
theorem scheduledBalancedFinalTraceRawTerminalPhase_relativeDeviation_le_final
    (q : VolumeParams) (I : VolumeInput q.n) {eps : ℝ} (heps : 0 < eps) :
    let count := figureOneSampleCount q
    let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
      figureOneExecutableMomentSlack q / 8
    (scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q))
      {trace | eps * figureOneIdealPhaseMean q I .terminal ≤
        |scheduledBalancedTracePhaseVariable q
            (terminalPhaseSteps q + 1) trace -
          figureOneIdealPhaseMean q I .terminal|} ≤
      ((ENNReal.ofReal (delta / eps ^ 2) +
          scheduledResetReferenceError q (count - 1)) +
        (scheduledBalancedStationaryTargetError q +
          (count - 1) • figureOneCorrectedTransitionBudget q)) +
        (figureOneCorrectedTransitionBudget q +
          figureOneScheduledRetainedError q (terminalPhaseSteps q)) := by
  dsimp only
  let count := figureOneSampleCount q
  let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
    figureOneExecutableMomentSlack q / 8
  let finalLaw := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let W := scheduledBalancedTracePhaseVariable q
    (terminalPhaseSteps q + 1)
  let target := figureOneIdealPhaseMean q I .terminal
  let scalarDeviation : Set ℝ :=
    {value | eps * target ≤ |value - target|}
  let bound :=
    (ENNReal.ofReal (delta / eps ^ 2) +
      scheduledResetReferenceError q (count - 1)) +
      (scheduledBalancedStationaryTargetError q +
        (count - 1) • figureOneCorrectedTransitionBudget q)
  have hset : MeasurableSet scalarDeviation := by
    apply measurableSet_le measurable_const
    exact (measurable_id.sub_const target).abs
  have hcomparison :=
    scheduledBalancedFinalTraceRawTerminalPhase_leUpTo_target q I
  have hevent := hcomparison.event_le scalarDeviation
  rw [Measure.map_apply
      (measurable_scheduledBalancedTracePhaseVariable q
        (terminalPhaseSteps q + 1)) hset,
    map_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_ratio,
    Measure.map_apply measurable_scheduledBalancedPhaseRatio hset] at hevent
  have htarget :
      figureOneScheduledTerminalPhaseTarget q I
          (scheduledBalancedPhaseRatio ⁻¹' scalarDeviation) ≤ bound := by
    simpa [scalarDeviation, target, bound, count, delta, Set.preimage] using
      figureOneScheduledTerminalPhaseTarget_relativeDeviation_le_final
        q I heps
  have hplus :
      figureOneScheduledTerminalPhaseTarget q I
          (scheduledBalancedPhaseRatio ⁻¹' scalarDeviation) +
          (figureOneCorrectedTransitionBudget q +
            figureOneScheduledRetainedError q (terminalPhaseSteps q)) ≤
        bound + (figureOneCorrectedTransitionBudget q +
          figureOneScheduledRetainedError q (terminalPhaseSteps q)) := by
    simpa only [add_comm] using
      add_le_add_right htarget
        (figureOneCorrectedTransitionBudget q +
          figureOneScheduledRetainedError q (terminalPhaseSteps q))
  have hfinal := hevent.trans hplus
  simpa [finalLaw, W, target, scalarDeviation, bound, count, delta,
    Set.preimage] using hfinal

#print axioms initializedScheduledRetainedHistory_terminal_deviation_eq_retainedSum
#print axioms figureOneScheduledTerminalPhaseTarget_deviation_eq_retainedSum
#print axioms
  figureOneScheduledTerminalPhaseTarget_deviation_le_of_initializedHistory
#print axioms figureOneScheduledTerminalShadow_dead_le
#print axioms
  figureOneScheduledTerminalPhaseTarget_relativeDeviation_le_final
#print axioms map_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_ratio
#print axioms
  scheduledBalancedFinalTraceRawTerminalPhase_relativeDeviation_le_final

end

end ArlibCommunity.Algorithms.CV18
