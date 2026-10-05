/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalResetDeviation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledPhaseMeanBridge
import ArlibCommunity.Algorithms.CV18.Analysis.Background.RecordedKernelReset

/-!
# Joint terminal reset target

The terminal reset reference is strengthened here to retain its exact final
state marginal together with its equation-(6) empirical-average moments.  Its
mapped joint law can therefore be used as the target of the outer
history-preserving recorded-output reset.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Terminal uniform-weight version of the fixed-reset reference, retaining
the exact final operational-state marginal. -/
theorem exists_terminalScheduledRetainedResetReference_all_approxIndep_with_state
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I
          (terminalPhaseSteps q) (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      (∀ j, j < count →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I (terminalPhaseSteps q)) ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      (∀ r, r < count →
        ApproxIndepFun
          (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal)
          (sequentialPrefixSum
            (retainedSampleObservation
              (uniformRatioWeight (n := q.n) (terminalVariance q))) r)
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q)) r)
          reference) := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, hstate, _⟩ :=
    exists_scheduledRetainedResetReference_all_approxIndep_with_state
      q I (terminalPhaseSteps q) count hcount0 hcountMax
  let actual := initializedScheduledRetainedHistoryLaw
    q I (terminalPhaseSteps q) (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I (terminalPhaseSteps q) (count - 1)
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  refine ⟨reference, hreferenceProb, hmlu, hcoordinates, hstate, ?_⟩
  intro r hr
  have hprefix : Measurable
      (sequentialPrefixSum (retainedSampleObservation weight) r) :=
    measurable_sequentialPrefixSum
      (fun j => measurable_retainedSampleObservation hweight j) r
  have hobs : Measurable (retainedSampleObservation weight r) :=
    measurable_retainedSampleObservation hweight r
  have hactualIndep :=
    approxIndepFun_initializedScheduledRetainedHistory_all_of_weight
      q I (terminalPhaseSteps q) count hcountMax weight hweight r hr
  have htv : TVLe reference actual
      (scheduledResetReferenceError q (count - 1)) := hmlu.to_tvLe.symm
  simpa only [actual, weight] using
    (ApproxIndepFun.of_tvLe reference actual
      (scheduledResetReferenceError_ne_top q (count - 1))
      (sequentialPrefixSum (retainedSampleObservation weight) r)
      (retainedSampleObservation weight r) hprefix hobs htv hactualIndep)

/-- Terminal equation-(6) reference with the exact retained-state marginal
kept in the same existential witness. -/
theorem exists_terminalScheduledRetainedResetReference_average_secondMoment_with_state
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I
          (terminalPhaseSteps q) (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      MemLp (fun history =>
        sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ)) 2 reference ∧
      (∫ history, sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ) ∂reference) =
        figureOneIdealPhaseMean q I .terminal ∧
      (∫ history, (sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + (Real.exp (1 / 2) - 1) / (count : ℝ)) *
            (figureOneIdealPhaseMean q I .terminal) ^ 2 +
          3 * (figureOneDependentEpsilon q +
              3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
                (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * (Real.exp (1 / 2)) ^ 2 := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, hstate, hind⟩ :=
    exists_terminalScheduledRetainedResetReference_all_approxIndep_with_state
      q I count hcount hcountMax
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let Y : ℕ → RetainedSampleHistory (AmbientSpace q.n) → ℝ :=
    retainedSampleObservation weight
  let mean := figureOneIdealPhaseMean q I .terminal
  let B : ℝ := Real.exp (1 / 2)
  let epsilon := figureOneDependentEpsilon q +
    3 * (scheduledResetReferenceError q (count - 1)).toReal
  have hweight : Measurable weight := measurable_uniformRatioWeight _
  have hYmeas : ∀ j, Measurable (Y j) := fun j =>
    measurable_retainedSampleObservation hweight j
  have hY0 : ∀ j, j < count → ∀ history, 0 ≤ Y j history := by
    intro j hj history
    unfold Y retainedSampleObservation retainedOptionWeight
    cases history.1 j <;> simp [weight, uniformRatioWeight_nonnegative]
  have hY3 : ∀ j, j < count → MemLp (Y j) 3 reference := by
    intro j hj
    simpa [Y, weight] using
      memLp_retainedSampleObservation_uniform_terminal_three_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYmeanEq : ∀ j, j < count →
      (∫ history, Y j history ∂reference) = mean := by
    intro j hj
    simpa [Y, weight, mean] using
      integral_retainedSampleObservation_uniform_terminal_eq_ideal_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYsecond : ∀ j, j < count →
      (∫ history, Y j history ^ 2 ∂reference) ≤ B * mean ^ 2 := by
    intro j hj
    simpa [Y, weight, B, mean] using
      integral_retainedSampleObservation_uniform_terminal_sq_le_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYcube : ∀ j, j < count →
      (∫ history, Y j history ^ 3 ∂reference) ≤ B ^ 3 := by
    intro j hj
    simpa [Y, weight, B] using
      integral_retainedSampleObservation_uniform_terminal_cube_le_of_map_eq
        q I j reference (hcoordinates j hj)
  have hprefix := terminalExactShadowHistory_prefix_thirdMoment_le
    q I count reference hcoordinates
  have hmean0 : 0 ≤ mean := (figureOneIdealPhaseMean_pos q I .terminal).le
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    have hdependent : 0 < figureOneDependentEpsilon q := by
      unfold figureOneDependentEpsilon
      have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
        exact_mod_cast figureOneDependentPhaseCount_pos q
      exact div_pos (sq_pos_of_pos q.heps.1)
        (mul_pos
          (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
    positivity
  have havg := sequentialAverage_secondMoment_le_of_approxIndepPrefix_thirdMoment
    reference hYmeas count hcount (Real.exp_pos ((1 : ℝ) / 2)) hmean0
      hepsilon hY0 hY3 (fun j hj => (hYmeanEq j hj).le) hYsecond
      (fun i hi => by simpa [Y, weight] using (hprefix i hi).1)
      (fun i hi => by simpa [Y, weight, B] using (hprefix i hi).2)
      hYcube (by simpa [epsilon, Y, weight] using hind)
  have hprefixLp := (hprefix count le_rfl).1
  have havgMem : MemLp (fun history =>
      sequentialPrefixSum Y count history / (count : ℝ)) 2 reference := by
    have h := (hprefixLp.mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 3)).const_mul ((count : ℝ)⁻¹)
    simpa [div_eq_mul_inv, mul_comm] using h
  have havgMean : (∫ history,
      sequentialPrefixSum Y count history / (count : ℝ) ∂reference) = mean := by
    have hcountR : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
    rw [integral_div]
    unfold sequentialPrefixSum
    rw [integral_finsetSum (Finset.range count) (fun j hj =>
      (hY3 j (Finset.mem_range.mp hj)).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun j hj => hYmeanEq j (Finset.mem_range.mp hj))]
    simp [hcountR]
  refine ⟨reference, hreferenceProb, hmlu, hstate, ?_, ?_, ?_⟩
  · simpa [Y, weight] using havgMem
  · simpa [Y, weight, mean] using havgMean
  · simpa [epsilon, Y, weight, B, mean] using havg

/-! ## The joint target consumed by the outer recorded-phase reset -/

/-- Package the terminal empirical average together with its final retained
state in the same output type as the executable terminal collector. -/
noncomputable def terminalScheduledResetJointOutput
    (q : VolumeParams) :
    RetainedSampleHistory (AmbientSpace q.n) →
      Option (ℝ × AmbientSpace q.n) :=
  balancedCoolingAverage (figureOneSampleCount q) ∘
    retainedSumOutput ∘
      retainedSampleHistoryToSum
        (uniformRatioWeight (n := q.n) (terminalVariance q))
        (figureOneSampleCount q)

theorem measurable_terminalScheduledResetJointOutput (q : VolumeParams) :
    Measurable (terminalScheduledResetJointOutput q) := by
  exact (measurable_balancedCoolingAverage (figureOneSampleCount q)).comp <|
    measurable_retainedSumOutput.comp <|
      measurable_retainedSampleHistoryToSum
        (measurable_uniformRatioWeight (terminalVariance q)) _

/-- The initialized terminal sample-history output is exactly the public
terminal phase target. -/
theorem map_initializedScheduledRetainedHistory_terminalJointOutput
    (q : VolumeParams) (I : VolumeInput q.n) :
    (initializedScheduledRetainedHistoryLaw q I (terminalPhaseSteps q)
      (figureOneSampleCount q - 1)).map
        (terminalScheduledResetJointOutput q) =
      figureOneScheduledTerminalPhaseTarget q I := by
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (terminalVariance_pos' q)
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  have hsum := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K hK.1 hK.2 weight hweight exact (count - 1)
  have htail : count - 1 + 1 = count := by
    have hcountPos := figureOneSampleCount_pos q
    omega
  rw [htail] at hsum
  rw [figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel]
  rw [← hsum]
  unfold terminalScheduledResetJointOutput
  rw [Measure.map_map
    ((measurable_balancedCoolingAverage count).comp
      measurable_retainedSumOutput)
    (measurable_retainedSampleHistoryToSum hweight count)]
  simp only [initializedScheduledRetainedHistoryLaw,
    scheduleValue_terminalPhaseSteps]
  rfl

@[simp] theorem optionSnd_terminalScheduledResetJointOutput
    (q : VolumeParams)
    (history : RetainedSampleHistory (AmbientSpace q.n)) :
    optionSnd (terminalScheduledResetJointOutput q history) =
      retainedSampleHistoryState history := by
  rcases history with ⟨coordinates, state⟩
  cases state <;>
    simp [terminalScheduledResetJointOutput, Function.comp_def,
      retainedSampleHistoryToSum, retainedSumOutput, balancedCoolingAverage,
      retainedSampleHistoryState, optionSnd]

theorem terminalScheduledResetJointOutput_liveRawOutput
    (q : VolumeParams)
    (history : RetainedSampleHistory (AmbientSpace q.n))
    (hlive : retainedSampleHistoryState history ≠ none) :
    figureOneScheduledTraceLiveRawOutput
        (terminalScheduledResetJointOutput q history) =
      sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q)))
          (figureOneSampleCount q) history /
        (figureOneSampleCount q : ℝ) := by
  rcases history with ⟨coordinates, state⟩
  cases state with
  | none => exact (hlive rfl).elim
  | some point =>
      simp only [terminalScheduledResetJointOutput, Function.comp_apply,
        retainedSampleHistoryToSum, retainedSumOutput, balancedCoolingAverage,
        figureOneScheduledTraceLiveRawOutput, sequentialPrefixSum]
      rw [max_eq_right]
      exact div_nonneg (Finset.sum_nonneg fun j _ => by
        unfold retainedSampleObservation retainedOptionWeight
        cases hcoord : coordinates j with
        | none => simp [hcoord]
        | some point =>
            simpa only [hcoord] using
              uniformRatioWeight_nonnegative (terminalVariance q) point)
        (Nat.cast_nonneg _)

/-- A reference whose retained-state pushforward is the exact `some` target
is live almost everywhere. -/
theorem ae_retainedSampleHistoryState_ne_none_of_map_eq_exactSome
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hstate : reference.map retainedSampleHistoryState =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    ∀ᵐ history ∂reference, retainedSampleHistoryState history ≠ none := by
  have hnone : scheduledRetainedExactSome q I (terminalPhaseSteps q)
      ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
    unfold scheduledRetainedExactSome
    rw [Measure.map_apply measurable_some measurableSet_option_none]
    have hpreimage : some ⁻¹'
        ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
      ext point
      simp
    rw [hpreimage, measure_empty]
  have hpreimage : reference
      (retainedSampleHistoryState ⁻¹' ({none} : Set (Option (AmbientSpace q.n)))) = 0 := by
    have happly := congrArg
      (fun nu : Measure (Option (AmbientSpace q.n)) =>
        nu ({none} : Set (Option (AmbientSpace q.n)))) hstate
    have hmapApply :
        (reference.map retainedSampleHistoryState)
            ({none} : Set (Option (AmbientSpace q.n))) =
          reference
            (retainedSampleHistoryState ⁻¹'
              ({none} : Set (Option (AmbientSpace q.n)))) := by
      exact Measure.map_apply measurable_snd measurableSet_option_none
    rw [hmapApply, hnone] at happly
    exact happly
  rw [ae_iff]
  have hnot : {history : RetainedSampleHistory (AmbientSpace q.n) |
        ¬ retainedSampleHistoryState history ≠ none} =
      {history : RetainedSampleHistory (AmbientSpace q.n) |
        retainedSampleHistoryState history = none} := by
    ext history
    simp
  have hset : {history | retainedSampleHistoryState history = none} =
      retainedSampleHistoryState ⁻¹'
        ({none} : Set (Option (AmbientSpace q.n))) := by
    ext history
    simp
  rw [hnot, hset]
  exact hpreimage

/-- The mapped joint terminal target carries the scalar equation-(6) facts
and the exact retained-state marginal required by
`exists_historyRecordedOutputReset_of_tvLe`. -/
theorem exists_terminalScheduledResetJointTarget
    (q : VolumeParams) (I : VolumeInput q.n) :
    let count := figureOneSampleCount q
    ∃ target : Measure (Option (ℝ × AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo
        (figureOneScheduledTerminalPhaseTarget q I)
        target (scheduledResetReferenceError q (count - 1)) ∧
      target.map optionSnd =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      MemLp (figureOneScheduledTraceLiveRawOutput (n := q.n)) 2 target ∧
      (∫ result, figureOneScheduledTraceLiveRawOutput result ∂target) =
        figureOneIdealPhaseMean q I .terminal ∧
      (∫ result, figureOneScheduledTraceLiveRawOutput result ^ 2 ∂target) ≤
        (1 + (Real.exp (1 / 2) - 1) / (count : ℝ) +
            figureOneExecutableMomentSlack q / 8) *
          (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
  dsimp only
  let count := figureOneSampleCount q
  obtain ⟨reference, hreferenceProb, hmlu, hstate, havgMem, havgMean,
      havgSecond⟩ :=
    exists_terminalScheduledRetainedResetReference_average_secondMoment_with_state
      q I count (figureOneSampleCount_pos q)
        (figureOneTerminalSampleCount_le_dependentMax q)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let output := terminalScheduledResetJointOutput q
  let average : RetainedSampleHistory (AmbientSpace q.n) → ℝ := fun history =>
    sequentialPrefixSum
      (retainedSampleObservation
        (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
      (count : ℝ)
  let target := reference.map output
  have houtput : Measurable output := measurable_terminalScheduledResetJointOutput q
  have htargetProb : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  have hlive := ae_retainedSampleHistoryState_ne_none_of_map_eq_exactSome
    q I reference hstate
  have hscalar : ∀ᵐ history ∂reference,
      figureOneScheduledTraceLiveRawOutput (output history) = average history := by
    filter_upwards [hlive] with history hhistory
    exact terminalScheduledResetJointOutput_liveRawOutput q history hhistory
  refine ⟨target, htargetProb, ?_, ?_, ?_, ?_, ?_⟩
  · have hmapped := hmlu.map houtput
    rw [map_initializedScheduledRetainedHistory_terminalJointOutput q I]
      at hmapped
    simpa only [target, output] using hmapped
  · calc
      target.map optionSnd =
          reference.map (optionSnd ∘ output) :=
        Measure.map_map measurable_optionSnd houtput
      _ = reference.map retainedSampleHistoryState := by
        apply Measure.map_congr
        filter_upwards with history
        exact optionSnd_terminalScheduledResetJointOutput q history
      _ = scheduledRetainedExactSome q I (terminalPhaseSteps q) := hstate
  · change MemLp figureOneScheduledTraceLiveRawOutput 2 (reference.map output)
    rw [memLp_map_measure_iff
      measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable
      houtput.aemeasurable]
    exact (memLp_congr_ae hscalar).2 havgMem
  · rw [integral_map houtput.aemeasurable
      measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable]
    rw [integral_congr_ae hscalar]
    exact havgMean
  · rw [integral_map houtput.aemeasurable
      (measurable_figureOneScheduledTraceLiveRawOutput.pow_const 2).aestronglyMeasurable]
    have hscalarSq : ∀ᵐ history ∂reference,
        (figureOneScheduledTraceLiveRawOutput (output history)) ^ 2 =
          (average history) ^ 2 := by
      filter_upwards [hscalar] with history hhistory
      rw [hhistory]
    rw [integral_congr_ae hscalarSq]
    have hdependence :=
      figureOne_terminalResetReference_average_dependence_le_slack_div_eight
        q (figureOneSampleCount_pos q)
          (figureOneTerminalSampleCount_le_dependentMax q)
    have hmeanOne : 1 ≤ figureOneIdealPhaseMean q I .terminal :=
      figureOneIdealPhaseMean_one_le q I .terminal
    have hslack0 : 0 ≤ figureOneExecutableMomentSlack q / 8 :=
      div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
    have hscaledSlack : figureOneExecutableMomentSlack q / 8 ≤
        figureOneExecutableMomentSlack q / 8 *
          (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
      have hmeanSq : 1 ≤ (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
        nlinarith
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmeanSq hslack0
    dsimp [count, average] at havgSecond hdependence ⊢
    nlinarith

#print axioms
  exists_terminalScheduledRetainedResetReference_all_approxIndep_with_state
#print axioms
  exists_terminalScheduledRetainedResetReference_average_secondMoment_with_state
#print axioms map_initializedScheduledRetainedHistory_terminalJointOutput
#print axioms exists_terminalScheduledResetJointTarget

end

end ArlibCommunity.Algorithms.CV18
