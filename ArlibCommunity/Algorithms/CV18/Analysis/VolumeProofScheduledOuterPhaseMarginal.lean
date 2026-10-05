/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.RecordedKernelReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetainedWarm
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad

/-!
# Output marginals for one outer scheduled phase

The chronological reset construction carries an arbitrary recorded history
beside the executable trace.  This file isolates the fact that the next raw
phase-output marginal only depends on the retained-state marginal of that
trace.  The operational comparison is stated with its genuine warm-start
premise and then specialized to the normalized accepted targets used between
CV18 cooling phases.

An exact truncated-Gaussian retained marginal is deliberately not used as an
operational start here: the available first-transition theorem requires a
warm start relative to the speedy stationary law, and that warmness is proved
for the accepted target.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib

noncomputable section

/-- The second marginal of a sequential pair law is the ordinary bind of the
source by the second-step kernel. -/
theorem map_sequentialPairLaw_snd
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (source : Measure S) (K : S → Measure T)
    (hK : Measurable K) (hKprob : ∀ state, IsProbabilityMeasure (K state)) :
    (sequentialPairLaw source K).map Prod.snd = source.bind K := by
  unfold sequentialPairLaw
  have hpair : Measurable fun state : S =>
      (K state).map fun result => (state, result) :=
    measurable_sequentialPairKernel (rho := source) hK hKprob
  rw [map_bind_eq_bind_map_of_measurable source hpair measurable_snd]
  apply Measure.bind_congr_right
  filter_upwards with state
  have hmk : Measurable fun result : T => (state, result) :=
    measurable_const.prodMk measurable_id
  calc
    ((K state).map fun result => (state, result)).map Prod.snd =
        (K state).map (Prod.snd ∘ fun result => (state, result)) :=
      Measure.map_map measurable_snd hmk
    _ = (K state).map id := by rfl
    _ = K state := Measure.map_id

/-- Optional form of one complete Gaussian observation phase. -/
noncomputable def scheduledGaussianObservationFromRetainedOption
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n))
  | none => Measure.dirac none
  | some point => figureOneScheduledScaledGaussianPhaseLaw q I phase
      (accuracyScaleFactor q • point)

theorem scheduledGaussianObservationFromRetainedOption_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (scheduledGaussianObservationFromRetainedOption q I phase) ∧
    ∀ state, IsProbabilityMeasure
      (scheduledGaussianObservationFromRetainedOption q I phase state) := by
  have hphase :=
    figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
      q I phase
  constructor
  · have hsome : Measurable fun point : AmbientSpace q.n =>
        figureOneScheduledScaledGaussianPhaseLaw q I phase
          (accuracyScaleFactor q • point) :=
      hphase.1.comp <|
        ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id)
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none =>
        change IsProbabilityMeasure (Measure.dirac none)
        infer_instance
    | some point => exact hphase.2 _

theorem scheduledBalancedTracePhaseObservationLaw_eq_fromRetainedOption
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase trace =
      scheduledGaussianObservationFromRetainedOption q I phase
        (scheduledBalancedTraceRetainedOption trace) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      simp [scheduledBalancedTracePhaseObservationLaw,
        scheduledBalancedTraceRetainedOption,
        scheduledGaussianObservationFromRetainedOption]
  | true =>
      simp only [scheduledBalancedTracePhaseObservationLaw, if_true, hphase,
        scheduledBalancedTraceRetainedOption,
        scheduledGaussianObservationFromRetainedOption]
      rfl

/-- A retained `some` marginal with the required contracted warmness gives
the public stationary-first Gaussian phase target, paying only the corrected
first-transition budget. -/
theorem sequentialPairLaw_gaussian_output_leUpTo_of_retainedSome_warm
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    (hretained : source.map scheduledBalancedTraceRetainedOption = mu.map some)
    (hwarm : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q))
      (mu.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase)) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map Prod.snd)
      (figureOneScheduledGaussianPhaseTarget q I phase)
      (figureOneCorrectedTransitionBudget q) := by
  let K := scheduledGaussianObservationFromRetainedOption q I phase
  have hK :=
    scheduledGaussianObservationFromRetainedOption_measurable_and_probability
      q I phase
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  rw [map_sequentialPairLaw_snd source _ hobs.1 hobs.2]
  have hfactor : source.bind
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase) =
      (source.map scheduledBalancedTraceRetainedOption).bind K := by
    rw [map_bind_eq_bind_comp_state source
      measurable_scheduledBalancedTraceRetainedOption hK.1]
    apply Measure.bind_congr_right
    filter_upwards with trace
    simpa only [Function.comp_apply] using
      scheduledBalancedTracePhaseObservationLaw_eq_fromRetainedOption
        q I phase hphase trace
  rw [hfactor, hretained]
  rw [map_bind_eq_bind_comp_state mu measurable_some hK.1]
  let _ : IsProbabilityMeasure
      (mu.map fun point => accuracyScaleFactor q • point) :=
    Measure.isProbabilityMeasure_map
      ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
        accuracyScaleFactor q).smul measurable_id).aemeasurable
  have hbase :=
    bind_figureOneScheduledScaledGaussianPhaseLaw_leUpTo_target_of_warmSixteen
      q I phase (mu.map fun point => accuracyScaleFactor q • point) hwarm
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hphaseK :=
    figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
      q I phase
  rw [map_bind_eq_bind_comp_state mu hscale hphaseK.1] at hbase
  change MeasureLeUpTo
    (mu.bind fun point => figureOneScheduledScaledGaussianPhaseLaw q I phase
      (accuracyScaleFactor q • point))
    (figureOneScheduledGaussianPhaseTarget q I phase)
    (figureOneCorrectedTransitionBudget q)
  exact hbase

/-- Same-phase accepted-target specialization, used for the first recorded
Gaussian phase. -/
theorem sequentialPairLaw_gaussian_output_leUpTo_of_accepted_same
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I phase).map some) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map Prod.snd)
      (figureOneScheduledGaussianPhaseTarget q I phase)
      (figureOneCorrectedTransitionBudget q) := by
  let mu := figureOneScheduledAcceptedTargetAt q I phase
  let _ : IsProbabilityMeasure mu :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  apply sequentialPairLaw_gaussian_output_leUpTo_of_retainedSome_warm
    q I phase hphase source mu hretained
  have hwarm8 := map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
    q I (scheduleValue_pos q phase)
  apply hwarm8.mono
  rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
  exact ENNReal.ofReal_le_ofReal <| by
    nlinarith [speedyAdjacentWarmConstant_one_le q]

/-- First/same-phase operational comparison composed with a public-phase
joint reset target. -/
theorem sequentialPairLaw_gaussian_output_tvLe_resetTarget_of_accepted_same
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I phase).map some)
    (target : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    {delta : ENNReal}
    (htarget : MeasureLeUpTo
      (figureOneScheduledGaussianPhaseTarget q I phase) target delta) :
    Arlib.TVLe
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map Prod.snd)
      target (figureOneCorrectedTransitionBudget q + delta) := by
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  let _ : IsProbabilityMeasure (sequentialPairLaw source
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase)) :=
    sequentialPairLaw_isProbabilityMeasure source hobs.1 hobs.2
  let _ : IsProbabilityMeasure
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact ((sequentialPairLaw_gaussian_output_leUpTo_of_accepted_same
    q I phase hphase source hretained).trans htarget).to_tvLe

/-- Adjacent-phase accepted-target specialization, used after each outer
state reset. -/
theorem sequentialPairLaw_gaussian_output_leUpTo_of_accepted_adjacent
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I previous).map some) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I (previous + 1))).map
            Prod.snd)
      (figureOneScheduledGaussianPhaseTarget q I (previous + 1))
      (figureOneCorrectedTransitionBudget q) := by
  let mu := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure mu :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  apply sequentialPairLaw_gaussian_output_leUpTo_of_retainedSome_warm
    q I (previous + 1) hnext source mu hretained
  have h := map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
    q I previous
  apply h.mono
  exact ENNReal.ofReal_le_ofReal <| by
    nlinarith [speedyAdjacentWarmConstant_one_le q]

/-- Compose the adjacent operational phase comparison with any public-phase
joint reset target.  This is the exact `TVLe` premise consumed by the outer
history-preserving reset constructor. -/
theorem sequentialPairLaw_gaussian_output_tvLe_resetTarget_of_accepted_adjacent
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I previous).map some)
    (target : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    {delta : ENNReal}
    (htarget : MeasureLeUpTo
      (figureOneScheduledGaussianPhaseTarget q I (previous + 1))
      target delta) :
    Arlib.TVLe
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I (previous + 1))).map
            Prod.snd)
      target (figureOneCorrectedTransitionBudget q + delta) := by
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I (previous + 1)
  let _ : IsProbabilityMeasure (sequentialPairLaw source
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I (previous + 1))) :=
    sequentialPairLaw_isProbabilityMeasure source hobs.1 hobs.2
  let _ : IsProbabilityMeasure
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I (previous + 1))).map
            Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact ((sequentialPairLaw_gaussian_output_leUpTo_of_accepted_adjacent
    q I previous hnext source hretained).trans htarget).to_tvLe

/-! ## Terminal phase -/

/-- Optional form of the complete terminal (uniform-ratio) observation
phase. -/
noncomputable def scheduledTerminalObservationFromRetainedOption
    (q : VolumeParams) (I : VolumeInput q.n) :
    Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n))
  | none => Measure.dirac none
  | some point => figureOneScheduledScaledTerminalPhaseLaw q I
      (accuracyScaleFactor q • point)

theorem scheduledTerminalObservationFromRetainedOption_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measurable (scheduledTerminalObservationFromRetainedOption q I) ∧
    ∀ state, IsProbabilityMeasure
      (scheduledTerminalObservationFromRetainedOption q I state) := by
  have hphase :=
    figureOneScheduledScaledTerminalPhaseLaw_measurable_and_probability q I
  constructor
  · have hsome : Measurable fun point : AmbientSpace q.n =>
        figureOneScheduledScaledTerminalPhaseLaw q I
          (accuracyScaleFactor q • point) :=
      hphase.1.comp <|
        ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id)
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none =>
        change IsProbabilityMeasure (Measure.dirac none)
        infer_instance
    | some point => exact hphase.2 _

theorem scheduledBalancedTraceTerminalObservationLaw_eq_fromRetainedOption
    (q : VolumeParams) (I : VolumeInput q.n)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q) trace =
      scheduledTerminalObservationFromRetainedOption q I
        (scheduledBalancedTraceRetainedOption trace) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      simp [scheduledBalancedTracePhaseObservationLaw,
        scheduledBalancedTraceRetainedOption,
        scheduledTerminalObservationFromRetainedOption]
  | true =>
      simp only [scheduledBalancedTracePhaseObservationLaw, if_true,
        lt_self_iff_false, if_false, scheduledBalancedTraceRetainedOption,
        scheduledTerminalObservationFromRetainedOption]
      rfl

/-- Warm retained-state form of the terminal raw-output marginal bridge. -/
theorem sequentialPairLaw_terminal_output_leUpTo_of_retainedSome_warm
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    (hretained : source.map scheduledBalancedTraceRetainedOption = mu.map some)
    (hwarm : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q))
      (mu.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q))) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))).map Prod.snd)
      (figureOneScheduledTerminalPhaseTarget q I)
      (figureOneCorrectedTransitionBudget q) := by
  let K := scheduledTerminalObservationFromRetainedOption q I
  have hK :=
    scheduledTerminalObservationFromRetainedOption_measurable_and_probability
      q I
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  rw [map_sequentialPairLaw_snd source _ hobs.1 hobs.2]
  have hfactor : source.bind
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)) =
      (source.map scheduledBalancedTraceRetainedOption).bind K := by
    rw [map_bind_eq_bind_comp_state source
      measurable_scheduledBalancedTraceRetainedOption hK.1]
    apply Measure.bind_congr_right
    filter_upwards with trace
    simpa only [Function.comp_apply] using
      scheduledBalancedTraceTerminalObservationLaw_eq_fromRetainedOption
        q I trace
  rw [hfactor, hretained]
  rw [map_bind_eq_bind_comp_state mu measurable_some hK.1]
  let _ : IsProbabilityMeasure
      (mu.map fun point => accuracyScaleFactor q • point) :=
    Measure.isProbabilityMeasure_map
      ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
        accuracyScaleFactor q).smul measurable_id).aemeasurable
  have hbase :=
    bind_figureOneScheduledScaledTerminalPhaseLaw_leUpTo_target_of_warmSixteen
      q I (mu.map fun point => accuracyScaleFactor q • point) hwarm
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hphaseK :=
    figureOneScheduledScaledTerminalPhaseLaw_measurable_and_probability q I
  rw [map_bind_eq_bind_comp_state mu hscale hphaseK.1] at hbase
  change MeasureLeUpTo
    (mu.bind fun point => figureOneScheduledScaledTerminalPhaseLaw q I
      (accuracyScaleFactor q • point))
    (figureOneScheduledTerminalPhaseTarget q I)
    (figureOneCorrectedTransitionBudget q)
  exact hbase

/-- The terminal phase starts from the accepted target of the final Gaussian
phase. -/
theorem sequentialPairLaw_terminal_output_leUpTo_of_accepted
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))).map Prod.snd)
      (figureOneScheduledTerminalPhaseTarget q I)
      (figureOneCorrectedTransitionBudget q) := by
  let previous := terminalPhaseSteps q - 1
  have hsucc : previous + 1 = terminalPhaseSteps q := by
    dsimp only [previous]
    exact Nat.sub_add_cancel (terminalPhaseSteps_pos q)
  let mu := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure mu :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  apply sequentialPairLaw_terminal_output_leUpTo_of_retainedSome_warm
    q I source mu (by simpa only [mu, previous] using hretained)
  have h := map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
    q I previous
  rw [hsucc] at h
  apply h.mono
  exact ENNReal.ofReal_le_ofReal <| by
    nlinarith [speedyAdjacentWarmConstant_one_le q]

/-- Terminal operational comparison composed with its joint equation-(6)
reset target. -/
theorem sequentialPairLaw_terminal_output_tvLe_resetTarget_of_accepted
    (q : VolumeParams) (I : VolumeInput q.n)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (target : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    {delta : ENNReal}
    (htarget : MeasureLeUpTo
      (figureOneScheduledTerminalPhaseTarget q I) target delta) :
    Arlib.TVLe
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))).map Prod.snd)
      target (figureOneCorrectedTransitionBudget q + delta) := by
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  let _ : IsProbabilityMeasure (sequentialPairLaw source
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q))) :=
    sequentialPairLaw_isProbabilityMeasure source hobs.1 hobs.2
  let _ : IsProbabilityMeasure
      ((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact ((sequentialPairLaw_terminal_output_leUpTo_of_accepted
    q I source hretained).trans htarget).to_tvLe

#print axioms map_sequentialPairLaw_snd
#print axioms sequentialPairLaw_gaussian_output_leUpTo_of_accepted_same
#print axioms sequentialPairLaw_gaussian_output_tvLe_resetTarget_of_accepted_same
#print axioms sequentialPairLaw_gaussian_output_leUpTo_of_accepted_adjacent
#print axioms sequentialPairLaw_gaussian_output_tvLe_resetTarget_of_accepted_adjacent
#print axioms sequentialPairLaw_terminal_output_leUpTo_of_accepted
#print axioms sequentialPairLaw_terminal_output_tvLe_resetTarget_of_accepted

end

end ArlibCommunity.Algorithms.CV18
