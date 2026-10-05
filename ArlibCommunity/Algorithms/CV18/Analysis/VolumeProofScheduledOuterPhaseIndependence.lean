/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledOuterPhaseMarginal
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorPrefixIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox

/-!
# Sharp one-step independence between scheduled phases

Once the outer reset has made the retained trace marginal the normalized
accepted target, conditioning on any half-probability event in the old trace
produces a `2`-warm trace law.  Its live retained submeasure is consequently
`16`-warm relative to the speedy stationary law.  The existing asymmetric
Markov lemma then charges one corrected transition budget for the conditioned
law and one for the unconditional law.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

noncomputable section

theorem scheduledBalancedTraceLiveStateLaw_eq_map_of_retainedSome
    (q : VolumeParams)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    (accepted : Measure (AmbientSpace q.n))
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceLiveStateLaw rho transform =
      accepted.map transform := by
  have hid : scheduledBalancedTraceLiveStateLaw rho id = accepted := by
    rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome,
      hretained, map_some_restrict_extract_eq]
  calc
    scheduledBalancedTraceLiveStateLaw rho transform =
        (scheduledBalancedTraceLiveStateLaw rho id).map transform := by
      unfold scheduledBalancedTraceLiveStateLaw
      rw [Measure.map_map htransform
        ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
          measurable_scheduledBalancedTraceRetainedState)]
      rfl
    _ = accepted.map transform := by rw [hid]

theorem scheduledBalancedTraceDeadStateLaw_mass_eq_zero_of_retainedSome
    (q : VolumeParams)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    (accepted : Measure (AmbientSpace q.n))
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw rho transform Set.univ = 0 := by
  rw [scheduledBalancedTraceDeadStateLaw_apply_univ rho transform htransform]
  have hevent := congrArg
    (fun law : Measure (Option (AmbientSpace q.n)) => law {none}) hretained
  rw [Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
      measurableSet_option_none,
    Measure.map_apply measurable_some measurableSet_option_none] at hevent
  have hleft : scheduledBalancedTraceRetainedOption ⁻¹'
      ({none} : Set (Option (AmbientSpace q.n))) =
        scheduledBalancedTraceDeadSet q.n := by
    ext trace
    rcases trace with ⟨history, live⟩
    cases live <;> simp [scheduledBalancedTraceRetainedOption,
      scheduledBalancedTraceDeadSet]
  have hright : (some : AmbientSpace q.n → Option (AmbientSpace q.n)) ⁻¹'
      ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
    ext point
    simp
  simpa [hleft, hright] using hevent

/-- A `2`-warm conditioning of a trace with an exact accepted retained
marginal still reaches the Gaussian public phase target within one corrected
transition budget. -/
theorem bind_gaussian_observation_leUpTo_of_warm_two_accepted_retained
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (rho mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (accepted : Measure (AmbientSpace q.n))
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase))
    (hwarm : Arlib.IsWarm 2 mu rho) :
    MeasureLeUpTo
      (mu.bind (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase))
      (figureOneScheduledGaussianPhaseTarget q I phase)
      (figureOneCorrectedTransitionBudget q) := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun point =>
    accuracyScaleFactor q • point
  let good : Measure (AmbientSpace q.n) :=
    (2 : ENNReal) • accepted.map scale
  let bad : Measure (AmbientSpace q.n) := 0
  let _ : IsFiniteMeasure bad := by
    dsimp only [bad]
    infer_instance
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hmule : mu ≤ (2 : ENNReal) • rho :=
    (isWarm_iff_le_smul mu rho).1 hwarm
  have hliveRho : scheduledBalancedTraceLiveStateLaw rho scale =
      accepted.map scale :=
    scheduledBalancedTraceLiveStateLaw_eq_map_of_retainedSome
      q rho accepted hretained scale hscale
  have hlive : scheduledBalancedTraceLiveStateLaw mu scale ≤ good + bad := by
    rw [show good + bad = good by simp [bad]]
    calc
      scheduledBalancedTraceLiveStateLaw mu scale ≤
          (2 : ENNReal) • scheduledBalancedTraceLiveStateLaw rho scale :=
        scheduledBalancedTraceLiveStateLaw_mono_smul
          q mu rho 2 scale hscale hmule
      _ = good := by rw [hliveRho]
  have hgood16 : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I phase) := by
    intro S hS
    rw [show good = (2 : ENNReal) • accepted.map scale by rfl,
      Measure.smul_apply, smul_eq_mul]
    have hg := hgood S hS
    have hcoef : (2 : ENNReal) *
        ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) =
          ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc
      2 * (accepted.map scale) S ≤
          2 * (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) *
            (figureOneScheduledSpeedyPiAt q I phase) S) := by gcongr
      _ = ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) *
          (figureOneScheduledSpeedyPiAt q I phase) S := by
        rw [← mul_assoc, hcoef]
  have hdeadRho : scheduledBalancedTraceDeadStateLaw rho scale Set.univ = 0 :=
    scheduledBalancedTraceDeadStateLaw_mass_eq_zero_of_retainedSome
      q rho accepted hretained scale hscale
  have hdead := scheduledBalancedTraceDeadStateLaw_mass_mono_smul
    q mu rho 2 scale hscale hmule
  have herror : bad Set.univ +
      scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤ 0 := by
    dsimp only [bad]
    simp only [Measure.coe_zero, Pi.zero_apply, zero_add]
    calc
      scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤
          2 * scheduledBalancedTraceDeadStateLaw rho scale Set.univ := hdead
      _ = 0 := by rw [hdeadRho, mul_zero]
  have hM : (1 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  simpa only [add_zero] using
    (bind_scheduledBalancedTracePhaseObservationLaw_leUpTo_of_live_good_bad
      q I phase hphase mu good bad hM ENNReal.ofReal_ne_top le_rfl
        hlive hgood16 herror)

/-- Gaussian Lemma 7.17(b) with the sharp local coefficient. -/
theorem approxIndepFun_gaussian_phase_of_accepted_retained
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (accepted : Measure (AmbientSpace q.n)) [IsProbabilityMeasure accepted]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase)) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      Prod.fst Prod.snd
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)) := by
  let K := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let target := figureOneScheduledGaussianPhaseTarget q I phase
  have hK :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I phase
  have hconditioned : ∀ mu : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu (rho.map id) →
      MeasureLeUpTo (mu.bind K) target
        (figureOneCorrectedTransitionBudget q) := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    apply bind_gaussian_observation_leUpTo_of_warm_two_accepted_retained
      q I phase hphase rho mu accepted hretained hgood
    simpa using hwarm
  have hbase : MeasureLeUpTo ((rho.map id).bind K) target
      (figureOneCorrectedTransitionBudget q) := by
    rw [Measure.map_id]
    have h := sequentialPairLaw_gaussian_output_leUpTo_of_retainedSome_warm
      q I phase hphase rho accepted hretained
      (hgood.mono <| ENNReal.ofReal_le_ofReal <| by
        nlinarith [speedyAdjacentWarmConstant_one_le q])
    rw [map_sequentialPairLaw_snd rho K hK.1 hK.2] at h
    exact h
  have hind := approxIndepFun_history_next_of_state_warm_base_leUpTo
    rho id measurable_id K hK.1 hK.2 target
    (by simp [figureOneCorrectedTransitionBudget])
    (by simp [figureOneCorrectedTransitionBudget]) hconditioned hbase
  simpa only [Function.comp_id] using hind

/-- Measurable old statistics and the new raw live score inherit the sharp
one-step Gaussian independence coefficient. -/
theorem approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_retained
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (accepted : Measure (AmbientSpace q.n)) [IsProbabilityMeasure accepted]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase))
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (hold : Measurable oldStatistic) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ Prod.fst)
      (figureOneScheduledTraceLiveRawOutput (n := q.n) ∘ Prod.snd)
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)) := by
  exact (approxIndepFun_gaussian_phase_of_accepted_retained
    q I phase hphase rho accepted hretained hgood).comp
      hold (measurable_figureOneScheduledTraceLiveRawOutput (n := q.n))

/-- First/same-phase specialization to the public accepted target. -/
theorem approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_same
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I phase).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (hold : Measurable oldStatistic) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ Prod.fst)
      (figureOneScheduledTraceLiveRawOutput (n := q.n) ∘ Prod.snd)
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)) := by
  let accepted := figureOneScheduledAcceptedTargetAt q I phase
  let _ : IsProbabilityMeasure accepted :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  apply approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_retained
    q I phase hphase rho accepted hretained
  · have h := map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
      q I (scheduleValue_pos q phase)
    apply h.mono
    rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  · exact hold

/-- Noninitial adjacent-phase specialization to the accepted target of the
preceding cooling phase. -/
theorem approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_adjacent
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I previous).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (hold : Measurable oldStatistic) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ Prod.fst)
      (figureOneScheduledTraceLiveRawOutput (n := q.n) ∘ Prod.snd)
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I (previous + 1))) := by
  let accepted := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure accepted :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  apply approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_retained
    q I (previous + 1) hnext rho accepted hretained
  · exact map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
      q I previous
  · exact hold

/-! ## Terminal phase -/

theorem bind_terminal_observation_leUpTo_of_warm_two_accepted_retained
    (q : VolumeParams) (I : VolumeInput q.n)
    (rho mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (accepted : Measure (AmbientSpace q.n))
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)))
    (hwarm : Arlib.IsWarm 2 mu rho) :
    MeasureLeUpTo
      (mu.bind (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q)))
      (figureOneScheduledTerminalPhaseTarget q I)
      (figureOneCorrectedTransitionBudget q) := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun point =>
    accuracyScaleFactor q • point
  let good : Measure (AmbientSpace q.n) :=
    (2 : ENNReal) • accepted.map scale
  let bad : Measure (AmbientSpace q.n) := 0
  let _ : IsFiniteMeasure bad := by
    dsimp only [bad]
    infer_instance
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hmule : mu ≤ (2 : ENNReal) • rho :=
    (isWarm_iff_le_smul mu rho).1 hwarm
  have hliveRho : scheduledBalancedTraceLiveStateLaw rho scale =
      accepted.map scale :=
    scheduledBalancedTraceLiveStateLaw_eq_map_of_retainedSome
      q rho accepted hretained scale hscale
  have hlive : scheduledBalancedTraceLiveStateLaw mu scale ≤ good + bad := by
    rw [show good + bad = good by simp [bad]]
    calc
      scheduledBalancedTraceLiveStateLaw mu scale ≤
          (2 : ENNReal) • scheduledBalancedTraceLiveStateLaw rho scale :=
        scheduledBalancedTraceLiveStateLaw_mono_smul
          q mu rho 2 scale hscale hmule
      _ = good := by rw [hliveRho]
  have hgood16 : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)) := by
    intro S hS
    rw [show good = (2 : ENNReal) • accepted.map scale by rfl,
      Measure.smul_apply, smul_eq_mul]
    have hg := hgood S hS
    have hcoef : (2 : ENNReal) *
        ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) =
          ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc
      2 * (accepted.map scale) S ≤
          2 * (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) *
            (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)) S) := by
        gcongr
      _ = ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) *
          (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)) S := by
        rw [← mul_assoc, hcoef]
  have hdeadRho : scheduledBalancedTraceDeadStateLaw rho scale Set.univ = 0 :=
    scheduledBalancedTraceDeadStateLaw_mass_eq_zero_of_retainedSome
      q rho accepted hretained scale hscale
  have hdead := scheduledBalancedTraceDeadStateLaw_mass_mono_smul
    q mu rho 2 scale hscale hmule
  have herror : bad Set.univ +
      scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤ 0 := by
    dsimp only [bad]
    simp only [Measure.coe_zero, Pi.zero_apply, zero_add]
    calc
      scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤
          2 * scheduledBalancedTraceDeadStateLaw rho scale Set.univ := hdead
      _ = 0 := by rw [hdeadRho, mul_zero]
  have hM : (1 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hout :=
    bind_scheduledBalancedTerminalTracePhaseOutputLaw_leUpTo_of_live_good_bad
      q I mu good bad hM ENNReal.ofReal_ne_top le_rfl hlive hgood16 herror
        id (none : Option (ℝ × AmbientSpace q.n)) measurable_id
  have houtEq : scheduledBalancedTracePhaseOutputLaw
      figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
        id (none : Option (ℝ × AmbientSpace q.n)) =
      scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q) := by
    funext trace
    rcases trace with ⟨history, live⟩
    cases live <;>
      simp [scheduledBalancedTracePhaseOutputLaw,
        scheduledBalancedTracePhaseObservationLaw]
  rw [houtEq, Measure.map_id] at hout
  simpa only [add_zero] using hout

theorem approxIndepFun_terminal_phase_of_accepted_retained
    (q : VolumeParams) (I : VolumeInput q.n)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (accepted : Measure (AmbientSpace q.n)) [IsProbabilityMeasure accepted]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q))) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      Prod.fst Prod.snd
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))) := by
  let K := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  let target := figureOneScheduledTerminalPhaseTarget q I
  have hK :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledTerminalPhaseTarget_isProbabilityMeasure q I
  have hconditioned : ∀ mu : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu (rho.map id) →
      MeasureLeUpTo (mu.bind K) target
        (figureOneCorrectedTransitionBudget q) := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    apply bind_terminal_observation_leUpTo_of_warm_two_accepted_retained
      q I rho mu accepted hretained hgood
    simpa using hwarm
  have hbase : MeasureLeUpTo ((rho.map id).bind K) target
      (figureOneCorrectedTransitionBudget q) := by
    rw [Measure.map_id]
    have h := sequentialPairLaw_terminal_output_leUpTo_of_retainedSome_warm
      q I rho accepted hretained
      (hgood.mono <| ENNReal.ofReal_le_ofReal <| by
        nlinarith [speedyAdjacentWarmConstant_one_le q])
    rw [map_sequentialPairLaw_snd rho K hK.1 hK.2] at h
    exact h
  have hind := approxIndepFun_history_next_of_state_warm_base_leUpTo
    rho id measurable_id K hK.1 hK.2 target
    (by simp [figureOneCorrectedTransitionBudget])
    (by simp [figureOneCorrectedTransitionBudget]) hconditioned hbase
  simpa only [Function.comp_id] using hind

theorem approxIndepFun_oldStatistic_terminal_liveRaw_of_accepted
    (q : VolumeParams) (I : VolumeInput q.n)
    (rho : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure rho]
    (hretained : rho.map scheduledBalancedTraceRetainedOption =
      (figureOneScheduledAcceptedTargetAt q I
        (terminalPhaseSteps q - 1)).map some)
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (hold : Measurable oldStatistic) :
    ApproxIndepFun
      (figureOneCorrectedTransitionBudget q +
        figureOneCorrectedTransitionBudget q).toReal
      (oldStatistic ∘ Prod.fst)
      (figureOneScheduledTraceLiveRawOutput (n := q.n) ∘ Prod.snd)
      (sequentialPairLaw rho
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q))) := by
  let previous := terminalPhaseSteps q - 1
  have hsucc : previous + 1 = terminalPhaseSteps q := by
    dsimp only [previous]
    exact Nat.sub_add_cancel (terminalPhaseSteps_pos q)
  let accepted := figureOneScheduledAcceptedTargetAt q I previous
  let _ : IsProbabilityMeasure accepted :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I previous
  have hgood := map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
    q I previous
  rw [hsucc] at hgood
  exact (approxIndepFun_terminal_phase_of_accepted_retained
    q I rho accepted (by simpa only [accepted, previous] using hretained)
      hgood).comp hold
        (measurable_figureOneScheduledTraceLiveRawOutput (n := q.n))

#print axioms approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_same
#print axioms approxIndepFun_oldStatistic_gaussian_liveRaw_of_accepted_adjacent
#print axioms approxIndepFun_oldStatistic_terminal_liveRaw_of_accepted

end

end ArlibCommunity.Algorithms.CV18
