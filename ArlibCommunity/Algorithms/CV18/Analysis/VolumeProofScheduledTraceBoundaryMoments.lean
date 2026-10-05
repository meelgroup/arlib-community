/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledInitialWarmStart

/-!
# Boundary-phase raw-coordinate adapters

The generic Gaussian raw-coordinate comparison starts after phase zero,
because its warm start is the preceding accepted target.  Phase zero instead
starts directly from the exact truncated initial Gaussian.  The terminal
phase uses the uniform-ratio collector.  This file supplies the corresponding
boundary adapters.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

/-- At horizon zero every scheduled trace is live, so its scaled live-state
marginal is exactly the scaled initial truncated Gaussian. -/
theorem scheduledBalancedForwardTraceLaw_zero_liveStateLaw
    (q : VolumeParams) (I : VolumeInput q.n)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceLiveStateLaw
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I 0) transform =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map transform := by
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let initial := scheduledBalancedInitialTrace (n := q.n)
  have hinitial : Measurable initial :=
    measurable_scheduledBalancedInitialTrace
  have hlive : ∀ᵐ trace ∂sigma.map initial,
      trace ∈ scheduledBalancedTraceLiveSet q.n := by
    apply (ae_map_iff hinitial.aemeasurable
      measurableSet_scheduledBalancedTraceLiveSet).2
    filter_upwards with point
    rfl
  unfold scheduledBalancedTraceLiveStateLaw
  change ((sigma.map initial).restrict
      (scheduledBalancedTraceLiveSet q.n)).map
        (transform ∘ scheduledBalancedTraceRetainedState) = sigma.map transform
  rw [Measure.restrict_eq_self_of_ae_mem hlive,
    Measure.map_map
      (htransform.comp measurable_scheduledBalancedTraceRetainedState) hinitial]
  apply Measure.map_congr
  filter_upwards with point
  rfl

/-- The horizon-zero trace has no dead mass. -/
theorem scheduledBalancedForwardTraceLaw_zero_deadStateLaw
    (q : VolumeParams) (I : VolumeInput q.n)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I 0) transform = 0 := by
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let initial := scheduledBalancedInitialTrace (n := q.n)
  have hinitial : Measurable initial :=
    measurable_scheduledBalancedInitialTrace
  have hdead : (sigma.map initial) (scheduledBalancedTraceDeadSet q.n) = 0 := by
    rw [Measure.map_apply hinitial measurableSet_scheduledBalancedTraceDeadSet]
    have hpre : initial ⁻¹' scheduledBalancedTraceDeadSet q.n = ∅ := by
      ext point
      simp [initial, scheduledBalancedInitialTrace,
        scheduledBalancedTraceDeadSet]
    rw [hpre, measure_empty]
  unfold scheduledBalancedTraceDeadStateLaw
  change ((sigma.map initial).restrict
      (scheduledBalancedTraceDeadSet q.n)).map
        (transform ∘ scheduledBalancedTraceRetainedState) = 0
  rw [Measure.restrict_eq_zero.2 hdead, Measure.map_zero]

/-- Phase zero has the same complete raw-coordinate comparison as every
later Gaussian phase, but its good/bad split comes directly from the initial
truncated Gaussian rather than from a preceding accepted target. -/
theorem scheduledBalancedFinalTraceRawGaussianPhase_zero_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q 1))
      ((figureOneScheduledGaussianPhaseTarget q I 0).map
        figureOneScheduledTraceLiveRawOutput)
      (figureOneCorrectedTransitionBudget q +
        scheduledBalancedStationaryTargetError q) := by
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I 0
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I (initialVariance q))
    (figureOneScheduledProposalRadius q (initialVariance q))
    (initialVariance q)
  let good := (scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    q I (initialVariance q) pi).map scale
  obtain ⟨bad, hgoodProb, hscaled, hgoodWarm, hbadMass⟩ :=
    exists_initialScaledScheduled_good_bad q I
  let _ : IsProbabilityMeasure rho :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I 0
  let _ : IsProbabilityMeasure good := by
    simpa [good, pi, scale] using hgoodProb
  let _ : IsFiniteMeasure bad := by
    constructor
    exact (hbadMass.trans_lt <|
      lt_top_iff_ne_top.mpr <|
        ne_top_of_le_ne_top
          (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
          (scheduledBalancedStationaryTargetError_le_targetBudget q))
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hlive : scheduledBalancedTraceLiveStateLaw rho scale ≤ good + bad := by
    rw [show scheduledBalancedTraceLiveStateLaw rho scale = sigma.map scale by
      simpa [rho, sigma] using
        scheduledBalancedForwardTraceLaw_zero_liveStateLaw q I scale hscale]
    simpa [sigma, good, pi, scale, scheduleValue] using hscaled
  have hdead : scheduledBalancedTraceDeadStateLaw rho scale Set.univ = 0 := by
    rw [show scheduledBalancedTraceDeadStateLaw rho scale = 0 by
      simpa [rho] using
        scheduledBalancedForwardTraceLaw_zero_deadStateLaw q I scale hscale]
    simp
  have herror : bad Set.univ +
      scheduledBalancedTraceDeadStateLaw rho scale Set.univ ≤
        scheduledBalancedStationaryTargetError q := by
    rw [hdead, add_zero]
    exact hbadMass
  have hgood : Arlib.IsWarm (8 : ENNReal) good
      (figureOneScheduledSpeedyPiAt q I 0) := by
    simpa [good, pi, scale, figureOneScheduledSpeedyPiAt, scheduleValue] using
      hgoodWarm
  have hM16 : (8 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  apply scheduledBalancedFinalTraceRawPhase_leUpTo_of_immediate
    q I 0 (figureOneDependentPhaseCount_pos q)
      (figureOneScheduledGaussianPhaseTarget q I 0)
  apply bind_scheduledBalancedTracePhaseOutputLaw_leUpTo_of_live_good_bad
    q I 0 (terminalPhaseSteps_pos q) rho good bad (by norm_num) (by norm_num)
      hM16 hlive hgood herror
  exact measurable_figureOneScheduledTraceLiveRawOutput

/-- The terminal uniform-ratio collector has the same final-trace raw-law
comparison as the Gaussian phases, with its dedicated complete terminal
target. -/
theorem scheduledBalancedFinalTraceRawTerminalPhase_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q
            (terminalPhaseSteps q + 1)))
      ((figureOneScheduledTerminalPhaseTarget q I).map
        figureOneScheduledTraceLiveRawOutput)
      (figureOneCorrectedTransitionBudget q +
        figureOneScheduledRetainedError q (terminalPhaseSteps q)) := by
  let phase := terminalPhaseSteps q
  have hphasePos : 0 < phase := terminalPhaseSteps_pos q
  let previous := phase - 1
  have hprevious : previous < terminalPhaseSteps q := by
    dsimp only [previous, phase]
    omega
  have hpreviousSucc : previous + 1 = phase := by
    dsimp only [previous]
    omega
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I previous).map scale
  let eta := figureOneScheduledRetainedError q phase
  obtain ⟨bad, hlive, herror⟩ :=
    exists_figureOneScheduledTraceScaledLive_good_bad
      q I previous hprevious
  have hetaTop : eta ≠ ⊤ := by
    dsimp only [eta, phase]
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun index _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure bad :=
    { measure_univ_lt_top := by
        apply lt_of_le_of_lt
        · exact le_trans (le_add_right le_rfl) herror
        · exact lt_top_iff_ne_top.mpr <| by
            simpa [eta, phase, hpreviousSucc] using hetaTop }
  let _ : IsProbabilityMeasure rho :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I phase
  have hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I phase) := by
    simpa [good, scale, phase, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, hpreviousSucc] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous
  have hM8 : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM8M16 : ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  apply scheduledBalancedFinalTraceRawPhase_leUpTo_of_immediate
    q I phase (by rw [figureOneDependentPhaseCount]; omega)
      (figureOneScheduledTerminalPhaseTarget q I)
  apply
    bind_scheduledBalancedTerminalTracePhaseOutputLaw_leUpTo_of_live_good_bad
      q I rho good bad hM8 ENNReal.ofReal_ne_top hM8M16
  · simpa [rho, good, scale, phase, hpreviousSucc] using hlive
  · exact hgood
  · simpa [rho, scale, eta, phase, hpreviousSucc] using herror
  · exact measurable_figureOneScheduledTraceLiveRawOutput

/-- Symmetric scalar-law form of the phase-zero adapter, ready for bounded
first- or second-moment transfer. -/
theorem scheduledBalancedFinalTraceRawGaussianPhase_zero_tv_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q 1))
      ((figureOneScheduledGaussianPhaseTarget q I 0).map
        figureOneScheduledTraceLiveRawOutput)
      (figureOneCorrectedTransitionBudget q +
        scheduledBalancedStationaryTargetError q) := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q 1)) :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledBalancedTracePhaseVariable q 1).aemeasurable
  let _ : IsProbabilityMeasure (figureOneScheduledGaussianPhaseTarget q I 0) :=
    figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I 0
  let _ : IsProbabilityMeasure
      ((figureOneScheduledGaussianPhaseTarget q I 0).map
        figureOneScheduledTraceLiveRawOutput) :=
    Measure.isProbabilityMeasure_map
      measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable
  exact
    (scheduledBalancedFinalTraceRawGaussianPhase_zero_leUpTo_target q I).to_tvLe

/-- Symmetric scalar-law form of the terminal adapter, ready for bounded
first- or second-moment transfer. -/
theorem scheduledBalancedFinalTraceRawTerminalPhase_tv_target
    (q : VolumeParams) (I : VolumeInput q.n) :
    Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q
            (terminalPhaseSteps q + 1)))
      ((figureOneScheduledTerminalPhaseTarget q I).map
        figureOneScheduledTraceLiveRawOutput)
      (figureOneCorrectedTransitionBudget q +
        figureOneScheduledRetainedError q (terminalPhaseSteps q)) := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q
            (terminalPhaseSteps q + 1))) :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledBalancedTracePhaseVariable q _).aemeasurable
  let _ : IsProbabilityMeasure (figureOneScheduledTerminalPhaseTarget q I) :=
    figureOneScheduledTerminalPhaseTarget_isProbabilityMeasure q I
  let _ : IsProbabilityMeasure
      ((figureOneScheduledTerminalPhaseTarget q I).map
        figureOneScheduledTraceLiveRawOutput) :=
    Measure.isProbabilityMeasure_map
      measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable
  exact
    (scheduledBalancedFinalTraceRawTerminalPhase_leUpTo_target q I).to_tvLe

#print axioms scheduledBalancedForwardTraceLaw_zero_liveStateLaw
#print axioms scheduledBalancedForwardTraceLaw_zero_deadStateLaw
#print axioms
  scheduledBalancedFinalTraceRawGaussianPhase_zero_leUpTo_target
#print axioms scheduledBalancedFinalTraceRawTerminalPhase_leUpTo_target
#print axioms scheduledBalancedFinalTraceRawGaussianPhase_zero_tv_target
#print axioms scheduledBalancedFinalTraceRawTerminalPhase_tv_target

end ArlibCommunity.Algorithms.CV18
