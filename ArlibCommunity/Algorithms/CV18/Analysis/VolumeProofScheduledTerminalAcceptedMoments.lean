/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedSupport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer

/-!
# Terminal moments of the scheduled accepted target

The terminal Gaussian-to-uniform ratio is bounded on both the exact target
and the scheduled accepted target.  This file transfers the paper's terminal
moment bound across the stationary-target total-variation error.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal
open _root_.Arlib

/-- The stationary accepted-target correction is far below the numerical
budget needed by the bounded terminal-moment transfer. -/
theorem scheduledBalancedStationaryTargetError_le_one_div_sixtyFour
    (q : VolumeParams) :
    scheduledBalancedStationaryTargetError q ≤
      ENNReal.ofReal (1 / 64 : ℝ) := by
  apply (scheduledBalancedStationaryTargetError_le_targetBudget q).trans
  unfold figureOneCorrectedTargetBudget figureOneCorrectedTransitionBudget
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have ha : 1 ≤ figureOneDependentAlpha q :=
    figureOneDependentAlpha_one_le q
  have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hden1 : 4096 ≤ 4096 * figureOneDependentAlpha q ^ 4 *
      (figureOneDependentPhaseCount q : ℝ) := by
    have ha4 : 1 ≤ figureOneDependentAlpha q ^ 4 := one_le_pow₀ ha
    nlinarith
  have hden2 : 1 ≤ 3 * (figureOneDependentMaxSampleCount q : ℝ) *
      (figureOneDependentPhaseCount q : ℝ) := by nlinarith
  have hden1pos : 0 < 4096 * figureOneDependentAlpha q ^ 4 *
      (figureOneDependentPhaseCount q : ℝ) := by nlinarith
  have hden2pos : 0 < 3 * (figureOneDependentMaxSampleCount q : ℝ) *
      (figureOneDependentPhaseCount q : ℝ) := by nlinarith
  have hfirst : q.eps ^ 2 /
      (4096 * figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ)) ≤ 1 / 4096 := by
    apply (div_le_iff₀ hden1pos).2
    nlinarith
  have hper : figureOnePerSampleMixingError q ≤ 1 / 4096 := by
    unfold figureOnePerSampleMixingError figureOneDependentEpsilon
    apply (div_le_iff₀ hden2pos).2
    nlinarith
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_div]
  simp only [ENNReal.toReal_ofReal (figureOnePerSampleMixingError_pos q).le,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by norm_num :
      (0 : ℝ) ≤ 1 / 64)]
  nlinarith

/-- The terminal accepted target has positive mean and a constant relative
second moment.  This is the single-coordinate terminal input used in the
dependent empirical-average argument. -/
theorem figureOneScheduledAcceptedTargetAt_terminal_positive_mean_and_second_le_four
    (q : VolumeParams) (I : VolumeInput q.n) :
    0 < ∫ x, uniformRatioWeight (terminalVariance q) x
        ∂figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q) ∧
      (∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
          ∂figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q)) ≤
        4 * (∫ x, uniformRatioWeight (terminalVariance q) x
          ∂figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q)) ^ 2 := by
  let mu := figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q)
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q)
  let f : AmbientSpace q.n → ℝ := uniformRatioWeight (terminalVariance q)
  let _ : IsProbabilityMeasure mu :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I
      (terminalPhaseSteps q)
  let _ : IsProbabilityMeasure nu := inferInstance
  have htv : Arlib.TVLe mu nu (scheduledBalancedStationaryTargetError q) := by
    simpa [mu, nu, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, scheduleValue_terminalPhaseSteps] using
      scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
        q I (terminalVariance_pos' q)
  have hmu :=
    figureOneScheduledAcceptedTargetAt_terminal_ae_uniformRatio_bounds q I
  have hnu :=
    truncatedGaussianProbability_terminal_ae_uniformRatio_bounds q I
  have hmeanOne : 1 ≤ ∫ x, f x ∂nu := by
    simpa [f, nu] using uniformRatioWeight_terminal_mean_one_le q I
  have hsecond : (∫ x, f x ^ 2 ∂nu) ≤ 2 * (∫ x, f x ∂nu) ^ 2 := by
    have hbase := uniformRatioWeight_terminal_secondMoment_le q I
    have hexp53 : Real.exp (1 / 2) ≤ (5 / 3 : ℝ) := by
      convert Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) using 1 <;> norm_num
    have hexp : Real.exp (1 / 2) ≤ (2 : ℝ) := hexp53.trans (by norm_num)
    have hm0 : 0 ≤ ∫ x, f x ∂nu := le_trans (by norm_num) hmeanOne
    have hmSq : (∫ x, f x ∂nu) ≤ (∫ x, f x ∂nu) ^ 2 := by
      nlinarith
    simpa [f, nu] using hbase.trans <|
      calc
        Real.exp (1 / 2) * (∫ x, f x ∂nu) ≤
            2 * (∫ x, f x ∂nu) :=
          mul_le_mul_of_nonneg_right hexp hm0
        _ ≤ 2 * (∫ x, f x ∂nu) ^ 2 := by nlinarith
  apply Arlib.TVLe.positive_mean_and_second_le_four_of_ae_expHalf htv
    (scheduledBalancedStationaryTargetError_le_one_div_sixtyFour q)
    (measurable_uniformRatioWeight (terminalVariance q))
  · exact hmu.mono fun _ hx => le_trans (by norm_num) hx.1
  · exact hmu.mono fun _ hx => hx.2
  · exact hnu.mono fun _ hx => le_trans (by norm_num) hx.1
  · exact hnu.mono fun _ hx => hx.2
  · rfl
  · exact hmeanOne
  · exact hsecond

#print axioms scheduledBalancedStationaryTargetError_le_one_div_sixtyFour
#print axioms
  figureOneScheduledAcceptedTargetAt_terminal_positive_mean_and_second_le_four

end ArlibCommunity.Algorithms.CV18
