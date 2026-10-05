/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMomentBounds

/-!
# Support and terminal bounds for the scheduled accepted target

The accepted target is produced by restricting to a homothetic scheduled
phase body and scaling back.  Consequently it is supported on the scheduled
phase body itself.  At the terminal phase this makes the Gaussian-to-uniform
weight genuinely bounded by `exp (1/2)`, as used in CV18.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- The normalized accepted target is almost surely in its scheduled phase
body.  This is proved from the rejection indicator, not inferred from its
positive-error TV comparison with the truncated Gaussian. -/
theorem figureOneScheduledAcceptedTargetAt_ae_mem_phaseBody
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    ∀ᵐ x ∂figureOneScheduledAcceptedTargetAt q I phase,
      x ∈ figureOneScheduledPhaseBody q I (scheduleValue q phase) := by
  let sigma2 := scheduleValue q phase
  let K := figureOneScheduledPhaseBody q I sigma2
  let pi := figureOneScheduledSpeedyPiAt q I phase
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let _ : IsProbabilityMeasure pi :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I phase
  have hscale : Measurable scale := by
    dsimp only [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hK : MeasurableSet K :=
    figureOneScheduledPhaseBody_measurable q I sigma2
  have hacceptMeas : Measurable
      (scheduledBalancedAccuracyGaussianAcceptance q I sigma2) :=
    measurable_scheduledBalancedAccuracyGaussianAcceptance q I sigma2
  have hacceptedSupport : ∀ᵐ x ∂accepted, scale x ∈ K := by
    dsimp only [accepted, scheduledBalancedAcceptedStateMeasure]
    apply (ae_withDensity_iff hacceptMeas).2
    filter_upwards with x
    intro hx
    by_contra hnot
    have hz : scheduledBalancedAccuracyGaussianAcceptance q I sigma2 x = 0 := by
      simp [scheduledBalancedAccuracyGaussianAcceptance,
        scheduledAccuracyGaussianRejectionAcceptance, scale, K, hnot]
    exact hx hz
  have hmappedSupport : ∀ᵐ x ∂accepted.map scale, x ∈ K :=
    (ae_map_iff hscale.aemeasurable hK).2 hacceptedSupport
  have hlower : ENNReal.ofReal (7 / 128 : ℝ) ≤ accepted Set.univ := by
    simpa [accepted, pi, figureOneScheduledSpeedyPiAt, sigma2] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I
        (scheduleValue_pos q phase)
  have hmass0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 128 : ℝ)).trans_le hlower
  have heq : accepted.map scale = accepted Set.univ •
      figureOneScheduledAcceptedTargetAt q I phase := by
    simpa [accepted, scale, pi, sigma2,
      figureOneScheduledAcceptedTargetAt, figureOneScheduledSpeedyPiAt] using
      scheduledBalancedAcceptedTargetSubmeasure_eq_mass_smul
        q I (scheduleValue_pos q phase) pi hlower
  rw [heq] at hmappedSupport
  exact (Measure.ae_ennreal_smul_measure_iff hmass0).1 hmappedSupport

/-- On the terminal scheduled body, the executable uniform importance
weight lies in the paper's interval `[1, exp (1/2)]`. -/
theorem uniformRatioWeight_terminal_bounds_of_mem_scheduledPhaseBody
    (q : VolumeParams) (I : VolumeInput q.n) {x : AmbientSpace q.n}
    (hx : x ∈ figureOneScheduledPhaseBody q I (terminalVariance q)) :
    1 ≤ uniformRatioWeight (terminalVariance q) x ∧
      uniformRatioWeight (terminalVariance q) x ≤ Real.exp (1 / 2) := by
  have hbody : x ∈ truncatedBody q I := hx.1
  rw [uniformRatioWeight_eq_sample q I (terminalVariance q) hbody]
  exact uniformRatio_terminal_bounds q I hbody

/-- Terminal uniform weights are almost surely in `[1, exp (1/2)]` under
the executable schedule's accepted target. -/
theorem figureOneScheduledAcceptedTargetAt_terminal_ae_uniformRatio_bounds
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ x ∂figureOneScheduledAcceptedTargetAt q I (terminalPhaseSteps q),
      1 ≤ uniformRatioWeight (terminalVariance q) x ∧
        uniformRatioWeight (terminalVariance q) x ≤ Real.exp (1 / 2) := by
  filter_upwards [
    figureOneScheduledAcceptedTargetAt_ae_mem_phaseBody
      q I (terminalPhaseSteps q)] with x hx
  rw [scheduleValue_terminalPhaseSteps] at hx
  exact uniformRatioWeight_terminal_bounds_of_mem_scheduledPhaseBody q I hx

/-- The same terminal bound under the exact truncated Gaussian target. -/
theorem truncatedGaussianProbability_terminal_ae_uniformRatio_bounds
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ x ∂(truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)),
      1 ≤ uniformRatioWeight (terminalVariance q) x ∧
        uniformRatioWeight (terminalVariance q) x ≤ Real.exp (1 / 2) := by
  filter_upwards [truncatedGaussianProbability_ae_mem q I
    (terminalVariance_pos' q)] with x hx
  rw [uniformRatioWeight_eq_sample q I (terminalVariance q) hx]
  exact uniformRatio_terminal_bounds q I hx

#print axioms figureOneScheduledAcceptedTargetAt_ae_mem_phaseBody
#print axioms
  figureOneScheduledAcceptedTargetAt_terminal_ae_uniformRatio_bounds
#print axioms truncatedGaussianProbability_terminal_ae_uniformRatio_bounds

end ArlibCommunity.Algorithms.CV18
