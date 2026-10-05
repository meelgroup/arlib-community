/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorSecondMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSlackMoments

/-!
# Sharp scalar-law moment transfer to an executable trace coordinate

This specializes the sharp perturbation algebra to the exact `hsecond`
premise of the unconditional scheduled capstone.  It deliberately leaves
only the law-comparison and its explicit error arithmetic as inputs.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

theorem figureOneExecutableMomentSlack_le_one (q : VolumeParams) :
    figureOneExecutableMomentSlack q ≤ 1 := by
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  unfold figureOneExecutableMomentSlack
  apply (div_le_one (by positivity :
    (0 : ℝ) < 4096 * figureOneDependentPhaseCount q)).2
  calc
    q.eps ^ 2 ≤ 1 := he2
    _ ≤ 4096 * (figureOneDependentPhaseCount q : ℝ) := by nlinarith

/-- Reserving one eighth of the executable slack for the mean perturbation
and one eighth for the second-moment perturbation still fits the enlarged
phase factor. -/
theorem figureOneExecutableMomentFactor_perturbation_budget
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalMomentFactor q j +
        figureOneExecutableMomentSlack q / 8 ≤
      figureOneChronologicalMomentFactor q j *
        (1 + figureOneExecutableMomentSlack q) *
          (1 - figureOneExecutableMomentSlack q / 8) ^ 2 := by
  let f := figureOneChronologicalMomentFactor q j
  let s := figureOneExecutableMomentSlack q
  have hf : 1 ≤ f := figureOneChronologicalMomentFactor_one_le q j
  have hs0 : 0 ≤ s := figureOneExecutableMomentSlack_nonneg q
  have hs1 : s ≤ 1 := figureOneExecutableMomentSlack_le_one q
  have hs2 : s ^ 2 ≤ s := by nlinarith [sq_nonneg s]
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  have hgain : s / 8 ≤
      (1 + s) * (1 - s / 8) ^ 2 - 1 := by
    nlinarith
  have hscale : s / 8 ≤ f *
      ((1 + s) * (1 - s / 8) ^ 2 - 1) := by
    have hgain0 : 0 ≤
        (1 + s) * (1 - s / 8) ^ 2 - 1 :=
      (div_nonneg hs0 (by norm_num)).trans hgain
    calc
      s / 8 ≤ (1 + s) * (1 - s / 8) ^ 2 - 1 := hgain
      _ ≤ f * ((1 + s) * (1 - s / 8) ^ 2 - 1) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hf hgain0
  dsimp only [f, s] at hscale ⊢
  nlinarith

/-- Direct ideal-to-executable comparison form of the sharp phase-moment
transfer.  This is the interface needed by a paper-faithful within-phase
coupling argument: it may establish the executable second moment directly,
without first proving total variation closeness of the entire (unbounded)
phase-estimator law. -/
theorem scheduledFigureOneTrace_second_le_executableMomentFactor_of_ideal_bounds
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hmeanLower :
      (1 - figureOneExecutableMomentSlack q / 8) *
          figureOneIdealPhaseMean q I
            (figureOneChronologicalPhaseAt q j) ≤
        scheduledFigureOneTraceRawMean q I j)
    (hsecondUpper :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (figureOneChronologicalMomentFactor q j +
            figureOneExecutableMomentSlack q / 8) *
          figureOneIdealPhaseMean q I
            (figureOneChronologicalPhaseAt q j) ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneExecutableMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let slack := figureOneExecutableMomentSlack q
  let factor := figureOneChronologicalMomentFactor q j
  let idealMean := figureOneIdealPhaseMean q I
    (figureOneChronologicalPhaseAt q j)
  let actualMean := scheduledFigureOneTraceRawMean q I j
  have hslack0 : 0 ≤ slack := figureOneExecutableMomentSlack_nonneg q
  have hslack1 : slack ≤ 1 := figureOneExecutableMomentSlack_le_one q
  have hideal0 : 0 ≤ idealMean :=
    (figureOneIdealPhaseMean_pos q I
      (figureOneChronologicalPhaseAt q j)).le
  have hlower0 : 0 ≤ (1 - slack / 8) * idealMean := by
    exact mul_nonneg (by nlinarith) hideal0
  have hactual0 : 0 ≤ actualMean := hlower0.trans hmeanLower
  have hsquare : ((1 - slack / 8) * idealMean) ^ 2 ≤ actualMean ^ 2 :=
    (sq_le_sq₀ hlower0 hactual0).2 hmeanLower
  have hcoefficient0 : 0 ≤ factor * (1 + slack) :=
    mul_nonneg
      (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
      (by linarith)
  calc
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (factor + slack / 8) * idealMean ^ 2 := hsecondUpper
    _ ≤ (factor * (1 + slack) * (1 - slack / 8) ^ 2) *
          idealMean ^ 2 :=
      mul_le_mul_of_nonneg_right
        (figureOneExecutableMomentFactor_perturbation_budget q j)
        (sq_nonneg idealMean)
    _ = factor * (1 + slack) *
          ((1 - slack / 8) * idealMean) ^ 2 := by ring
    _ ≤ factor * (1 + slack) * actualMean ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hcoefficient0
    _ = figureOneExecutableMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2 := by
      rfl

/-- A sufficiently small scalar-law perturbation of the ideal chronological
phase preserves its paper factor, enlarged only by the executable moment
slack. -/
theorem scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    {epsilon : ENNReal} (hepsilonTop : epsilon ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    (hscalar : Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q j))
      ((figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j)).map
        (figureOneIdealPhaseEstimator q
          (figureOneChronologicalPhaseAt q j))) epsilon)
    (hWB : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      scheduledBalancedTracePhaseVariable q j trace ≤ B)
    (hidealB : ∀ᵐ samples
        ∂figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j),
      figureOneIdealPhaseEstimator q (figureOneChronologicalPhaseAt q j)
        samples ≤ B)
    {eta zeta : ℝ} (heta1 : eta < 1)
    (hmeanError : B * epsilon.toReal ≤
      eta * figureOneIdealPhaseMean q I
        (figureOneChronologicalPhaseAt q j))
    (hsecondError : B ^ 2 * epsilon.toReal ≤
      zeta * figureOneIdealPhaseMean q I
        (figureOneChronologicalPhaseAt q j) ^ 2)
    (hfactorBudget :
      figureOneChronologicalMomentFactor q j + zeta ≤
        figureOneChronologicalMomentFactor q j *
          (1 + figureOneExecutableMomentSlack q) * (1 - eta) ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneExecutableMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let phase := figureOneChronologicalPhaseAt q j
  let idealLaw := figureOneIdealPhaseLaw q I phase
  let W := scheduledBalancedTracePhaseVariable q j
  let estimator := figureOneIdealPhaseEstimator q phase
  let actualScalar := mu.map W
  let idealScalar := idealLaw.map estimator
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure idealLaw :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure actualScalar :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
  let _ : IsProbabilityMeasure idealScalar :=
    Measure.isProbabilityMeasure_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
  have hactual0 : ∀ᵐ y ∂actualScalar, 0 ≤ y :=
    (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (scheduledBalancedTracePhaseVariable_nonnegative q j)
  have hactualB : ∀ᵐ y ∂actualScalar, y ≤ B :=
    (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Iic).2 hWB
  have hideal0 : ∀ᵐ y ∂idealScalar, 0 ≤ y :=
    (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (figureOneIdealPhaseEstimator_nonneg q phase)
  have hidealScalarB : ∀ᵐ y ∂idealScalar, y ≤ B :=
    (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Iic).2 hidealB
  have hidealMoments := figureOneIdealPhase_moments q I
    (figureOneSharpAcceleratedMoments q I) phase
  have hidealMean : figureOneIdealPhaseMean q I phase =
      ∫ y, id y ∂idealScalar := by
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurable_id.aestronglyMeasurable]
    simpa only [id_eq] using hidealMoments.1.symm
  have hidealSecond : (∫ y, id y ^ 2 ∂idealScalar) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneIdealPhaseMean q I phase ^ 2 := by
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simpa [phase, figureOneChronologicalMomentFactor] using hidealMoments.2
  have htransport := Arlib.TVLe.second_le_factor_mul_mean_sq_of_ae
    (show Arlib.TVLe actualScalar idealScalar epsilon from hscalar)
    hepsilonTop measurable_id hB hactual0 hactualB hideal0 hidealScalarB
    hidealMean (figureOneIdealPhaseMean_pos q I phase) hidealSecond
    (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
    (figureOneExecutableMomentSlack_nonneg q) heta1 hmeanError hsecondError
    hfactorBudget
  have hmeanMap : (∫ y, id y ∂actualScalar) =
      scheduledFigureOneTraceRawMean q I j := by
    rw [integral_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurable_id.aestronglyMeasurable]
    rfl
  have hsecondMap : (∫ y, id y ^ 2 ∂actualScalar) =
      ∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2 ∂mu := by
    rw [integral_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    rfl
  change (∫ y, id y ^ 2 ∂actualScalar) ≤
    figureOneChronologicalMomentFactor q j *
      (1 + figureOneExecutableMomentSlack q) *
        (∫ y, id y ∂actualScalar) ^ 2 at htransport
  rw [hmeanMap, hsecondMap] at htransport
  simpa only [mu, figureOneExecutableMomentFactor] using htransport

/-- Concrete one-eighth-slack form of the sharp trace moment transfer. -/
theorem scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv_eighth
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    {epsilon : ENNReal} (hepsilonTop : epsilon ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    (hscalar : Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q j))
      ((figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j)).map
        (figureOneIdealPhaseEstimator q
          (figureOneChronologicalPhaseAt q j))) epsilon)
    (hWB : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      scheduledBalancedTracePhaseVariable q j trace ≤ B)
    (hidealB : ∀ᵐ samples
        ∂figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j),
      figureOneIdealPhaseEstimator q (figureOneChronologicalPhaseAt q j)
        samples ≤ B)
    (hmeanError : B * epsilon.toReal ≤
      figureOneExecutableMomentSlack q / 8 *
        figureOneIdealPhaseMean q I
          (figureOneChronologicalPhaseAt q j))
    (hsecondError : B ^ 2 * epsilon.toReal ≤
      figureOneExecutableMomentSlack q / 8 *
        figureOneIdealPhaseMean q I
          (figureOneChronologicalPhaseAt q j) ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneExecutableMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  apply scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv
    q I j hepsilonTop hB hscalar hWB hidealB
    (eta := figureOneExecutableMomentSlack q / 8)
    (zeta := figureOneExecutableMomentSlack q / 8)
  · have hs := figureOneExecutableMomentSlack_le_one q
    nlinarith
  · exact hmeanError
  · exact hsecondError
  · exact figureOneExecutableMomentFactor_perturbation_budget q j

#print axioms
  scheduledFigureOneTrace_second_le_executableMomentFactor_of_ideal_bounds
#print axioms
  scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv
#print axioms
  scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv_eighth

end ArlibCommunity.Algorithms.CV18
