/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalKernelInstantiation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPhaseMomentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-!
# Moment transfer for one scheduled trace coordinate

This is the finite-phase moment adapter needed by the executable trace
capstone.  It deliberately records the quantitative support bound: TV alone
does not transfer an unbounded Gaussian importance-weight second moment.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal

/-- Every exact ideal Figure-One phase ratio has mean at least one. -/
theorem figureOneIdealPhaseMean_one_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase : FigureOneIdealPhase q) :
    1 ≤ figureOneIdealPhaseMean q I phase := by
  cases phase with
  | fixed k =>
      simp only [figureOneIdealPhaseMean]
      have hden : 0 < gaussianIntegral (truncatedBody q I)
          (scheduleValue q k) :=
        gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q k)
      apply (le_div_iff₀ hden).2
      simpa using gaussianIntegral_mono_variance (truncatedBody q I)
        (truncatedBody_measurable q I) (scheduleValue_pos q k)
        (scheduleValue_mono q (Nat.le_add_right k 1))
  | accelerated k =>
      simp only [figureOneIdealPhaseMean]
      have hden : 0 < gaussianIntegral (truncatedBody q I)
          (scheduleValue q k) :=
        gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q k)
      apply (le_div_iff₀ hden).2
      simpa using gaussianIntegral_mono_variance (truncatedBody q I)
        (truncatedBody_measurable q I) (scheduleValue_pos q k)
        (scheduleValue_mono q (Nat.le_add_right k 1))
  | terminal =>
      simp only [figureOneIdealPhaseMean]
      have hden : 0 < gaussianIntegral (truncatedBody q I)
          (terminalVariance q) :=
        gaussianIntegral_pos q (truncatedVolumeInput q I)
          (terminalVariance_pos' q)
      apply (le_div_iff₀ hden).2
      simpa using gaussianIntegral_le_euclideanVolume q
        (truncatedVolumeInput q I) (terminalVariance_pos' q)

/-- A scalar-law TV comparison with an explicit common support bound supplies
exactly the three raw-moment premises of
`scheduledFigureOneTrace_moment_package`.

The bound is almost-everywhere under the two source laws.  This is the useful
form for the executable trace and the ideal empirical phase: neither
observable must be globally bounded on its ambient type. -/
theorem scheduledPhase_raw_moments_of_mapped_tv
    {S : Type*} [MeasurableSpace S]
    (q : VolumeParams) (I : VolumeInput q.n)
    (phase : FigureOneIdealPhase q)
    (mu : Measure S) [IsProbabilityMeasure mu]
    (W : S → ℝ) (hW : Measurable W)
    {epsilon : ENNReal} (hepsilonTop : epsilon ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    (hscalar : Arlib.TVLe
      (mu.map W)
      ((figureOneIdealPhaseLaw q I phase).map
        (figureOneIdealPhaseEstimator q phase)) epsilon)
    (hW0 : ∀ᵐ x ∂mu, 0 ≤ W x)
    (hWB : ∀ᵐ x ∂mu, W x ≤ B)
    (hidealB : ∀ᵐ samples ∂figureOneIdealPhaseLaw q I phase,
      figureOneIdealPhaseEstimator q phase samples ≤ B)
    (hmeanError : B * epsilon.toReal ≤
      figureOneIdealPhaseMean q I phase / 8)
    (hsecondError : B ^ 2 * epsilon.toReal ≤
      figureOneIdealPhaseMean q I phase ^ 2 / 8) :
    MemLp W 2 mu ∧
      0 < ∫ x, W x ∂mu ∧
      (∫ x, W x ^ 2 ∂mu) ≤ 4 * (∫ x, W x ∂mu) ^ 2 := by
  let idealLaw := figureOneIdealPhaseLaw q I phase
  let estimator := figureOneIdealPhaseEstimator q phase
  let actualScalar := mu.map W
  let idealScalar := idealLaw.map estimator
  let _ : IsProbabilityMeasure idealLaw := by
    dsimp only [idealLaw]
    exact figureOneIdealPhaseLaw_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure actualScalar := by
    dsimp only [actualScalar]
    exact Measure.isProbabilityMeasure_map hW.aemeasurable
  let _ : IsProbabilityMeasure idealScalar := by
    dsimp only [idealScalar, idealLaw, estimator]
    exact Measure.isProbabilityMeasure_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
  have hWmem : MemLp W 2 mu :=
    memLp_two_of_ae_nonnegative_le hW hB.le hW0 hWB
  have hscalar0Actual : ∀ᵐ y ∂actualScalar, 0 ≤ y := by
    dsimp only [actualScalar]
    exact (ae_map_iff hW.aemeasurable measurableSet_Ici).2 hW0
  have hscalarBActual : ∀ᵐ y ∂actualScalar, y ≤ B := by
    dsimp only [actualScalar]
    exact (ae_map_iff hW.aemeasurable measurableSet_Iic).2 hWB
  have hideal0 : ∀ᵐ samples ∂idealLaw, 0 ≤ estimator samples := by
    filter_upwards with samples
    exact figureOneIdealPhaseEstimator_nonneg q phase samples
  have hscalar0Ideal : ∀ᵐ y ∂idealScalar, 0 ≤ y := by
    dsimp only [idealScalar]
    exact (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Ici).2 hideal0
  have hscalarBIdeal : ∀ᵐ y ∂idealScalar, y ≤ B := by
    dsimp only [idealScalar, idealLaw, estimator]
    exact (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Iic).2 hidealB
  have hidealMoments := figureOneIdealPhase_moments q I
    (figureOneSharpAcceleratedMoments q I) phase
  have hidealMean : figureOneIdealPhaseMean q I phase =
      ∫ y, y ∂idealScalar := by
    dsimp only [idealScalar, idealLaw, estimator]
    change figureOneIdealPhaseMean q I phase =
      ∫ y, id y ∂(figureOneIdealPhaseLaw q I phase).map
        (figureOneIdealPhaseEstimator q phase)
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurable_id.aestronglyMeasurable]
    exact hidealMoments.1.symm
  have hidealSecond : (∫ y, y ^ 2 ∂idealScalar) ≤
      2 * figureOneIdealPhaseMean q I phase ^ 2 := by
    dsimp only [idealScalar, idealLaw, estimator]
    change (∫ y, id y ^ 2
      ∂(figureOneIdealPhaseLaw q I phase).map
        (figureOneIdealPhaseEstimator q phase)) ≤ _
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    exact hidealMoments.2.trans <|
      mul_le_mul_of_nonneg_right
        (figureOneIdealPhaseFactor_le_two q phase)
        (sq_nonneg (figureOneIdealPhaseMean q I phase))
  have hresult := Arlib.TVLe.positive_mean_and_second_le_four_of_ae
    (show Arlib.TVLe actualScalar idealScalar epsilon from hscalar)
    hepsilonTop measurable_id hB hscalar0Actual hscalarBActual
    hscalar0Ideal hscalarBIdeal hidealMean
    (figureOneIdealPhaseMean_pos q I phase) hidealSecond
    hmeanError hsecondError
  have hmeanMap : (∫ y, y ∂actualScalar) = ∫ x, W x ∂mu := by
    dsimp only [actualScalar]
    change (∫ y, id y ∂mu.map W) = _
    rw [integral_map hW.aemeasurable measurable_id.aestronglyMeasurable]
    rfl
  have hsecondMap : (∫ y, y ^ 2 ∂actualScalar) =
      ∫ x, W x ^ 2 ∂mu := by
    dsimp only [actualScalar]
    change (∫ y, id y ^ 2 ∂mu.map W) = _
    rw [integral_map hW.aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    rfl
  simp only [id_eq] at hresult
  rw [hmeanMap, hsecondMap] at hresult
  exact ⟨hWmem, hresult⟩

/-- Direct specialization to the finite executable forward trace.  This is
the precise adapter to the three raw-moment arguments of the trace capstone;
all that remains visible is a scalar-law comparison and its quantitative
support/error estimates. -/
theorem scheduledFigureOneTrace_raw_moments_of_mapped_tv
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
      figureOneIdealPhaseMean q I (figureOneChronologicalPhaseAt q j) / 8)
    (hsecondError : B ^ 2 * epsilon.toReal ≤
      figureOneIdealPhaseMean q I (figureOneChronologicalPhaseAt q j) ^ 2 / 8) :
    MemLp (scheduledBalancedTracePhaseVariable q j) 2
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ∧
      0 < scheduledFigureOneTraceRawMean q I j ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        4 * scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have hresult := scheduledPhase_raw_moments_of_mapped_tv q I
    (figureOneChronologicalPhaseAt q j) mu
    (scheduledBalancedTracePhaseVariable q j)
    (measurable_scheduledBalancedTracePhaseVariable q j)
    hepsilonTop hB hscalar
    (Filter.Eventually.of_forall
      (scheduledBalancedTracePhaseVariable_nonnegative q j))
    hWB hidealB hmeanError hsecondError
  simpa [mu, scheduledFigureOneTraceRawMean] using hresult

#print axioms figureOneIdealPhaseMean_one_le
#print axioms scheduledPhase_raw_moments_of_mapped_tv
#print axioms scheduledFigureOneTrace_raw_moments_of_mapped_tv

end ArlibCommunity.Algorithms.CV18
