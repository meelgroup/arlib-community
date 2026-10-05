/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianChronologicalReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceConstruction
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalOuterStepErrorSum

/-!
# Gaussian step of the global chronological reset invariant

This file turns the concrete Gaussian reset into the induction step consumed
by the finite global reference construction.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- A Gaussian phase advances the accepted-endpoint chronological invariant
by one coordinate and charges exactly its named outer-step error. -/
theorem exists_scheduledGlobalGaussianPrefixInvariant_succ
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (hsource : ScheduledGlobalGaussianPrefixInvariant q I phase source) :
    ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (source.bind (scheduledBalancedTracePhaseKernel
          figureOneFinalScheduledBalancedParameters q I phase))
        reference (figureOneScheduledGaussianOuterStepError q phase) ∧
      ScheduledGlobalGaussianPrefixInvariant q I (phase + 1) reference := by
  let W := figureOneScheduledReferenceCoordinateExtension q I
  let mean := figureOneChronologicalTruncatedMean q I source W
  let oldStatistic := dependentTruncatedProduct
    (figureOneDependentAlpha q) mean
      (figureOneChronologicalTruncatedPhase q I W) phase
  let accepted := figureOneScheduledAcceptedTargetAt q I (phase - 1)
  let _ : IsProbabilityMeasure accepted :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  have hphaseDependent : phase < figureOneDependentPhaseCount q := by
    rw [figureOneDependentPhaseCount]
    omega
  have holdMeas : Measurable oldStatistic := by
    dsimp only [oldStatistic]
    exact measurable_dependentTruncatedProduct
      (figureOneDependentAlpha q) mean
      (figureOneChronologicalTruncatedPhase q I W)
      (fun j => figureOneChronologicalTruncatedPhase_measurable q I W
        (fun k => measurable_figureOneScheduledReferenceCoordinateExtension
          q I k) j) phase
  have holdAppend : ∀ trace result,
      ScheduledBalancedCoolingTraceValid phase trace → trace.2 = true →
      ScheduledResetPairGood result →
      oldStatistic (scheduledResetTraceAppend (trace, result)) =
        oldStatistic trace := by
    intro trace result hvalid _ _
    have hfactor :=
      dependentTruncatedProduct_chronological_extension_factor_prefix
        q I phase phase hphaseDependent.le le_rfl mean
    have hfactor' :
        dependentTruncatedProduct (figureOneDependentAlpha q) mean
            (figureOneChronologicalTruncatedPhase q I W) phase =
          scheduledResetPrefixChronologicalTruncatedProduct
              q I phase mean phase ∘
            scheduledResetPrefixCoordinates q phase := by
      simpa only [W] using hfactor
    dsimp only [oldStatistic]
    rw [hfactor']
    simp only [Function.comp_apply]
    rw [scheduledResetPrefixCoordinates_resetAppend_eq q phase
      hphaseDependent trace hvalid result]
  have hwarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase) := by
    cases phase with
    | zero =>
        have h := map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
          q I (scheduleValue_pos q 0)
        apply h.mono
        rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
        exact ENNReal.ofReal_le_ofReal <| by
          nlinarith [speedyAdjacentWarmConstant_one_le q]
    | succ previous =>
        simpa [accepted, figureOneScheduledAcceptedTargetAt,
          figureOneScheduledSpeedyPiAt] using
          map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
            q I previous
  obtain ⟨reference, hreferenceProb, hcomparison, hretained, hprefix,
      hnewMem, hnewMean, hnewSecond, hnewRawInd, hsupport⟩ :=
    exists_scheduledGaussianTraceRecordedReset
      q I phase hphase source
      hsource.toScheduledGlobalResetPrefixInvariant.valid
      hsource.toScheduledGlobalResetPrefixInvariant.coordinates_nonnegative
      accepted (by simpa only [accepted] using hsource.retained) hwarm
      oldStatistic holdMeas holdAppend
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hcreated :=
    ApproxIndepFun.chronological_extension_created_of_resetPrefix_map_eq
      q I phase hphaseDependent source reference hprefix
      (by simpa only [oldStatistic, mean, W] using hnewRawInd)
  have hcount :
      figureOnePhaseSampleCount q (scheduleValue q phase) ≤
        figureOneDependentMaxSampleCount q :=
    figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hnewInd : ApproxIndepFun
      ((5 / 2 : ℝ) * figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference W)
        (figureOneChronologicalTruncatedPhase q I W) phase)
      (figureOneChronologicalTruncatedPhase q I W (phase + 1))
      reference :=
    hcreated.mono (by
      simpa only [two_mul] using
        figureOne_localTransitionResetStationary_dependence_le q hcount)
  have hinvariant : ScheduledGlobalResetPrefixInvariant q I (phase + 1)
      reference :=
    hsource.toScheduledGlobalResetPrefixInvariant.extend q I phase
      hphaseDependent source reference hprefix hnewMem hnewMean hnewSecond
      (by simpa only [W] using hnewInd) hsupport
  refine ⟨reference, hreferenceProb, ?_, ?_⟩
  · simpa only [figureOneScheduledGaussianOuterStepError, add_assoc] using
      hcomparison
  · exact
      { toScheduledGlobalResetPrefixInvariant := hinvariant
        retained := by simpa using hretained }

#print axioms exists_scheduledGlobalGaussianPrefixInvariant_succ

end

end ArlibCommunity.Algorithms.CV18
