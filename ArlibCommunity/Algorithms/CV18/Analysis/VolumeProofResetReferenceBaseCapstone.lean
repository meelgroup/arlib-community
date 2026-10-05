/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceFailureBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceProduct
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-!
# Executable base wrapper for a global reset reference

This module identifies the post-initial scheduled executable with the mapped
product of its loss-preserving chronological trace.  It then packages the
existing reset-reference Lemma 7.15 consumer and the aborting initial draw.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Exact executable post-initial law in the scalar-product form used by the
global reset-reference comparison. -/
theorem figureOneFinalScheduled_postInitialLaw_eq_traceProduct
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) :
    (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (fun point =>
          (scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).runEstimate
              oracle.query) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
        (fun trace => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (scheduledBalancedTracePhaseVariable q)
            (figureOneDependentPhaseCount q) trace) := by
  let parameters := figureOneFinalScheduledBalancedParameters
  let traceLaw := scheduledBalancedForwardTraceLaw parameters q I
    (figureOneDependentPhaseCount q)
  have hhistory :=
    bind_scheduledBalancedFigureOnePointContinuation_eq_forwardHistory_map_of_pointwise
      parameters q I oracle
        (scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map
          parameters q I oracle)
  have htraceProjection := map_scheduledBalancedForwardTraceLaw_project
    parameters q I (figureOneDependentPhaseCount q)
  rw [hhistory, ← htraceProjection]
  rw [Measure.map_map (measurable_balancedFigureOneHistoryEstimate q)
    measurable_scheduledBalancedCoolingTraceProject]
  apply Measure.map_congr
  filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
    parameters q I (figureOneDependentPhaseCount q),
    scheduledBalancedForwardTraceLaw_ae_coordinatesNonnegative
      parameters q I (figureOneDependentPhaseCount q)]
    with trace hvalid hnonnegative
  change balancedFigureOneHistoryEstimate q
    (scheduledBalancedCoolingTraceProject trace) = _
  rw [balancedFigureOneHistoryEstimate_traceProject_eq q trace hvalid]
  congr 1
  rw [← dependentPhaseSampleProduct_scheduledBalancedTrace_eq q trace hvalid]
  unfold dependentPhaseSampleProduct
  apply Finset.prod_congr rfl
  intro j hj
  simp only [scheduledBalancedTracePhaseVariable]
  rw [max_eq_right]
  unfold ScheduledBalancedCoolingTraceCoordinatesNonnegative at hnonnegative
  have hjraw := hnonnegative.2 j (Finset.mem_range.mp hj)
  simpa [scheduledBalancedTraceChronologicalPhaseVariable,
    balancedCoolingChronologicalPhaseVariable_apply_succ q j
      (Finset.mem_range.mp hj)] using hjraw

/-- Final uncapped executable theorem from one global chronological reset
reference.  All program-law and initial-abort bookkeeping is discharged;
the caller supplies the reference coordinate facts and its single mapped-law
comparison to the scheduled trace. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_globalResetReference
    {Reference : Type*} [MeasurableSpace Reference]
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (reference : Measure Reference) [IsProbabilityMeasure reference]
    (W : ℕ → Reference → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j state, 0 ≤ W j state)
    (hWmem : ∀ j, MemLp (W j) 2 reference)
    (hWmean : ∀ j, (∫ state, W j state ∂reference) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ state, W j state ^ 2 ∂reference) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun epsilon
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I reference W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) reference)
    {error boundary : ENNReal}
    (htransfer : MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
        (fun trace => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (scheduledBalancedTracePhaseVariable q)
            (figureOneDependentPhaseCount q) trace))
      (reference.map (fun state => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) state)) error)
    (herror : error ≤
      figureOneScheduledGlobalResetReferenceError q + boundary)
    (hboundary : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ)) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let actualLaw := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let actualProduct := dependentPhaseSampleProduct
    (scheduledBalancedTracePhaseVariable q)
      (figureOneDependentPhaseCount q)
  let continuation : AmbientSpace q.n → Measure ℝ := fun point =>
    (scheduledBalancedFigureOnePointContinuation
      figureOneFinalScheduledBalancedParameters q point).runEstimate
        oracle.query
  have hactualMeas : Measurable actualProduct := by
    unfold actualProduct dependentPhaseSampleProduct
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j _ => measurable_scheduledBalancedTracePhaseVariable q (j + 1)
  have htransfer64 : MeasureLeUpTo
      (actualLaw.map
        (fun trace => initialGaussianIntegral q * actualProduct trace))
      (reference.map (fun state => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) state))
      (ENNReal.ofReal (1 / 64 : ℝ)) := by
    apply htransfer.mono_resetReference_finalTransfer q herror hboundary
  have hpost : FigureOnePostInitialDirectFailureBoundFor q I continuation := by
    apply figureOnePostInitialDirectFailureBoundFor_of_resetReferenceMappedProductLe
      q I continuation (figureOneRadialTruncationBound q I hrounded)
        actualLaw reference actualProduct W hactualMeas hWmeas hW0 hWmem
          hWmean hWsecond hepsilon0 hepsilon hind htransfer64
    simpa [continuation, actualLaw, actualProduct] using
      figureOneFinalScheduled_postInitialLaw_eq_traceProduct q I oracle
  exact figureOneFinalScheduledAbortBase_failure_le_of_directPostInitial
    q I oracle hpost

#print axioms figureOneFinalScheduled_postInitialLaw_eq_traceProduct
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_globalResetReference

end


end ArlibCommunity.Algorithms.CV18
