/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetrySemantics

/-! # Executable cooling primitives at schedule-targeted geometry

This module is the executable transport missing from the analytic scheduled
radius development.  In particular, changing `BalancedCoolingParameters`
alone does not change the body or proposal radius used by the sampler.  The
definitions below call `scheduledBalancedAccuracyRetryCollect` directly.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

theorem scheduledBalancedAccuracyRetryCollectLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ) :
    Measurable (scheduledBalancedAccuracyRetryCollectLaw q I sigma2 weight
      proposalCap properStride retryLimit samples) ∧
    ∀ current, IsProbabilityMeasure
      (scheduledBalancedAccuracyRetryCollectLaw q I sigma2 weight
        proposalCap properStride retryLimit samples current) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  let R := scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
  have hraw := balancedRetryCollectLawAux_measurable_and_probability
    B R hweight retryLimit retryLimit samples
  have hout := measurable_balancedAccuracyRetryOutput q
  constructor
  · unfold scheduledBalancedAccuracyRetryCollectLaw
    exact (Measure.measurable_map _ hout).comp <|
      hraw.1.comp (measurable_const.prodMk measurable_id)
  · intro current
    unfold scheduledBalancedAccuracyRetryCollectLaw
    letI : IsProbabilityMeasure
        (balancedRetryCollectLawAux B R weight retryLimit retryLimit samples
          0 current) := hraw.2 0 current
    exact Measure.isProbabilityMeasure_map hout.aemeasurable

/-- One averaged Gaussian cooling phase driven by the scheduled-body sampler. -/
noncomputable def scheduledBalancedCoolingRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2) result)

/-- The scheduled terminal Gaussian-to-uniform phase, retaining its endpoint. -/
noncomputable def scheduledBalancedCoolingUniformEstimateWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOneSampleCount q) result)

/-- Forget the retained endpoint after the scheduled terminal phase. -/
noncomputable def scheduledBalancedCoolingUniformRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).bind
    fun result => .pure (balancedCoolingForgetState result)

/-- Actual scheduled-body implementation of the Figure-One cooling interface. -/
noncomputable def scheduledBalancedCoolingPrimitives
    (parameters : BalancedCoolingParameters) : VolumeCoolingPrimitives where
  initialSample := figureOneInitialSample
  ratioEstimate := scheduledBalancedCoolingRatioEstimate parameters
  uniformRatioEstimate := scheduledBalancedCoolingUniformRatioEstimate parameters

/-- Exact target-coordinate law of one scheduled averaged Gaussian phase. -/
noncomputable def scheduledBalancedCoolingRatioLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollectLaw q I sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2))

theorem scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ) :
    Measurable (fun current =>
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
        oracle.query) ∧
    (∀ current,
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).StronglyMeasurable
        oracle.query) ∧
    ∀ current,
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
          oracle.query =
        scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOnePhaseSampleCount q sigma2
  let weight : AmbientSpace q.n → ℝ := gaussianRatioWeight sigma2 tau2
  let scalePoint : AmbientSpace q.n → AmbientSpace q.n :=
    fun current => accuracyScaleFactor q • current
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight sigma2 tau2
  have htransition :=
    scheduledBalancedAccuracyRetryCollectLaw_measurable_and_probability
      q I hsigma2 hweight cap stride retries samples
  have hscale : Measurable scalePoint :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      scheduledBalancedAccuracyRetryCollectLaw q I sigma2 weight cap stride
        retries samples (scalePoint current) := htransition.1.comp hscale
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  have hlaw : Measurable fun current =>
      scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
    unfold scheduledBalancedCoolingRatioLaw
    exact (Measure.measurable_map _ havg).comp hsource
  have hcollectorStrong : ∀ current,
      (scheduledBalancedAccuracyRetryCollect q sigma2 weight cap stride retries
        samples (scalePoint current)).StronglyMeasurable oracle.query := by
    intro current
    have haux := scheduledBalancedAccuracyRetryCollectAux_semantics
      q I oracle hsigma2 hweight cap stride retries retries samples
    let output : Option (ℝ × AmbientSpace q.n) →
        MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
      fun result => .pure (balancedAccuracyRetryOutput q result)
    have houtputRun : Measurable fun result =>
        (output result).runEstimate oracle.query := by
      simp only [output, MembershipOracleProgram.runEstimate]
      exact Measure.measurable_dirac.comp
        (measurable_balancedAccuracyRetryOutput q)
    unfold scheduledBalancedAccuracyRetryCollect
    exact (haux.1 0 (scalePoint current)).bind (fun _ => by trivial) houtputRun
  have havgRun : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (.pure (balancedCoolingAverage samples result) :
        MembershipOracleProgram q.n
          (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp havg
  have hstrong : ∀ current,
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).StronglyMeasurable
        oracle.query := by
    intro current
    unfold scheduledBalancedCoolingRatioEstimate
    change (scheduledBalancedAccuracyRetryCollect q sigma2 weight cap stride
      retries samples (scalePoint current)).bind _ |>.StronglyMeasurable
        oracle.query
    exact (hcollectorStrong current).bind (fun _ => by trivial) havgRun
  have hrun : ∀ current,
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
          oracle.query =
        scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
    intro current
    unfold scheduledBalancedCoolingRatioEstimate scheduledBalancedCoolingRatioLaw
    change ((scheduledBalancedAccuracyRetryCollect q sigma2 weight cap stride
      retries samples (scalePoint current)).bind fun result =>
        .pure (balancedCoolingAverage samples result)).runEstimate oracle.query = _
    rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
      (hcollectorStrong current) (fun _ => by trivial) havgRun]
    rw [scheduledBalancedAccuracyRetryCollect_semantics
      q I oracle hsigma2 hweight]
    exact Measure.bind_dirac_eq_map _ havg
  refine ⟨?_, hstrong, hrun⟩
  simpa only [hrun] using hlaw

/-- The finite scheduled-body Figure-One base program. -/
noncomputable def figureOneScheduledBalancedBaseProgram (q : VolumeParams) :
    MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling
    (scheduledBalancedCoolingPrimitives figureOneScheduledBalancedParameters)
    explicitVolumeCoolingSchedule q

/-- Install the same single whole-run cutoff used by the global analysis. -/
noncomputable def figureOneScheduledGloballyCappedBalancedBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n (Option ℝ) :=
  (figureOneScheduledBalancedBaseProgram q).withQueryCap
    (figureOneGlobalQueryBudget q)

theorem figureOneScheduledGloballyCappedBalancedBaseProgram_queryBound
    (q : VolumeParams) :
    (figureOneScheduledGloballyCappedBalancedBaseProgram q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  exact MembershipOracleProgram.withQueryCap_queryBound _ _

#print axioms figureOneScheduledGloballyCappedBalancedBaseProgram_queryBound
#print axioms scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law

end ArlibCommunity.Algorithms.CV18
