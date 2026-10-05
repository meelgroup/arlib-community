/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLossPreservingTrace

/-! # Exact executable identification for scheduled chronological histories -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The collector recursion used by the executable-law bridge is definitionally
the collector recursion used by the chronological phase construction. -/
theorem scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples total current,
      scheduledBalancedAccuracyTransitionCollectLaw q I sigma2 weight
          proposalCap properStride retryLimit samples total current =
        scheduledBalancedTransitionCollectLaw q I sigma2 weight
          proposalCap properStride retryLimit samples total current := by
  intro samples
  induction samples with
  | zero =>
      intro total current
      rfl
  | succ samples ih =>
      intro total current
      simp only [scheduledBalancedAccuracyTransitionCollectLaw,
        scheduledBalancedTransitionCollectLaw]
      apply Measure.bind_congr_right
      filter_upwards with result
      cases result with
      | none => rfl
      | some target => exact ih _ _

/-- The law exported by the executable scheduled primitive is exactly the
chronological transition law used by the trace construction. -/
theorem scheduledBalancedCoolingRatioLaw_eq_transitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ)
    (current : AmbientSpace q.n) :
    scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 current =
      scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2
        current := by
  unfold scheduledBalancedCoolingRatioLaw
    scheduledBalancedCoolingRatioTransitionLaw
  rw [scheduledBalancedAccuracyRetryCollectLaw_eq_transitionCollectLaw
    q I hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)]
  rw [scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological]

theorem scheduledBalancedCoolingRatioLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) :
    Measurable (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2) ∧
    ∀ current, IsProbabilityMeasure
      (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 current) := by
  have heq : scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 =
      scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2 := by
    funext current
    exact scheduledBalancedCoolingRatioLaw_eq_transitionLaw
      parameters q I hsigma2 tau2 current
  rw [heq]
  exact scheduledBalancedCoolingRatioTransitionLaw_measurable_and_probability
    parameters q I hsigma2 tau2

theorem scheduledBalancedCoolingRatioEstimate_runEstimate_eq_transitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ)
    (current : AmbientSpace q.n) :
    (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
        oracle.query =
      scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2
        current := by
  rw [(scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law
    parameters q I oracle hsigma2 tau2).2.2 current]
  exact scheduledBalancedCoolingRatioLaw_eq_transitionLaw
    parameters q I hsigma2 tau2 current

/-- The exact public collector law of the scheduled terminal phase. -/
noncomputable def scheduledBalancedCoolingUniformCollectorLawWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollectLaw q I sigma2
      (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOneSampleCount q))

/-- Terminal counterpart of
`scheduledBalancedCoolingRatioLaw_eq_transitionLaw`. -/
theorem scheduledBalancedCoolingUniformLaw_eq_transitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2 current =
      scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2
        current := by
  unfold scheduledBalancedCoolingUniformCollectorLawWithState
    scheduledBalancedCoolingUniformTransitionLaw
  rw [scheduledBalancedAccuracyRetryCollectLaw_eq_transitionCollectLaw
    q I hsigma2 (measurable_uniformRatioWeight sigma2)]
  rw [scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological]

theorem scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2) ∧
    ∀ current, IsProbabilityMeasure
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2 current) := by
  have heq :
      scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2 =
        scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2 := by
    funext current
    exact scheduledBalancedCoolingUniformLaw_eq_transitionLaw
      parameters q I hsigma2 current
  rw [heq]
  exact scheduledBalancedCoolingUniformTransitionLaw_measurable_and_probability
    parameters q I hsigma2

theorem scheduledBalancedCoolingUniformEstimateWithState_runEstimate_eq_transitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2
        current).runEstimate oracle.query =
      scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2
        current := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOneSampleCount q
  let weight : AmbientSpace q.n → ℝ := uniformRatioWeight sigma2
  let start := accuracyScaleFactor q • current
  have hcollector := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle hsigma2 (measurable_uniformRatioWeight sigma2)
      cap stride retries samples
  have hstrong :
      (scheduledBalancedAccuracyRetryCollect q sigma2 weight cap stride
        retries samples start).StronglyMeasurable oracle.query :=
    (hcollector.2 start).stronglyMeasurable
  have havg := measurable_balancedCoolingAverage
    (n := q.n) (figureOneSampleCount q)
  have hpure : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (.pure (balancedCoolingAverage (figureOneSampleCount q) result) :
        MembershipOracleProgram q.n
          (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp havg
  unfold scheduledBalancedCoolingUniformEstimateWithState
  rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
    hstrong (fun _ => by trivial) hpure]
  rw [scheduledBalancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
    q I oracle hsigma2 (measurable_uniformRatioWeight sigma2)]
  change (scheduledBalancedAccuracyTransitionCollectLaw q I sigma2 weight cap
    stride retries samples 0 start).bind
      (fun result => Measure.dirac
        (balancedCoolingAverage (figureOneSampleCount q) result)) = _
  rw [Measure.bind_dirac_eq_map _ havg]
  unfold scheduledBalancedCoolingUniformTransitionLaw
  rw [scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological]

theorem scheduledBalancedCoolingUniformEstimateWithState_measurable_strong_and_law
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable (fun current =>
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
        oracle.query) ∧
    (∀ current,
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).StronglyMeasurable
        oracle.query) ∧
    ∀ current,
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
          oracle.query =
        scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2 current := by
  have hlaw := scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
    parameters q I hsigma2
  have hrun : ∀ current,
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).runEstimate
          oracle.query =
        scheduledBalancedCoolingUniformCollectorLawWithState parameters q I sigma2 current := by
    intro current
    calc
      _ = scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2 current :=
        scheduledBalancedCoolingUniformEstimateWithState_runEstimate_eq_transitionLaw
          parameters q I oracle hsigma2 current
      _ = _ := (scheduledBalancedCoolingUniformLaw_eq_transitionLaw
        parameters q I hsigma2 current).symm
  constructor
  · simpa only [hrun] using hlaw.1
  constructor
  · intro current
    exact (scheduledBalancedCoolingUniformEstimateWithState_countedMeasurable
      parameters q I oracle hsigma2).2 current |>.stronglyMeasurable
  · exact hrun

#print axioms scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological
#print axioms scheduledBalancedCoolingRatioLaw_eq_transitionLaw
#print axioms scheduledBalancedCoolingRatioLaw_measurable_and_probability
#print axioms scheduledBalancedCoolingUniformLaw_eq_transitionLaw
#print axioms scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
#print axioms scheduledBalancedCoolingRatioEstimate_runEstimate_eq_transitionLaw
#print axioms scheduledBalancedCoolingUniformEstimateWithState_runEstimate_eq_transitionLaw
#print axioms scheduledBalancedCoolingUniformEstimateWithState_measurable_strong_and_law

end ArlibCommunity.Algorithms.CV18
