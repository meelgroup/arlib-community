/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialCoupling

/-! # Abort-on-failure initialization for the scheduled CV18 executable

The legacy executable replaces a Gaussian proposal outside the truncated body
by the origin and then runs the whole cooling schedule from that singular
point.  The paper treats failure of the initial rejection test as an aborted
run.  The primitive below implements that semantics literally: it returns
`none` after the one initial membership query.  Consequently the failed
initial branch has no post-initial query cost.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Keep an initial proposal precisely on the truncated body. -/
noncomputable def initialTruncatedOption (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Option (AmbientSpace q.n) :=
  if point ∈ truncatedBody q I then some point else none

theorem measurable_initialTruncatedOption (q : VolumeParams)
    (I : VolumeInput q.n) : Measurable (initialTruncatedOption q I) := by
  unfold initialTruncatedOption
  exact Measurable.ite (truncatedBody_measurable q I)
    (measurable_some.comp measurable_id) measurable_const

/-- One Gaussian proposal and one membership query, aborting rather than
continuing from the origin when the proposal misses the truncated body. -/
noncomputable def figureOneAbortInitialSample (q : VolumeParams) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  .randomPoint (initialGaussianSamplingMeasure q) inferInstance fun point =>
    .query point fun inside =>
      .pure (if inside = true ∧
        ‖point‖ ≤ Real.sqrt (terminalVariance q) then some point else none)

theorem figureOneAbortInitialSample_queryBound (q : VolumeParams) :
    (figureOneAbortInitialSample q).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro point
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

theorem figureOneAbortInitialSample_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneAbortInitialSample q).StronglyMeasurable oracle.query := by
  simp only [figureOneAbortInitialSample,
    MembershipOracleProgram.StronglyMeasurable]
  constructor
  · simp only [MembershipOracleProgram.runEstimate]
    apply Measure.measurable_dirac.comp
    apply Measurable.ite
    · exact (oracle.measurable_query (measurableSet_singleton true)).inter
        (measurableSet_le measurable_norm measurable_const)
    · exact measurable_some.comp measurable_id
    · exact measurable_const
  · intro point
    trivial

theorem figureOneAbortInitialSample_fixedQueryCount (q : VolumeParams) :
    (figureOneAbortInitialSample q).FixedQueryCount 1 := by
  unfold figureOneAbortInitialSample
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro point
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  split <;> exact .pure _

theorem figureOneAbortInitialSample_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneAbortInitialSample q).CountedStronglyMeasurable oracle.query :=
  (figureOneAbortInitialSample_fixedQueryCount q).countedStronglyMeasurable
    oracle.query (figureOneAbortInitialSample_stronglyMeasurable q I oracle)

/-- Exact law of the aborting initial sampler. -/
theorem runEstimate_figureOneAbortInitialSample
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneAbortInitialSample q).runEstimate oracle.query =
      (initialGaussianSamplingMeasure q).map (initialTruncatedOption q I) := by
  unfold figureOneAbortInitialSample
  simp only [MembershipOracleProgram.runEstimate]
  have hfun : (fun point : AmbientSpace q.n =>
      if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) then some point else none) =
      initialTruncatedOption q I := by
    funext point
    unfold initialTruncatedOption truncatedBody
    by_cases hc : oracle.query point = true ∧
        ‖point‖ ≤ Real.sqrt (terminalVariance q)
    · have hp : point ∈
          (I.body : Set (AmbientSpace q.n)) ∩
            Metric.closedBall 0 (Real.sqrt (terminalVariance q)) := by
        exact ⟨(oracle.correct point).mp hc.1, by
          simpa [Metric.mem_closedBall, dist_zero_right] using hc.2⟩
      simp [hc, hp]
    · have hp : point ∉
          (I.body : Set (AmbientSpace q.n)) ∩
            Metric.closedBall 0 (Real.sqrt (terminalVariance q)) := by
        intro hp
        apply hc
        exact ⟨(oracle.correct point).mpr hp.1, by
          simpa [Metric.mem_closedBall, dist_zero_right] using hp.2⟩
      simp [hc, hp]
  rw [show (fun point : AmbientSpace q.n =>
      Measure.dirac (if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) then some point else none)) =
      fun point => Measure.dirac (initialTruncatedOption q I point) by
        funext point
        rw [congrFun hfun point]]
  rw [Measure.bind_dirac_eq_map _ (measurable_initialTruncatedOption q I)]

/-- The live law of the aborting initializer is a submeasure of the ideal
normalized initial Gaussian used by the CV18 warm-start proof. -/
theorem initialGaussianSamplingMeasure_restrict_truncatedBody_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (initialGaussianSamplingMeasure q).restrict (truncatedBody q I) ≤
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)) := by
  rw [initialGaussianSamplingMeasure_restrict_truncatedBody q I]
  intro E
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left bot_le
    (initialGaussianRestrictedMassCoefficient_le_one q I)

/-- Scheduled primitives with paper-faithful aborting initialization. -/
noncomputable def scheduledBalancedAbortCoolingPrimitives
    (parameters : BalancedCoolingParameters) : VolumeCoolingPrimitives where
  initialSample := figureOneAbortInitialSample
  ratioEstimate := scheduledBalancedCoolingRatioEstimate parameters
  uniformRatioEstimate := scheduledBalancedCoolingUniformRatioEstimate parameters

/-- `coolingProduct` does not inspect the initialization field, so changing
only that field leaves every post-initial continuation definitionally
equivalent. -/
theorem scheduledBalancedAbort_coolingProduct_eq
    (parameters : BalancedCoolingParameters) (q : VolumeParams) :
    ∀ (variances : List ℝ) (point : AmbientSpace q.n),
      coolingProduct (scheduledBalancedAbortCoolingPrimitives parameters) q
          variances point =
        coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
          variances point := by
  intro variances
  induction variances with
  | nil =>
      intro point
      simp [coolingProduct, scheduledBalancedAbortCoolingPrimitives,
        scheduledBalancedCoolingPrimitives]
  | cons sigma2 tail ih =>
      intro point
      cases tail with
      | nil =>
          simp [coolingProduct, scheduledBalancedAbortCoolingPrimitives,
            scheduledBalancedCoolingPrimitives]
      | cons tau2 rest =>
          simp only [coolingProduct, scheduledBalancedAbortCoolingPrimitives,
            scheduledBalancedCoolingPrimitives]
          congr 1
          funext phase
          cases phase with
          | none => rfl
          | some value =>
              rcases value with ⟨ratio, nextPoint⟩
              simp only
              change
                (coolingProduct
                    (scheduledBalancedAbortCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind _ =
                  (coolingProduct
                    (scheduledBalancedCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind _
              rw [ih nextPoint]

/-- Replacing the initializer by the aborting version leaves the complete
post-initial point continuation unchanged. -/
theorem scheduledBalancedAbort_pointContinuation_eq
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) :
    (coolingProduct (scheduledBalancedAbortCoolingPrimitives parameters) q
        (explicitVolumeCoolingSchedule q).variances point).bind (fun product =>
      match product with
      | none => .pure (0 : ℝ)
      | some (gaussianProduct, lastPoint) =>
          ((scheduledBalancedAbortCoolingPrimitives parameters).uniformRatioEstimate
              q (terminalVariance q) lastPoint).bind (fun finalRatio =>
            .pure (match finalRatio with
              | some uniformRatio =>
                  initialGaussianIntegral q * gaussianProduct * uniformRatio
              | none => (0 : ℝ)))) =
      scheduledBalancedFigureOnePointContinuation parameters q point := by
  rw [scheduledBalancedAbort_coolingProduct_eq]
  rfl

/-- Candidate final scheduled base program whose failed initialization costs
exactly one query and performs no cooling transitions. -/
noncomputable def figureOneFinalScheduledAbortBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling
    (scheduledBalancedAbortCoolingPrimitives
      figureOneFinalScheduledBalancedParameters)
    explicitVolumeCoolingSchedule q

#print axioms runEstimate_figureOneAbortInitialSample
#print axioms figureOneAbortInitialSample_countedStronglyMeasurable
#print axioms initialGaussianSamplingMeasure_restrict_truncatedBody_le
#print axioms scheduledBalancedAbort_coolingProduct_eq
#print axioms scheduledBalancedAbort_pointContinuation_eq

end ArlibCommunity.Algorithms.CV18
