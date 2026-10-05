/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCostBounds

/-! # Exact zero-cost output-map identities for the scheduled executable -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem MembershipOracleProgram.countedQueryCost_pure
    {n : ℕ} {A : Type} [MeasurableSpace A]
    (oracle : AmbientSpace n → Bool) (value : A) :
    countedQueryCost
      ((MembershipOracleProgram.pure (n := n) value).run oracle) = 0 := by
  unfold countedQueryCost
  simp only [MembershipOracleProgram.run]
  rw [lintegral_dirac' _ measurable_countedQueryCost_integrand]
  simp

/-- Postcomposing a counted program with a measurable pure output map does
not change its expected membership-query cost. -/
theorem MembershipOracleProgram.countedQueryCost_bind_pure_eq
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (f : A → B) (hf : Measurable f)
    (hprogram : program.CountedStronglyMeasurable oracle) :
    countedQueryCost ((program.bind fun value => .pure (f value)).run oracle) =
      countedQueryCost (program.run oracle) := by
  let next : A → MembershipOracleProgram n B := fun value => .pure (f value)
  have hnext : ∀ value, (next value).CountedStronglyMeasurable oracle := by
    intro value
    trivial
  have hnextRun : Measurable fun value => (next value).run oracle := by
    simp only [next, MembershipOracleProgram.run]
    exact Measure.measurable_dirac.comp (hf.prodMk measurable_const)
  rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle program next
    hprogram hnext hnextRun]
  have hzero : (fun value => countedQueryCost ((next value).run oracle)) =
      fun _ => 0 := by
    funext value
    exact MembershipOracleProgram.countedQueryCost_pure oracle (f value)
  rw [hzero]
  simp

/-- The averaging wrapper of a scheduled Gaussian phase is query-free, so
the phase cost is exactly the cost of its finite retry collector. -/
theorem scheduledBalancedCoolingRatioEstimate_countedQueryCost_eq
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ)
    (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2
          current).run oracle.query) =
      countedQueryCost
        ((scheduledBalancedAccuracyRetryCollect q sigma2
          (gaussianRatioWeight sigma2 tau2)
          (parameters.proposalCap q sigma2)
          (parameters.properStride q sigma2)
          (parameters.retryLimit q sigma2)
          (figureOnePhaseSampleCount q sigma2)
          (accuracyScaleFactor q • current)).run oracle.query) := by
  unfold scheduledBalancedCoolingRatioEstimate
  apply MembershipOracleProgram.countedQueryCost_bind_pure_eq
  · exact measurable_balancedCoolingAverage _
  · exact (scheduledBalancedAccuracyRetryCollect_countedMeasurable
      q I oracle hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)).2 _

/-- The terminal averaging wrapper is likewise query-free. -/
theorem scheduledBalancedCoolingUniformEstimateWithState_countedQueryCost_eq
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2
          current).run oracle.query) =
      countedQueryCost
        ((scheduledBalancedAccuracyRetryCollect q sigma2
          (uniformRatioWeight sigma2)
          (parameters.proposalCap q sigma2)
          (parameters.properStride q sigma2)
          (parameters.retryLimit q sigma2)
          (figureOneSampleCount q)
          (accuracyScaleFactor q • current)).run oracle.query) := by
  unfold scheduledBalancedCoolingUniformEstimateWithState
  apply MembershipOracleProgram.countedQueryCost_bind_pure_eq
  · exact measurable_balancedCoolingAverage _
  · exact (scheduledBalancedAccuracyRetryCollect_countedMeasurable
      q I oracle hsigma2 (measurable_uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)).2 _

/-- Forgetting the retained terminal state adds no membership queries. -/
theorem scheduledBalancedCoolingUniformRatioEstimate_countedQueryCost_eq
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedCoolingUniformRatioEstimate parameters q sigma2
          current).run oracle.query) =
      countedQueryCost
        ((scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2
          current).run oracle.query) := by
  unfold scheduledBalancedCoolingUniformRatioEstimate
  apply MembershipOracleProgram.countedQueryCost_bind_pure_eq
  · exact measurable_balancedCoolingForgetState
  · exact (scheduledBalancedCoolingUniformEstimateWithState_countedMeasurable
      parameters q I oracle hsigma2).2 current

end ArlibCommunity.Algorithms.CV18
