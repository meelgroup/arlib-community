/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAbortInitialSample
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCostComposition

/-! # Initial cost reduction for the aborting final scheduled executable -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneFinalScheduledAbortBaseProgram q).CountedStronglyMeasurable
      oracle.query := by
  have hpoint := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  let tail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point
  have htailRun : Measurable fun initialPoint =>
      (tail initialPoint).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hpoint.1 using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have htail : ∀ initialPoint,
      (tail initialPoint).CountedStronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hpoint.2 point
  have hbase : figureOneFinalScheduledAbortBaseProgram q =
      (figureOneAbortInitialSample q).bind tail := by
    unfold figureOneFinalScheduledAbortBaseProgram baseVolumeCooling tail
    congr 1
    funext initialPoint
    cases initialPoint with
    | none => rfl
    | some point =>
        exact scheduledBalancedAbort_pointContinuation_eq
          figureOneFinalScheduledBalancedParameters q point
  rw [hbase]
  exact (figureOneAbortInitialSample_countedStronglyMeasurable q I oracle).bind
    htail htailRun

/-- After the paper-faithful initial abort, expected cost is bounded by one
initial query plus the post-initial cost under the ideal normalized truncated
Gaussian.  The failed initial branch contributes exactly zero continuation
queries. -/
theorem figureOneFinalScheduledAbortBaseProgram_countedQueryCost_le_initial_add
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query) ≤
      1 + ∫⁻ point, countedQueryCost
          ((scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).run oracle.query)
        ∂(truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q)) := by
  let continuation (point : AmbientSpace q.n) :=
    scheduledBalancedFigureOnePointContinuation
      figureOneFinalScheduledBalancedParameters q point
  let tail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => continuation point
  have hcontinuation := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  have htailRun : Measurable fun initialPoint =>
      (tail initialPoint).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hcontinuation.1 using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have htail : ∀ initialPoint,
      (tail initialPoint).CountedStronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hcontinuation.2 point
  have hbase : figureOneFinalScheduledAbortBaseProgram q =
      (figureOneAbortInitialSample q).bind tail := by
    unfold figureOneFinalScheduledAbortBaseProgram baseVolumeCooling tail
      continuation
    congr 1
    funext initialPoint
    cases initialPoint with
    | none => rfl
    | some point =>
        exact scheduledBalancedAbort_pointContinuation_eq
          figureOneFinalScheduledBalancedParameters q point
  have hinitialCost : countedQueryCost
      ((figureOneAbortInitialSample q).run oracle.query) ≤ 1 := by
    simpa only [countedQueryCost, Nat.cast_one] using
      (figureOneAbortInitialSample_queryBound q).lintegral_queryCount_le
        (figureOneAbortInitialSample_countedStronglyMeasurable q I oracle)
  have hcostMeas : Measurable fun point => countedQueryCost
      ((continuation point).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hcontinuation.1
  have htailCostMeas : Measurable fun initialPoint => countedQueryCost
      ((tail initialPoint).run oracle.query) := by
    convert Measurable.optionElim
      (countedQueryCost
        ((MembershipOracleProgram.pure (n := q.n) (0 : ℝ)).run oracle.query))
      hcostMeas using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have hintegral :
      (∫⁻ initialPoint, countedQueryCost ((tail initialPoint).run oracle.query)
          ∂((initialGaussianSamplingMeasure q).map
            (initialTruncatedOption q I))) ≤
        ∫⁻ point, countedQueryCost ((continuation point).run oracle.query)
          ∂(truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q)) := by
    calc
      _ = ∫⁻ point, countedQueryCost
          ((tail (initialTruncatedOption q I point)).run oracle.query)
            ∂(initialGaussianSamplingMeasure q) := by
        simpa only using
          (lintegral_map (μ := initialGaussianSamplingMeasure q) htailCostMeas
            (measurable_initialTruncatedOption q I))
      _ = ∫⁻ point in truncatedBody q I,
          countedQueryCost ((continuation point).run oracle.query)
            ∂(initialGaussianSamplingMeasure q) := by
        rw [← lintegral_indicator (truncatedBody_measurable q I)]
        apply lintegral_congr
        intro point
        by_cases hp : point ∈ truncatedBody q I
        · simp [initialTruncatedOption, hp, tail]
        · simp [initialTruncatedOption, hp, tail,
            MembershipOracleProgram.countedQueryCost_pure]
      _ ≤ _ := lintegral_mono'
        (initialGaussianSamplingMeasure_restrict_truncatedBody_le q I) le_rfl
  rw [hbase, MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
    (figureOneAbortInitialSample q) tail
    (figureOneAbortInitialSample_countedStronglyMeasurable q I oracle)
    htail htailRun,
    runEstimate_figureOneAbortInitialSample q I oracle]
  exact add_le_add hinitialCost hintegral

#print axioms
  figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
#print axioms
  figureOneFinalScheduledAbortBaseProgram_countedQueryCost_le_initial_add

end ArlibCommunity.Algorithms.CV18
