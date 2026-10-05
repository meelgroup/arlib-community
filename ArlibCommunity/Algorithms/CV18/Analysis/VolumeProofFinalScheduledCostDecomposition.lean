/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCostComposition

/-! # Initial-bind decomposition of final scheduled expected cost -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The initial proposal costs one query.  All remaining expected cost is the
post-initial continuation cost averaged under the executable fallback law. -/
theorem figureOneFinalScheduledBalancedBaseProgram_countedQueryCost_le_initial_add
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledBalancedBaseProgram q).run oracle.query) ≤
      1 + ∫⁻ point, countedQueryCost
          ((scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).run oracle.query)
        ∂((initialGaussianSamplingMeasure q).map
          (initialTruncatedFallback q I)) := by
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
  have hbase : figureOneFinalScheduledBalancedBaseProgram q =
      (figureOneInitialSample q).bind tail := by
    unfold figureOneFinalScheduledBalancedBaseProgram baseVolumeCooling tail
      continuation scheduledBalancedFigureOnePointContinuation
    congr 1
  have hinitialCost : countedQueryCost
      ((figureOneInitialSample q).run oracle.query) ≤ 1 := by
    simpa only [countedQueryCost, Nat.cast_one] using
      (figureOneInitialSample_queryBound q).lintegral_queryCount_le
        (figureOneInitialSample_countedStronglyMeasurable q I oracle)
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
            (some ∘ initialTruncatedFallback q I))) =
        ∫⁻ point, countedQueryCost ((continuation point).run oracle.query)
          ∂((initialGaussianSamplingMeasure q).map
            (initialTruncatedFallback q I)) := by
    calc
      _ = ∫⁻ point, countedQueryCost
          ((tail (some (initialTruncatedFallback q I point))).run oracle.query)
            ∂(initialGaussianSamplingMeasure q) := by
        simpa only [Function.comp_apply] using
          (lintegral_map (μ := initialGaussianSamplingMeasure q) htailCostMeas
            (measurable_some.comp (measurable_initialTruncatedFallback q I)))
      _ = ∫⁻ point, countedQueryCost
          ((continuation (initialTruncatedFallback q I point)).run oracle.query)
            ∂(initialGaussianSamplingMeasure q) := by rfl
      _ = _ := (lintegral_map hcostMeas
        (measurable_initialTruncatedFallback q I)).symm
  rw [hbase, MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
    (figureOneInitialSample q) tail
    (figureOneInitialSample_countedStronglyMeasurable q I oracle)
    htail htailRun,
    runEstimate_figureOneInitialSample q I oracle]
  apply add_le_add hinitialCost
  exact le_of_eq hintegral

#print axioms
  figureOneFinalScheduledBalancedBaseProgram_countedQueryCost_le_initial_add

end ArlibCommunity.Algorithms.CV18
