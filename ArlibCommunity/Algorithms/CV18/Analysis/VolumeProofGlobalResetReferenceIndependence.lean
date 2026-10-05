/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.RecordedKernelResetIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceFailureBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad

/-!
# Lemma 7.17(c) on a global reset reference

The executable chronological trace already satisfies CV18 Lemma 7.17(c).
A history-preserving reset changes its law by a single global additive error.
This module transports every phasewise independence fact to the reset
reference and checks that the complete fixed-reset error consumes at most the
extra `3/2` dependence budget allowed by the reference-side product theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- Every phasewise Lemma 7.17(c) fact on the executable trace transfers to a
dominating global reset reference, at the standard `3 * delta` TV cost. -/
theorem figureOneScheduledTrace_lemma717c_of_globalResetReference
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure reference]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hdom : MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
      reference delta) :
    ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun
        (figureOneDependentEpsilon q + 3 * delta.toReal)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        reference := by
  intro i hi
  let actual := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let _ : IsProbabilityMeasure actual :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct
      (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I)
      (fun j => (measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const) i
  have hY : Measurable Y :=
    (measurable_scheduledBalancedTracePhaseVariable q (i + 1)).min
      measurable_const
  exact ApproxIndepFun.of_measureLeUpTo_symm
    actual reference hdelta X Y hX hY hdom
      (figureOneScheduledTrace_lemma717c q I i hi)

/-- The complete fixed-reset error is finite. -/
theorem figureOneScheduledGlobalResetReferenceError_ne_top
    (q : VolumeParams) :
    figureOneScheduledGlobalResetReferenceError q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (figureOneScheduledGlobalResetReferenceError_le q)

/-- Relative (rather than coarse absolute) accounting for the global reset
error.  Its factor-three independence-transfer cost is at most `3/2` times
the original coefficient, so the old and new costs total at most `5/2`. -/
theorem figureOneDependentEpsilon_add_three_globalResetError_toReal_le
    (q : VolumeParams) :
    figureOneDependentEpsilon q +
        3 * (figureOneScheduledGlobalResetReferenceError q).toReal ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
  let samples := figureOneDependentMaxSampleCount q *
    figureOneDependentPhaseCount q
  let base := samples • ENNReal.ofReal (figureOnePerSampleMixingError q)
  have hbaseTop : base ≠ ⊤ := by
    dsimp [base]
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top
  have hglobalTop := figureOneScheduledGlobalResetReferenceError_ne_top q
  have hglobal := figureOneScheduledGlobalResetReferenceError_le_count q
  have hrewrite :
      samples • ENNReal.ofReal
          ((3 / 2 : ℝ) * figureOnePerSampleMixingError q) =
        ENNReal.ofReal (3 / 2 : ℝ) * base := by
    simp only [base, samples, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    ring
  rw [hrewrite] at hglobal
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbaseTop) hglobal
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] at hreal
  have hexact : 3 * base.toReal = figureOneDependentEpsilon q := by
    simpa [base, samples] using figureOne_exactChance_budget q
  nlinarith [figureOneDependentEpsilon_nonneg q]

/-- Specialized global transfer: any comparison whose error is bounded by
the exact chronological fixed-reset sum gives all reference-side Lemma
7.17(c) facts at the `5/2` coefficient accepted by the final product
capstone. -/
theorem figureOneScheduledTrace_lemma717c_of_globalResetReference_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure reference]
    {delta : ENNReal}
    (hdom : MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
      reference delta)
    (hdelta : delta ≤ figureOneScheduledGlobalResetReferenceError q) :
    ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun
        ((5 / 2 : ℝ) * figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        reference := by
  have hdeltaTop : delta ≠ ⊤ :=
    ne_top_of_le_ne_top
      (figureOneScheduledGlobalResetReferenceError_ne_top q) hdelta
  have hdeltaReal : delta.toReal ≤
      (figureOneScheduledGlobalResetReferenceError q).toReal :=
    ENNReal.toReal_mono
      (figureOneScheduledGlobalResetReferenceError_ne_top q) hdelta
  intro i hi
  have hind := figureOneScheduledTrace_lemma717c_of_globalResetReference
    q I reference hdeltaTop hdom i hi
  apply hind.mono
  have hmul : (3 : ℝ) * delta.toReal ≤
      3 * (figureOneScheduledGlobalResetReferenceError q).toReal :=
    mul_le_mul_of_nonneg_left hdeltaReal (by norm_num)
  calc
    figureOneDependentEpsilon q + 3 * delta.toReal ≤
        figureOneDependentEpsilon q +
          3 * (figureOneScheduledGlobalResetReferenceError q).toReal := by
      gcongr
    _ ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q :=
      figureOneDependentEpsilon_add_three_globalResetError_toReal_le q

#print axioms figureOneScheduledTrace_lemma717c_of_globalResetReference
#print axioms figureOneScheduledGlobalResetReferenceError_ne_top
#print axioms
  figureOneDependentEpsilon_add_three_globalResetError_toReal_le
#print axioms figureOneScheduledTrace_lemma717c_of_globalResetReference_le

end

end ArlibCommunity.Algorithms.CV18
