/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceBaseCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSlackMoments

/-!
# Total coordinates for a finite chronological reset reference

The reset recurrence records exactly the one-based coordinates used by the
CV18 dependent product.  The final analytic interface asks for a coordinate
family on every natural index.  This module supplies the harmless total
extension: retain the public trace coordinate on the used finite interval,
and use the corresponding deterministic ideal mean everywhere else.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- Extend the finite family of recorded trace coordinates by the positive
ideal raw mean outside `1, ..., figureOneDependentPhaseCount q`. -/
noncomputable def figureOneScheduledReferenceCoordinateExtension
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    ScheduledBalancedCoolingTrace q.n → ℝ :=
  if 1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q then
    scheduledBalancedTracePhaseVariable q j
  else fun _ => figureOneChronologicalRawMean q I j

theorem figureOneScheduledReferenceCoordinateExtension_eq_of_used
    (q : VolumeParams) (I : VolumeInput q.n) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ figureOneDependentPhaseCount q) :
    figureOneScheduledReferenceCoordinateExtension q I j =
      scheduledBalancedTracePhaseVariable q j := by
  simp [figureOneScheduledReferenceCoordinateExtension, hj1, hj]

theorem figureOneScheduledReferenceCoordinateExtension_eq_rawMean_of_not_used
    (q : VolumeParams) (I : VolumeInput q.n) {j : ℕ}
    (hj : ¬(1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q)) :
    figureOneScheduledReferenceCoordinateExtension q I j =
      fun _ => figureOneChronologicalRawMean q I j := by
  simp [figureOneScheduledReferenceCoordinateExtension, hj]

theorem measurable_figureOneScheduledReferenceCoordinateExtension
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    Measurable (figureOneScheduledReferenceCoordinateExtension q I j) := by
  unfold figureOneScheduledReferenceCoordinateExtension
  split_ifs
  · exact measurable_scheduledBalancedTracePhaseVariable q j
  · exact measurable_const

theorem figureOneScheduledReferenceCoordinateExtension_nonnegative
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    0 ≤ figureOneScheduledReferenceCoordinateExtension q I j trace := by
  unfold figureOneScheduledReferenceCoordinateExtension
  split_ifs
  · exact scheduledBalancedTracePhaseVariable_nonnegative q j trace
  · exact (figureOneChronologicalRawMean_pos q I j).le

theorem figureOneScheduledReferenceCoordinateExtension_apply_of_used
    (q : VolumeParams) (I : VolumeInput q.n) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ figureOneDependentPhaseCount q)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    figureOneScheduledReferenceCoordinateExtension q I j trace =
      scheduledBalancedTracePhaseVariable q j trace := by
  rw [figureOneScheduledReferenceCoordinateExtension_eq_of_used q I hj1 hj]

/-- The extension leaves the full product used by the estimator unchanged. -/
theorem dependentPhaseSampleProduct_referenceCoordinateExtension_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    dependentPhaseSampleProduct
        (figureOneScheduledReferenceCoordinateExtension q I)
        (figureOneDependentPhaseCount q) trace =
      dependentPhaseSampleProduct
        (scheduledBalancedTracePhaseVariable q)
        (figureOneDependentPhaseCount q) trace := by
  unfold dependentPhaseSampleProduct
  apply Finset.prod_congr rfl
  intro j hj
  apply figureOneScheduledReferenceCoordinateExtension_apply_of_used q I
  · omega
  · exact Finset.mem_range.mp hj

/-! ## Automatic facts outside the finite recorded interval -/

theorem figureOneScheduledReferenceCoordinateExtension_memLp_of_not_used
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure mu] {j : ℕ}
    (hj : ¬(1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q)) :
    MemLp (figureOneScheduledReferenceCoordinateExtension q I j) 2 mu := by
  rw [figureOneScheduledReferenceCoordinateExtension_eq_rawMean_of_not_used
    q I hj]
  exact memLp_const _

theorem integral_figureOneScheduledReferenceCoordinateExtension_of_not_used
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure mu] {j : ℕ}
    (hj : ¬(1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q)) :
    (∫ trace, figureOneScheduledReferenceCoordinateExtension q I j trace ∂mu) =
      figureOneChronologicalRawMean q I j := by
  rw [figureOneScheduledReferenceCoordinateExtension_eq_rawMean_of_not_used
    q I hj]
  simp

theorem integral_sq_figureOneScheduledReferenceCoordinateExtension_of_not_used
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure mu] {j : ℕ}
    (hj : ¬(1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q)) :
    (∫ trace,
        figureOneScheduledReferenceCoordinateExtension q I j trace ^ 2 ∂mu) =
      figureOneChronologicalRawMean q I j ^ 2 := by
  rw [figureOneScheduledReferenceCoordinateExtension_eq_rawMean_of_not_used
    q I hj]
  simp

theorem integral_sq_figureOneScheduledReferenceCoordinateExtension_le_of_not_used
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure mu] {j : ℕ}
    (hj : ¬(1 ≤ j ∧ j ≤ figureOneDependentPhaseCount q)) :
    (∫ trace,
        figureOneScheduledReferenceCoordinateExtension q I j trace ^ 2 ∂mu) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2 := by
  rw [integral_sq_figureOneScheduledReferenceCoordinateExtension_of_not_used
    q I mu hj]
  apply le_mul_of_one_le_left (sq_nonneg _)
  exact le_add_of_le_of_nonneg
    (figureOneChronologicalMomentFactor_one_le q j)
    (div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num))

#print axioms measurable_figureOneScheduledReferenceCoordinateExtension
#print axioms figureOneScheduledReferenceCoordinateExtension_nonnegative
#print axioms dependentPhaseSampleProduct_referenceCoordinateExtension_eq
#print axioms
  figureOneScheduledReferenceCoordinateExtension_memLp_of_not_used
#print axioms
  integral_figureOneScheduledReferenceCoordinateExtension_of_not_used
#print axioms
  integral_sq_figureOneScheduledReferenceCoordinateExtension_le_of_not_used

end

end ArlibCommunity.Algorithms.CV18
