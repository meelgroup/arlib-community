/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorConditionedTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule

/-!
# Error arithmetic for killed-collector Lemma 7.17(b)

The conditioned transition pays twice the accumulated endpoint error, while
the unconditioned endpoint pays it once.  Their asymmetric sum is bounded by
`3 (i+1) ν`, hence by the global `3 k m ν` dependence allocation.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- The exact conditioned/base error sum for sample `i` fits the dependence
coefficient allocated to CV18 Lemma 7.17(b). -/
theorem killedCollector_asymmetric_error_le_dependentEpsilon
    (q : VolumeParams) {i count : ℕ} (hi : i < count)
    (hcount : count ≤ figureOneDependentMaxSampleCount q) :
    ((figureOneCorrectedTransitionBudget q +
          2 * (scheduledBalancedStationaryTargetError q +
            i • figureOneCorrectedTransitionBudget q)) +
        (2 * scheduledBalancedStationaryTargetError q +
          (i + 1) • figureOneCorrectedTransitionBudget q)).toReal ≤
      figureOneDependentEpsilon q := by
  let delta := figureOneCorrectedTransitionBudget q
  let stationary := scheduledBalancedStationaryTargetError q
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hdeltaTop : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have htargetTop : figureOneCorrectedTargetBudget q ≠ ⊤ :=
    ENNReal.div_ne_top hdeltaTop (by norm_num)
  have hstationaryTop : stationary ≠ ⊤ :=
    ne_top_of_le_ne_top htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
  have hiDeltaTop : i • delta ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hdeltaTop
  have hisuccDeltaTop : (i + 1) • delta ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hdeltaTop
  have hstationaryAddTop : stationary + i • delta ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hstationaryTop, hiDeltaTop⟩
  have htwiceAccumTop : 2 * (stationary + i • delta) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hstationaryAddTop
  have hconditionedTop : delta + 2 * (stationary + i • delta) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hdeltaTop, htwiceAccumTop⟩
  have htwiceStationaryTop : 2 * stationary ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hstationaryTop
  have hbaseTop : 2 * stationary + (i + 1) • delta ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨htwiceStationaryTop, hisuccDeltaTop⟩
  have hstationaryReal : stationary.toReal ≤
      figureOnePerSampleMixingError q / 4 := by
    have htarget := scheduledBalancedStationaryTargetError_le_targetBudget q
    have hreal := ENNReal.toReal_mono htargetTop htarget
    simpa [stationary, figureOneCorrectedTargetBudget, delta,
      figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hnu.le] using hreal
  have hcountReal : (i + 1 : ℝ) ≤
      figureOneDependentMaxSampleCount q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi |>.trans hcount)
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have htwiceAccumReal :
      (2 * (stationary + i • delta)).toReal =
        2 * (stationary.toReal + (i : ℝ) * delta.toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_add hstationaryTop hiDeltaTop,
      ENNReal.toReal_nsmul]
    simp [nsmul_eq_mul]
  have htwiceStationaryReal :
      (2 * stationary).toReal = 2 * stationary.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have herrorReal :
      ((delta + 2 * (stationary + i • delta)) +
          (2 * stationary + (i + 1) • delta)).toReal =
        4 * stationary.toReal +
          (3 * (i : ℝ) + 2) * figureOnePerSampleMixingError q := by
    rw [ENNReal.toReal_add hconditionedTop hbaseTop,
      ENNReal.toReal_add hdeltaTop htwiceAccumTop,
      htwiceAccumReal,
      ENNReal.toReal_add htwiceStationaryTop hisuccDeltaTop,
      htwiceStationaryReal, ENNReal.toReal_nsmul]
    simp only [delta, figureOneCorrectedTransitionBudget,
      ENNReal.toReal_ofReal hnu.le]
    ring
  rw [herrorReal, ← figureOne_lemma717c_budget q]
  have hleft : 4 * stationary.toReal +
      (3 * (i : ℝ) + 2) * figureOnePerSampleMixingError q ≤
        3 * ((i : ℝ) + 1) * figureOnePerSampleMixingError q := by
    nlinarith
  have hsample :
      3 * ((i : ℝ) + 1) * figureOnePerSampleMixingError q ≤
        3 * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcountReal (by norm_num)) hnu.le
  have hphase :
      3 * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q ≤
        3 * (figureOneDependentMaxSampleCount q : ℝ) *
          (figureOneDependentPhaseCount q : ℝ) *
            figureOnePerSampleMixingError q := by
    have hk0 : 0 ≤ (3 : ℝ) * figureOneDependentMaxSampleCount q := by positivity
    have hmul := mul_le_mul_of_nonneg_left hm hk0
    nlinarith
  exact hleft.trans (hsample.trans hphase)

#print axioms killedCollector_asymmetric_error_le_dependentEpsilon

end ArlibCommunity.Algorithms.CV18
