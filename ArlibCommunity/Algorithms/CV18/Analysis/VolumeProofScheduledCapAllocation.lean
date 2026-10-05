import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledBranchMass

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The corrected allocation's deliberately unused quarter exactly pays a
second copy of every block budget, for finite local-cap exhaustion. -/
theorem figureOneCorrected_components_with_double_block_le
    (q : VolumeParams) (attempts : ℕ) :
    (attempts + 1) • (2 * figureOneCorrectedBlockBudget q attempts) +
        figureOneCorrectedRetryTailBudget q +
      figureOneCorrectedTargetBudget q ≤
        figureOneCorrectedTransitionBudget q := by
  have hblock : figureOneCorrectedBlockBudget q attempts ≠ ∞ := by
    simp [figureOneCorrectedBlockBudget]
  have htotal : figureOneCorrectedTransitionBudget q ≠ ∞ := by
    simp [figureOneCorrectedTransitionBudget]
  have hretry : figureOneCorrectedRetryTailBudget q ≠ ∞ := by
    exact ENNReal.div_ne_top htotal (by norm_num)
  have htarget : figureOneCorrectedTargetBudget q ≠ ∞ := by
    exact ENNReal.div_ne_top htotal (by norm_num)
  have hdouble : 2 * figureOneCorrectedBlockBudget q attempts ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hblock
  have hblocks :
      (attempts + 1) • (2 * figureOneCorrectedBlockBudget q attempts) ≠ ∞ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hdouble
  have hblocksRetry :
      (attempts + 1) • (2 * figureOneCorrectedBlockBudget q attempts) +
          figureOneCorrectedRetryTailBudget q ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hblocks, hretry⟩
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.2 ⟨hblocksRetry, htarget⟩) htotal).mp
  rw [ENNReal.toReal_add hblocksRetry htarget]
  rw [ENNReal.toReal_add hblocks hretry]
  rw [ENNReal.toReal_nsmul]
  rw [ENNReal.toReal_mul]
  simp only [figureOneCorrectedBlockBudget,
    figureOneCorrectedRetryTailBudget,
    figureOneCorrectedTargetBudget,
    figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.toReal_ofReal
    (figureOneCorrectedBlockMixingError_pos q attempts).le]
  rw [ENNReal.toReal_ofReal (figureOnePerSampleMixingError_pos q).le]
  unfold figureOneCorrectedBlockMixingError
  have hden : (0 : ℝ) < attempts + 1 := by positivity
  field_simp
  nlinarith [figureOnePerSampleMixingError_pos q]

/-- One cap budget plus one mixing budget per proper block, followed by the
retry tail and scheduled KLS target correction, still fits the exact-chance
budget for one retained sample. -/
theorem scheduledBalancedTransitionError_with_cap_le_budget
    (q : VolumeParams) {rejectMass : ENNReal} {attempts : ℕ}
    (hreject : rejectMass ≤ 1)
    (hretry : rejectMass ^ (attempts + 1) ≤
      figureOneCorrectedRetryTailBudget q) :
    (2 * figureOneCorrectedBlockBudget q attempts) + rejectMass *
        balancedRetryError (2 * figureOneCorrectedBlockBudget q attempts)
          rejectMass attempts +
      scheduledBalancedStationaryTargetError q ≤
        figureOneCorrectedTransitionBudget q := by
  have hrecursive := reject_mul_balancedRetryError_le
    (blockError := 2 * figureOneCorrectedBlockBudget q attempts)
    hreject attempts
  calc
    2 * figureOneCorrectedBlockBudget q attempts + rejectMass *
          balancedRetryError (2 * figureOneCorrectedBlockBudget q attempts)
            rejectMass attempts +
        scheduledBalancedStationaryTargetError q ≤
      2 * figureOneCorrectedBlockBudget q attempts +
          (attempts • (2 * figureOneCorrectedBlockBudget q attempts) +
            rejectMass ^ (attempts + 1)) +
        scheduledBalancedStationaryTargetError q := by gcongr
    _ = (attempts + 1) •
          (2 * figureOneCorrectedBlockBudget q attempts) +
        rejectMass ^ (attempts + 1) +
          scheduledBalancedStationaryTargetError q := by
      rw [add_nsmul]
      simp only [one_nsmul]
      ac_rfl
    _ ≤ (attempts + 1) •
          (2 * figureOneCorrectedBlockBudget q attempts) +
        figureOneCorrectedRetryTailBudget q +
          figureOneCorrectedTargetBudget q := by
      exact add_le_add (add_le_add le_rfl hretry)
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    _ ≤ figureOneCorrectedTransitionBudget q :=
      figureOneCorrected_components_with_double_block_le q attempts

#print axioms figureOneCorrected_components_with_double_block_le
#print axioms scheduledBalancedTransitionError_with_cap_le_budget

end ArlibCommunity.Algorithms.CV18
