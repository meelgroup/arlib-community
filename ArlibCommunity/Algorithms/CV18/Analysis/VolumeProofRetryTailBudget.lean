import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedTarget

namespace ArlibCommunity.Algorithms.CV18

noncomputable def figureOneSafeRetryCount (q : VolumeParams) : ℕ :=
  Nat.ceil (128 * protectedLog (4 / figureOnePerSampleMixingError q))

theorem figureOneSafeRetryCount_pos (q : VolumeParams) :
    0 < figureOneSafeRetryCount q := by
  apply Nat.ceil_pos.mpr
  have hlog : (1 : ℝ) ≤
      protectedLog (4 / figureOnePerSampleMixingError q) := le_max_left _ _
  nlinarith

theorem pow_121_div_128_safeRetryCount_le (q : VolumeParams) :
    ENNReal.ofReal (121 / 128 : ℝ) ^ figureOneSafeRetryCount q ≤
      figureOneCorrectedRetryTailBudget q := by
  let nu := figureOnePerSampleMixingError q
  let N := figureOneSafeRetryCount q
  have hnu : 0 < nu := figureOnePerSampleMixingError_pos q
  have hb : (121 / 128 : ℝ) ≤ Real.exp (-(1 / 128 : ℝ)) := by
    calc
      (121 / 128 : ℝ) ≤ 1 - 1 / 128 := by norm_num
      _ ≤ Real.exp (-(1 / 128 : ℝ)) := Real.one_sub_le_exp_neg _
  have hp : (121 / 128 : ℝ) ^ N ≤
      Real.exp (-(1 / 128 : ℝ)) ^ N :=
    pow_le_pow_left₀ (by norm_num) hb N
  have hN : 128 * Real.log (4 / nu) ≤ (N : ℝ) := by
    calc
      128 * Real.log (4 / nu) ≤
          128 * protectedLog (4 / nu) := by
        gcongr
        exact le_max_right _ _
      _ ≤ (N : ℝ) := by
        exact Nat.le_ceil _
  have hexp : Real.exp (-(N : ℝ) / 128) ≤ nu / 4 := by
    calc
      Real.exp (-(N : ℝ) / 128) ≤
          Real.exp (-Real.log (4 / nu)) := by
        rw [Real.exp_le_exp]
        nlinarith
      _ = nu / 4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 / nu)]
        field_simp
  have hreal : (121 / 128 : ℝ) ^ N ≤ nu / 4 := by
    calc
      (121 / 128 : ℝ) ^ N ≤
          Real.exp (-(1 / 128 : ℝ)) ^ N := hp
      _ = Real.exp (-(N : ℝ) / 128) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ nu / 4 := hexp
  unfold figureOneCorrectedRetryTailBudget
    figureOneCorrectedTransitionBudget
  change ENNReal.ofReal (121 / 128 : ℝ) ^ N ≤ ENNReal.ofReal nu / 4
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 121 / 128)]
  rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem figureOneSafeRetryTail_le (q : VolumeParams)
    {rejectMass : ENNReal}
    (hreject : rejectMass ≤ ENNReal.ofReal (121 / 128 : ℝ)) :
    rejectMass ^ (figureOneSafeRetryCount q - 1 + 1) ≤
      figureOneCorrectedRetryTailBudget q := by
  rw [Nat.sub_add_cancel (figureOneSafeRetryCount_pos q)]
  exact (pow_le_pow_left₀ bot_le hreject _).trans
    (pow_121_div_128_safeRetryCount_le q)

end ArlibCommunity.Algorithms.CV18
