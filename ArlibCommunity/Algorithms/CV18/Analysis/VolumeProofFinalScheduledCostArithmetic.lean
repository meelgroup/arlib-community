/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryShadowDomination
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledConcreteTransition
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Arithmetic envelopes for the final scheduled expected-cost proof -/

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal BigOperators

/-- The safe finite retry horizon is controlled by the same protected
logarithm that appears in the corrected scheduled mixing stride. -/
theorem figureOneSafeRetryCount_cast_le_correctedMixingLog
    (q : VolumeParams) :
    (figureOneSafeRetryCount q : ℝ) ≤
      129 * protectedLog
        (1 / figureOneCorrectedBlockMixingError q
          (figureOneSafeRetryCount q - 1)) := by
  let nu := figureOnePerSampleMixingError q
  let N := figureOneSafeRetryCount q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q (N - 1))
  have hnu : 0 < nu := by
    simpa [nu] using figureOnePerSampleMixingError_pos q
  have hNpos : 0 < N := by
    simpa [N] using figureOneSafeRetryCount_pos q
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hrawNonneg : 0 ≤ 128 * protectedLog (4 / nu) := by
    have : 1 ≤ protectedLog (4 / nu) := le_max_left _ _
    positivity
  have hceil : (N : ℝ) < 128 * protectedLog (4 / nu) + 1 := by
    simpa [N, figureOneSafeRetryCount, nu] using
      Nat.ceil_lt_add_one hrawNonneg
  have harg : 4 / nu ≤
      1 / figureOneCorrectedBlockMixingError q (N - 1) := by
    unfold figureOneCorrectedBlockMixingError
    change 4 / nu ≤ 1 / (nu / (4 * (((N - 1 : ℕ) : ℝ) + 1)))
    have hNcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
      exact_mod_cast Nat.sub_add_cancel hNpos
    rw [hNcast]
    rw [one_div_div]
    apply (div_le_div_iff_of_pos_right hnu).2
    nlinarith
  have hargPos : 0 < 4 / nu := by positivity
  have hprotected : protectedLog (4 / nu) ≤ B := by
    dsimp only [B, protectedLog]
    apply max_le_max_left
    exact Real.strictMonoOn_log.monotoneOn hargPos
      (hargPos.trans_le harg) harg
  have hBone : 1 ≤ B := by
    dsimp only [B, protectedLog]
    exact le_max_left _ _
  dsimp only [N, B, nu] at hceil hprotected hBone ⊢
  nlinarith

/-- The adjacent-speedy warmness factor is an absolute numerical constant. -/
theorem speedyAdjacentWarmConstant_le_twelve (q : VolumeParams) :
    speedyAdjacentWarmConstant q ≤ 12 := by
  unfold speedyAdjacentWarmConstant
  calc
    Real.exp (1 / 2) * (4 * Real.exp (1 / 2)) =
        4 * Real.exp 1 := by
      rw [show Real.exp (1 / 2) * (4 * Real.exp (1 / 2)) =
          4 * (Real.exp (1 / 2) * Real.exp (1 / 2)) by ring,
        ← Real.exp_add]
      norm_num
    _ ≤ 12 := by nlinarith [Real.exp_one_lt_three]

/-- Reciprocal-square envelope for the conductance denominator after the
scheduled proposal radius is substituted. -/
theorem figureOneScheduledMixingDenominator_inv_sq_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let d := figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)
    1 / d ^ 2 ≤
      10 ^ 14 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
        figureOneScheduledAccuracyLog q := by
  dsimp only
  let n : ℝ := q.n
  let A := figureOneScheduledAccuracyLog q
  let s := Real.sqrt sigma2
  let rn := Real.sqrt n
  let rA := Real.sqrt (n * A)
  let d := (min s 1 / (4096 * rA)) * Real.log 2 / (640 * s * rn)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hA : 1 ≤ A := by
    simpa [A] using figureOneScheduledAccuracyLog_one_le q
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.2 hsigma2
  have hrn : 0 < rn := by simpa [rn] using Real.sqrt_pos.2 hn
  have hrA : 0 < rA := by
    dsimp only [rA]
    positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  change 1 / d ^ 2 ≤ 10 ^ 14 * max 1 sigma2 * n ^ 2 * A
  rw [div_le_iff₀ (sq_pos_of_pos hd)]
  by_cases hsmall : sigma2 ≤ 1
  · have hsle : s ≤ 1 := by
      dsimp only [s]
      nlinarith [Real.sq_sqrt hsigma2.le,
        Real.sqrt_nonneg sigma2]
    have hmax : max 1 sigma2 = 1 := max_eq_left hsmall
    have hmin : min s 1 = s := min_eq_left hsle
    have hs2 : s ^ 2 = sigma2 := by
      simpa [s] using Real.sq_sqrt hsigma2.le
    have hrn2 : rn ^ 2 = n := by
      simpa [rn] using Real.sq_sqrt hn.le
    have hrA2 : rA ^ 2 = n * A := by
      simpa [rA] using Real.sq_sqrt
        (mul_nonneg hn.le (le_trans zero_le_one hA))
    have hcoef : (4096 : ℝ) ^ 2 * 640 ^ 2 ≤
        10 ^ 14 * Real.log 2 ^ 2 := by
      nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (sq_nonneg n) (le_trans zero_le_one hA))
    rw [hmax]
    dsimp only [d]
    rw [hmin]
    field_simp
    rw [hrA2, hrn2]
    nlinarith
  · have hone : 1 < sigma2 := lt_of_not_ge hsmall
    have hsone : 1 ≤ s := by
      dsimp only [s]
      nlinarith [Real.sq_sqrt hsigma2.le,
        Real.sqrt_nonneg sigma2]
    have hmax : max 1 sigma2 = sigma2 := max_eq_right hone.le
    have hmin : min s 1 = 1 := min_eq_right hsone
    have hs2 : s ^ 2 = sigma2 := by
      simpa [s] using Real.sq_sqrt hsigma2.le
    have hrn2 : rn ^ 2 = n := by
      simpa [rn] using Real.sq_sqrt hn.le
    have hrA2 : rA ^ 2 = n * A := by
      simpa [rA] using Real.sq_sqrt
        (mul_nonneg hn.le (le_trans zero_le_one hA))
    have hcoef : (4096 : ℝ) ^ 2 * 640 ^ 2 ≤
        10 ^ 14 * Real.log 2 ^ 2 := by
      nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hsigma2.le
        (mul_nonneg (sq_nonneg n) (le_trans zero_le_one hA)))
    rw [hmax]
    dsimp only [d]
    rw [hmin]
    field_simp
    rw [hrA2, hs2, hrn2]
    nlinarith

/-- The corrected scheduled proper stride has exactly one accuracy-log and
one corrected-mixing-log overhead over the legacy walk scale. -/
theorem figureOneScheduledCorrectedProperStride_cast_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let B := protectedLog
      (1 / figureOneCorrectedBlockMixingError q
        (figureOneSafeRetryCount q - 1))
    (figureOneScheduledCorrectedProperStride q sigma2
        (figureOneSafeRetryCount q - 1) : ℝ) ≤
      (9 * 10 ^ 16) * max 1 sigma2 * (q.n : ℝ) ^ 2 *
        protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
        figureOneScheduledAccuracyLog q * B := by
  dsimp only
  let attempts := figureOneSafeRetryCount q - 1
  let e := figureOneCorrectedBlockMixingError q attempts
  let B := protectedLog (1 / e)
  let A := figureOneScheduledAccuracyLog q
  let L := protectedLog ((q.n : ℝ) / q.eps)
  let X := max 1 sigma2 * (q.n : ℝ) ^ 2 * L ^ 2 * A
  let d := figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
    (640 * Real.sqrt sigma2 * Real.sqrt q.n)
  have he : 0 < e := by
    simpa [e, attempts] using figureOneCorrectedBlockMixingError_pos q attempts
  have hB : 1 ≤ B := by
    dsimp only [B, protectedLog]
    exact le_max_left _ _
  have hA : 1 ≤ A := by
    simpa [A] using figureOneScheduledAccuracyLog_one_le q
  have hL : 1 ≤ L := by
    dsimp only [L, protectedLog]
    exact le_max_left _ _
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hX : 1 ≤ X := by
    dsimp only [X]
    have hm : (1 : ℝ) ≤ max 1 sigma2 := le_max_left _ _
    have hn2 : 1 ≤ (q.n : ℝ) ^ 2 := one_le_pow₀ (by nlinarith)
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
      intro a b ha hb
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    exact hmul (hmul (hmul hm hn2) hL2) hA
  have hd : 0 < d := by
    dsimp only [d]
    positivity [figureOneScheduledProposalRadius_pos q hsigma2]
  have hinv : 1 / d ^ 2 ≤ 10 ^ 14 * X := by
    have h := figureOneScheduledMixingDenominator_inv_sq_le q hsigma2
    dsimp only at h
    dsimp only [d, X]
    let Y := 10 ^ 14 * max 1 sigma2 * (q.n : ℝ) ^ 2 * A
    have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
    calc
      1 / (figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
          (640 * Real.sqrt sigma2 * Real.sqrt ↑q.n)) ^ 2 ≤ Y := by
        simpa [Y, A] using h
      _ ≤ Y * L ^ 2 := by
        have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
        nlinarith [mul_nonneg hY0 (sub_nonneg.mpr hL2)]
      _ = 10 ^ 14 * (max 1 sigma2 * ↑q.n ^ 2 * L ^ 2 * A) := by
        dsimp only [Y]
        ring
  have hM : speedyAdjacentWarmConstant q ≤ 12 :=
    speedyAdjacentWarmConstant_le_twelve q
  have hMpos : 0 < speedyAdjacentWarmConstant q :=
    speedyAdjacentWarmConstant_pos q
  have hfirstLog : Real.log (16 * speedyAdjacentWarmConstant q) ≤ 191 := by
    calc
      Real.log (16 * speedyAdjacentWarmConstant q) ≤
          16 * speedyAdjacentWarmConstant q - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 191 := by nlinarith
  have hreLog : Real.log (1 / e) ≤ B := by
    dsimp only [B, protectedLog]
    exact le_max_right _ _
  have hfirstNum : Real.log (16 * speedyAdjacentWarmConstant q) +
      2 * Real.log (1 / e) ≤ 193 * B := by
    nlinarith
  have hretryNum : Real.log 2 + 2 * Real.log (1 / e) ≤ 3 * B := by
    have hlogTwo : Real.log 2 ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hfirstQuot :
      (Real.log (16 * speedyAdjacentWarmConstant q) +
          2 * Real.log (1 / e)) / d ^ 2 ≤
        193 * B * (10 ^ 14 * X) := by
    calc
      _ ≤ (193 * B) / d ^ 2 := by gcongr
      _ = (193 * B) * (1 / d ^ 2) := by ring
      _ ≤ 193 * B * (10 ^ 14 * X) := by gcongr
  have hretryQuot :
      (Real.log 2 + 2 * Real.log (1 / e)) / d ^ 2 ≤
        3 * B * (10 ^ 14 * X) := by
    calc
      _ ≤ (3 * B) / d ^ 2 := by gcongr
      _ = (3 * B) * (1 / d ^ 2) := by ring
      _ ≤ 3 * B * (10 ^ 14 * X) := by gcongr
  have hfirst :
      figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts ≤
        (8 * 10 ^ 16) * X * B := by
    rw [figureOneScheduledCorrectedFirstWalkRequirement_explicit]
    change 4 * ((Real.log (16 * speedyAdjacentWarmConstant q) +
      2 * Real.log (1 / e)) / d ^ 2) + 1 ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hB)]
  have hretry :
      figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts ≤
        (8 * 10 ^ 16) * X * B := by
    rw [figureOneScheduledCorrectedRetryWalkRequirement_explicit]
    change 4 * ((Real.log 2 + 2 * Real.log (1 / e)) / d ^ 2) + 1 ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hB)]
  have hrawNonneg : 0 ≤ max 1 (max
      (figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts)
      (figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hceil := Nat.ceil_lt_add_one hrawNonneg
  change (figureOneScheduledCorrectedProperStride q sigma2 attempts : ℝ) ≤ _
  unfold figureOneScheduledCorrectedProperStride
  have hmax : max 1 (max
      (figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts)
      (figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts)) ≤
      (8 * 10 ^ 16) * X * B := by
    apply max_le
    · nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hB)]
    · exact max_le hfirst hretry
  dsimp only [attempts] at hceil ⊢
  dsimp only [X, A, B, e, L] at hmax ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hB)]

/-- Relative to the legacy walk count, the final scheduled stride costs at
most nine times the two explicit logarithmic overheads. -/
theorem figureOneFinalScheduledStride_cast_le_walk
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let A := figureOneScheduledAccuracyLog q
    let B := protectedLog
      (1 / figureOneCorrectedBlockMixingError q
        (figureOneSafeRetryCount q - 1))
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2 : ℝ) ≤
      9 * A * B * (figureOneWalkSteps q sigma2 : ℝ) := by
  dsimp only [figureOneFinalScheduledBalancedParameters_properStride]
  let A := figureOneScheduledAccuracyLog q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q
      (figureOneSafeRetryCount q - 1))
  let raw := 10 ^ 16 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
    protectedLog ((q.n : ℝ) / q.eps) ^ 2
  have hstride := figureOneScheduledCorrectedProperStride_cast_le q hsigma2
  have hraw : raw ≤ (figureOneWalkSteps q sigma2 : ℝ) := by
    unfold figureOneWalkSteps
    exact Nat.le_ceil raw
  have hAB0 : 0 ≤ 9 * A * B := by
    have hA0 : 0 ≤ A := (figureOneScheduledAccuracyLog_one_le q).trans' zero_le_one
    have hB0 : 0 ≤ B := by
      dsimp only [B, protectedLog]
      exact zero_le_one.trans (le_max_left _ _)
    positivity
  calc
    (figureOneScheduledCorrectedProperStride q sigma2
        (figureOneSafeRetryCount q - 1) : ℝ) ≤
        (9 * A * B) * raw := by
      dsimp only [A, B, raw] at hstride ⊢
      nlinarith
    _ ≤ (9 * A * B) * (figureOneWalkSteps q sigma2 : ℝ) :=
      mul_le_mul_of_nonneg_left hraw hAB0
    _ = 9 * A * B * (figureOneWalkSteps q sigma2 : ℝ) := rfl

/-- The complete scheduled proper-stride work sum is the legacy Figure-One
work sum times only the two explicit logarithmic overheads. -/
theorem figureOneScheduledProperWork_cast_le_old
    (q : VolumeParams) :
    let A := figureOneScheduledAccuracyLog q
    let B := protectedLog
      (1 / figureOneCorrectedBlockMixingError q
        (figureOneSafeRetryCount q - 1))
    (figureOneScheduledProperWork q : ℝ) ≤
      9 * A * B *
        (figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q) : ℕ) := by
  dsimp only
  let A := figureOneScheduledAccuracyLog q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q
      (figureOneSafeRetryCount q - 1))
  rw [figureOneCoolingQueryBudget_explicit]
  unfold figureOneScheduledProperWork
  push_cast
  have hphase :
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
        (figureOnePhaseSampleCount q (scheduleValue q k) : ℝ) *
          (figureOneScheduledBalancedParameters.properStride q
            (scheduleValue q k) : ℝ)) ≤
      9 * A * B *
        ∑ k ∈ Finset.range (terminalPhaseSteps q),
          (figureOnePhaseSampleCount q (scheduleValue q k) : ℝ) *
            (figureOneWalkSteps q (scheduleValue q k) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hs := figureOneFinalScheduledStride_cast_le_walk q
      (scheduleValue_pos q k)
    dsimp only [A, B] at hs ⊢
    simp only [figureOneScheduledBalancedParameters_properStride,
      figureOneFinalScheduledBalancedParameters_properStride] at hs ⊢
    convert mul_le_mul_of_nonneg_left hs
      (Nat.cast_nonneg (figureOnePhaseSampleCount q (scheduleValue q k))) using 1 <;>
        ring
  have hterminal := figureOneFinalScheduledStride_cast_le_walk q
    (terminalVariance_pos' q)
  have hterminal' :
      (figureOneSampleCount q : ℝ) *
          (figureOneScheduledBalancedParameters.properStride q
            (terminalVariance q) : ℝ) ≤
        9 * A * B *
          ((figureOneSampleCount q : ℝ) *
            (figureOneWalkSteps q (terminalVariance q) : ℝ)) := by
    dsimp only [A, B] at hterminal ⊢
    simp only [figureOneScheduledBalancedParameters_properStride,
      figureOneFinalScheduledBalancedParameters_properStride] at hterminal ⊢
    calc
      (figureOneSampleCount q : ℝ) *
          (figureOneScheduledCorrectedProperStride q (terminalVariance q)
            (figureOneSafeRetryCount q - 1) : ℝ) ≤
        (figureOneSampleCount q : ℝ) *
          (9 * figureOneScheduledAccuracyLog q *
            protectedLog (1 / figureOneCorrectedBlockMixingError q
              (figureOneSafeRetryCount q - 1)) *
                (figureOneWalkSteps q (terminalVariance q) : ℝ)) :=
        mul_le_mul_of_nonneg_left hterminal (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ 9 * A * B *
          (∑ k ∈ Finset.range (terminalPhaseSteps q),
            (figureOnePhaseSampleCount q (scheduleValue q k) : ℝ) *
              (figureOneWalkSteps q (scheduleValue q k) : ℝ)) +
        9 * A * B *
          ((figureOneSampleCount q : ℝ) *
            (figureOneWalkSteps q (terminalVariance q) : ℝ)) :=
      add_le_add hphase hterminal'
    _ = _ := by ring

/-- Even charging the complete fixed retry horizon, the scheduled proper-step
work is bounded by a small absolute multiple of the scheduled soft-O rate.
This deliberately does not use a local proposal cap. -/
theorem figureOneSafeRetryCount_mul_scheduledProperWork_cast_le_sharp
    (q : VolumeParams) :
    ((figureOneSafeRetryCount q * figureOneScheduledProperWork q : ℕ) : ℝ) ≤
      (2322 * 10 ^ 24) * volumeScheduledBaseComplexityRate q := by
  let N := figureOneSafeRetryCount q
  let work := figureOneScheduledProperWork q
  let oldWork := figureOneCoolingQueryBudget q
      (explicitVolumeCoolingSchedule q).variances +
    figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q)
  let A := figureOneScheduledAccuracyLog q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q (N - 1))
  let base := volumeBaseComplexityRate q
  have hN : (N : ℝ) ≤ 129 * B := by
    simpa only [N, B] using
      figureOneSafeRetryCount_cast_le_correctedMixingLog q
  have hwork : (work : ℝ) ≤ 9 * A * B * (oldWork : ℝ) := by
    simpa only [work, oldWork, A, B, N] using
      figureOneScheduledProperWork_cast_le_old q
  have hbase : (oldWork : ℝ) ≤ (2 * 10 ^ 24) * base := by
    have hnat := figureOne_base_query_cost_sharp q
    have hcast : ((1 + oldWork : ℕ) : ℝ) ≤
        (Nat.ceil ((2 * 10 ^ 24) * base) : ℝ) := by
      exact_mod_cast hnat
    have hx : 0 ≤ (2 * 10 ^ 24) * base := by
      dsimp only [base]
      unfold volumeBaseComplexityRate
      positivity
    have hceil := Nat.ceil_lt_add_one hx
    push_cast at hcast
    linarith
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hwork0 : 0 ≤ (work : ℝ) := Nat.cast_nonneg _
  have hA0 : 0 ≤ A :=
    zero_le_one.trans (figureOneScheduledAccuracyLog_one_le q)
  have hB0 : 0 ≤ B := by
    dsimp only [B, protectedLog]
    exact zero_le_one.trans (le_max_left _ _)
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    unfold volumeBaseComplexityRate
    positivity
  calc
    ((N * work : ℕ) : ℝ) = (N : ℝ) * (work : ℝ) := by push_cast; rfl
    _ ≤ (129 * B) * (9 * A * B * (oldWork : ℝ)) := by
      exact mul_le_mul hN hwork hwork0 (by positivity)
    _ ≤ (129 * B) * (9 * A * B * ((2 * 10 ^ 24) * base)) := by
      gcongr
    _ = (2322 * 10 ^ 24) * volumeScheduledBaseComplexityRate q := by
      dsimp only [volumeScheduledBaseComplexityRate, base, A, B, N]
      ring

/-- Rounded decimal version of the sharp complete-retry work envelope. -/
theorem figureOneSafeRetryCount_mul_scheduledProperWork_cast_le
    (q : VolumeParams) :
    ((figureOneSafeRetryCount q * figureOneScheduledProperWork q : ℕ) : ℝ) ≤
      (3 * 10 ^ 27) * volumeScheduledBaseComplexityRate q := by
  calc
    _ ≤ (2322 * 10 ^ 24) * volumeScheduledBaseComplexityRate q :=
      figureOneSafeRetryCount_mul_scheduledProperWork_cast_le_sharp q
    _ ≤ (3 * 10 ^ 27) * volumeScheduledBaseComplexityRate q := by
      apply mul_le_mul_of_nonneg_right _
        (volumeScheduledBaseComplexityRate_pos q).le
      norm_num

/-- After multiplying by the worst scheduled warmness (`96`) and by the
factor two that absorbs each trial's endpoint queries, the full fixed-shadow
cost still fits below `9·10^29` times the scheduled rate. -/
theorem figureOneWarmShadowScheduledWork_cast_le
    (q : VolumeParams) :
    ((384 * (figureOneSafeRetryCount q * figureOneScheduledProperWork q) : ℕ) : ℝ) ≤
      (9 * 10 ^ 29) * volumeScheduledBaseComplexityRate q := by
  calc
    _ = 384 *
        ((figureOneSafeRetryCount q * figureOneScheduledProperWork q : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ 384 * ((2322 * 10 ^ 24) *
        volumeScheduledBaseComplexityRate q) := by
      gcongr
      exact figureOneSafeRetryCount_mul_scheduledProperWork_cast_le_sharp q
    _ ≤ (9 * 10 ^ 29) * volumeScheduledBaseComplexityRate q := by
      have hrate := (volumeScheduledBaseComplexityRate_pos q).le
      nlinarith

/-- The one-query initializer plus the complete warm chronological shadow
still fits strictly inside the `9·10^29` reference-cost allowance. -/
theorem one_add_figureOneWarmShadowScheduledWork_le
    (q : VolumeParams) :
    (1 : ENNReal) +
        ((384 * (figureOneSafeRetryCount q *
          figureOneScheduledProperWork q) : ℕ) : ENNReal) ≤
      ENNReal.ofReal ((9 * 10 ^ 29) *
        volumeScheduledBaseComplexityRate q) := by
  have hmain :=
    figureOneSafeRetryCount_mul_scheduledProperWork_cast_le_sharp q
  have hrate := volumeScheduledBaseComplexityRate_one_le q
  have hmain' :
      ((384 * (figureOneSafeRetryCount q *
        figureOneScheduledProperWork q) : ℕ) : ℝ) ≤
        384 * ((2322 * 10 ^ 24) *
          volumeScheduledBaseComplexityRate q) := by
    calc
      _ = 384 * ((figureOneSafeRetryCount q *
          figureOneScheduledProperWork q : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := by gcongr
  have hreal :
      (1 : ℝ) +
          ((384 * (figureOneSafeRetryCount q *
            figureOneScheduledProperWork q) : ℕ) : ℝ) ≤
        (9 * 10 ^ 29) * volumeScheduledBaseComplexityRate q := by
    nlinarith
  have hofReal := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
    (Nat.cast_nonneg _), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast] at hofReal
  exact hofReal

/-- The apparently large local cap has the paper's essential cancellation:
after multiplication by one corrected block-error budget, its ceiling costs
only an absolute constant times the scheduled stride. -/
theorem figureOneFinalScheduledLocalCapCeil_mul_blockError_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let attempts := figureOneSafeRetryCount q - 1
    let e := figureOneCorrectedBlockMixingError q attempts
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    (Nat.ceil (figureOneFinalScheduledLocalCapRequirement q sigma2) : ℝ) * e ≤
      385 * stride := by
  dsimp only
  let attempts := figureOneSafeRetryCount q - 1
  let e := figureOneCorrectedBlockMixingError q attempts
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let requirement := figureOneFinalScheduledLocalCapRequirement q sigma2
  have he : 0 < e := by
    simpa [e, attempts] using figureOneCorrectedBlockMixingError_pos q attempts
  have heone : e ≤ 1 := by
    simpa [e, attempts] using figureOneCorrectedBlockMixingError_le_one q attempts
  have hstrideNat : 0 < stride := by
    simpa [stride] using figureOneScheduledCorrectedProperStride_pos q sigma2
      (figureOneSafeRetryCount q - 1)
  have hstride : (1 : ℝ) ≤ stride := by exact_mod_cast hstrideNat
  have hM := speedyAdjacentWarmConstant_le_twelve q
  have hreq0 : 0 ≤ requirement := by
    dsimp only [requirement, figureOneFinalScheduledLocalCapRequirement]
    positivity [speedyAdjacentWarmConstant_pos q]
  have hceil := Nat.ceil_lt_add_one hreq0
  have hmul : (Nat.ceil requirement : ℝ) * e < (requirement + 1) * e :=
    mul_lt_mul_of_pos_right hceil he
  have hcancel : requirement * e =
      32 * speedyAdjacentWarmConstant q * (stride : ℝ) := by
    dsimp only [requirement, figureOneFinalScheduledLocalCapRequirement,
      stride, e, attempts]
    rw [div_mul_cancel₀ _ (figureOneCorrectedBlockMixingError_pos q _).ne']
    simp only [figureOneFinalScheduledBalancedParameters_properStride]
    ring
  dsimp only [requirement, e, attempts, stride] at hmul hcancel ⊢
  rw [add_mul, hcancel] at hmul
  nlinarith

/-- Including the global-budget prefix and the two endpoint queries, one
block-error charge splits into the global budget times that small error plus
`387` scheduled strides. -/
theorem figureOneFinalScheduledProposalCap_add_two_mul_blockError_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let attempts := figureOneSafeRetryCount q - 1
    let e := figureOneCorrectedBlockMixingError q attempts
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    ((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 : ℕ) : ℝ) * e ≤
      (figureOneFinalScheduledQueryBudget q : ℝ) * e + 387 * stride := by
  dsimp only
  let attempts := figureOneSafeRetryCount q - 1
  let e := figureOneCorrectedBlockMixingError q attempts
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  have hceil := figureOneFinalScheduledLocalCapCeil_mul_blockError_le q hsigma2
  have he : 0 < e := by
    simpa [e, attempts] using figureOneCorrectedBlockMixingError_pos q attempts
  have heone : e ≤ 1 := by
    simpa [e, attempts] using figureOneCorrectedBlockMixingError_le_one q attempts
  have hstrideNat : 0 < stride := by
    simpa [stride] using figureOneScheduledCorrectedProperStride_pos q sigma2
      (figureOneSafeRetryCount q - 1)
  have hstride : (1 : ℝ) ≤ stride := by exact_mod_cast hstrideNat
  simp only [figureOneFinalScheduledBalancedParameters_proposalCap,
    figureOneFinalScheduledLocalProposalCap]
  push_cast
  dsimp only [e, attempts, stride] at hceil ⊢
  nlinarith

/-- At the final retry horizon, the scheduled stationary-target quarter is
exactly one block budget per possible trial.  This is the arithmetic identity
that makes charging a target-replacement submeasure compatible with the large
local syntactic cap: the cap is multiplied by the small block error before the
retry factor is introduced. -/
theorem figureOneCorrectedTargetBudget_eq_safeRetryCount_nsmul_blockBudget
    (q : VolumeParams) :
    figureOneCorrectedTargetBudget q =
      figureOneSafeRetryCount q •
        figureOneCorrectedBlockBudget q (figureOneSafeRetryCount q - 1) := by
  let N := figureOneSafeRetryCount q
  have hN : 0 < N := by
    simpa [N] using figureOneSafeRetryCount_pos q
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  unfold figureOneCorrectedTargetBudget figureOneCorrectedTransitionBudget
    figureOneCorrectedBlockBudget figureOneCorrectedBlockMixingError
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by norm_num))
    (by
      rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (by simp) (by simp))).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hnu.le,
    ENNReal.toReal_ofNat, ENNReal.toReal_nsmul]
  simp only [nsmul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity :
    0 ≤ figureOnePerSampleMixingError q /
      (4 * (((figureOneSafeRetryCount q - 1 : ℕ) : ℝ) + 1)))]
  have hNcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
    exact_mod_cast Nat.sub_add_cancel hN
  dsimp only [N] at hNcast ⊢
  rw [hNcast]
  have hN0 : (figureOneSafeRetryCount q : ℝ) ≠ 0 := by
    exact_mod_cast hN.ne'
  field_simp [hN0]

/-- `ENNReal` form of the local-cap cancellation, ready for use in the
expected-cost integral. -/
theorem figureOneFinalScheduledProposalCap_add_two_mul_blockBudget_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let attempts := figureOneSafeRetryCount q - 1
    let block := figureOneCorrectedBlockBudget q attempts
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    ((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 : ℕ) :
        ENNReal) * block ≤
      (figureOneFinalScheduledQueryBudget q : ENNReal) * block +
        387 * (stride : ENNReal) := by
  dsimp only
  let attempts := figureOneSafeRetryCount q - 1
  let e := figureOneCorrectedBlockMixingError q attempts
  have he : 0 < e := figureOneCorrectedBlockMixingError_pos q attempts
  have hreal :=
    figureOneFinalScheduledProposalCap_add_two_mul_blockError_le q hsigma2
  have hblockTop : figureOneCorrectedBlockBudget q attempts ≠ ∞ := by
    simp [figureOneCorrectedBlockBudget]
  have hleftTop :
      ((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 :
        ℕ) : ENNReal) * figureOneCorrectedBlockBudget q attempts ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hblockTop
  have hbudgetTop :
      (figureOneFinalScheduledQueryBudget q : ENNReal) *
        figureOneCorrectedBlockBudget q attempts ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hblockTop
  have hstrideTop :
      387 * (figureOneFinalScheduledBalancedParameters.properStride q sigma2 :
        ENNReal) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (by simp)
  apply (ENNReal.toReal_le_toReal hleftTop
    (ENNReal.add_ne_top.2 ⟨hbudgetTop, hstrideTop⟩)).mp
  simp only [figureOneCorrectedBlockBudget]
  have hbudgetTop' :
      (figureOneFinalScheduledQueryBudget q : ENNReal) *
        ENNReal.ofReal (figureOneCorrectedBlockMixingError q attempts) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal he.le,
    ENNReal.toReal_add hbudgetTop' hstrideTop,
    ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal he.le,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  simpa only [attempts, e] using hreal

/-- Charging the complete scheduled stationary-target replacement at a
phase start costs only the retry factor times the cap-cancelled block bound.
In particular, this term has no inverse transition-error factor. -/
theorem figureOneFinalScheduledProposalCap_mul_stationaryTargetError_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let attempts := figureOneSafeRetryCount q - 1
    let block := figureOneCorrectedBlockBudget q attempts
    let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
    ((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 : ℕ) :
        ENNReal) * scheduledBalancedStationaryTargetError q ≤
      figureOneSafeRetryCount q •
        ((figureOneFinalScheduledQueryBudget q : ENNReal) * block +
          387 * (stride : ENNReal)) := by
  dsimp only
  calc
    _ ≤ ((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 :
          ℕ) : ENNReal) * figureOneCorrectedTargetBudget q := by
      gcongr
      exact scheduledBalancedStationaryTargetError_le_targetBudget q
    _ = figureOneSafeRetryCount q •
        (((figureOneFinalScheduledBalancedParameters.proposalCap q sigma2 + 2 :
            ℕ) : ENNReal) *
          figureOneCorrectedBlockBudget q (figureOneSafeRetryCount q - 1)) := by
      rw [figureOneCorrectedTargetBudget_eq_safeRetryCount_nsmul_blockBudget]
      simp only [nsmul_eq_mul]
      ring
    _ ≤ figureOneSafeRetryCount q •
        ((figureOneFinalScheduledQueryBudget q : ENNReal) *
            figureOneCorrectedBlockBudget q (figureOneSafeRetryCount q - 1) +
          387 * (figureOneFinalScheduledBalancedParameters.properStride q sigma2 :
            ENNReal)) := by
      gcongr
      exact figureOneFinalScheduledProposalCap_add_two_mul_blockBudget_le
        q hsigma2

#print axioms figureOneSafeRetryCount_cast_le_correctedMixingLog
#print axioms figureOneScheduledMixingDenominator_inv_sq_le
#print axioms figureOneScheduledCorrectedProperStride_cast_le
#print axioms figureOneScheduledProperWork_cast_le_old
#print axioms figureOneSafeRetryCount_mul_scheduledProperWork_cast_le_sharp
#print axioms figureOneSafeRetryCount_mul_scheduledProperWork_cast_le
#print axioms figureOneWarmShadowScheduledWork_cast_le
#print axioms one_add_figureOneWarmShadowScheduledWork_le
#print axioms figureOneFinalScheduledLocalCapCeil_mul_blockError_le
#print axioms figureOneFinalScheduledProposalCap_add_two_mul_blockError_le
#print axioms
  figureOneCorrectedTargetBudget_eq_safeRetryCount_nsmul_blockBudget
#print axioms
  figureOneFinalScheduledProposalCap_add_two_mul_blockBudget_le
#print axioms
  figureOneFinalScheduledProposalCap_mul_stationaryTargetError_le

end ArlibCommunity.Algorithms.CV18
