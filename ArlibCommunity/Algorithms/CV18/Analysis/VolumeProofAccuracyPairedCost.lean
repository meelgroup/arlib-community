/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPairedPhases
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedySpectral

/-! # Explicit spectral cost for paired CV18 phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open Arlib MarkovChains

/-- The min/max cancellation behind the uniform inverse-gap estimate. -/
theorem figureOneProposalRadius_sq_mul_max_eq
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ^ 2 * max 1 sigma2 =
      sigma2 /
        (4096 ^ 2 * (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps)) := by
  let n : ℝ := q.n
  let L : ℝ := protectedLog (n / q.eps)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLone : 1 ≤ L := le_max_left _ _
  have hnL : 0 ≤ n * L := (mul_pos hn hL).le
  have hsqrtDen : (Real.sqrt (n * L)) ^ 2 = n * L :=
    Real.sq_sqrt hnL
  by_cases hsone : sigma2 ≤ 1
  · have hsqrtOne : Real.sqrt sigma2 ≤ 1 :=
      Real.sqrt_le_one.mpr hsone
    rw [figureOneProposalRadius, min_eq_left hsqrtOne,
      max_eq_left hsone, mul_one, div_pow,
      Real.sq_sqrt hsigma2.le]
    dsimp [n, L] at hsqrtDen ⊢
    rw [mul_pow, hsqrtDen]
    field_simp
  · have hone : 1 < sigma2 := lt_of_not_ge hsone
    have hsqrtOne : 1 ≤ Real.sqrt sigma2 :=
      Real.one_le_sqrt.mpr hone.le
    rw [figureOneProposalRadius, min_eq_right hsqrtOne,
      max_eq_right hone.le, one_div, inv_pow]
    dsimp [n, L] at hsqrtDen ⊢
    rw [mul_pow, hsqrtDen]
    field_simp

/-- The large walk-step constant already present in Figure 1 dominates the
inverse spectral gap of one retained proper-step trajectory. -/
theorem accuracyPhase_speedy_inverseSpectralGap_le_figureOneWalkSteps
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (spectralGap
      (lazy (speedyMetropolisGaussian
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))⁻¹ ≤
      (figureOneWalkSteps q sigma2 : ℝ) := by
  let n : ℝ := q.n
  let L : ℝ := protectedLog (n / q.eps)
  let delta := figureOneProposalRadius q sigma2
  let gap := spectralGap
    (lazy (speedyMetropolisGaussian
      (accuracyPhaseTruncatedBody q I sigma2) delta sigma2))
    (ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2) delta sigma2)
  let lower :=
    (delta * Real.log 2 /
      (1280 * Real.sqrt sigma2 * Real.sqrt n)) ^ 2 / 2
  let raw := 10 ^ 16 * max 1 sigma2 * n ^ 2 * L ^ 2
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLone : 1 ≤ L := le_max_left _ _
  have hdelta : 0 < delta := by
    simpa [delta] using figureOneProposalRadius_pos q hsigma2
  have hlog : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hsqrts : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hlowerGap : lower ≤ gap := by
    simpa [lower, gap, delta, n] using
      accuracyPhase_speedy_spectralGap_ge q I hsigma2
  have hinv : gap⁻¹ ≤ lower⁻¹ := by
    exact (inv_le_inv₀ (hlower.trans_le hlowerGap) hlower).2 hlowerGap
  have hdeltaSq := figureOneProposalRadius_sq_mul_max_eq q hsigma2
  have hsqrtS : (Real.sqrt sigma2) ^ 2 = sigma2 :=
    Real.sq_sqrt hsigma2.le
  have hsqrtN : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have hrawLower : 1 ≤ lower * raw := by
    have heq : lower * raw =
        (10 ^ 16 : ℝ) * (Real.log 2) ^ 2 * L /
          (2 * 1280 ^ 2 * 4096 ^ 2) := by
      dsimp [lower, raw]
      have hdenSq :
          (1280 * Real.sqrt sigma2 * Real.sqrt n) ^ 2 =
            1280 ^ 2 * sigma2 * n := by
        rw [mul_pow, mul_pow, hsqrtS, hsqrtN]
      rw [div_pow, show (delta * Real.log 2) ^ 2 =
          delta ^ 2 * (Real.log 2) ^ 2 by ring, hdenSq]
      have hdeltaSq' : delta ^ 2 * max 1 sigma2 =
          sigma2 / (4096 ^ 2 * n * L) := by
        simpa [delta, n, L] using hdeltaSq
      field_simp [hsigma2.ne', hn.ne', hL.ne', hdelta.ne'] at hdeltaSq' ⊢
      nlinarith
    rw [heq]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) <
      2 * 1280 ^ 2 * 4096 ^ 2)).2
    have hlogSq : (1 / 4 : ℝ) < (Real.log 2) ^ 2 := by nlinarith
    have hconst : (2 * 1280 ^ 2 * 4096 ^ 2 : ℝ) ≤
        10 ^ 16 * (1 / 4 : ℝ) := by norm_num
    have hlogProd : (1 / 4 : ℝ) ≤ (Real.log 2) ^ 2 * L := by
      calc
        (1 / 4 : ℝ) ≤ (Real.log 2) ^ 2 := hlogSq.le
        _ = (Real.log 2) ^ 2 * 1 := by ring
        _ ≤ (Real.log 2) ^ 2 * L :=
          mul_le_mul_of_nonneg_left hLone (sq_nonneg _)
    simpa [mul_assoc] using hconst.trans
      (mul_le_mul_of_nonneg_left hlogProd (by norm_num))
  have hlowerInvRaw : lower⁻¹ ≤ raw := by
    rw [inv_le_iff_one_le_mul₀' hlower]
    exact hrawLower
  have hrawCeil : raw ≤ (figureOneWalkSteps q sigma2 : ℝ) := by
    dsimp [raw, n, L, figureOneWalkSteps]
    exact Nat.le_ceil _
  exact hinv.trans (hlowerInvRaw.trans hrawCeil)

/-! ## Executable paired primitive counts -/

/-- Correlated observations per Gaussian phase.  The first factor pays the
inverse spectral gap; the second is exactly the paper's empirical count. -/
noncomputable def accuracyPairedPhaseSampleCount
    (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  figureOneWalkSteps q sigma2 * figureOnePhaseSampleCount q sigma2

/-- Correlated observations in the terminal Gaussian-to-uniform phase. -/
noncomputable def accuracyPairedTerminalSampleCount
    (q : VolumeParams) : ℕ :=
  figureOneWalkSteps q (terminalVariance q) * figureOneSampleCount q

/-- A deliberately generous syntax-level retry cutoff.  The outer global
query cap controls worst-case execution; this local cutoff only makes every
proper-step collector a finite oracle syntax tree. -/
noncomputable def accuracyPairedProposalCap
    (q : VolumeParams) (samples : ℕ) : ℕ :=
  2 ^ 20 * samples * (terminalPhaseSteps q + 1)

theorem figureOneWalkSteps_pos (q : VolumeParams) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) : 0 < figureOneWalkSteps q sigma2 := by
  apply Nat.ceil_pos.mpr
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 0 < protectedLog ((q.n : ℝ) / q.eps) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem figureOnePhaseSampleCount_pos (q : VolumeParams) (sigma2 : ℝ) :
    0 < figureOnePhaseSampleCount q sigma2 := by
  unfold figureOnePhaseSampleCount
  split_ifs
  · exact figureOneFixedSampleCount_pos q
  · exact figureOneSampleCount_pos q

theorem accuracyPairedPhaseSampleCount_pos
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < accuracyPairedPhaseSampleCount q sigma2 := by
  exact Nat.mul_pos (figureOneWalkSteps_pos q hsigma2)
    (figureOnePhaseSampleCount_pos q sigma2)

theorem accuracyPairedTerminalSampleCount_pos (q : VolumeParams) :
    0 < accuracyPairedTerminalSampleCount q := by
  exact Nat.mul_pos (figureOneWalkSteps_pos q (terminalVariance_pos' q))
    (figureOneSampleCount_pos q)

/-- Postprocessing of a paired Gaussian-phase sum. -/
noncomputable def accuracyPairedRatioOutput {n : ℕ} :
    Option ((ℝ × ℝ) × AmbientSpace n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some (totals, last) =>
      if totals.2 = 0 then none else some (totals.1 / totals.2, last)

/-- Postprocessing of the terminal paired sum. -/
noncomputable def accuracyPairedUniformOutput {n : ℕ} :
    Option ((ℝ × ℝ) × AmbientSpace n) → Option ℝ
  | none => none
  | some (totals, _) =>
      if totals.2 = 0 then none else some (totals.1 / totals.2)

/-- Paired self-normalized ratio estimator for one Gaussian transition. -/
noncomputable def accuracyPairedRatioEstimate (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  let samples := accuracyPairedPhaseSampleCount q sigma2
  let proposalCap := accuracyPairedProposalCap q samples
  (cappedAccuracyProperCollectPairs q sigma2
      (gaussianRatioWeight sigma2 tau2)
      (proposalCap + samples) 1 samples current).bind fun result =>
    .pure (accuracyPairedRatioOutput result)

/-- Paired self-normalized terminal Gaussian-to-uniform estimator. -/
noncomputable def accuracyPairedUniformRatioEstimate (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  let samples := accuracyPairedTerminalSampleCount q
  let proposalCap := accuracyPairedProposalCap q samples
  (cappedAccuracyProperCollectPairs q sigma2
      (uniformRatioWeight sigma2)
      (proposalCap + samples) 1 samples current).bind fun result =>
    .pure (accuracyPairedUniformOutput result)

/-- Concrete CV18 primitive package whose empirical ratios are taken from
shared numerator-denominator speedy trajectories. -/
noncomputable def accuracyPairedPrimitives : VolumeCoolingPrimitives where
  initialSample := figureOneInitialSample
  ratioEstimate := accuracyPairedRatioEstimate
  uniformRatioEstimate := accuracyPairedUniformRatioEstimate

end ArlibCommunity.Algorithms.CV18
