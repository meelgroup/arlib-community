/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPairedRatio
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments

/-! # Schedule-specialized paired phase moments for CV18

The general paired KLS analysis is specialized here to the two Gaussian
cooling rates.  In both cases the complete executable numerator variance,
including accepted-law bias, is proportional to the same `factor - 1` charge
used by the ideal CV18 product proof.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- An accelerated paired numerator pays exactly the square-root
`sigma² / terminalVariance` scale. -/
theorem scheduleValue_accelerated_accuracyPairedNumerator_variance_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (_hsone : 1 < scheduleValue q k) :
    let s := scheduleValue q k
    let t := scheduleValue q (k + 1)
    let weight := gaussianRatioWeight (n := q.n) s t
    let mean := ∫ x, weight x
      ∂(truncatedGaussianProbability q I s (scheduleValue_pos q k) :
        Measure (AmbientSpace q.n))
    let R := Real.sqrt (s / terminalVariance q) * mean
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I s)
        (figureOneProposalRadius q s) s)
      (fun x => accuracyImportanceWeight q I s
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I s weight) x) ≤
      4 * (R ^ 2 + (67 * accuracyAcceptedBiasScale q * R) ^ 2) := by
  dsimp only
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q k)
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hmean : 0 < ∫ x, weight x ∂nu := by
    rw [show (∫ x, weight x ∂nu) =
        gaussianIntegral (truncatedBody q I) t /
          gaussianIntegral (truncatedBody q I) s by
      simpa [weight, nu, s, t] using
        gaussianRatioWeight_mean_eq q I hs]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I) ht)
      (gaussianIntegral_pos q (truncatedVolumeInput q I) hs)
  have hrelative :
      (∫ x, weight x ^ 2 ∂nu) / (∫ x, weight x ∂nu) ^ 2 ≤
        1 + s / terminalVariance q := by
    let T := terminalVariance q
    have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
    have hsT : s ≤ T := scheduleValue_le_terminal q k
    have htNext : t = nextVariance q s := by
      simpa [s, t] using scheduleValue_succ q k
    have hraw : t ≤ s * (1 + s / (2 * T)) := by
      rw [htNext]
      unfold nextVariance
      refine (min_le_right _ _).trans_eq ?_
      rw [coolingRate, if_neg]
      simpa [s, T] using not_le_of_gt _hsone
    simpa [weight, nu, s, t, T] using
      gaussianRatioWeight_accelerated_relativeSecondMoment_le_localized
        q I hs hst (by simpa [T] using hsT) (by simpa [T] using hraw)
  have hfactor : 1 < 1 + s / terminalVariance q := by
    have : 0 < s / terminalVariance q :=
      div_pos hs (terminalVariance_pos' q)
    linarith
  have hcontinuous : Continuous weight := by
    dsimp only [weight]
    unfold gaussianRatioWeight
    refine (by fun_prop : Continuous fun x : AmbientSpace q.n =>
      Real.exp (-‖x‖ ^ 2 / (2 * t))).div₀ (by fun_prop) ?_
    intro x
    exact Real.exp_ne_zero _
  have hmem : MemLp weight 2 nu := by
    simpa [weight, nu, s, t] using
      gaussianRatioWeight_memLp q I hs ht 2
  simpa [s, t, weight, nu] using
    varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_relativeSecondMoment_sharp
      q I hs hcontinuous hmem hfactor hmean hrelative

/-- A fixed-rate paired numerator pays the paper's `2/n` phase charge. -/
theorem scheduleValue_fixedRate_accuracyPairedNumerator_variance_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    let s := scheduleValue q k
    let t := scheduleValue q (k + 1)
    let weight := gaussianRatioWeight (n := q.n) s t
    let mean := ∫ x, weight x
      ∂(truncatedGaussianProbability q I s (scheduleValue_pos q k) :
        Measure (AmbientSpace q.n))
    let R := Real.sqrt (2 / (q.n : ℝ)) * mean
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I s)
        (figureOneProposalRadius q s) s)
      (fun x => accuracyImportanceWeight q I s
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I s weight) x) ≤
      4 * (R ^ 2 + (67 * accuracyAcceptedBiasScale q * R) ^ 2) := by
  dsimp only
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q k)
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hmean : 0 < ∫ x, weight x ∂nu := by
    rw [show (∫ x, weight x ∂nu) =
        gaussianIntegral (truncatedBody q I) t /
          gaussianIntegral (truncatedBody q I) s by
      simpa [weight, nu, s, t] using
        gaussianRatioWeight_mean_eq q I hs]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I) ht)
      (gaussianIntegral_pos q (truncatedVolumeInput q I) hs)
  have hrelative :
      (∫ x, weight x ^ 2 ∂nu) / (∫ x, weight x ∂nu) ^ 2 ≤
        1 + 2 / (q.n : ℝ) := by
    simpa [weight, nu, s, t] using
      scheduleValue_fixedRate_relativeSecondMoment_le q I k hsone
  have hfactor : 1 < 1 + 2 / (q.n : ℝ) := by
    have : 0 < (2 : ℝ) / (q.n : ℝ) := div_pos (by norm_num) hn
    linarith
  have hcontinuous : Continuous weight := by
    dsimp only [weight]
    unfold gaussianRatioWeight
    refine (by fun_prop : Continuous fun x : AmbientSpace q.n =>
      Real.exp (-‖x‖ ^ 2 / (2 * t))).div₀ (by fun_prop) ?_
    intro x
    exact Real.exp_ne_zero _
  have hmem : MemLp weight 2 nu := by
    simpa [weight, nu, s, t] using
      gaussianRatioWeight_memLp q I hs ht 2
  simpa [s, t, weight, nu] using
    varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_relativeSecondMoment_sharp
      q I hs hcontinuous hmem hfactor hmean hrelative

/-- The terminal Gaussian-to-uniform paired numerator pays only the constant
`exp(1/2) - 1` relative-moment charge. -/
theorem terminal_accuracyPairedNumerator_variance_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    let s := terminalVariance q
    let weight := uniformRatioWeight (n := q.n) s
    let mean := ∫ x, weight x
      ∂(truncatedGaussianProbability q I s (terminalVariance_pos' q) :
        Measure (AmbientSpace q.n))
    let R := Real.sqrt (Real.exp (1 / 2) - 1) * mean
    Arlib.MarkovChains.varianceReal
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I s)
        (figureOneProposalRadius q s) s)
      (fun x => accuracyImportanceWeight q I s
        (fun y => weight y -
          accuracyStationaryAcceptedMean q I s weight) x) ≤
      4 * (R ^ 2 + (67 * accuracyAcceptedBiasScale q * R) ^ 2) := by
  dsimp only
  let s := terminalVariance q
  let weight := uniformRatioWeight (n := q.n) s
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (terminalVariance_pos' q)
  have hs : 0 < s := terminalVariance_pos' q
  have hmean : 0 < ∫ x, weight x ∂nu := by
    have h := uniformRatioWeight_terminal_mean_one_le q I
    have : 1 ≤ ∫ x, weight x ∂nu := by
      simpa [weight, nu, s] using h
    linarith
  have hrelative :
      (∫ x, weight x ^ 2 ∂nu) / (∫ x, weight x ∂nu) ^ 2 ≤
        Real.exp (1 / 2) := by
    simpa [weight, nu, s] using
      uniformRatioWeight_terminal_relativeSecondMoment_le q I
  have hfactor : 1 < Real.exp (1 / 2) := by
    exact Real.one_lt_exp_iff.2 (by norm_num)
  have hcontinuous : Continuous weight := by
    dsimp only [weight]
    unfold uniformRatioWeight
    fun_prop
  have hmem : MemLp weight 2 nu := by
    simpa [weight, nu, s] using
      uniformRatioWeight_memLp q I hs 2
  simpa [s, weight, nu] using
    varianceReal_accuracyImportanceWeight_sub_acceptedMean_le_of_relativeSecondMoment_sharp
      q I hs hcontinuous hmem hfactor hmean hrelative

end ArlibCommunity.Algorithms.CV18
