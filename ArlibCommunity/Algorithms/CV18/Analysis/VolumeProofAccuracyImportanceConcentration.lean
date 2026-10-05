/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedySpectral

/-! # Concentration of executable CV18 importance phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Arlib.MarkovChains

/-- The successful output of the actual, query-bounded importance collector
inherits the warm-start spectral concentration of the lazy speedy chain.  One
query per observation is accounted for by the `proposalCap + samples` offset. -/
theorem bind_accuracyImportanceProgram_success_deviation_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap samples : ℕ)
    {mu : Measure (AmbientSpace q.n)}
    {M : ℝ≥0∞}
    (hwarm : Arlib.IsWarm M mu
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (m : ℝ)
    (hmean : ∫ x,
        (accuracyImportanceWeight q I sigma2 weight x - m)
        ∂ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2 = 0)
    (hmem : MemLp (fun x =>
        accuracyImportanceWeight q I sigma2 weight x - m) 2
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x,
      |accuracyImportanceWeight q I sigma2 weight x - m| ≤ B)
    {c : ℝ} (hc : 0 < c) :
    (mu.bind fun current =>
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap + samples) 1 samples current).runEstimate oracle.query)
      (optionSomeEvent {output | c ≤
        |output.1 - (samples : ℝ) * m|}) ≤
      M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap
          (lazy (speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
          (ellGaussianProb
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))⁻¹ *
          varianceReal
            (ellGaussianProb
              (accuracyPhaseTruncatedBody q I sigma2)
              (figureOneProposalRadius q sigma2) sigma2)
            (fun x => accuracyImportanceWeight q I sigma2 weight x - m)))) /
          c ^ 2) := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := lazy (speedyMetropolisGaussian K delta sigma2)
  let pi := ellGaussianProb K delta sigma2
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 := by
    dsimp [K]
    exact ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ := by
    dsimp [K]
    exact ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  obtain ⟨hrev, hpsd, hne⟩ := accuracyPhase_speedy_spectralFacts q I hsigma2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hphi : 0 < delta * Real.log 2 /
      (1280 * Real.sqrt sigma2 * Real.sqrt q.n) := by positivity
  have hgapLower :
      (delta * Real.log 2 /
        (1280 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2 / 2 ≤
        spectralGap P pi := by
    simpa [K, delta, P, pi] using
      accuracyPhase_speedy_spectralGap_ge q I hsigma2
  have hgap : 0 < spectralGap P pi :=
    (div_pos (sq_pos_of_pos hphi) (by norm_num : (0 : ℝ) < 2)).trans_le hgapLower
  have hrev1 : IsReversible (P ^ 1) pi := by simpa using hrev
  have hpsd1 : HasNonnegSpectrum (P ^ 1) pi := by simpa using hpsd
  have hne1 : (rayleighSet (P ^ 1) pi).Nonempty := by simpa using hne
  have hgap1 : 0 < spectralGap (P ^ 1) pi := by simpa using hgap
  have hlaw : (fun current =>
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap + samples) 1 samples current).runEstimate oracle.query) =
      fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux K
          (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2)
        (accuracyImportanceWeight q I sigma2 weight)
        proposalCap 1 samples current := by
    funext current
    simpa [K, delta] using
      cappedAccuracyProperCollectWeights_add_samples_semantics
        q I oracle hsigma2 hweight proposalCap 1 samples current
  rw [hlaw]
  have hmain := bind_cappedProperCollectLaw_success_deviation_le_of_isWarm
    K (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
    (measurable_accuracyImportanceWeight q I sigma2 hweight)
    proposalCap 1 samples hrev1 hpsd1 hne1 m hmean hmem hB hbound hgap1 hwarm hc
  simpa [K, delta, P, pi] using hmain

end ArlibCommunity.Algorithms.CV18
