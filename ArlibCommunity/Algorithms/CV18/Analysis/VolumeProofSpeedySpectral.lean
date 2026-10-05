import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovVariance

/-! # A spectral package for the executable CV18 speedy phase kernel -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal
open Arlib MarkovChains

/-- The reversible, nonnegative-spectrum and nondegeneracy facts needed by
the dependent Markov-sum estimate, specialized to an accuracy phase. -/
theorem accuracyPhase_speedy_spectralFacts
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := lazy (speedyMetropolisGaussian K delta sigma2)
    let pi := ellGaussianProb K delta sigma2
    IsReversible P pi ∧ HasNonnegSpectrum P pi ∧
      (rayleighSet P pi).Nonempty := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
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
  have hbase : IsReversible (speedyMetropolisGaussian K delta sigma2) pi := by
    dsimp [pi, K, delta]
    exact isReversible_speedyMetropolisGaussian_prob
      (accuracyPhaseTruncatedBody_measurable q I sigma2) _ _
  have hrev : IsReversible (lazy (speedyMetropolisGaussian K delta sigma2)) pi :=
    isReversible_lazy hbase
  have hpsd : HasNonnegSpectrum
      (lazy (speedyMetropolisGaussian K delta sigma2)) pi :=
    hasNonnegSpectrum_lazy hbase
  obtain ⟨S, hS, hSpos, hShalf⟩ :=
    exists_smallSet_of_absolutelyContinuous (n := q.n)
      (le_trans (by norm_num : 1 ≤ 3) q.dim_ok) pi
      (by
        dsimp [pi]
        exact ellGaussianProb_absolutelyContinuous K delta sigma2)
  exact ⟨hrev, hpsd,
    rayleighSet_nonempty_of_smallSet
      (lazy (speedyMetropolisGaussian K delta sigma2)) hS hSpos hShalf⟩

/-- Cheeger's inequality turns the already-proved CV18 conductance estimate
into the explicit spectral-gap lower bound used for dependent empirical
averages.  Laziness accounts for the factor two inside the square. -/
theorem accuracyPhase_speedy_spectralGap_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := lazy (speedyMetropolisGaussian K delta sigma2)
    let pi := ellGaussianProb K delta sigma2
    (delta * Real.log 2 /
        (1280 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2 / 2 ≤
      spectralGap P pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := lazy (speedyMetropolisGaussian K delta sigma2)
  let pi := ellGaussianProb K delta sigma2
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
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
  obtain ⟨hrev, hpsd, hne⟩ :=
    accuracyPhase_speedy_spectralFacts q I hsigma2
  have hplain : ENNReal.ofReal
        (delta * Real.log 2 / (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ≤
      conductance (speedyMetropolisGaussian K delta sigma2) pi := by
    have h := conductance_speedyMetropolisGaussian_ge_radiusStepProduct_cv18
      (le_trans (by norm_num : 2 ≤ 3) q.dim_ok) hsigma hdelta
      (figureOneProposalRadius_le_sigma_div_eight_sqrt q hsigma2)
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      (accuracyPhaseRadius_pos q hsigma2).le
      (fun _ hx => accuracyPhaseTruncatedBody_norm_le q I hx)
      (by simpa [delta, Real.sq_sqrt hsigma2.le] using
        accuracyPhaseRadius_mul_figureOneProposalRadius_le q hsigma2)
    simpa [K, delta, pi, Real.sq_sqrt hsigma2.le] using h
  have hlazy : ENNReal.ofReal
        (delta * Real.log 2 /
          (1280 * Real.sqrt sigma2 * Real.sqrt q.n)) ≤ conductance P pi := by
    have hhalf := ofReal_half_le_conductance_lazy hplain
    simpa only [P, show
      delta * Real.log 2 / (640 * Real.sqrt sigma2 * Real.sqrt q.n) / 2 =
        delta * Real.log 2 / (1280 * Real.sqrt sigma2 * Real.sqrt q.n) by ring]
      using hhalf
  have hctop : conductance P pi ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (conductance_le_one P pi (by
        obtain ⟨S, hS, hSpos, hShalf⟩ :=
          exists_smallSet_of_absolutelyContinuous (n := q.n)
            (le_trans (by norm_num : 1 ≤ 3) q.dim_ok) pi
            (by
              dsimp [pi]
              exact ellGaussianProb_absolutelyContinuous K delta sigma2)
        exact ⟨S, hS, hSpos, hShalf⟩))
  have hphi0 : 0 ≤ delta * Real.log 2 /
      (1280 * Real.sqrt sigma2 * Real.sqrt q.n) := by positivity
  have hreal : delta * Real.log 2 /
        (1280 * Real.sqrt sigma2 * Real.sqrt q.n) ≤
      (conductance P pi).toReal := by
    have := ENNReal.toReal_mono hctop hlazy
    rwa [ENNReal.toReal_ofReal hphi0] at this
  exact (div_le_div_of_nonneg_right
      (sq_le_sq₀ hphi0 ENNReal.toReal_nonneg |>.2 hreal)
      (by norm_num : (0 : ℝ) ≤ 2)).trans
    (sq_conductance_div_two_le_spectralGap hrev hne)

end ArlibCommunity.Algorithms.CV18
