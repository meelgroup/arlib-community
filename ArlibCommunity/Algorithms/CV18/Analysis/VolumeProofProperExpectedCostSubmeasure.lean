/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperExpectedCost

/-! # Proper-block cost from warm subprobability laws

Retry continuation laws are subprobabilities.  This version of the proper
clock estimate therefore keeps the endpoint-observation term multiplied by
the incoming mass, instead of assuming that every live law has mass one.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- Abstract subprobability form of the proper-clock expected-cost estimate.
It applies to any executable block whose pointwise counted cost is bounded by
the untruncated lazy-proper Bellman potential plus a fixed endpoint cost. -/
theorem lintegral_blockCost_le_of_isWarm
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpiK : pi Kᶜ = 0)
    (hinv : Kernel.Invariant (lazy (speedyMetropolisGaussian K delta s)) pi)
    {M : ENNReal} {mu : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : Arlib.IsWarm M mu pi)
    (properStride : ℕ) (endpointCost stationaryLocalMean : ENNReal)
    (hstationary :
      (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ stationaryLocalMean)
    (blockCost : EuclideanSpace ℝ (Fin n) → ENNReal)
    (hblock : ∀ current,
      blockCost current ≤
        totalLazyProperExpectedRawCost K hK delta s properStride current +
          endpointCost) :
    (∫⁻ current, blockCost current ∂mu) ≤
      (properStride : ENNReal) * (M * stationaryLocalMean) +
        endpointCost * mu Set.univ := by
  have hE := lintegral_totalLazyProperExpectedRawCost_le_of_isWarm
    K hK delta s pi hpiK hinv hwarm properStride
  calc
    (∫⁻ current, blockCost current ∂mu) ≤
        ∫⁻ current,
          totalLazyProperExpectedRawCost K hK delta s properStride current +
            endpointCost ∂mu := lintegral_mono hblock
    _ = (∫⁻ current,
          totalLazyProperExpectedRawCost K hK delta s properStride current ∂mu) +
        endpointCost * mu Set.univ := by
      rw [lintegral_add_left
        (measurable_totalLazyProperExpectedRawCost K hK delta s properStride),
        lintegral_const]
    _ ≤ (properStride : ENNReal) *
          (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) +
        endpointCost * mu Set.univ := by gcongr
    _ ≤ (properStride : ENNReal) * (M * stationaryLocalMean) +
        endpointCost * mu Set.univ := by gcongr

/-- Existing accuracy-body executable block, now integrated against an
arbitrary warm subprobability law. -/
theorem lintegral_cappedAccuracyProperCollectOne_countedQueryCost_le_of_isWarm_submeasure
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (weight : AmbientSpace q.n → ℝ) (hweight : Measurable weight)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (ellGaussianProb (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
          properStride 1 current).run oracle.query) ∂mu ≤
      (properStride : ENNReal) * (M * 2) + mu Set.univ := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let hKm : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hpoint : ∀ current, countedQueryCost
      ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
        properStride 1 current).run oracle.query) ≤
      totalLazyProperExpectedRawCost K hKm delta sigma2 properStride current + 1 := by
    intro current
    unfold cappedAccuracyProperCollectWeights
    simpa only [K, hKm, delta] using
      cappedAccuracyProperCollectOne_countedQueryCost_le
        q I oracle hsigma2 weight hweight properStride rawCap properStride 0 current
  have hlocal : (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ 2 := by
    have hKc : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
    have hKb : Bornology.IsBounded K :=
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
    have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
    have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
    have hZ0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
      ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 hdelta sigma2
    have hZtop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
      ellGaussianMeasure_ne_top_cv18
        (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
    have hlambda : ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ x in K, gaussianWeight sigma2 x) ≤
          ellGaussianMeasure K delta sigma2 Set.univ := by
      simpa only [K, delta] using
        half_mul_gaussianWeight_le_accuracyPhaseEllGaussian q I hsigma2
    have hhalf := mul_lintegral_inv_ell_ellGaussianProb_le_one
      hKm hdelta sigma2 hZ0 hZtop hlambda
    have hhalfEq : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [hhalfEq] at hhalf
    calc
      (∫⁻ current, (ell K delta current)⁻¹ ∂pi) =
          2 * ((2 : ENNReal)⁻¹ *
            ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel]
        · simp
        · norm_num
        · norm_num
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := mul_one _
  have h := lintegral_blockCost_le_of_isWarm K hKm delta sigma2 pi
    (ellGaussianProb_compl_eq_zero hKm delta sigma2)
    (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hKm delta sigma2)).invariant
    hwarm properStride 1 2 hlocal
    (fun current => countedQueryCost
      ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
        properStride 1 current).run oracle.query)) hpoint
  simpa [one_mul] using h

#print axioms lintegral_blockCost_le_of_isWarm
#print axioms
  lintegral_cappedAccuracyProperCollectOne_countedQueryCost_le_of_isWarm_submeasure

end ArlibCommunity.Algorithms.CV18
