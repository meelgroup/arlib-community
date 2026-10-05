/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryShadowDomination

/-! # Warm-plus-error expected cost for a scheduled retry collector -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- A complete finite retry collector keeps the cap-independent shadow bound
on its warm component.  Only the explicitly separated error submeasure is
charged at the syntactic local query budget. -/
theorem lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_le_warm_add
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M error : ENNReal}
    {mu good bad : Measure (AmbientSpace q.n)}
    (hle : mu ≤ good + bad)
    (hwarm : _root_.Arlib.IsWarm M good
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hbad : bad Set.univ ≤ error)
    (proposalCap properStride retryLimit samples : ℕ) :
    ∫⁻ current, countedQueryCost
        ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
          properStride retryLimit samples current).run oracle.query) ∂mu ≤
      ((samples * retryLimit : ℕ) : ENNReal) *
          ((properStride : ENNReal) * (M * 2) + 2 * M) +
        ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) * error := by
  let cost : AmbientSpace q.n → ENNReal := fun current => countedQueryCost
    ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
      properStride retryLimit samples current).run oracle.query)
  have hgood : ∫⁻ current, cost current ∂good ≤
      ((samples * retryLimit : ℕ) : ENNReal) *
        ((properStride : ENNReal) * (M * 2) + 2 * M) := by
    simpa only [cost] using
      lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_isWarm
        q I oracle hsigma2 hweight hwarm proposalCap properStride retryLimit samples
  have hpoint : ∀ current, cost current ≤
      ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) := by
    intro current
    dsimp only [cost]
    simpa only [countedQueryCost] using
      (scheduledBalancedAccuracyRetryCollect_queryBound q sigma2 weight proposalCap
        properStride retryLimit samples current).lintegral_queryCount_le
        ((scheduledBalancedAccuracyRetryCollect_countedMeasurable q I oracle hsigma2
          hweight proposalCap properStride retryLimit samples).2 current)
  have hbadCost : ∫⁻ current, cost current ∂bad ≤
      ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) * error := by
    calc
      _ ≤ ∫⁻ _current,
          ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) ∂bad :=
        lintegral_mono hpoint
      _ = ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) *
          bad Set.univ := by rw [lintegral_const]
      _ ≤ ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) *
          error := by gcongr
  calc
    (∫⁻ current, cost current ∂mu) ≤ ∫⁻ current, cost current ∂(good + bad) :=
      lintegral_mono' hle le_rfl
    _ = (∫⁻ current, cost current ∂good) + ∫⁻ current, cost current ∂bad :=
      lintegral_add_measure _ _ _
    _ ≤ _ := add_le_add hgood hbadCost

/-- Numerical specialization used by the final schedule.  A warmness factor
at most `96` and a nonzero stride turn the complete live collector cost into
`384 · samples · retries · stride`; the separated error charge is unchanged. -/
theorem lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_finalEnvelope
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M error : ENNReal}
    {mu good bad : Measure (AmbientSpace q.n)}
    (hle : mu ≤ good + bad)
    (hwarm : _root_.Arlib.IsWarm M good
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hM : M ≤ 96) (hbad : bad Set.univ ≤ error)
    (proposalCap properStride retryLimit samples : ℕ)
    (hstride : 0 < properStride) :
    ∫⁻ current, countedQueryCost
        ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
          properStride retryLimit samples current).run oracle.query) ∂mu ≤
      ((384 * (samples * retryLimit * properStride) : ℕ) : ENNReal) +
        ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) * error := by
  have hmain :=
    lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_le_warm_add
      q I oracle hsigma2 hweight hle hwarm hbad proposalCap properStride
        retryLimit samples
  apply hmain.trans
  gcongr
  have hM2 : M * 2 ≤ 192 := by
    calc M * 2 ≤ 96 * 2 := by gcongr
      _ = 192 := by norm_num
  have hproper : (1 : ENNReal) ≤ properStride := by
    exact_mod_cast hstride
  calc
    ((samples * retryLimit : ℕ) : ENNReal) *
        ((properStride : ENNReal) * (M * 2) + 2 * M) ≤
      ((samples * retryLimit : ℕ) : ENNReal) *
        ((properStride : ENNReal) * 192 + 192) := by
      gcongr
      simpa [mul_comm] using hM2
    _ ≤ ((samples * retryLimit : ℕ) : ENNReal) *
        ((properStride : ENNReal) * 384) := by
      gcongr
      calc
        (properStride : ENNReal) * 192 + 192 ≤
            (properStride : ENNReal) * 192 +
              (properStride : ENNReal) * 192 := by
          gcongr
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hproper (by norm_num : (0 : ENNReal) ≤ 192)
        _ = (properStride : ENNReal) * 384 := by ring
    _ = ((384 * (samples * retryLimit * properStride) : ℕ) : ENNReal) := by
      push_cast
      ring

#print axioms
  lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_le_warm_add
#print axioms
  lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_finalEnvelope

end ArlibCommunity.Algorithms.CV18
