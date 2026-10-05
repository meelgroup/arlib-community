import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCapFailure

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A capped scheduled proper block differs from its uncapped lazy-speedy
counterpart only through the explicit `none` outcome. -/
theorem bind_scheduledBalancedAccuracyRetryBlockKernel_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)) {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride))
      ((mu.bind <| frontMarkovCollectLaw (P ^ properStride)
        (fun _ => 0) 1).map some) capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux K
    (figureOneScheduledPhaseBody_measurable q I sigma2) delta sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let f : AmbientSpace q.n → ℝ := fun _ => 0
  let L := mu.bind
    (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)
  let nu := mu.bind <| frontMarkovCollectLaw (P ^ properStride) f 1
  have hdom : ∀ A, MeasurableSet A → L (optionSomeEvent A) ≤ nu A := by
    intro A hA
    dsimp only [L, nu, scheduledBalancedAccuracyRetryBlockKernel]
    simpa [K, delta, Q, P, f] using
      (bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
        K (figureOneScheduledPhaseBody_measurable q I sigma2) delta sigma2
        (measurable_const : Measurable f) proposalCap properStride 1 mu hA)
  exact optionMeasure_leUpTo_map_some L nu hdom (by simpa [L] using hfail)

/-- Endpoint-only form of the scheduled capped-block comparison. -/
theorem bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)) {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      ((mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)).map optionSnd)
      ((Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some)
      capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  let f : AmbientSpace q.n → ℝ := fun _ => 0
  have h := bind_scheduledBalancedAccuracyRetryBlockKernel_leUpTo_uncapped
    q I hsigma2 proposalCap properStride mu hfail
  have hmap := h.map (measurable_optionSnd (S := AmbientSpace q.n))
  have hendpoint :
      (mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map Prod.snd =
        Arlib.MarkovChains.iterate (P ^ properStride) mu 1 :=
    bind_frontMarkovCollectLaw_map_snd (P ^ properStride)
      (measurable_const : Measurable f) 1 mu
  have hnu :
      ((mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map some).map
          optionSnd =
        (Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some := by
    rw [Measure.map_map measurable_optionSnd measurable_some]
    rw [show (optionSnd ∘ some : ℝ × AmbientSpace q.n →
          Option (AmbientSpace q.n)) = some ∘ Prod.snd by
      funext output
      rfl]
    rw [← Measure.map_map measurable_some measurable_snd, hendpoint]
  rw [hnu] at hmap
  exact hmap

/-- Adding scheduled speedy mixing to cap exhaustion gives a stationary
endpoint comparison for one proper block. -/
theorem bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    {capError mixError : ENNReal}
    (hfail :
      (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)) {none} ≤ capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2))
        mu properStride) pi mixError) :
    MeasureLeUpTo
      ((mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)).map optionSnd)
      (pi.map some) (capError + mixError) := by
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  have hcap :=
    bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
      q I hsigma2 proposalCap properStride mu hfail
  dsimp only at hcap
  rw [iterate_pow_one P mu properStride] at hcap
  have hmixSome : Arlib.TVLe
      ((Arlib.MarkovChains.iterate P mu properStride).map some)
      (pi.map some) mixError := hmix.map measurable_some
  exact hcap.trans (MeasureLeUpTo.of_tvLe hmixSome)

/-- Warm-start and explicit local-cap inequalities yield the scheduled
stationary endpoint approximation needed by finite retries. -/
theorem bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    {M capError mixError : ENNReal}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hbudget : (properStride : ENNReal) * M ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2))
        mu properStride)
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2) mixError) :
    MeasureLeUpTo
      ((mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride)).map optionSnd)
      ((Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2).map some)
      (capError + mixError) := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 := Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledPhaseBody_convex q I sigma2)
    (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
    (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
    (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hfail := bind_scheduledBalancedAccuracyRetryBlockKernel_none_le_of_isWarm
    q I hsigma2 hwarm proposalCap properStride hproposalCap hbudget
  exact bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
    q I hsigma2 proposalCap properStride mu pi hfail hmix

#print axioms bind_scheduledBalancedAccuracyRetryBlockKernel_leUpTo_uncapped
#print axioms bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
#print axioms bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm

end ArlibCommunity.Algorithms.CV18
