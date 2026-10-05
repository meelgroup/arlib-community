import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperExpectedCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledBranchMass

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Scheduled-body specialization of the one-half average-local-conductance
cutoff bound for a finite proper collector. -/
theorem half_mul_natCast_mul_bind_scheduledCappedProperCollectLaw_none_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (rawCap properStride samples : ℕ) :
    ENNReal.ofReal (1 / 2) * (rawCap : ENNReal) *
        (mu.bind fun current => cappedProperCollectLaw
          (Arlib.MarkovChains.lazyProperProposalGaussianAux
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledPhaseBody_measurable q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2)
          weight rawCap properStride samples current) {none} ≤
      ((properStride * samples : ℕ) : ENNReal) * M := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux K
    (figureOneScheduledPhaseBody_measurable q I sigma2) delta sigma2
  have hK : MeasurableSet K :=
    figureOneScheduledPhaseBody_measurable q I sigma2
  have hKc : Convex ℝ K := figureOneScheduledPhaseBody_convex q I sigma2
  have hKcompact : IsCompact K :=
    figureOneScheduledPhaseBody_isCompact q I sigma2
  have hKb : Bornology.IsBounded K := hKcompact.isBounded
  have hK0 : volume K ≠ 0 :=
    figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hZ0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      hK hKc hKb hK0 hdelta sigma2
  have hZtop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  have hlambda : ENNReal.ofReal (1 / 2) *
      (∫⁻ x in K, Arlib.MarkovChains.gaussianWeight sigma2 x) ≤
        Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ := by
    simpa [K, delta] using
      half_mul_gaussianWeight_le_scheduledPhaseEllGaussian q I hsigma2
  have hcollect : Measurable fun current =>
      cappedProperCollectLaw Q weight rawCap properStride samples current := by
    unfold cappedProperCollectLaw
    exact (cappedProperCollectLawAux_measurable_and_probability
      Q hweight properStride rawCap properStride samples).1.comp
        (measurable_const.prodMk measurable_id)
  have hmarked : Measurable fun current =>
      cappedProperMarkedLaw Q rawCap (properStride * samples) current :=
    measurable_cappedProperMarkedLaw Q rawCap (properStride * samples)
  have hfailure : (mu.bind fun current =>
        cappedProperCollectLaw Q weight rawCap properStride samples current) {none} =
      (mu.bind fun current =>
        cappedProperMarkedLaw Q rawCap (properStride * samples) current) {none} := by
    rw [Measure.bind_apply measurableSet_option_none hcollect.aemeasurable,
      Measure.bind_apply measurableSet_option_none hmarked.aemeasurable]
    apply lintegral_congr
    intro current
    exact cappedProperCollectLaw_none_eq_cappedProperMarkedLaw_none
      Q hweight rawCap properStride samples current
  change ENNReal.ofReal (1 / 2) * (rawCap : ENNReal) *
      (mu.bind fun current => cappedProperCollectLaw Q weight rawCap
        properStride samples current) {none} ≤ _
  rw [hfailure]
  exact Arlib.MarkovChains.mul_natCast_mul_bind_cappedLazyProperMarkedLaw_none_le
    K hK hKc hKb hK0 hdelta sigma2 hZ0 hZtop hlambda hwarm rawCap
      (properStride * samples)

/-- If the explicit cap budget dominates the scheduled warm-start work, one
scheduled retry block exhausts its local proposal cap with at most the stated
error. -/
theorem bind_scheduledBalancedAccuracyRetryBlockKernel_none_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    {capError : ENNReal}
    (hbudget : (properStride : ENNReal) * M ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capError) :
    (mu.bind
      (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
        properStride)) {none} ≤ capError := by
  let fail := (mu.bind
    (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
      properStride)) {none}
  let coefficient := ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)
  have hmoment :=
    half_mul_natCast_mul_bind_scheduledCappedProperCollectLaw_none_le
      q I hsigma2 (weight := fun _ => 0) measurable_const hwarm
        proposalCap properStride 1
  have hmoment' : coefficient * fail ≤ (properStride : ENNReal) * M := by
    simpa [coefficient, fail, scheduledBalancedAccuracyRetryBlockKernel] using hmoment
  have hcoeff0 : coefficient ≠ 0 := by
    simp [coefficient, hproposalCap.ne']
  have hcoeffTop : coefficient ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [coefficient])
  have hcombined : coefficient * fail ≤ coefficient * capError :=
    hmoment'.trans hbudget
  calc
    fail = coefficient⁻¹ * (coefficient * fail) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcoeff0 hcoeffTop, one_mul]
    _ ≤ coefficient⁻¹ * (coefficient * capError) :=
      mul_le_mul' le_rfl hcombined
    _ = capError := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcoeff0 hcoeffTop, one_mul]

#print axioms half_mul_natCast_mul_bind_scheduledCappedProperCollectLaw_none_le
#print axioms bind_scheduledBalancedAccuracyRetryBlockKernel_none_le_of_isWarm

end ArlibCommunity.Algorithms.CV18
