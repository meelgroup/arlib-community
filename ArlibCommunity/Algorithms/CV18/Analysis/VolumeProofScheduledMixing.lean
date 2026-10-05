import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledBlockApproximation

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

theorem figureOneScheduledProposalRadius_le_sigma_div_eight_sqrt
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneScheduledProposalRadius q sigma2 ≤
      Real.sqrt sigma2 / (8 * Real.sqrt q.n) := by
  let s := Real.sqrt sigma2
  let rn := Real.sqrt (q.n : ℝ)
  let L := figureOneScheduledAccuracyLog q
  let b := Real.sqrt ((q.n : ℝ) * L)
  have hs : 0 < s := Real.sqrt_pos.2 hsigma2
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hrn : 0 < rn := Real.sqrt_pos.2 hn
  have hL : 1 ≤ L := by
    simpa [L] using figureOneScheduledAccuracyLog_one_le q
  have hb : 0 < b := by dsimp [b]; positivity
  have hrnb : rn ≤ b := by
    apply Real.sqrt_le_sqrt
    change (q.n : ℝ) ≤ (q.n : ℝ) * L
    nlinarith
  have hmin : min s 1 ≤ s := min_le_left _ _
  unfold figureOneScheduledProposalRadius
  change min s 1 / (4096 * b) ≤ s / (8 * rn)
  rw [div_le_div_iff₀ (by positivity : 0 < 4096 * b)
    (by positivity : 0 < 8 * rn)]
  calc
    min s 1 * (8 * rn) ≤ s * (8 * rn) := by
      gcongr
    _ ≤ s * (4096 * b) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      nlinarith

/-- Warm-start speedy mixing on the schedule-targeted body and proposal
radius. -/
theorem mixesWithin_scheduledPhaseBody_figureOne_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2))
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
      mu0 t (ENNReal.ofReal eps) := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hR : 0 ≤ figureOneScheduledPhaseRadius q sigma2 :=
    (figureOneScheduledPhaseRadius_pos q hsigma2).le
  have hwarm' : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2)
        (Real.sqrt sigma2 ^ 2)) := by
    simpa [Real.sq_sqrt hsigma2.le] using hwarm
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_radiusStepProduct_cv18
      hn2 hsigma hdelta
      (figureOneScheduledProposalRadius_le_sigma_div_eight_sqrt q hsigma2)
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hR (fun _ hx => by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2)
      (by simpa [Real.sq_sqrt hsigma2.le] using
        figureOneScheduledRadius_mul_proposal_le q hsigma2)
      hM hwarm' heps0 heps1 ht
  simpa [Real.sq_sqrt hsigma2.le] using hmix

#print axioms figureOneScheduledProposalRadius_le_sigma_div_eight_sqrt
#print axioms mixesWithin_scheduledPhaseBody_figureOne_cv18

end ArlibCommunity.Algorithms.CV18
