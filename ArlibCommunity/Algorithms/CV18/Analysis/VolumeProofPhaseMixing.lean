import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.SpeedyGaussianMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofTruncation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKLSCore

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- The small numerical margin needed to use the paper's full
`4 * sigma * sqrt n` phase radius in the Metropolis overlap estimate. -/
theorem three_fifths_le_exp_neg_sixtyfive_div_onetwentyeight_cv18 :
    (3 / 5 : ℝ) ≤ Real.exp (-(65 / 128 : ℝ)) := by
  have hx : |-(65 / 128 : ℝ)| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hlower := (abs_le.mp h).1
  norm_num [abs_of_nonneg] at hlower
  linarith

/-- The Metropolis acceptance floor remains large enough on a body of radius
`4 * sigma * sqrt n`.  The endpoint exponent is `65/128`, whose exponential
is just above `3/5`; a degree-five Taylor remainder proves the required
strict numerical margin without floating-point computation. -/
theorem acceptance_floor_of_cv_four_cv18 (hn : 2 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) *
      (1 / 8) * (2 / 3) := by
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    simpa using Real.sqrt_le_sqrt hn1
  have hsqrtpos : 0 < Real.sqrt n := one_pos.trans_le hsqrt1
  have hδmul : δ * (8 * Real.sqrt n) ≤ σ :=
    (le_div_iff₀ (by positivity)).1 hδσ
  have hδ8 : 8 * δ ≤ σ := by nlinarith
  have hRδ : 2 * R * δ ≤ σ ^ 2 := by nlinarith
  have hδ2 : δ ^ 2 ≤ σ ^ 2 / 64 := by nlinarith
  have hnum : 2 * R * δ + δ ^ 2 ≤ (65 / 64 : ℝ) * σ ^ 2 := by
    nlinarith
  have hden : 0 < 2 * σ ^ 2 := by positivity
  have hquot : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ (65 / 128 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hexp : (3 / 5 : ℝ) ≤
      Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by
    refine three_fifths_le_exp_neg_sixtyfive_div_onetwentyeight_cv18.trans ?_
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hquot
    simpa only [neg_div] using hneg
  nlinarith

/-- CV18 speedy Metropolis conductance on the paper's phase-truncated body.
This strengthens the previously available radius hypothesis from
`R ≤ 2 * sigma * sqrt n` to the paper's `R ≤ 4 * sigma * sqrt n`, with
the same conductance constant. -/
theorem conductance_speedyMetropolisGaussian_ge_phaseRadius_cv18
    (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤
      conductance (speedyMetropolisGaussian K δ (σ ^ 2))
        (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn2 hσ hδ hδσ
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg
        (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2))
    (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian_perPair hn hK hKc hKb hK0
      hσ hδ hδσ hR hKR hRσ
      (acceptance_floor_of_cv_four_cv18 hn2 hσ hδ hδσ hRσ))
    (hiso_speedyMetropolisGaussian_uncond hn2 hσ hδ hK hKc hKb hK0)

/-- Warm-start TV mixing for the lazy speedy Metropolis-Gaussian walk on the
full `4 * sigma * sqrt n` phase truncation used in CV18 Figure 1. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_phaseRadius_cv18
    (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  let _ : IsProbabilityMeasure (ellGaussianProb K δ (σ ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hδ (σ ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K δ))
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous (n := n) (by omega)
      (ellGaussianProb K δ (σ ^ 2))
      (ellGaussianProb_absolutelyContinuous K δ (σ ^ 2))
  exact mixesWithin_lazy_of_conductance_sqrt (by omega) hσ hδ hδσ
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm heps0 heps1
    (conductance_speedyMetropolisGaussian_ge_phaseRadius_cv18
      hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ) ht

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- The phase-local body from CV18 Figure 1, intersected with the fixed radial
truncation already used to reduce the well-rounded input to a bounded body. -/
noncomputable def phaseTruncatedBody (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : Set (AmbientSpace q.n) :=
  truncatedBody q I ∩
    Metric.closedBall 0 (4 * Real.sqrt sigma2 * Real.sqrt q.n)

theorem phaseTruncatedBody_measurable (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : MeasurableSet (phaseTruncatedBody q I sigma2) :=
  (truncatedBody_measurable q I).inter measurableSet_closedBall

theorem phaseTruncatedBody_convex (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : Convex ℝ (phaseTruncatedBody q I sigma2) :=
  (truncatedVolumeInput q I).body.convex.inter (convex_closedBall 0 _)

theorem phaseTruncatedBody_isCompact (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : IsCompact (phaseTruncatedBody q I sigma2) :=
  (truncatedVolumeInput q I).body.isCompact.inter_right isClosed_closedBall

theorem phaseTruncatedBody_isClosed (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : IsClosed (phaseTruncatedBody q I sigma2) :=
  (phaseTruncatedBody_isCompact q I sigma2).isClosed

theorem phaseTruncatedBody_isBounded (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) : Bornology.IsBounded (phaseTruncatedBody q I sigma2) :=
  (phaseTruncatedBody_isCompact q I sigma2).isBounded

theorem phaseTruncatedBody_volume_ne_top (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    volume (phaseTruncatedBody q I sigma2) ≠ ⊤ :=
  (phaseTruncatedBody_isCompact q I sigma2).measure_lt_top.ne

theorem unitBall_subset_phaseTruncatedBody (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ}
    (hradius : 1 ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n) :
    Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆
      phaseTruncatedBody q I sigma2 := by
  intro x hx
  refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
  · simpa [unitBall] using hx
  · rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact hx.trans hradius

theorem phaseTruncatedBody_norm_le (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} {x : AmbientSpace q.n}
    (hx : x ∈ phaseTruncatedBody q I sigma2) :
    ‖x‖ ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n := by
  simpa [phaseTruncatedBody, Metric.mem_closedBall, dist_zero_right] using hx.2

theorem phaseTruncatedBody_volume_ne_zero (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    volume (phaseTruncatedBody q I sigma2) ≠ 0 := by
  let radius : ℝ := 4 * Real.sqrt sigma2 * Real.sqrt q.n
  have hnpos : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hsmall : 0 < min 1 radius := lt_min one_pos hradius
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume (0 : AmbientSpace q.n) hsmall).trans_le
    (measure_mono fun x hx => by
      have hdist_one : dist x 0 ≤ 1 :=
        (le_of_lt hx).trans (min_le_left _ _)
      have hdist_radius : dist x 0 ≤ radius :=
        (le_of_lt hx).trans (min_le_right _ _)
      refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
      · simpa [unitBall, Metric.mem_closedBall, dist_comm] using hdist_one
      · simpa [radius, Metric.mem_closedBall, dist_comm] using hdist_radius)

/-- The exact paper-radius geometry required by the strengthened conductance
and mixing theorems. -/
theorem phaseTruncatedBody_radius_bundle (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let sigma := Real.sqrt sigma2
    0 < sigma ∧
      volume (phaseTruncatedBody q I sigma2) ≠ 0 ∧
      (∀ x ∈ phaseTruncatedBody q I sigma2,
        ‖x‖ ≤ 4 * sigma * Real.sqrt q.n) := by
  dsimp
  exact ⟨Real.sqrt_pos.2 hsigma2,
    phaseTruncatedBody_volume_ne_zero q I hsigma2,
    fun _ hx => phaseTruncatedBody_norm_le q I hx⟩

/-- The executable Figure-1 radius is far below the generic speedy-mixing
step cap. -/
theorem figureOneProposalRadius_le_phaseMixingStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      Real.sqrt sigma2 / (8 * Real.sqrt q.n) := by
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
  have hmul : (q.n : ℝ) ≤
      (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) := by nlinarith
  have hsqrtLe : Real.sqrt q.n ≤
      Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps)) :=
    Real.sqrt_le_sqrt hmul
  unfold figureOneProposalRadius
  calc
    min (Real.sqrt sigma2) 1 /
          (4096 * Real.sqrt
            ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))) ≤
        Real.sqrt sigma2 /
          (4096 * Real.sqrt
            ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))) := by
      gcongr
      exact min_le_left _ _
    _ ≤ Real.sqrt sigma2 / (8 * Real.sqrt q.n) := by
      apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      · positivity
      · nlinarith [Real.sqrt_nonneg
          ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))]

/-- The same executable radius satisfies the KLS core condition with the
algorithm's global accuracy parameter as core error. -/
theorem figureOneProposalRadius_le_paperCoreStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / q.eps))) := by
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hratio : 1 < (q.n : ℝ) / q.eps := by
    rw [lt_div_iff₀ q.heps.1]
    have hn1 : (1 : ℝ) ≤ q.n := by exact_mod_cast (le_trans (by norm_num) q.dim_ok)
    nlinarith [q.heps.2]
  have hlog0 : 0 < Real.log ((q.n : ℝ) / q.eps) := Real.log_pos hratio
  have hL : Real.log ((q.n : ℝ) / q.eps) ≤
      protectedLog ((q.n : ℝ) / q.eps) := le_max_right _ _
  have hmul : (q.n : ℝ) * Real.log ((q.n : ℝ) / q.eps) ≤
      (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) := by gcongr
  have hsqrtLe : Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / q.eps)) ≤
      Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps)) :=
    Real.sqrt_le_sqrt hmul
  unfold figureOneProposalRadius
  calc
    min (Real.sqrt sigma2) 1 /
          (4096 * Real.sqrt
            ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))) ≤
        1 /
          (4096 * Real.sqrt
            ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))) := by
      gcongr
      exact min_le_right _ _
    _ ≤ 1 / (8 * Real.sqrt
          ((q.n : ℝ) * Real.log ((q.n : ℝ) / q.eps))) := by
      apply div_le_div_of_nonneg_left zero_le_one
      · positivity
      · nlinarith [Real.sqrt_nonneg
          ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))]

/-- The strengthened speedy-walk mixing theorem instantiated on CV18's
phase-local body.  All geometry is discharged; the remaining hypotheses are
exactly the warm start, error, and advertised step-count arithmetic consumed
phase by phase. -/
theorem mixesWithin_phaseTruncatedBody_cv18
    (q : VolumeParams) (I : VolumeInput q.n) (hn : 21 ≤ q.n)
    {sigma2 delta : ℝ} (hsigma2 : 0 < sigma2) (hdelta0 : 0 < delta)
    (hdeltaStep : delta ≤
      Real.sqrt sigma2 / (8 * Real.sqrt q.n))
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2) delta sigma2))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (delta * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (phaseTruncatedBody q I sigma2) delta sigma2))
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2) delta sigma2)
      mu0 t (ENNReal.ofReal eps) := by
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hR : 0 ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n := by positivity
  have hwarm' : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2) delta (Real.sqrt sigma2 ^ 2)) := by
    simpa [Real.sq_sqrt hsigma2.le] using hwarm
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_phaseRadius_cv18
      hn hsigma hdelta0 hdeltaStep
      (phaseTruncatedBody_measurable q I sigma2)
      (phaseTruncatedBody_convex q I sigma2)
      (phaseTruncatedBody_volume_ne_zero q I hsigma2)
      hR (fun _ hx => phaseTruncatedBody_norm_le q I hx) le_rfl
      hM hwarm' heps0 heps1 ht
  simpa [Real.sq_sqrt hsigma2.le] using hmix

/-- A complete phase-local CV18 sampler theorem.  The warm-start conductance
bound produces a speedy sample, and the KLS core conversion turns it into the
restricted Gaussian target with explicit total-variation error. -/
theorem phaseSampleToGaussian_of_paperStep_cv18
    (q : VolumeParams) (I : VolumeInput q.n) (hn : 21 ≤ q.n)
    {sigma2 delta coreError mixError : ℝ}
    (hsigma2 : 0 < sigma2) (hdelta0 : 0 < delta)
    (hradius : 1 ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n)
    (hmixingStep : delta ≤ Real.sqrt sigma2 / (8 * Real.sqrt q.n))
    (hcoreError0 : 0 < coreError) (hcoreError16 : coreError ≤ 1 / 16)
    (hpaperStep : delta ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / coreError))))
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2) delta sigma2))
    (hmixError0 : 0 < mixError) (hmixError1 : mixError ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (delta * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ))
    (hcombined : 8 * ENNReal.ofReal mixError +
        4 * ENNReal.ofReal coreError ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
    let K := phaseTruncatedBody q I sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ)
      (Arlib.condOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2)) K)
      (64 * ENNReal.ofReal mixError + 32 * ENNReal.ofReal coreError) := by
  dsimp only
  let K := phaseTruncatedBody q I sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hmixPhase := mixesWithin_phaseTruncatedBody_cv18 q I hn hsigma2
    hdelta0 hmixingStep hM hwarm hmixError0 hmixError1 ht
  have hmix : Arlib.TVLe mu
      (Arlib.MarkovChains.ellGaussianProb K delta sigma2)
      (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, mu, P, K] using hmixPhase
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hmix' : Arlib.TVLe mu
      (Arlib.MarkovChains.ellGaussianProb K delta (Real.sqrt sigma2 ^ 2))
      (ENNReal.ofReal mixError) := by
    simpa [Real.sq_sqrt hsigma2.le] using hmix
  have htransfer :=
    Arlib.MarkovChains.TVLe.speedyToGaussian_of_paperStep_of_body_cv18
      (n := q.n) (K := K) (le_trans (by norm_num) q.dim_ok)
      (phaseTruncatedBody_convex q I sigma2)
      (phaseTruncatedBody_isClosed q I sigma2)
      (phaseTruncatedBody_isBounded q I sigma2)
      (phaseTruncatedBody_volume_ne_zero q I hsigma2)
      (phaseTruncatedBody_volume_ne_top q I sigma2)
      (unitBall_subset_phaseTruncatedBody q I hradius)
      hdelta0 hsigma hcoreError0 hcoreError16 hpaperStep
      hmix' ENNReal.ofReal_ne_top hcombined
  simpa [K, Real.sq_sqrt hsigma2.le] using htransfer

end ArlibCommunity.Algorithms.CV18
