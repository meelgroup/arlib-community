/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperCostBound

/-!
# An unconditional average-local-conductance bound at a smaller step size

For `delta ≤ 1/(2n)`, the homothetic core
`(1 - 1/(2n)) • K` has local conductance one and retains at least half of the
Gaussian mass.  This proves the weighted average-local-conductance hypothesis
with `lambda = 1/2` in that regime.

This is deliberately not presented as CV18's advertised larger-step estimate.
At the paper's larger step size, an averaged boundary-shell/smoothing argument
is still required.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

theorem measurableSet_smul_set_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {c : ℝ} (hc : c ≠ 0) : MeasurableSet (c • K) := by
  have hEq : c • K =
      (fun y : EuclideanSpace ℝ (Fin n) => c⁻¹ • y) ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact hy
    · intro hz
      exact ⟨c⁻¹ • z, hz, by simp [smul_smul, mul_inv_cancel₀ hc]⟩
  rw [hEq]
  exact hK.preimage (continuous_const_smul _).measurable

theorem mem_smul_set_iff_of_ne_zero_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ} (hc : c ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) : c • y ∈ c • K ↔ y ∈ K := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h : z = y := by
      have h' := congrArg (fun w : EuclideanSpace ℝ (Fin n) => c⁻¹ • w) hzy
      simpa [smul_smul, inv_mul_cancel₀ hc] using h'
    exact h ▸ hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem lintegral_comp_smul_euclidean_cv18
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g)
    {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ y, g (c • y) = ENNReal.ofReal |(c ^ n)⁻¹| * ∫⁻ x, g x := by
  have hmap : ∫⁻ x, g x
      ∂(Measure.map (fun y : EuclideanSpace ℝ (Fin n) => c • y) volume) =
      ∫⁻ y, g (c • y) :=
    lintegral_map hg (continuous_const_smul c).measurable
  rw [← hmap, Measure.map_addHaar_smul volume hc, finrank_euclideanSpace_fin,
    lintegral_smul_measure, smul_eq_mul]

theorem gaussianWeightReal_smul_cv18 {c : ℝ} (hc : c ≠ 0)
    (variance : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal variance (c • y) =
      gaussianWeightReal (variance / c ^ 2) y := by
  unfold gaussianWeightReal
  congr 1
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp

theorem gaussianWeight_smul_cv18 {c : ℝ} (hc : c ≠ 0)
    (variance : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight variance (c • y) =
      gaussianWeight (variance / c ^ 2) y := by
  unfold gaussianWeight
  rw [gaussianWeightReal_smul_cv18 hc]

theorem gaussianWeight_mono_variance_cv18 {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≤ gaussianWeight t x := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianWeightReal
  refine Real.exp_le_exp.2 ?_
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h : ‖x‖ ^ 2 / (2 * t) ≤ ‖x‖ ^ 2 / (2 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ‖x‖]
  rw [neg_div, neg_div]
  linarith

theorem lintegral_gaussianWeight_smul_set_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {c : ℝ} (hc : 0 < c) (variance : ℝ) :
    ∫⁻ x in c • K, gaussianWeight variance x =
      ENNReal.ofReal (c ^ n) *
        ∫⁻ x in K, gaussianWeight (variance / c ^ 2) x := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hS : MeasurableSet (c • K) := measurableSet_smul_set_cv18 hK hc0
  set g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    (c • K).indicator (gaussianWeight variance) with hgdef
  have hgm : Measurable g := (measurable_gaussianWeight variance).indicator hS
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin n),
      g (c • y) = K.indicator (gaussianWeight (variance / c ^ 2)) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [hgdef, Set.indicator_of_mem
          ((mem_smul_set_iff_of_ne_zero_cv18 hc0 y).2 hy),
        Set.indicator_of_mem hy, gaussianWeight_smul_cv18 hc0]
    · rw [hgdef, Set.indicator_of_notMem
          (fun h => hy ((mem_smul_set_iff_of_ne_zero_cv18 hc0 y).1 h)),
        Set.indicator_of_notMem hy]
  have hleft : ∫⁻ y, g (c • y) =
      ∫⁻ x in K, gaussianWeight (variance / c ^ 2) x := by
    simp_rw [hpoint]
    exact lintegral_indicator hK _
  have hscale : ∫⁻ y, g (c • y) =
      ENNReal.ofReal |(c ^ n)⁻¹| *
        ∫⁻ x in c • K, gaussianWeight variance x := by
    rw [lintegral_comp_smul_euclidean_cv18 hgm hc0, hgdef,
      lintegral_indicator hS]
  have habs : |(c ^ n)⁻¹| = (c ^ n)⁻¹ := abs_of_pos (by positivity)
  rw [← hleft, hscale, habs, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_ne_zero n hc0), ENNReal.ofReal_one, one_mul]

theorem ball_smul_subset_of_convex_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ y ∈ K, ball ((1 - r) • y) r ⊆ K := by
  intro y hy z hz
  rw [mem_ball, dist_eq_norm] at hz
  have hw : r⁻¹ • (z - (1 - r) • y) ∈
      ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hr0)]
    calc
      r⁻¹ * ‖z - (1 - r) • y‖ < r⁻¹ * r :=
        mul_lt_mul_of_pos_left hz (inv_pos.2 hr0)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hr0)
  have hmem := hKc hy (hball hw) (a := 1 - r) (b := r)
    (by linarith) hr0.le (by ring)
  have heq : (1 - r) • y + r • (r⁻¹ • (z - (1 - r) • y)) = z := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr0), one_smul]
    abel
  rwa [heq] at hmem

theorem ell_eq_one_on_shrunken_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdelta_c : delta ≤ 1 - c)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c • K) :
    ell K delta x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hsub : ball (c • y) (1 - c) ⊆ K := by
    have h := ball_smul_subset_of_convex_cv18 hKc hball
      (by linarith : 0 < 1 - c) (by linarith : 1 - c < 1) y hy
    simpa only [sub_sub_cancel] using h
  have hball' : ball (c • y) delta ⊆ K :=
    (Metric.ball_subset_ball hdelta_c).trans hsub
  rw [ell_apply, Set.inter_eq_left.2 hball', ENNReal.div_self]
  · exact (measure_ball_pos volume _ hdelta).ne'
  · exact measure_ball_lt_top.ne

theorem one_sub_mul_le_one_sub_pow_cv18 {r : ℝ} (hr2 : r ≤ 2) (m : ℕ) :
    1 - (m : ℝ) * r ≤ (1 - r) ^ m := by
  have h := one_add_mul_le_pow (a := -r) (by linarith) m
  simpa [sub_eq_add_neg, mul_neg] using h

theorem half_le_one_sub_inv_two_mul_pow_cv18 (hn : 1 ≤ n) :
    (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (n : ℝ))) ^ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr2 : 1 / (2 * (n : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h := one_sub_mul_le_one_sub_pow_cv18 hr2 n
  have heq : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp
  rw [heq] at h
  linarith

/-- At the smaller step `delta ≤ 1/(2n)`, the weighted average local
conductance is at least one half. -/
theorem half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ))) (hvariance : 0 < variance) :
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfrac : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hfrac_pos : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hc1 : c < 1 := by
    dsimp [c]
    linarith
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hdelta_c : delta ≤ 1 - c := by dsimp [c]; linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hsub : c • K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKc.smul_mem_of_zero_mem h0K hy ⟨hc0.le, hc1.le⟩
  have hone : (∫⁻ x in c • K, ell K delta x * gaussianWeight variance x) =
      ∫⁻ x in c • K, gaussianWeight variance x := by
    refine setLIntegral_congr_fun
      (measurableSet_smul_set_cv18 hK hc0.ne') (fun x hx => ?_)
    rw [ell_eq_one_on_shrunken_cv18 hKc hball hc0 hc1
      hdelta hdelta_c hx, one_mul]
  have hscale := lintegral_gaussianWeight_smul_set_cv18 hK hc0 variance
  have hmono : (∫⁻ x in K, gaussianWeight variance x) ≤
      ∫⁻ x in K, gaussianWeight (variance / c ^ 2) x := by
    refine lintegral_mono fun x => gaussianWeight_mono_variance_cv18
      hvariance ?_ x
    rw [le_div_iff₀ (by positivity)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith
    nlinarith [hvariance.le]
  have hhalf : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
    ENNReal.ofReal_le_ofReal (by
      dsimp [c]
      exact half_le_one_sub_inv_two_mul_pow_cv18 hn)
  rw [ellGaussianMeasure_univ]
  calc
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) ≤
        ENNReal.ofReal (c ^ n) *
          ∫⁻ x in K, gaussianWeight variance x := by
      simpa [mul_comm] using
        (mul_le_mul_right hhalf (∫⁻ x in K, gaussianWeight variance x))
    _ ≤ ENNReal.ofReal (c ^ n) *
        ∫⁻ x in K, gaussianWeight (variance / c ^ 2) x := by gcongr
    _ = ∫⁻ x in c • K, ell K delta x * gaussianWeight variance x := by
      rw [hone, hscale]
    _ ≤ ∫⁻ x in K, ell K delta x * gaussianWeight variance x :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-- The small-step lower bound also discharges the nonzero normalisation guard
for the speedy stationary law. -/
theorem ellGaussianMeasure_ne_zero_of_smallStep_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ))) (hvariance : 0 < variance) :
    ellGaussianMeasure K delta variance Set.univ ≠ 0 := by
  have hunit : 0 < ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      gaussianWeight variance x := by
    rw [← withDensity_apply _ measurableSet_ball]
    exact (pos_iff_ne_zero.mpr
      (withDensity_gaussianWeight_unitBall_ne_zero hvariance))
  have hGpos : 0 < ∫⁻ x in K, gaussianWeight variance x :=
    lt_of_lt_of_le hunit
      (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl)
  have hhalfpos : 0 < ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_pos.2 (by norm_num)
  exact ne_of_gt (lt_of_lt_of_le
    (ENNReal.mul_pos hhalfpos.ne' hGpos.ne')
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_cv18
      hn hK hKc hball hdelta hdelta_n hvariance))

/-- Finiteness of the body discharges the finite-normalisation guard. -/
theorem ellGaussianMeasure_ne_top_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKtop : volume K ≠ ⊤)
    (delta : ℝ) {variance : ℝ} (hvariance : 0 < variance) :
    ellGaussianMeasure K delta variance Set.univ ≠ ⊤ :=
  ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hvariance K delta)

/-- At the small step size, `t` independently restarted proper speedy steps
use at most `2 t M` raw proposals in expectation, in multiplication form. -/
theorem half_mul_lintegral_properProposalTotalCost_le_smallStep_cv18
    (hn : 1 ≤ n) {K : Set (GaussianState n)}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : GaussianState n) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ))) (hvariance : 0 < variance)
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance)) (t : ℕ) :
    ENNReal.ofReal (1 / 2) * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu)) ≤
      (t : ℝ≥0∞) * M := by
  exact mul_lintegral_properProposalTotalCost_le hK hdelta variance
    (ellGaussianMeasure_ne_zero_of_smallStep_cv18
      hn hK hKc hball hdelta hdelta_n hvariance)
    (ellGaussianMeasure_ne_top_cv18 hKtop delta hvariance)
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_cv18
      hn hK hKc hball hdelta hdelta_n hvariance)
    hwarm t

/-- Markov cutoff form of the small-step proper-proposal cost bound. -/
theorem half_mul_mul_measure_properProposalTotalCost_ge_le_smallStep_cv18
    (hn : 1 ≤ n) {K : Set (GaussianState n)}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : GaussianState n) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ))) (hvariance : 0 < variance)
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance))
    (t : ℕ) (cutoff : ℝ≥0∞) :
    ENNReal.ofReal (1 / 2) * cutoff *
        restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega} ≤
      (t : ℝ≥0∞) * M := by
  exact mul_mul_measure_properProposalTotalCost_ge_le hK hdelta variance
    (ellGaussianMeasure_ne_zero_of_smallStep_cv18
      hn hK hKc hball hdelta hdelta_n hvariance)
    (ellGaussianMeasure_ne_top_cv18 hKtop delta hvariance)
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_cv18
      hn hK hKc hball hdelta hdelta_n hvariance)
    hwarm t cutoff

end Arlib.MarkovChains
