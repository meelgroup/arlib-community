import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPhaseMixing

/-!
# CV18 speedy mixing at the executable strong step

The generic overlap route used `n ≥ 21` only to control the Gaussian density
ratio when `delta ≤ sigma/(8 sqrt n)`.  Figure 1 actually uses the much smaller
`delta ≤ sigma/(4096 sqrt n)`.  At that radius the same ratio estimate holds in
every positive dimension, removing the low-dimensional gap in Theorem 1.1.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- The Metropolis acceptance floor depends only on the product `R * delta`,
not on a separate paper-radius bound.  This form permits accuracy-dependent
radial truncations while retaining a constant acceptance probability. -/
theorem MarkovChains.acceptance_floor_of_radiusStepProduct_cv18
    (hn : 1 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / 8) (hRδ : R * δ ≤ σ ^ 2 / 9) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) *
      (1 / 8) * (2 / 3) := by
  have hδ8 : 8 * δ ≤ σ := by nlinarith
  have hδ2 : δ ^ 2 ≤ σ ^ 2 / 64 := by nlinarith
  have hnum : 2 * R * δ + δ ^ 2 ≤ (137 / 576 : ℝ) * σ ^ 2 := by
    nlinarith
  have hden : 0 < 2 * σ ^ 2 := by positivity
  have hquot : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ (137 / 1152 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hquot' : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ (65 / 128 : ℝ) := by
    norm_num at hquot ⊢
    linarith
  have hexp : (3 / 5 : ℝ) ≤
      Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by
    refine MarkovChains.three_fifths_le_exp_neg_sixtyfive_div_onetwentyeight_cv18.trans ?_
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hquot'
    simpa only [neg_div] using hneg
  nlinarith

/-- Density comparability at a bounded radial core, expressed through the
dimension-free product condition actually used by the proof. -/
theorem gaussianWeightReal_le_of_radiusStepProduct_cv18
    (hn : 1 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    (hRδ : R * δ ≤ σ ^ 2 / 9)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (huv : ‖u - v‖ ≤ δ / Real.sqrt n) :
    MarkovChains.gaussianWeightReal (σ ^ 2) u ≤
      9 / 8 * MarkovChains.gaussianWeightReal (σ ^ 2) v := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt hnR
  have hsqrtpos : 0 < Real.sqrt n := zero_lt_one.trans_le hsqrt1
  have hR0 : 0 ≤ R := (norm_nonneg u).trans hu
  have hsep : ‖u - v‖ ≤ δ := by
    have hδ0 : 0 ≤ δ := by
      have hdiv0 : 0 ≤ δ / Real.sqrt n := (norm_nonneg (u - v)).trans huv
      by_contra hneg
      have : δ / Real.sqrt n < 0 :=
        div_neg_of_neg_of_pos (lt_of_not_ge hneg) hsqrtpos
      linarith
    exact huv.trans (div_le_self hδ0 hsqrt1)
  have hprod : R * ‖u - v‖ ≤ σ ^ 2 / 9 := by
    exact (mul_le_mul_of_nonneg_left hsep hR0).trans hRδ
  have hexponent : R / σ ^ 2 * ‖u - v‖ ≤ 1 / 9 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hσ)]
    nlinarith
  have hexp19 : Real.exp (1 / 9 : ℝ) ≤ 9 / 8 := by
    have h9 : (8 : ℝ) / 9 ≤ Real.exp (-(1 / 9) : ℝ) := by
      have := Real.add_one_le_exp (-(1 / 9) : ℝ)
      linarith
    have hmul : Real.exp (1 / 9 : ℝ) * Real.exp (-(1 / 9) : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (1 / 9 : ℝ)]
  have hbase := gaussianWeightReal_le_mul_exp hσ hu hv
  calc
    MarkovChains.gaussianWeightReal (σ ^ 2) u ≤
        MarkovChains.gaussianWeightReal (σ ^ 2) v *
          Real.exp (R / σ ^ 2 * ‖u - v‖) := hbase
    _ ≤ MarkovChains.gaussianWeightReal (σ ^ 2) v * Real.exp (1 / 9) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v).le
    _ ≤ MarkovChains.gaussianWeightReal (σ ^ 2) v * (9 / 8) := by
      exact mul_le_mul_of_nonneg_left hexp19
        (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v).le
    _ = 9 / 8 * MarkovChains.gaussianWeightReal (σ ^ 2) v := by ring

theorem ell_comparable_of_densDist_radiusStepProduct_cv18
    (hn : 1 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    (hRδ : R * δ ≤ σ ^ 2 / 9)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {u v : EuclideanSpace ℝ (Fin n)} (huK : u ∈ K) (hvK : v ∈ K)
    (hu : MarkovChains.ell K δ u ≠ 0) (hv : MarkovChains.ell K δ v ≠ 0)
    (hsep : ‖u - v‖ ≤ δ / Real.sqrt n)
    (hd : densDist (fun x => (MarkovChains.ell K δ x).toReal *
      MarkovChains.gaussianWeightReal (σ ^ 2) x) u v < 1 / 4) :
    MarkovChains.ell K δ u ≤ ENNReal.ofReal (3 / 2) * MarkovChains.ell K δ v ∧
      MarkovChains.ell K δ v ≤ ENNReal.ofReal (3 / 2) * MarkovChains.ell K δ u := by
  have hutop : MarkovChains.ell K δ u ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.one_ne_top (MarkovChains.ell_le_one K δ u)
  have hvtop : MarkovChains.ell K δ v ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.one_ne_top (MarkovChains.ell_le_one K δ v)
  have hA : 0 < (MarkovChains.ell K δ u).toReal := ENNReal.toReal_pos hu hutop
  have hB : 0 < (MarkovChains.ell K δ v).toReal := ENNReal.toReal_pos hv hvtop
  have hsep' : ‖v - u‖ ≤ δ / Real.sqrt n := by rwa [norm_sub_rev]
  obtain ⟨h1, h2⟩ := MarkovChains.le_three_halves_of_densDist_mul_lt hA hB
    (MarkovChains.gaussianWeightReal_pos (σ ^ 2) u)
    (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v)
    (gaussianWeightReal_le_of_radiusStepProduct_cv18 hn hσ hRδ
      (hKR u huK) (hKR v hvK) hsep)
    (gaussianWeightReal_le_of_radiusStepProduct_cv18 hn hσ hRδ
      (hKR v hvK) (hKR u huK) hsep')
    (by simpa only [densDist] using hd)
  exact ⟨MarkovChains.ell_le_of_toReal_le h1,
    MarkovChains.ell_le_of_toReal_le h2⟩

theorem hoverlap_speedyMetropolisGaussian_radiusStepProduct_cv18
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRδ : R * δ ≤ σ ^ 2 / 9) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n →
      densDist (Set.indicator K (fun x =>
        (MarkovChains.ell K δ x).toReal *
          MarkovChains.gaussianWeightReal (σ ^ 2) x)) u v < 1 / 4 →
      1 ≤ 20 * (MarkovChains.speedyMetropolisGaussian K δ (σ ^ 2) u Tᶜ +
        MarkovChains.speedyMetropolisGaussian K δ (σ ^ 2) v T) := by
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    simpa using Real.sqrt_le_sqrt hn1
  have hδσ8 : δ ≤ σ / 8 := by
    calc
      δ ≤ σ / (8 * Real.sqrt n) := hδσ
      _ ≤ σ / 8 := by
        apply div_le_div_of_nonneg_left hσ.le
        · norm_num
        · nlinarith
  intro T hT u v _ huK hvK _ hsep hd
  rw [MarkovChains.densDist_indicator_of_mem huK hvK] at hd
  obtain ⟨h1, h2⟩ := ell_comparable_of_densDist_radiusStepProduct_cv18
    (Nat.one_le_of_lt hn) hσ hRδ hKR huK hvK
    (MarkovChains.ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ))
    (MarkovChains.ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hvK hδ))
    hsep.le hd
  exact MarkovChains.one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable
    hn hK hKc hδ (by positivity : (0 : ℝ) < σ ^ 2) hR huK hvK
    (hKR u huK) (hKR v hvK) hsep.le
    (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    (MarkovChains.max_volume_ball_inter_le_of_ell_comparable hδ h1 h2)
    (MarkovChains.acceptance_floor_of_radiusStepProduct_cv18
      (Nat.one_le_of_lt hn) hσ hδ hδσ8 hRδ) hT

theorem gaussianWeightReal_le_of_strongStep_cv18
    (hn : 1 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (4096 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (huv : ‖u - v‖ ≤ δ / Real.sqrt n) :
    MarkovChains.gaussianWeightReal (σ ^ 2) u ≤
      9 / 8 * MarkovChains.gaussianWeightReal (σ ^ 2) v := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt hnR
  have hsqrtpos : 0 < Real.sqrt n := zero_lt_one.trans_le hsqrt1
  have hδmul : δ * (4096 * Real.sqrt n) ≤ σ :=
    (le_div_iff₀ (by positivity)).1 hδσ
  have hsep : ‖u - v‖ * Real.sqrt n ≤ δ := by
    have hmul : ‖u - v‖ * Real.sqrt n ≤
        (δ / Real.sqrt n) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right huv (Real.sqrt_nonneg (n : ℝ))
    rwa [div_mul_cancel₀ δ hsqrtpos.ne'] at hmul
  have hR0 : 0 ≤ R := (norm_nonneg u).trans hu
  have hprod : R * ‖u - v‖ * Real.sqrt n ≤
      4 * σ * δ * Real.sqrt n := by
    nlinarith [mul_le_mul_of_nonneg_left hsep hR0,
      mul_le_mul_of_nonneg_right hRσ (norm_nonneg (u - v))]
  have hprod' : R * ‖u - v‖ ≤ 4 * σ * δ :=
    le_of_mul_le_mul_right hprod hsqrtpos
  have hsmall : 4 * σ * δ ≤ σ ^ 2 / 9 := by
    nlinarith
  have hexponent : R / σ ^ 2 * ‖u - v‖ ≤ 1 / 9 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hσ)]
    nlinarith
  have hexp19 : Real.exp (1 / 9 : ℝ) ≤ 9 / 8 := by
    have h9 : (8 : ℝ) / 9 ≤ Real.exp (-(1 / 9) : ℝ) := by
      have := Real.add_one_le_exp (-(1 / 9) : ℝ)
      linarith
    have hmul : Real.exp (1 / 9 : ℝ) * Real.exp (-(1 / 9) : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (1 / 9 : ℝ)]
  have hbase := gaussianWeightReal_le_mul_exp hσ hu hv
  calc
    MarkovChains.gaussianWeightReal (σ ^ 2) u ≤
        MarkovChains.gaussianWeightReal (σ ^ 2) v *
          Real.exp (R / σ ^ 2 * ‖u - v‖) := hbase
    _ ≤ MarkovChains.gaussianWeightReal (σ ^ 2) v * Real.exp (1 / 9) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v).le
    _ ≤ MarkovChains.gaussianWeightReal (σ ^ 2) v * (9 / 8) := by
      exact mul_le_mul_of_nonneg_left hexp19
        (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v).le
    _ = 9 / 8 * MarkovChains.gaussianWeightReal (σ ^ 2) v := by ring

theorem ell_comparable_of_densDist_strongStep_cv18
    (hn : 1 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (4096 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {u v : EuclideanSpace ℝ (Fin n)} (huK : u ∈ K) (hvK : v ∈ K)
    (hu : MarkovChains.ell K δ u ≠ 0) (hv : MarkovChains.ell K δ v ≠ 0)
    (hsep : ‖u - v‖ ≤ δ / Real.sqrt n)
    (hd : densDist (fun x => (MarkovChains.ell K δ x).toReal *
      MarkovChains.gaussianWeightReal (σ ^ 2) x) u v < 1 / 4) :
    MarkovChains.ell K δ u ≤ ENNReal.ofReal (3 / 2) * MarkovChains.ell K δ v ∧
      MarkovChains.ell K δ v ≤ ENNReal.ofReal (3 / 2) * MarkovChains.ell K δ u := by
  have hutop : MarkovChains.ell K δ u ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.one_ne_top (MarkovChains.ell_le_one K δ u)
  have hvtop : MarkovChains.ell K δ v ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.one_ne_top (MarkovChains.ell_le_one K δ v)
  have hA : 0 < (MarkovChains.ell K δ u).toReal := ENNReal.toReal_pos hu hutop
  have hB : 0 < (MarkovChains.ell K δ v).toReal := ENNReal.toReal_pos hv hvtop
  have hsep' : ‖v - u‖ ≤ δ / Real.sqrt n := by rwa [norm_sub_rev]
  obtain ⟨h1, h2⟩ := MarkovChains.le_three_halves_of_densDist_mul_lt hA hB
    (MarkovChains.gaussianWeightReal_pos (σ ^ 2) u)
    (MarkovChains.gaussianWeightReal_pos (σ ^ 2) v)
    (gaussianWeightReal_le_of_strongStep_cv18 hn hσ hδ hδσ hRσ
      (hKR u huK) (hKR v hvK) hsep)
    (gaussianWeightReal_le_of_strongStep_cv18 hn hσ hδ hδσ hRσ
      (hKR v hvK) (hKR u huK) hsep')
    (by simpa only [densDist] using hd)
  exact ⟨MarkovChains.ell_le_of_toReal_le h1,
    MarkovChains.ell_le_of_toReal_le h2⟩

theorem hoverlap_speedyMetropolisGaussian_strongStep_cv18
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (4096 * Real.sqrt n))
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) /
      (2 * σ ^ 2)) * (1 / 8) * (2 / 3)) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n →
      densDist (Set.indicator K (fun x =>
        (MarkovChains.ell K δ x).toReal *
          MarkovChains.gaussianWeightReal (σ ^ 2) x)) u v < 1 / 4 →
      1 ≤ 20 * (MarkovChains.speedyMetropolisGaussian K δ (σ ^ 2) u Tᶜ +
        MarkovChains.speedyMetropolisGaussian K δ (σ ^ 2) v T) := by
  intro T hT u v _ huK hvK _ hsep hd
  rw [MarkovChains.densDist_indicator_of_mem huK hvK] at hd
  obtain ⟨h1, h2⟩ := ell_comparable_of_densDist_strongStep_cv18
    (Nat.one_le_iff_ne_zero.mpr (by omega)) hσ hδ hδσ hRσ hKR huK hvK
    (MarkovChains.ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ))
    (MarkovChains.ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hvK hδ))
    hsep.le hd
  exact MarkovChains.one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable
    hn hK hKc hδ (by positivity : (0 : ℝ) < σ ^ 2) hR huK hvK
    (hKR u huK) (hKR v hvK) hsep.le
    (MarkovChains.volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    (MarkovChains.max_volume_ball_inter_le_of_ell_comparable hδ h1 h2) hfloor hT

end Arlib

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal

variable {n : ℕ}

/-- CV18 speedy-Gaussian conductance under the product condition controlling
both density variation and Metropolis rejection on a bounded radial core. -/
theorem conductance_speedyMetropolisGaussian_ge_radiusStepProduct_cv18
    (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRδ : R * δ ≤ σ ^ 2 / 9) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤
      conductance (speedyMetropolisGaussian K δ (σ ^ 2))
        (ellGaussianProb K δ (σ ^ 2)) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn hσ hδ hδσ
    (fun x => Set.indicator_nonneg (fun y _ =>
      mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2))
    (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (Arlib.hoverlap_speedyMetropolisGaussian_radiusStepProduct_cv18
      hn hK hKc hKb hK0 hσ hδ hδσ hR hKR hRδ)
    (Arlib.hiso_speedyMetropolisGaussian_uncond hn hσ hδ hK hKc hKb hK0)

theorem conductance_speedyMetropolisGaussian_ge_strongStep_cv18
    (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (4096 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤
      conductance (speedyMetropolisGaussian K δ (σ ^ 2))
        (ellGaussianProb K δ (σ ^ 2)) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hweak : δ ≤ σ / (8 * Real.sqrt n) := by
    calc
      δ ≤ σ / (4096 * Real.sqrt n) := hδσ
      _ ≤ σ / (8 * Real.sqrt n) := by
        apply div_le_div_of_nonneg_left hσ.le
        · positivity
        · nlinarith
  have hKcb : K ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn hσ hδ hweak
    (fun x => Set.indicator_nonneg (fun y _ =>
      mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2))
    (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (Arlib.hoverlap_speedyMetropolisGaussian_strongStep_cv18
      hn hK hKc hKb hK0 hσ hδ hδσ hR hKR hRσ
      (acceptance_floor_of_cv_four_cv18 hn hσ hδ hweak hRσ))
    (Arlib.hiso_speedyMetropolisGaussian_uncond hn hσ hδ hK hKc hKb hK0)

theorem mixesWithin_lazy_speedyMetropolisGaussian_radiusStepProduct_cv18
    (hn : 2 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRδ : R * δ ≤ σ ^ 2 / 9)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hKR x hx
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
    (conductance_speedyMetropolisGaussian_ge_radiusStepProduct_cv18
      hn hσ hδ hδσ hK hKc hK0 hR hKR hRδ) ht

/-- Warm-start TV mixing at Figure 1's stronger proposal-step cap.  Unlike
the generic phase-radius theorem, this works in every dimension `n ≥ 2`. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_strongStep_cv18
    (hn : 2 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (4096 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hK0 : volume K ≠ 0)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hweak : δ ≤ σ / (8 * Real.sqrt n) := by
    calc
      δ ≤ σ / (4096 * Real.sqrt n) := hδσ
      _ ≤ σ / (8 * Real.sqrt n) := by
        apply div_le_div_of_nonneg_left hσ.le
        · positivity
        · nlinarith
  have hKcb : K ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hKR x hx
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
  exact mixesWithin_lazy_of_conductance_sqrt (by omega) hσ hδ hweak
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm heps0 heps1
    (conductance_speedyMetropolisGaussian_ge_strongStep_cv18
      hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ) ht

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- Figure 1's executable proposal radius satisfies the strong step cap used
to remove the old `n ≥ 21` restriction. -/
theorem figureOneProposalRadius_le_strongMixingStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      Real.sqrt sigma2 / (4096 * Real.sqrt q.n) := by
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
    _ ≤ Real.sqrt sigma2 / (4096 * Real.sqrt q.n) := by
      apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      · positivity
      · nlinarith [Real.sqrt_nonneg
          ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))]

/-- Phase-local warm-start mixing for the actual Figure-1 proposal radius,
with the input model's native `n ≥ 3` assumption and no extra dimension
threshold. -/
theorem mixesWithin_phaseTruncatedBody_figureOne_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (phaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2))
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      mu0 t (ENNReal.ofReal eps) := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdelta0 : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hR : 0 ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n := by positivity
  have hwarm' : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) (Real.sqrt sigma2 ^ 2)) := by
    simpa [Real.sq_sqrt hsigma2.le] using hwarm
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_strongStep_cv18
      hn2 hsigma hdelta0
      (figureOneProposalRadius_le_strongMixingStep q hsigma2)
      (phaseTruncatedBody_measurable q I sigma2)
      (phaseTruncatedBody_convex q I sigma2)
      (phaseTruncatedBody_volume_ne_zero q I hsigma2)
      hR (fun _ hx => phaseTruncatedBody_norm_le q I hx) le_rfl
      hM hwarm' heps0 heps1 ht
  simpa [Real.sq_sqrt hsigma2.le] using hmix

/-- The complete phase-local sampler at the actual Figure-1 radius, with no
dimension assumption beyond `VolumeParams.dim_ok`. -/
theorem phaseSampleToGaussian_figureOne_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 coreError mixError : ℝ}
    (hsigma2 : 0 < sigma2)
    (hradius : 1 ≤ 4 * Real.sqrt sigma2 * Real.sqrt q.n)
    (hcoreError0 : 0 < coreError) (hcoreError16 : coreError ≤ 1 / 16)
    (hpaperStep : figureOneProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / coreError))))
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (phaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError1 : mixError ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ))
    (hcombined : 8 * ENNReal.ofReal mixError +
        4 * ENNReal.ofReal coreError ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
    let K := phaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
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
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hdelta0 : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmixPhase := mixesWithin_phaseTruncatedBody_figureOne_cv18 q I hsigma2
    hM hwarm hmixError0 hmixError1 ht
  have hmix : Arlib.TVLe mu
      (Arlib.MarkovChains.ellGaussianProb K delta sigma2)
      (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, mu, P, K, delta] using hmixPhase
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
  simpa [K, delta, Real.sq_sqrt hsigma2.le] using htransfer

end ArlibCommunity.Algorithms.CV18
