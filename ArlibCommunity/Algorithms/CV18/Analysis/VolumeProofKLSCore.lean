import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyToTarget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductanceLV
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyGaussianConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.KLS97Sharp

/-!
# KLS97 homothetic-core estimates used by CV18

This module follows KLS97 Theorem 4.16, the result cited in CV18's
speedy-to-target argument.  The first lemmas formalize its key separation
geometry: if `K` contains the unit ball, then `c • K` is at distance at least
`a - c` from the complement of `a • K`.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- A ball of radius `a-c` around `c y` lies in the enlarged homothet
`a • K`.  This is the tangent-plane separation used in KLS97 Theorem 4.16. -/
theorem ball_smul_subset_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a) :
    ∀ y ∈ K, ball (c • y) (a - c) ⊆ a • K := by
  intro y hy z hz
  have ha0 : 0 < a := lt_of_le_of_lt hc0 hca
  have hac0 : 0 < a - c := sub_pos.mpr hca
  let w : EuclideanSpace ℝ (Fin n) := (a - c)⁻¹ • (z - c • y)
  have hw : w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hac0)]
    rw [mem_ball, dist_eq_norm] at hz
    calc
      (a - c)⁻¹ * ‖z - c • y‖ < (a - c)⁻¹ * (a - c) :=
        mul_lt_mul_of_pos_left hz (inv_pos.mpr hac0)
      _ = 1 := inv_mul_cancel₀ hac0.ne'
  have hcoeff0 : 0 ≤ c / a := div_nonneg hc0 ha0.le
  have hcoeff1 : 0 ≤ (a - c) / a := div_nonneg hac0.le ha0.le
  have hsum : c / a + (a - c) / a = 1 := by field_simp; ring
  have hk : (c / a) • y + ((a - c) / a) • w ∈ K :=
    hKc hy (hball hw) hcoeff0 hcoeff1 hsum
  refine ⟨(c / a) • y + ((a - c) / a) • w, hk, ?_⟩
  dsimp [w]
  have hca_mul : a * (c / a) = c := by field_simp
  have hac_scale : a * ((a - c) / a) = a - c := by field_simp
  rw [smul_add, smul_smul, smul_smul, hca_mul, hac_scale, smul_smul,
    mul_inv_cancel₀ hac0.ne', one_smul]
  abel

/-- Closed-ball form of the homothetic inclusion, used for distance
sublevel sets. -/
theorem closedBall_smul_subset_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a) :
    ∀ y ∈ K, closedBall (c • y) (a - c) ⊆ a • K := by
  intro y hy z hz
  have ha0 : 0 < a := lt_of_le_of_lt hc0 hca
  have hac0 : 0 < a - c := sub_pos.mpr hca
  let w : EuclideanSpace ℝ (Fin n) := (a - c)⁻¹ • (z - c • y)
  have hw : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hac0)]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc
      (a - c)⁻¹ * ‖z - c • y‖ ≤ (a - c)⁻¹ * (a - c) :=
        mul_le_mul_of_nonneg_left hz (inv_pos.mpr hac0).le
      _ = 1 := inv_mul_cancel₀ hac0.ne'
  have hcoeff0 : 0 ≤ c / a := div_nonneg hc0 ha0.le
  have hcoeff1 : 0 ≤ (a - c) / a := div_nonneg hac0.le ha0.le
  have hsum : c / a + (a - c) / a = 1 := by field_simp; ring
  have hk : (c / a) • y + ((a - c) / a) • w ∈ K :=
    hKc hy (hball hw) hcoeff0 hcoeff1 hsum
  refine ⟨(c / a) • y + ((a - c) / a) • w, hk, ?_⟩
  dsimp [w]
  have hca_mul : a * (c / a) = c := by field_simp
  have hac_scale : a * ((a - c) / a) = a - c := by field_simp
  rw [smul_add, smul_smul, smul_smul, hca_mul, hac_scale, smul_smul,
    mul_inv_cancel₀ hac0.ne', one_smul]
  abel

/-- Points outside `a • K` are at least `a-c` away from the inner core
`c • K`. -/
theorem sub_le_infDist_smul_of_not_mem_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ a • K) :
    a - c ≤ Metric.infDist z (c • K) := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  rw [Metric.le_infDist hcoreNonempty]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_contra hdist
  have hzball : z ∈ ball (c • y) (a - c) := by
    rw [mem_ball]
    exact lt_of_not_ge hdist
  exact hz (ball_smul_subset_outer_smul_cv18 hKc hball hc0 hca y hy hzball)

/-- Sharp spherical-cap bound expressed at the exact distance from a closed
convex body. -/
theorem volume_inter_closedBall_le_gaussian_infDist_cv18
    {L : Set (EuclideanSpace ℝ (Fin n))} (hLc : Convex ℝ L)
    (hLcl : IsClosed L) (hLne : L.Nonempty)
    {delta : ℝ} (hdelta : 0 < delta)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ L) :
    volume (L ∩ closedBall z delta) ≤
      ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  have hcap := Arlib.volume_inter_closedBall_le_sqrt
    hLc hLcl hLne hz delta
  have hpow := Arlib.sqrt_pow_le_gaussian_exp
    (n := n) (t := delta) (h := Metric.infDist z L) hdelta
  calc
    volume (L ∩ closedBall z delta) ≤
        ENNReal.ofReal
            (Real.sqrt (delta ^ 2 - Metric.infDist z L ^ 2) ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcap
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2))) * delta ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ = ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        MeasureTheory.Measure.addHaar_closedBall volume _ hdelta.le,
        finrank_euclideanSpace_fin]
      ring

/-- The sharp cap estimate on the inner core, with the KLS97 separation
inserted into the Gaussian exponent. -/
theorem volume_core_inter_closedBall_le_exp_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKcl : IsClosed K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a delta : ℝ} (hc0 : 0 < c) (hca : c < a) (hdelta : 0 < delta)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ a • K) :
    volume (c • K ∩ closedBall z delta) ≤
      ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  have hsep : a - c ≤ Metric.infDist z (c • K) :=
    sub_le_infDist_smul_of_not_mem_outer_smul_cv18
      hKc hball hc0.le hca hz
  have hzcore : z ∉ c • K := by
    intro hzmem
    rw [Metric.infDist_zero_of_mem hzmem] at hsep
    linarith
  have hcap := Arlib.volume_inter_closedBall_le_sqrt
    (hKc.smul c)
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl)
    hcoreNonempty hzcore delta
  have hpow := Arlib.sqrt_pow_le_gaussian_exp
    (n := n) (t := delta) (h := Metric.infDist z (c • K)) hdelta
  have hdist0 : 0 ≤ Metric.infDist z (c • K) := Metric.infDist_nonneg
  have hac0 : 0 ≤ a - c := sub_nonneg.mpr hca.le
  have hsquares : (a - c) ^ 2 ≤ Metric.infDist z (c • K) ^ 2 :=
    (sq_le_sq₀ hac0 hdist0).2 hsep
  have hexp :
      Real.exp (-((n : ℝ) * Metric.infDist z (c • K) ^ 2 /
          (2 * delta ^ 2))) ≤
        Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2))) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hden : 0 < 2 * delta ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsquares hn0
    exact neg_le_neg (div_le_div_of_nonneg_right hmul hden.le)
  calc
    volume (c • K ∩ closedBall z delta) ≤
        ENNReal.ofReal
            (Real.sqrt (delta ^ 2 - Metric.infDist z (c • K) ^ 2) ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcap
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z (c • K) ^ 2 /
            (2 * delta ^ 2))) * delta ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2))) *
            delta ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ = ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        MeasureTheory.Measure.addHaar_closedBall volume _ hdelta.le,
        finrank_euclideanSpace_fin]
      ring

/-- Tonelli swap for two different inside/outside bodies.  This is the exact
double-integral identity needed for the KLS core `cK` against the complement
of the original body `K`. -/
theorem lintegral_sdiff_eq_lintegral_inter_twoSets_cv18
    (A B : Set (EuclideanSpace ℝ (Fin n))) (delta : ℝ) :
    ∫⁻ x in A, volume (closedBall x delta \ B) =
      ∫⁻ y in Bᶜ, volume (A ∩ closedBall y delta) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | dist p.1 p.2 ≤ delta}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ENNReal :=
    fun x y => S.indicator 1 (x, y)
  have hmeas : Measurable (Function.uncurry f) := by
    dsimp [f]
    exact measurable_one.indicator hS
  have hx : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y in Bᶜ, f x y = volume (closedBall x delta \ B) := by
    intro x
    have hrw : ∀ y, f x y =
        (closedBall x delta).indicator
          (1 : EuclideanSpace ℝ (Fin n) → ENNReal) y := by
      intro y
      simp only [f, Set.indicator_apply, S, Set.mem_ofPred_eq,
        mem_closedBall, Pi.one_apply]
      rw [dist_comm y x]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.sdiff_eq]
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ x in A, f x y = volume (A ∩ closedBall y delta) := by
    intro y
    have hrw : ∀ x, f x y =
        (closedBall y delta).indicator
          (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x := by
      intro x
      simp only [f, Set.indicator_apply, S, Set.mem_ofPred_eq,
        mem_closedBall, Pi.one_apply]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
  have hswap := lintegral_lintegral_swap (μ := volume.restrict A)
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Bᶜ)
      hmeas.aemeasurable
  simp_rw [hx, hy] at hswap
  exact hswap

/-- Layer cake for an exponential of distance, restricted to an arbitrary
measurable-domain measure. -/
theorem layercake_infDist_on_cv18
    (A K : Set (EuclideanSpace ℝ (Fin n))) {rate : ℝ} (hrate : 0 < rate)
    (shift : ℝ) :
    ∫⁻ y in A,
        ENNReal.ofReal
          (Real.exp (shift - rate * Metric.infDist y K)) =
      ∫⁻ h in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (rate * Real.exp (shift - rate * h)) *
          volume (A ∩ {y | Metric.infDist y K ≤ h}) := by
  classical
  have hinfc : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      Metric.infDist y K := Metric.continuous_infDist_pt K
  let T : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
    {p | Metric.infDist p.1 K ≤ p.2}
  have hT : MeasurableSet T :=
    measurableSet_le (hinfc.measurable.comp measurable_fst) measurable_snd
  let F : EuclideanSpace ℝ (Fin n) → ℝ → ENNReal :=
    fun y h => T.indicator
      (fun p => ENNReal.ofReal
        (rate * Real.exp (shift - rate * p.2))) (y, h)
  have hmeas : Measurable (Function.uncurry F) := by
    dsimp [F]
    refine Measurable.indicator ?_ hT
    exact ENNReal.measurable_ofReal.comp
      (((measurable_const.mul measurable_snd).const_sub shift).exp.const_mul rate)
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ h in Set.Ioi (0 : ℝ), F y h =
        ENNReal.ofReal
          (Real.exp (shift - rate * Metric.infDist y K)) := by
    intro y
    have hd0 : 0 ≤ Metric.infDist y K := Metric.infDist_nonneg
    have hrw : ∀ h : ℝ, F y h =
        (Set.Ici (Metric.infDist y K)).indicator
          (fun h => ENNReal.ofReal
            (rate * Real.exp (shift - rate * h))) h := by
      intro h
      simp only [F, Set.indicator_apply, T, Set.mem_ofPred_eq, Set.mem_Ici]
    simp_rw [hrw]
    rw [lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hae :
        (Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume]
          Set.Ioi (Metric.infDist y K) := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null ?_
          (measure_singleton (Metric.infDist y K))
        rintro x ⟨⟨hx1, _⟩, hx2⟩
        simp only [Set.mem_Ioi, not_lt] at hx2
        exact le_antisymm hx2 hx1
      · have hsub : Set.Ioi (Metric.infDist y K) ⊆
            Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0 : ℝ) := by
          intro x hx
          exact ⟨Set.mem_Ici.mpr hx.le,
            Set.mem_Ioi.mpr (lt_of_le_of_lt hd0 hx)⟩
        rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
    rw [MeasureTheory.setLIntegral_congr hae]
    exact Arlib.lintegral_Ioi_exp_neg hrate shift _
  have hx : ∀ h : ℝ, ∫⁻ y in A, F y h =
      ENNReal.ofReal (rate * Real.exp (shift - rate * h)) *
        volume (A ∩ {y | Metric.infDist y K ≤ h}) := by
    intro h
    have hSm : MeasurableSet
        {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} :=
      measurableSet_le hinfc.measurable measurable_const
    have hrw : ∀ y : EuclideanSpace ℝ (Fin n), F y h =
        {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}.indicator
          (fun _ => ENNReal.ofReal
            (rate * Real.exp (shift - rate * h))) y := by
      intro y
      simp only [F, Set.indicator_apply, T, Set.mem_ofPred_eq]
    simp_rw [hrw]
    rw [lintegral_indicator hSm, setLIntegral_const,
      Measure.restrict_apply hSm, Set.inter_comm]
  have hswap := lintegral_lintegral_swap
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict A)
    (ν := (volume : Measure ℝ).restrict (Set.Ioi 0)) hmeas.aemeasurable
  simp_rw [hy, hx] at hswap
  exact hswap

/-- Distance shells of the inner homothet outside `K` fit in the elementary
homothetic volume shell `(c+h)K \ K`. -/
theorem volume_compl_inter_infDist_core_le_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c h : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hh : 1 - c ≤ h) :
    volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
      ENNReal.ofReal ((c + h) ^ n - 1) * volume K := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_closedBall_self zero_le_one)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  have hcoreClosed : IsClosed (c • K) :=
    (isClosedMap_smul_of_ne_zero hc0.ne') K hKcl
  have hh0 : 0 < h := (sub_pos.mpr hc1).trans_le hh
  have hca : c < c + h := by linarith
  have ha1 : 1 ≤ c + h := by linarith
  have ha0 : 0 ≤ c + h := zero_le_one.trans ha1
  have houter :
      Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h} ⊆ (c + h) • K \ K := by
    rintro y ⟨hyK, hyd⟩
    obtain ⟨x, hxcore, hxy⟩ :=
      hcoreClosed.exists_infDist_eq_dist hcoreNonempty y
    have hyball : y ∈ closedBall x h := by
      rw [mem_closedBall, ← hxy]
      exact hyd
    obtain ⟨z, hz, rfl⟩ := hxcore
    have hyouter := closedBall_smul_subset_outer_smul_cv18
      hKc hball hc0.le hca z hz
    exact ⟨hyouter (by simpa only [add_sub_cancel_left] using hyball), hyK⟩
  have hKouter : K ⊆ (c + h) • K := by
    intro x hx
    refine ⟨(c + h)⁻¹ • x, ?_, ?_⟩
    · exact hKc.smul_mem_of_zero_mem hzero hx
        ⟨by positivity, by rw [inv_le_one₀ (by positivity)]; exact ha1⟩
    · change (c + h) • ((c + h)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (by positivity : c + h ≠ 0), one_smul]
  calc
    volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
        volume ((c + h) • K \ K) := measure_mono houter
    _ = volume ((c + h) • K) - volume K :=
      measure_sdiff hKouter hKcl.measurableSet.nullMeasurableSet hKfin
    _ = ENNReal.ofReal ((c + h) ^ n) * volume K - volume K := by
      rw [Arlib.volume_smul_euclidean ha0]
    _ = (ENNReal.ofReal ((c + h) ^ n) - 1) * volume K := by
      rw [ENNReal.sub_mul (fun _ _ => hKfin), one_mul]
    _ = ENNReal.ofReal ((c + h) ^ n - 1) * volume K := by
      congr 1
      calc
        ENNReal.ofReal ((c + h) ^ n) - 1 =
            ENNReal.ofReal ((c + h) ^ n) - ENNReal.ofReal 1 := by norm_num
        _ = ENNReal.ofReal ((c + h) ^ n - 1) :=
          (ENNReal.ofReal_sub _ zero_le_one).symm

/-- The explicit one-dimensional integral at the heart of KLS97 Theorem
4.16.  When `rate ≥ 2n`, the homothetic shell growth is absorbed by half of
the exponential decay. -/
theorem lintegral_kls_exp_majorant_le_cv18
    {dim rate h0 : ℝ} (hdim : 0 < dim) (hrate : 2 * dim ≤ rate) :
    ∫⁻ h in Set.Ioi h0,
        ENNReal.ofReal
          (rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0))) ≤
      ENNReal.ofReal (2 * Real.exp (-rate * h0)) := by
  let decay : ℝ := rate - dim
  have hrate0 : 0 < rate := lt_of_lt_of_le (by linarith) hrate
  have hdecay : 0 < decay := by dsimp [decay]; linarith
  have hratio : rate / decay ≤ 2 := by
    rw [div_le_iff₀ hdecay]
    dsimp [decay]
    linarith
  have hfun : (fun h : ℝ => ENNReal.ofReal
        (rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0)))) =
      fun h => ENNReal.ofReal (rate / decay) *
        ENNReal.ofReal
          (decay * Real.exp (-dim * h0 - decay * h)) := by
    funext h
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hexponent : -rate * h + dim * (h - h0) =
        -dim * h0 - decay * h := by
      dsimp [decay]
      ring
    calc
      rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0)) =
          rate * Real.exp (-rate * h + dim * (h - h0)) := by
        rw [Real.exp_add]
        ring
      _ = rate * Real.exp (-dim * h0 - decay * h) := by rw [hexponent]
      _ = rate / decay *
          (decay * Real.exp (-dim * h0 - decay * h)) := by
        field_simp
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    Arlib.lintegral_Ioi_exp_neg hdecay (-dim * h0) h0]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hexpEq : Real.exp (-dim * h0 - decay * h0) =
      Real.exp (-rate * h0) := by
    congr 1
    dsimp [decay]
    ring
  rw [hexpEq]
  exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le

/-- KLS97's exponential distance integral over the complement of `K`, after
the homothetic shell estimate and the one-dimensional calculation. -/
theorem lintegral_exp_neg_infDist_core_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c rate : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hrate : 2 * (n : ℝ) ≤ rate) :
    ∫⁻ y in Kᶜ,
        ENNReal.ofReal (Real.exp (-rate * Metric.infDist y (c • K))) ≤
      ENNReal.ofReal (2 * Real.exp (-rate * (1 - c))) * volume K := by
  let h0 : ℝ := 1 - c
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h0pos : 0 < h0 := by dsimp [h0]; linarith
  have hrate0 : 0 < rate := lt_of_lt_of_le (by positivity : 0 < 2 * (n : ℝ)) hrate
  have hlayer := layercake_infDist_on_cv18
    (n := n) Kᶜ (c • K) hrate0 0
  simp only [zero_sub] at hlayer
  have hlayer' :
      (∫⁻ y in Kᶜ,
        ENNReal.ofReal (Real.exp (-rate * Metric.infDist y (c • K)))) =
        ∫⁻ h in Set.Ioi 0,
          ENNReal.ofReal (rate * Real.exp (-rate * h)) *
            volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) := by
    simpa only [neg_mul] using hlayer
  rw [hlayer']
  let major : ℝ → ENNReal := fun h =>
    ENNReal.ofReal
      (rate * Real.exp (-rate * h) * Real.exp ((n : ℝ) * (h - h0))) *
        volume K
  have hmajorMeas : Measurable major := by
    dsimp [major]
    fun_prop
  have hpoint : ∀ h ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal (rate * Real.exp (-rate * h)) *
          volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
        (Set.Ici h0).indicator major h := by
    intro h hh
    by_cases hh0 : h0 ≤ h
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hh0)]
      have hshell := volume_compl_inter_infDist_core_le_cv18
        hKc hKcl hKfin hball hc0 hc1 (by simpa [h0] using hh0)
      have hx0 : 0 ≤ h - h0 := sub_nonneg.mpr hh0
      have hpow : (c + h) ^ n ≤ Real.exp ((n : ℝ) * (h - h0)) := by
        have hone := Real.add_one_le_exp (h - h0)
        have hbase : c + h ≤ Real.exp (h - h0) := by
          have heq : c + h = 1 + (h - h0) := by dsimp [h0]; ring
          rw [heq]
          simpa [add_comm] using hone
        calc
          (c + h) ^ n ≤ Real.exp (h - h0) ^ n :=
            pow_le_pow_left₀ (by linarith) hbase n
          _ = Real.exp ((n : ℝ) * (h - h0)) := by
            rw [← Real.exp_nat_mul]
      have hshellReal : (c + h) ^ n - 1 ≤
          Real.exp ((n : ℝ) * (h - h0)) := by
        linarith [Real.exp_pos ((n : ℝ) * (h - h0))]
      calc
        ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
            ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              (ENNReal.ofReal ((c + h) ^ n - 1) * volume K) := by gcongr
        _ ≤ ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              (ENNReal.ofReal (Real.exp ((n : ℝ) * (h - h0))) * volume K) := by
            gcongr
        _ = major h := by
          dsimp [major]
          repeat' rw [ENNReal.ofReal_mul (by positivity)]
          ac_rfl
    · rw [Set.indicator_of_notMem (by simpa [Set.mem_Ici] using hh0)]
      have hempty : Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h} = ∅ := by
        by_contra hne
        obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hsep := sub_le_infDist_smul_of_not_mem_outer_smul_cv18
          hKc (fun _ hx => hball (Metric.ball_subset_closedBall hx))
          hc0.le hc1 (z := y) (by simpa using hy.1)
        exact hh0 (by dsimp [h0]; exact hsep.trans hy.2)
      rw [hempty, measure_empty, mul_zero]
  calc
    (∫⁻ h in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (rate * Real.exp (-rate * h)) *
          volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h})) ≤
        ∫⁻ h in Set.Ioi (0 : ℝ), (Set.Ici h0).indicator major h :=
      setLIntegral_mono' measurableSet_Ioi hpoint
    _ = ∫⁻ h in Set.Ioi h0, major h := by
      rw [lintegral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici]
      have hae : (Set.Ici h0 ∩ Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume]
          Set.Ioi h0 := by
        refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
        · refine measure_mono_null ?_ (measure_singleton h0)
          rintro x ⟨⟨hx1, _⟩, hx2⟩
          simp only [Set.mem_Ioi, not_lt] at hx2
          exact le_antisymm hx2 hx1
        · have hsub : Set.Ioi h0 ⊆ Set.Ici h0 ∩ Set.Ioi (0 : ℝ) := by
            intro x hx
            exact ⟨Set.mem_Ici.mpr hx.le,
              Set.mem_Ioi.mpr (h0pos.trans hx)⟩
          rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
      exact MeasureTheory.setLIntegral_congr hae
    _ = (∫⁻ h in Set.Ioi h0,
          ENNReal.ofReal
            (rate * Real.exp (-rate * h) *
              Real.exp ((n : ℝ) * (h - h0)))) * volume K := by
      dsimp [major]
      rw [lintegral_mul_const' _ _ hKfin]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-rate * h0)) * volume K := by
      gcongr
      exact lintegral_kls_exp_majorant_le_cv18 hnR hrate
    _ = ENNReal.ofReal (2 * Real.exp (-rate * (1 - c))) * volume K := by
      rfl

/-- KLS97 Theorem 4.16's unweighted core-escape estimate.  The left side is
the total volume of ball-walk proposals from `c K` that leave `K`.  The
condition `4 δ² ≤ 1-c` is exactly what lets the radial exponential dominate
homothetic shell growth. -/
theorem lintegral_core_closedBall_escape_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    ∫⁻ x in c • K, volume (closedBall x delta \ K) ≤
      ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) *
        volume K * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  let h0 : ℝ := 1 - c
  let rate : ℝ := (n : ℝ) * h0 / (2 * delta ^ 2)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h0pos : 0 < h0 := by dsimp [h0]; linarith
  have hden : 0 < 2 * delta ^ 2 := by positivity
  have hrate : 2 * (n : ℝ) ≤ rate := by
    rw [le_div_iff₀ hden]
    dsimp [rate, h0]
    nlinarith
  let V : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact measure_closedBall_lt_top.ne
  have hpoint : ∀ y ∈ Kᶜ,
      volume (c • K ∩ closedBall y delta) ≤
        ENNReal.ofReal
            (Real.exp (-rate * Metric.infDist y (c • K))) * V := by
    intro y hy
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
      hball (Metric.mem_closedBall_self zero_le_one)
    have hcoreNe : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
    have hcoreCl : IsClosed (c • K) :=
      (isClosedMap_smul_of_ne_zero hc0.ne') K hKcl
    have hsep : h0 ≤ Metric.infDist y (c • K) := by
      have hs := sub_le_infDist_smul_of_not_mem_outer_smul_cv18
        hKc (fun _ hx => hball (Metric.ball_subset_closedBall hx))
        hc0.le hc1 (z := y) (by simpa using hy)
      simpa [h0] using hs
    have hycore : y ∉ c • K := by
      intro hymem
      rw [Metric.infDist_zero_of_mem hymem] at hsep
      linarith
    have hcap := volume_inter_closedBall_le_gaussian_infDist_cv18
      (hKc.smul c) hcoreCl hcoreNe hdelta hycore
    have hd0 : 0 ≤ Metric.infDist y (c • K) := Metric.infDist_nonneg
    have hquad : rate * Metric.infDist y (c • K) ≤
        (n : ℝ) * Metric.infDist y (c • K) ^ 2 /
          (2 * delta ^ 2) := by
      dsimp [rate]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hden.le
      have hsquare : h0 * Metric.infDist y (c • K) ≤
          Metric.infDist y (c • K) ^ 2 := by
        simpa [pow_two] using mul_le_mul_of_nonneg_right hsep hd0
      calc
        (n : ℝ) * h0 * Metric.infDist y (c • K) =
            (n : ℝ) * (h0 * Metric.infDist y (c • K)) := by ring
        _ ≤ (n : ℝ) * Metric.infDist y (c • K) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare hnR.le
    calc
      volume (c • K ∩ closedBall y delta) ≤
          ENNReal.ofReal
              (Real.exp (-((n : ℝ) * Metric.infDist y (c • K) ^ 2 /
                (2 * delta ^ 2)))) * V := hcap
      _ ≤ ENNReal.ofReal
              (Real.exp (-rate * Metric.infDist y (c • K))) * V := by
        gcongr
        simpa only [neg_mul] using neg_le_neg hquad
  rw [lintegral_sdiff_eq_lintegral_inter_twoSets_cv18 (c • K) K delta]
  calc
    (∫⁻ y in Kᶜ, volume (c • K ∩ closedBall y delta)) ≤
        ∫⁻ y in Kᶜ,
          ENNReal.ofReal
              (Real.exp (-rate * Metric.infDist y (c • K))) * V :=
      setLIntegral_mono' hKcl.measurableSet.compl hpoint
    _ = (∫⁻ y in Kᶜ,
          ENNReal.ofReal
            (Real.exp (-rate * Metric.infDist y (c • K)))) * V := by
      rw [lintegral_mul_const' _ _ hVtop]
    _ ≤ (ENNReal.ofReal (2 * Real.exp (-rate * h0)) * volume K) * V := by
      gcongr
      exact lintegral_exp_neg_infDist_core_le_cv18 hn hKc hKcl hKfin
        hball hc0 hc1 hrate
    _ = ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) *
        volume K * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      dsimp [rate, h0, V]
      congr 2
      congr 2
      ring

/-- Normalized form of the KLS97 core-escape estimate: the average
ball-walk rejection probability on `c K` is exponentially small. -/
theorem setLIntegral_one_sub_ell_core_le_exp_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    ∫⁻ x in c • K, (1 - ell K delta x) ≤
      ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  let V : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Metric.measure_closedBall_pos volume 0 hdelta).ne'
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact measure_closedBall_lt_top.ne
  have hbadm : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      1 - ell K delta x :=
    measurable_const.sub (measurable_ell hKcl.measurableSet delta)
  have hpoint : ∀ x ∈ c • K,
      V * (1 - ell K delta x) ≤ volume (closedBall x delta \ K) := by
    intro x _
    change volume (closedBall 0 delta) * (1 - ell K delta x) ≤ _
    rw [mul_comm, Measure.addHaar_closedBall_eq_addHaar_ball,
      ← volume_ball_eq x delta,
      one_sub_ell_mul_volume_ball_eq hKcl.measurableSet hdelta]
    exact measure_mono fun _ hy =>
      ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  apply (ENNReal.mul_le_mul_iff_right hV0 hVtop).1
  rw [← lintegral_const_mul _ hbadm]
  calc
    (∫⁻ x in c • K, V * (1 - ell K delta x)) ≤
        ∫⁻ x in c • K, volume (closedBall x delta \ K) :=
      setLIntegral_mono' ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
        hpoint
    _ ≤ ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K * V :=
      lintegral_core_closedBall_escape_le_cv18 hn hKc hKcl hKfin hball
        hc0 hc1 hdelta hscale
    _ = V * (ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K) := by ac_rfl

/-- Scaling an intersection with a centered ball.  This is the exact set
identity needed to apply KLS to the enlarged Gaussian level body
`K ∩ (r/c)B` while estimating the desired set `cK ∩ rB`. -/
theorem smul_inter_closedBall_div_cv18
    (K : Set (EuclideanSpace ℝ (Fin n))) {c r : ℝ}
    (hc : 0 < c) :
    c • (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / c)) =
      c • K ∩ closedBall 0 r := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyK, hyball⟩, rfl⟩
    refine ⟨⟨y, hyK, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc]
    rw [mem_closedBall, dist_zero_right] at hyball
    rw [le_div_iff₀ hc] at hyball
    simpa [mul_comm] using hyball
  · rintro ⟨⟨y, hyK, rfl⟩, hyball⟩
    refine ⟨y, ⟨hyK, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    apply (le_div_iff₀ hc).2
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc] at hyball
    simpa [mul_comm] using hyball

/-- Uniform KLS defect bound on a Gaussian level section.  The key corrected
body is `K ∩ (r/c)B`; its `c`-core is the desired `cK ∩ rB`. -/
theorem setLIntegral_one_sub_ell_levelCore_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) {eta : ENNReal}
    (hcoeff : ENNReal.ofReal
        (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta * ENNReal.ofReal (c ^ n))
    {r : ℝ} (hr : c ≤ r) :
    ∫⁻ x in c • K ∩ closedBall 0 r, (1 - ell K delta x) ≤
      eta * volume (c • K ∩ closedBall 0 r) := by
  let L : Set (EuclideanSpace ℝ (Fin n)) :=
    K ∩ closedBall 0 (r / c)
  have hr0 : 0 ≤ r := hc0.le.trans hr
  have hLcore : c • L = c • K ∩ closedBall 0 r := by
    exact smul_inter_closedBall_div_cv18 K hc0
  have hLc : Convex ℝ L := hKc.inter (convex_closedBall 0 _)
  have hLcl : IsClosed L := hKcl.inter isClosed_closedBall
  have hLfin : volume L ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin (measure_mono fun _ hx => hx.1)
  have hballL : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ L := by
    intro x hx
    refine ⟨hball hx, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [mem_closedBall, dist_zero_right] using hx
    have hone : 1 ≤ r / c := (le_div_iff₀ hc0).2 (by simpa using hr)
    exact hxnorm.trans hone
  have hmono : ∀ x, 1 - ell K delta x ≤ 1 - ell L delta x := by
    intro x
    apply tsub_le_tsub_left _ 1
    rw [ell_apply, ell_apply]
    have hinter : ball x delta ∩ L ⊆ ball x delta ∩ K := by
      rintro z ⟨hzball, hzL⟩
      exact ⟨hzball, hzL.1⟩
    exact ENNReal.div_le_div (measure_mono hinter) le_rfl
  rw [← hLcore]
  calc
    (∫⁻ x in c • L, (1 - ell K delta x)) ≤
        ∫⁻ x in c • L, (1 - ell L delta x) :=
      setLIntegral_mono'
        ((isClosedMap_smul_of_ne_zero hc0.ne') L hLcl).measurableSet
        (fun x _ => hmono x)
    _ ≤ ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume L :=
      setLIntegral_one_sub_ell_core_le_exp_cv18 hn hLc hLcl hLfin
        hballL hc0 hc1 hdelta hscale
    _ ≤ (eta * ENNReal.ofReal (c ^ n)) * volume L := by gcongr
    _ = eta * volume (c • L) := by
      rw [Arlib.volume_smul_euclidean hc0.le]
      ac_rfl

/-- A proposal ball centred at norm at most `c` can leave the unit ball only
through a spherical cap of depth at least `(1-c)/2`.  This supplies CV18's
"standard calculation" for the small Gaussian level sets. -/
theorem volume_closedBall_sdiff_unitBall_le_exp_cv18
    {x : EuclideanSpace ℝ (Fin n)} {c delta : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hx : ‖x‖ ≤ c)
    (hdelta : 0 < delta) (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    volume (closedBall x delta \ closedBall 0 1) ≤
      ENNReal.ofReal
          (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
            (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  let h : ℝ := (1 - c) / 2
  have hh0 : 0 < h := by dsimp [h]; linarith
  have hdelta1 : delta < 1 := by
    have hd2 : delta ^ 2 < 1 := by nlinarith [sq_nonneg delta]
    nlinarith [sq_nonneg (delta - 1)]
  by_cases hx0 : x = 0
  · subst x
    have hempty : closedBall (0 : EuclideanSpace ℝ (Fin n)) delta \
        closedBall 0 1 = ∅ := by
      rw [Set.sdiff_eq_empty]
      exact closedBall_subset_closedBall hdelta1.le
    rw [hempty, measure_empty]
    positivity
  · let q : ℝ := ‖x‖
    have hq0 : 0 < q := by dsimp [q]; exact norm_pos_iff.mpr hx0
    let nu : EuclideanSpace ℝ (Fin n) := q⁻¹ • x
    have hnu : ‖nu‖ = 1 := by
      dsimp [nu, q]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq0)]
      exact inv_mul_cancel₀ hq0.ne'
    let H : Set (EuclideanSpace ℝ (Fin n)) :=
      {y | h + inner ℝ nu x ≤ inner ℝ nu y}
    have hHc : Convex ℝ H := by
      intro a ha b hb u v hu hv huv
      dsimp [H] at ha hb ⊢
      rw [inner_add_right, real_inner_smul_right,
        real_inner_smul_right]
      have hua := mul_le_mul_of_nonneg_left ha hu
      have hvb := mul_le_mul_of_nonneg_left hb hv
      calc
        h + inner ℝ nu x =
            u * (h + inner ℝ nu x) + v * (h + inner ℝ nu x) := by
          rw [← add_mul, huv, one_mul]
        _ ≤ u * inner ℝ nu a + v * inner ℝ nu b := add_le_add hua hvb
    have hHcl : IsClosed H := by
      dsimp [H]
      exact isClosed_le continuous_const (by fun_prop)
    have hHne : H.Nonempty := by
      refine ⟨x + h • nu, ?_⟩
      dsimp [H]
      rw [inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hnu]
      linarith
    have hxH : x ∉ H := by
      dsimp [H]
      linarith
    have hhsep : h ≤ Metric.infDist x H := by
      rw [Metric.le_infDist hHne]
      intro y hy
      rw [dist_eq_norm]
      have hyinner : h ≤ inner ℝ nu (y - x) := by
        dsimp [H] at hy
        rw [inner_sub_right]
        linarith
      calc
        h ≤ inner ℝ nu (y - x) := hyinner
        _ ≤ ‖nu‖ * ‖y - x‖ := real_inner_le_norm _ _
        _ = ‖x - y‖ := by rw [hnu, one_mul, norm_sub_rev]
    have hsub : closedBall x delta \ closedBall 0 1 ⊆
        H ∩ closedBall x delta := by
      rintro y ⟨hyball, hyunit⟩
      refine ⟨?_, hyball⟩
      dsimp [H]
      have hyout : 1 < ‖y‖ := by
        simpa [mem_closedBall, dist_zero_right, not_le] using hyunit
      have hzle : ‖y - x‖ ≤ delta := by
        simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hyball
      have hexpand : ‖y‖ ^ 2 =
          ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
        calc
          ‖y‖ ^ 2 = ‖x + (y - x)‖ ^ 2 := by congr 2 <;> abel
          _ = _ := norm_add_sq_real _ _
      have hinnerx : q * (1 - c) / 2 ≤ inner ℝ x (y - x) := by
        have hqle : q ≤ c := by simpa [q] using hx
        have hq2 : q ^ 2 ≤ c * q := by nlinarith
        have hd2 : delta ^ 2 ≤ (1 - c) / 4 := by linarith
        have hnormsq : ‖y - x‖ ^ 2 ≤ delta ^ 2 := by nlinarith [norm_nonneg (y - x)]
        have hyone : 1 < ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
        dsimp [q] at hq2 ⊢
        nlinarith
      have hnux : inner ℝ nu (y - x) = q⁻¹ * inner ℝ x (y - x) := by
        dsimp [nu]
        rw [real_inner_smul_left]
      have hnuShift : h ≤ inner ℝ nu (y - x) := by
        rw [hnux]
        have := mul_le_mul_of_nonneg_left hinnerx (inv_pos.mpr hq0).le
        dsimp [h]
        have heq : q * (1 - c) / 2 / q = (1 - c) / 2 := by
          field_simp
        rw [inv_mul_eq_div, heq] at this
        exact this
      rw [inner_sub_right] at hnuShift
      linarith
    have hcap := volume_inter_closedBall_le_gaussian_infDist_cv18
      hHc hHcl hHne hdelta hxH
    have hdist0 : 0 ≤ Metric.infDist x H := Metric.infDist_nonneg
    have hsquare : h ^ 2 ≤ Metric.infDist x H ^ 2 :=
      (sq_le_sq₀ hh0.le hdist0).2 hhsep
    have hexp :
        Real.exp (-((n : ℝ) * Metric.infDist x H ^ 2 /
          (2 * delta ^ 2))) ≤
        Real.exp (-((n : ℝ) * h ^ 2 / (2 * delta ^ 2))) := by
      apply Real.exp_le_exp.mpr
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hden : 0 ≤ 2 * delta ^ 2 := by positivity
      exact neg_le_neg (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hn0) hden)
    calc
      volume (closedBall x delta \ closedBall 0 1) ≤
          volume (H ∩ closedBall x delta) := measure_mono hsub
      _ ≤ ENNReal.ofReal
            (Real.exp (-((n : ℝ) * Metric.infDist x H ^ 2 /
              (2 * delta ^ 2)))) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := hcap
      _ ≤ ENNReal.ofReal
            (Real.exp (-((n : ℝ) * h ^ 2 /
              (2 * delta ^ 2)))) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
        gcongr
      _ = ENNReal.ofReal
            (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
              (2 * delta ^ 2)))) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by rfl

/-- Pointwise version of CV18's small-level-set calculation. -/
theorem one_sub_ell_le_exp_of_norm_le_core_cv18
    (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {x : EuclideanSpace ℝ (Fin n)} {c delta : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hx : ‖x‖ ≤ c)
    (hdelta : 0 < delta) (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    1 - ell K delta x ≤
      ENNReal.ofReal
        (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
          (2 * delta ^ 2)))) := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  let V : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Metric.measure_closedBall_pos volume 0 hdelta).ne'
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact measure_closedBall_lt_top.ne
  apply (ENNReal.mul_le_mul_iff_right hV0 hVtop).1
  calc
    V * (1 - ell K delta x) = volume (ball x delta \ K) := by
      dsimp [V]
      rw [mul_comm]
      rw [Measure.addHaar_closedBall_eq_addHaar_ball,
        ← volume_ball_eq x delta,
        one_sub_ell_mul_volume_ball_eq hK hdelta]
    _ ≤ volume (closedBall x delta \ closedBall 0 1) :=
      measure_mono fun _ hy =>
        ⟨Metric.ball_subset_closedBall hy.1, fun hz => hy.2 (hball hz)⟩
    _ ≤ V * ENNReal.ofReal
          (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
            (2 * delta ^ 2)))) := by
      simpa [mul_comm] using
        volume_closedBall_sdiff_unitBall_le_exp_cv18
          (n := n) hc0 hc1 hx hdelta hscale

/-- Every Gaussian level section of the core has relative defect at most
`eta`: large levels use the corrected KLS body, while small levels use the
pointwise unit-ball cap calculation. -/
theorem setLIntegral_one_sub_ell_levelCore_le_uniform_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) {eta : ENNReal}
    (hcoeffCore : ENNReal.ofReal
        (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta * ENNReal.ofReal (c ^ n))
    (hcoeffPoint : ENNReal.ofReal
        (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta)
    {r : ℝ} (hr0 : 0 ≤ r) :
    ∫⁻ x in c • K ∩ closedBall 0 r, (1 - ell K delta x) ≤
      eta * volume (c • K ∩ closedBall 0 r) := by
  by_cases hr : c ≤ r
  · exact setLIntegral_one_sub_ell_levelCore_le_cv18 hn hKc hKcl
      hKfin hball hc0 hc1 hdelta hscale hcoeffCore hr
  · have hpoint : ∀ x ∈ c • K ∩ closedBall 0 r,
        1 - ell K delta x ≤ eta := by
      intro x hx
      have hxnorm : ‖x‖ ≤ c := by
        have hxr : ‖x‖ ≤ r := by
          simpa [mem_closedBall, dist_zero_right] using hx.2
        exact hxr.trans (le_of_not_ge hr)
      exact (one_sub_ell_le_exp_of_norm_le_core_cv18 hn hKcl.measurableSet
        hball hc0 hc1 hxnorm hdelta hscale).trans hcoeffPoint
    calc
      (∫⁻ x in c • K ∩ closedBall 0 r, (1 - ell K delta x)) ≤
          ∫⁻ _x in c • K ∩ closedBall 0 r, eta :=
        setLIntegral_mono'
          (((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).inter
            isClosed_closedBall).measurableSet hpoint
      _ = eta * volume (c • K ∩ closedBall 0 r) := by
        simp

/-- Layer-cake integration of the uniform level-section estimate gives the
Gaussian-weighted KLS core defect used by CV18. -/
theorem gaussianWeighted_coreDefect_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta sigma : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) {eta : ENNReal}
    (hcoeffCore : ENNReal.ofReal
        (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta * ENNReal.ofReal (c ^ n))
    (hcoeffPoint : ENNReal.ofReal
        (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta) :
    ∫⁻ x in c • K,
        (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x ≤
      eta * ∫⁻ x in c • K, gaussianWeight (sigma ^ 2) x := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := c • K
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    gaussianWeightReal (sigma ^ 2)
  let bad : EuclideanSpace ℝ (Fin n) → ENNReal :=
    fun x => 1 - ell K delta x
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.restrict S
  let nu : Measure (EuclideanSpace ℝ (Fin n)) := mu.withDensity bad
  have hSm : MeasurableSet S :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
  have hfm : Measurable f :=
    (continuous_gaussianWeightReal (sigma ^ 2)).measurable
  have hf0 : ∀ x, 0 ≤ f x := fun _ => by
    dsimp [f, gaussianWeightReal]
    positivity
  have hfof : ∀ x, ENNReal.ofReal (f x) = gaussianWeight (sigma ^ 2) x :=
    fun _ => rfl
  have hbadm : Measurable bad :=
    measurable_const.sub (measurable_ell hKcl.measurableSet delta)
  have hmuLevel : ∀ t, mu {x | t ≤ f x} =
      volume (S ∩ {x | t ≤ f x}) := by
    intro t
    dsimp [mu]
    rw [Measure.restrict_apply (measurableSet_le measurable_const hfm)]
    rw [Set.inter_comm]
  have hnuLevel : ∀ t, nu {x | t ≤ f x} =
      ∫⁻ x in S ∩ {x | t ≤ f x}, bad x := by
    intro t
    dsimp [nu]
    rw [withDensity_apply _ (measurableSet_le measurable_const hfm)]
    change (∫⁻ x in {x | t ≤ f x}, bad x ∂volume.restrict S) = _
    rw [Measure.restrict_restrict (measurableSet_le measurable_const hfm)]
    congr 2
    ext x
    simp [Set.inter_comm]
  have hcake : ∀ m : Measure (EuclideanSpace ℝ (Fin n)),
      ∫⁻ x, gaussianWeight (sigma ^ 2) x ∂m =
        ∫⁻ t in Ioi (0 : ℝ), m {x | t ≤ f x} := by
    intro m
    simpa only [hfof] using
      (lintegral_eq_lintegral_meas_le m
        (Filter.Eventually.of_forall hf0) hfm.aemeasurable)
  have hleft : ∫⁻ x, gaussianWeight (sigma ^ 2) x ∂nu =
      ∫⁻ x in S, bad x * gaussianWeight (sigma ^ 2) x := by
    change (∫⁻ x, gaussianWeight (sigma ^ 2) x ∂mu.withDensity bad) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hbadm
      (measurable_gaussianWeight _)]
    rfl
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      nu {x | t ≤ f x} ≤ eta * mu {x | t ≤ f x} := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · let r : ℝ := Real.sqrt (-(2 * sigma ^ 2 * Real.log t))
      have hlevel : {x | t ≤ f x} =
          closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
        have h := levelSet_gaussianWeightReal_direct
          (n := n) (s := sigma ^ 2) (by positivity) ht ht1
          (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
        simpa [f, r] using h
      rw [hnuLevel, hmuLevel, hlevel]
      exact setLIntegral_one_sub_ell_levelCore_le_uniform_cv18
        hn hKc hKcl hKfin hball hc0 hc1 hdelta hscale
        hcoeffCore hcoeffPoint (Real.sqrt_nonneg _)
    · have hempty : {x | t ≤ f x} = ∅ := by
        by_contra hne
        obtain ⟨x, htx⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hf1 : f x ≤ 1 :=
          gaussianWeightReal_le_one (by positivity) x
        exact ht1 (htx.trans hf1)
      rw [hempty]
      simp
  have htailMu : Measurable fun t => mu {x | t ≤ f x} :=
    Antitone.measurable fun s t hst => measure_mono fun _ hx => hst.trans hx
  rw [← hleft, hcake nu]
  calc
    (∫⁻ t in Ioi (0 : ℝ), nu {x | t ≤ f x}) ≤
        ∫⁻ t in Ioi (0 : ℝ), eta * mu {x | t ≤ f x} :=
      setLIntegral_mono' measurableSet_Ioi hpoint
    _ = eta * ∫⁻ t in Ioi (0 : ℝ), mu {x | t ≤ f x} := by
      rw [lintegral_const_mul _ htailMu]
    _ = eta * ∫⁻ x in S, gaussianWeight (sigma ^ 2) x := by
      rw [← hcake mu]

/-- Probability-normalized form of the weighted core defect, ready to fill
the `hcoreDefect` input of CV18's speedy-to-target theorem. -/
theorem condOn_gaussian_coreDefect_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta sigma : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) {eta : ENNReal}
    (hcoeffCore : ENNReal.ofReal
        (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta * ENNReal.ofReal (c ^ n))
    (hcoeffPoint : ENNReal.ofReal
        (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
          (2 * delta ^ 2)))) ≤ eta)
    (hmass0 :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K) (c • K) ≠ 0)
    (hmasstop :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K) (c • K) ≠ ⊤) :
    ∫⁻ x, (1 - ell K delta x)
      ∂Arlib.condOn
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))).restrict K) (c • K) ≤ eta := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := c • K
  let w : EuclideanSpace ℝ (Fin n) → ENNReal := gaussianWeight (sigma ^ 2)
  let bad : EuclideanSpace ℝ (Fin n) → ENNReal := fun x => 1 - ell K delta x
  let gammaK : Measure (EuclideanSpace ℝ (Fin n)) :=
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity w).restrict K
  have hSm : MeasurableSet S :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
  have hwm : Measurable w := by
    dsimp [w]
    exact measurable_gaussianWeight _
  have hbadm : Measurable bad := by
    dsimp [bad]
    exact measurable_const.sub (measurable_ell hKcl.measurableSet delta)
  change gammaK S ≠ 0 at hmass0
  change gammaK S ≠ ⊤ at hmasstop
  have hSK : S ∩ K = S := by
    apply Set.inter_eq_left.2
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
      hball (Metric.mem_closedBall_self zero_le_one)
    exact hKc.smul_mem_of_zero_mem hzero hy ⟨hc0.le, hc1.le⟩
  have hmass : gammaK S = ∫⁻ x in S, w x := by
    dsimp [gammaK]
    rw [Measure.restrict_apply hSm, hSK,
      withDensity_apply _ hSm]
  have hraw : ∫⁻ x in S, bad x ∂gammaK =
      ∫⁻ x in S, bad x * w x := by
    change (∫⁻ x, bad x ∂gammaK.restrict S) = _
    dsimp [gammaK]
    rw [Measure.restrict_restrict hSm, hSK]
    change (∫⁻ x in S, bad x ∂
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity w) = _
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hwm hbadm hSm]
    apply setLIntegral_congr_fun hSm
    intro x _
    exact mul_comm _ _
  have hweighted : ∫⁻ x in S, bad x * w x ≤
      eta * ∫⁻ x in S, w x := by
    exact gaussianWeighted_coreDefect_le_cv18 hn hKc hKcl hKfin hball
      hc0 hc1 hdelta hsigma hscale hcoeffCore hcoeffPoint
  rw [Arlib.condOn_def, lintegral_smul_measure]
  change (gammaK S)⁻¹ * (∫⁻ x in S, bad x ∂gammaK) ≤ eta
  rw [hraw, hmass]
  calc
    (∫⁻ x in S, w x)⁻¹ * (∫⁻ x in S, bad x * w x) ≤
        (∫⁻ x in S, w x)⁻¹ *
          (eta * ∫⁻ x in S, w x) := by gcongr
    _ = eta := by
      calc
        (∫⁻ x in S, w x)⁻¹ *
              (eta * ∫⁻ x in S, w x) =
            eta * ((∫⁻ x in S, w x)⁻¹ * ∫⁻ x in S, w x) := by
          ac_rfl
        _ = eta := by
          rw [ENNReal.inv_mul_cancel]
          · simp
          · rw [← hmass]
            exact hmass0
          · rw [← hmass]
            exact hmasstop

/-- The KLS defect estimate also supplies a constant first-rejection
probability.  The coarse Gaussian fact `mass(cK) ≥ 1/2` and defect at most
`1/16` give speedy mass at least `7/16`; this is enough to retain the paper's
`1/4` conditioning floor once the mixing error is small. -/
theorem seven_sixteenths_le_ellGaussianProb_standardCore_of_defect_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    {delta variance : ℝ} (hvariance : 0 < variance)
    (hmass0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hmasstop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {eta : ENNReal} (heta : eta ≤ ENNReal.ofReal (1 / 16 : ℝ))
    (hdefect :
      ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K,
          (1 - ell K delta x) * gaussianWeight variance x ≤
        eta * ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K,
          gaussianWeight variance x) :
    ENNReal.ofReal (7 / 16 : ℝ) ≤
      ellGaussianProb K delta variance
        ((1 - 1 / (2 * (n : ℝ))) • K) := by
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hcoreM : MeasurableSet (c • K) :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
  have hsub : c • K ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem hzero hx ⟨hc0.le, hc1.le⟩
  let G : ENNReal := ∫⁻ x in c • K, gaussianWeight variance x
  let E : ENNReal := ∫⁻ x in c • K,
    ell K delta x * gaussianWeight variance x
  let D : ENNReal := ∫⁻ x in c • K,
    (1 - ell K delta x) * gaussianWeight variance x
  let T : ENNReal := ellGaussianMeasure K delta variance Set.univ
  let GT : ENNReal := ∫⁻ x in K, gaussianWeight variance x
  have hTle : T ≤ GT := by
    dsimp [T, GT]
    rw [ellGaussianMeasure_univ]
    exact setLIntegral_mono' hKcl.measurableSet fun x _ => by
      calc
        ell K delta x * gaussianWeight variance x ≤
            1 * gaussianWeight variance x := by gcongr; exact ell_le_one _ _ _
        _ = gaussianWeight variance x := one_mul _
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * GT ≤ G := by
    dsimp [GT, G, c]
    exact half_mul_gaussianWeight_le_standardCore_cv18
      hn hKcl.measurableSet hvariance
  have hD : D ≤ ENNReal.ofReal (1 / 16 : ℝ) * G := by
    calc
      D ≤ eta * G := by simpa [D, G, c] using hdefect
      _ ≤ ENNReal.ofReal (1 / 16 : ℝ) * G := by gcongr
  have hsplit : G = E + D := by
    dsimp [G, E, D]
    calc
      (∫⁻ x in c • K, gaussianWeight variance x) =
          ∫⁻ x in c • K,
            ell K delta x * gaussianWeight variance x +
              (1 - ell K delta x) * gaussianWeight variance x := by
        apply setLIntegral_congr_fun hcoreM
        intro x _
        change gaussianWeight variance x =
          ell K delta x * gaussianWeight variance x +
            (1 - ell K delta x) * gaussianWeight variance x
        rw [← add_mul]
        rw [add_tsub_cancel_of_le (ell_le_one K delta x), one_mul]
      _ = (∫⁻ x in c • K,
            ell K delta x * gaussianWeight variance x) +
          ∫⁻ x in c • K,
            (1 - ell K delta x) * gaussianWeight variance x :=
        lintegral_add_left
          ((measurable_ell hKcl.measurableSet delta).mul
            (measurable_gaussianWeight variance)) _
  have hGtop : G ≠ ⊤ := by
    apply ne_top_of_le_ne_top hKfin
    dsimp [G]
    calc
      (∫⁻ x in c • K, gaussianWeight variance x) ≤
          ∫⁻ _x in c • K, (1 : ENNReal) :=
        setLIntegral_mono' hcoreM fun x _ => gaussianWeight_le_one hvariance x
      _ = volume (c • K) := by simp
      _ ≤ volume K := measure_mono hsub
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGtop) hD
  have hEmeasure : ellGaussianMeasure K delta variance (c • K) = E := by
    rw [ellGaussianMeasure, withDensity_apply _ hcoreM]
    change (∫⁻ x in c • K,
      ell K delta x * gaussianWeight variance x ∂volume.restrict K) = E
    rw [Measure.restrict_restrict hcoreM]
    have hset : c • K ∩ K = c • K := Set.inter_eq_left.2 hsub
    rw [hset]
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, hEmeasure]
  change ENNReal.ofReal (7 / 16 : ℝ) ≤ T⁻¹ * E
  rw [← ENNReal.div_eq_inv_mul]
  refine (ENNReal.le_div_iff_mul_le (Or.inl hmass0) (Or.inl hmasstop)).2 ?_
  apply ENNReal.le_of_add_le_add_right hDtop
  rw [← hsplit]
  calc
    ENNReal.ofReal (7 / 16 : ℝ) * T + D ≤
        ENNReal.ofReal (7 / 16 : ℝ) * GT +
          ENNReal.ofReal (1 / 16 : ℝ) * G := add_le_add (by gcongr) hD
    _ ≤ ENNReal.ofReal (7 / 8 : ℝ) * G +
          ENNReal.ofReal (1 / 16 : ℝ) * G := by
      have hseven : ENNReal.ofReal (7 / 16 : ℝ) * GT ≤
          ENNReal.ofReal (7 / 8 : ℝ) * G := by
        calc
        ENNReal.ofReal (7 / 16 : ℝ) * GT =
            ENNReal.ofReal (7 / 8 : ℝ) *
              (ENNReal.ofReal (1 / 2 : ℝ) * GT) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal (7 / 8 : ℝ) * G := by gcongr
      exact add_le_add hseven le_rfl
    _ ≤ G := by
      calc
        ENNReal.ofReal (7 / 8 : ℝ) * G +
              ENNReal.ofReal (1 / 16 : ℝ) * G =
            ENNReal.ofReal (15 / 16 : ℝ) * G := by
          rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
        _ ≤ 1 * G := by gcongr <;> norm_num
        _ = G := one_mul _

/-- The elementary parameter calculation behind CV18's choice of proposal
radius.  A logarithmic rate bound implies both exponential coefficients
required by `condOn_gaussian_coreDefect_le_cv18`. -/
theorem standardCore_exp_coefficients_cv18
    (hn : 1 ≤ n) {delta eps : ℝ}
    (hdelta : 0 < delta) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 10)
    (hrate : Real.log ((n : ℝ) / eps) ≤
      1 / (32 * (n : ℝ) * delta ^ 2)) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    ENNReal.ofReal
        (Real.exp (-((n : ℝ) * ((1 - c) / 2) ^ 2 /
          (2 * delta ^ 2)))) ≤ ENNReal.ofReal eps ∧
      ENNReal.ofReal
        (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
          (2 * delta ^ 2)))) ≤
        ENNReal.ofReal eps * ENNReal.ofReal (c ^ n) := by
  dsimp only
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : 0 < (n : ℝ) / eps := div_pos hn0 heps0
  let rate : ℝ := 1 / (32 * (n : ℝ) * delta ^ 2)
  have hpointEq : (n : ℝ) * ((1 - c) / 2) ^ 2 /
      (2 * delta ^ 2) = rate := by
    dsimp [c, rate]
    field_simp
    ring
  have hcoreEq : (n : ℝ) * (1 - c) ^ 2 /
      (2 * delta ^ 2) = 4 * rate := by
    dsimp [c, rate]
    field_simp
    ring
  have hexpLog : Real.exp (-Real.log ((n : ℝ) / eps)) =
      eps / (n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hq0]
    field_simp
  have hratio : eps / (n : ℝ) ≤ eps := by
    rw [div_le_iff₀ hn0]
    nlinarith
  have hpointReal : Real.exp (-rate) ≤ eps := by
    calc
      Real.exp (-rate) ≤ Real.exp (-Real.log ((n : ℝ) / eps)) := by
        exact Real.exp_le_exp.mpr (neg_le_neg hrate)
      _ = eps / (n : ℝ) := hexpLog
      _ ≤ eps := hratio
  have hexpFour : Real.exp (-4 * Real.log ((n : ℝ) / eps)) =
      (eps / (n : ℝ)) ^ 4 := by
    calc
      Real.exp (-4 * Real.log ((n : ℝ) / eps)) =
          Real.exp (-Real.log ((n : ℝ) / eps)) ^ 4 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ = (eps / (n : ℝ)) ^ 4 := by rw [hexpLog]
  have hcoreExp : Real.exp (-(4 * rate)) ≤
      (eps / (n : ℝ)) ^ 4 := by
    calc
      Real.exp (-(4 * rate)) ≤
          Real.exp (-4 * Real.log ((n : ℝ) / eps)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hrate]
      _ = _ := hexpFour
  have hratio0 : 0 ≤ eps / (n : ℝ) := (div_pos heps0 hn0).le
  have hratioPow : (eps / (n : ℝ)) ^ 4 ≤ eps ^ 4 :=
    pow_le_pow_left₀ hratio0 hratio 4
  have heps3 : eps ^ 3 ≤ (1 / 10 : ℝ) ^ 3 :=
    pow_le_pow_left₀ heps0.le heps1 3
  have heps4 : 2 * eps ^ 4 ≤ eps / 2 := by
    have hmul := mul_le_mul_of_nonneg_left heps3 heps0.le
    have heq : eps * eps ^ 3 = eps ^ 4 := by ring
    rw [heq] at hmul
    norm_num at hmul ⊢
    linarith
  have hcoreReal : 2 * Real.exp (-(4 * rate)) ≤ eps / 2 := by
    calc
      2 * Real.exp (-(4 * rate)) ≤
          2 * (eps / (n : ℝ)) ^ 4 := by gcongr
      _ ≤ 2 * eps ^ 4 := by gcongr
      _ ≤ eps / 2 := heps4
  have hcpow : (1 : ℝ) / 2 ≤ c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow_cv18 hn
  constructor
  · apply ENNReal.ofReal_le_ofReal
    rw [hpointEq]
    exact hpointReal
  · rw [← ENNReal.ofReal_mul heps0.le]
    apply ENNReal.ofReal_le_ofReal
    rw [hcoreEq]
    change 2 * Real.exp (-(4 * rate)) ≤ eps * c ^ n
    have hcpow' : (2 : ℝ)⁻¹ ≤ c ^ n := by
      simpa [one_div] using hcpow
    exact hcoreReal.trans (mul_le_mul_of_nonneg_left hcpow' heps0.le)

/-- CV18's displayed proposal-radius condition implies the logarithmic rate
hypothesis used by `standardCore_exp_coefficients_cv18`. -/
theorem paper_step_implies_standardCore_rate_cv18
    (hn : 1 ≤ n) {delta eps : ℝ}
    (hdelta : 0 < delta) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 10)
    (hstep : delta ≤
      1 / (8 * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) / eps)))) :
    Real.log ((n : ℝ) / eps) ≤
      1 / (32 * (n : ℝ) * delta ^ 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hratio : 1 < (n : ℝ) / eps := by
    rw [lt_div_iff₀ heps0]
    linarith
  have hlog : 0 < Real.log ((n : ℝ) / eps) := Real.log_pos hratio
  let L : ℝ := Real.log ((n : ℝ) / eps)
  let b : ℝ := 1 / (8 * Real.sqrt ((n : ℝ) * L))
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * L) :=
    Real.sqrt_pos.2 (mul_pos hn0 (by simpa [L] using hlog))
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hsq : delta ^ 2 ≤ b ^ 2 := by
    nlinarith [sq_nonneg (b - delta)]
  have hbSq : b ^ 2 = 1 / (64 * (n : ℝ) * L) := by
    dsimp [b]
    rw [div_pow, one_pow, mul_pow, show (8 : ℝ) ^ 2 = 64 by norm_num,
      Real.sq_sqrt (mul_nonneg hn0.le (by simpa [L] using hlog.le))]
    ring
  rw [hbSq] at hsq
  change L ≤ 1 / (32 * (n : ℝ) * delta ^ 2)
  rw [le_div_iff₀ (by positivity : 0 < 32 * (n : ℝ) * delta ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 32 * (n : ℝ) * L by positivity)
  have hLne : L ≠ 0 := ne_of_gt (by simpa [L] using hlog)
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hn0
  field_simp [hLne, hnNe] at hmul
  rw [div_self hLne] at hmul
  nlinarith

/-- The same displayed CV18 proposal-radius condition also supplies the
geometric scale separation required by the KLS core argument. -/
theorem paper_step_implies_standardCore_scale_cv18
    (hn : 1 ≤ n) {delta eps : ℝ}
    (hdelta : 0 < delta) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 10)
    (hstep : delta ≤
      1 / (8 * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) / eps)))) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    4 * delta ^ 2 ≤ 1 - c := by
  dsimp only
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hratio10 : 10 ≤ (n : ℝ) / eps := by
    rw [le_div_iff₀ heps0]
    nlinarith
  have hratio0 : 0 < (n : ℝ) / eps := div_pos hn0 heps0
  have hlog1 : 1 ≤ Real.log ((n : ℝ) / eps) :=
    (Real.le_log_iff_exp_le hratio0).2
      (Real.exp_one_lt_three.le.trans
        ((by norm_num : (3 : ℝ) ≤ 10).trans hratio10))
  let L : ℝ := Real.log ((n : ℝ) / eps)
  let b : ℝ := 1 / (8 * Real.sqrt ((n : ℝ) * L))
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * L) :=
    Real.sqrt_pos.2 (mul_pos hn0 (by simpa [L] using (lt_of_lt_of_le zero_lt_one hlog1)))
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hsq : delta ^ 2 ≤ b ^ 2 := by
    nlinarith [sq_nonneg (b - delta)]
  have hbSq : b ^ 2 = 1 / (64 * (n : ℝ) * L) := by
    dsimp [b]
    rw [div_pow, one_pow, mul_pow, show (8 : ℝ) ^ 2 = 64 by norm_num,
      Real.sq_sqrt (mul_nonneg hn0.le (by dsimp [L]; linarith))]
    ring
  rw [hbSq] at hsq
  calc
    4 * delta ^ 2 ≤ 4 * (1 / (64 * (n : ℝ) * L)) := by gcongr
    _ = 1 / (16 * (n : ℝ) * L) := by ring
    _ ≤ 1 / (2 * (n : ℝ)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (1 : ℝ) ≤ L := by simpa [L] using hlog1
        nlinarith
    _ = 1 - (1 - 1 / (2 * (n : ℝ))) := by ring

/-- Paper-shaped packaging of the KLS calculation.  Under CV18's displayed
proposal-radius condition, the standard homothetic core simultaneously has
small normalized local-conductance defect and constant speedy mass. -/
theorem standardCore_defect_and_speedyMass_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta sigma eps : ℝ} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (heps0 : 0 < eps) (heps16 : eps ≤ 1 / 16)
    (hstep : delta ≤
      1 / (8 * Real.sqrt ((n : ℝ) * Real.log ((n : ℝ) / eps))))
    (hgaussCore0 :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K)
          ((1 - 1 / (2 * (n : ℝ))) • K) ≠ 0)
    (hgaussCoretop :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K)
          ((1 - 1 / (2 * (n : ℝ))) • K) ≠ ⊤)
    (hspeedy0 : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ 0)
    (hspeedytop : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ ⊤) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    (∫⁻ x, (1 - ell K delta x)
        ∂Arlib.condOn
          (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (sigma ^ 2))).restrict K) (c • K)) ≤
          ENNReal.ofReal eps ∧
      ENNReal.ofReal (7 / 16 : ℝ) ≤
        ellGaussianProb K delta (sigma ^ 2) (c • K) := by
  dsimp only
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have heps10 : eps ≤ 1 / 10 := by linarith
  have hrate := paper_step_implies_standardCore_rate_cv18
    hn hdelta heps0 heps10 hstep
  have hcoeff := standardCore_exp_coefficients_cv18
    hn hdelta heps0 heps10 hrate
  have hscale : 4 * delta ^ 2 ≤ 1 - c := by
    simpa [c] using paper_step_implies_standardCore_scale_cv18
      hn hdelta heps0 heps10 hstep
  have hraw := gaussianWeighted_coreDefect_le_cv18
    hn hKc hKcl hKfin hball hc0 hc1 hdelta hsigma hscale
      hcoeff.2 hcoeff.1
  constructor
  · exact condOn_gaussian_coreDefect_le_cv18
      hn hKc hKcl hKfin hball hc0 hc1 hdelta hsigma hscale
        hcoeff.2 hcoeff.1 hgaussCore0 hgaussCoretop
  · have heta : ENNReal.ofReal eps ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
      ENNReal.ofReal_le_ofReal heps16
    simpa [c] using
      (seven_sixteenths_le_ellGaussianProb_standardCore_of_defect_cv18
        hn hKc hKcl hKfin
        (hball (Metric.mem_closedBall_self zero_le_one))
        (by positivity : 0 < sigma ^ 2) hspeedy0 hspeedytop heta hraw)

/-- End-to-end form of the paper's phase-local speedy-to-Gaussian conversion.
The KLS core hypotheses are discharged from the displayed proposal radius;
only normalization guards and the incoming speedy mixing estimate remain. -/
theorem TVLe.speedyToGaussian_of_paperStep_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta sigma coreError : ℝ} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hcoreError0 : 0 < coreError) (hcoreError16 : coreError ≤ 1 / 16)
    (hstep : delta ≤
      1 / (8 * Real.sqrt
        ((n : ℝ) * Real.log ((n : ℝ) / coreError))))
    (hgaussCore0 :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K)
          ((1 - 1 / (2 * (n : ℝ))) • K) ≠ 0)
    (hgaussCoretop :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K)
          ((1 - 1 / (2 * (n : ℝ))) • K) ≠ ⊤)
    (hspeedy0 : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ 0)
    (hspeedytop : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ ⊤)
    (hproposal0 :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (sigma ^ 2 / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ 0)
    (hproposaltop :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (sigma ^ 2 / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ ⊤)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu]
    {mixError : ENNReal}
    (hmix : Arlib.TVLe mu (ellGaussianProb K delta (sigma ^ 2)) mixError)
    (hmixTop : mixError ≠ ⊤)
    (hcombined : 8 * mixError + 4 * ENNReal.ofReal coreError ≤
      ENNReal.ofReal (1 / 4 : ℝ)) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (gaussianScaleAcceptance (sigma ^ 2) c)) Set.univ)
      (Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))) K)
      (64 * mixError + 32 * ENNReal.ofReal coreError) := by
  dsimp only
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hpaper := standardCore_defect_and_speedyMass_cv18
    hn hKc hKcl hKfin hball hdelta hsigma hcoreError0 hcoreError16
      hstep hgaussCore0 hgaussCoretop hspeedy0 hspeedytop
  have hetaTop : ENNReal.ofReal coreError ≠ ⊤ := ENNReal.ofReal_ne_top
  have hetaHalf : ENNReal.ofReal coreError ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    ENNReal.ofReal_le_ofReal (hcoreError16.trans (by norm_num))
  exact TVLe.speedyToGaussian_twoStage_of_coreDefect_cv18
    hn hKcl.measurableSet hKc
      (hball (Metric.mem_closedBall_self zero_le_one))
      (by positivity : 0 < sigma ^ 2)
      hspeedy0 hspeedytop hproposal0 hproposaltop
      (by simpa [c] using hpaper.2)
      (by simpa [c] using hgaussCore0)
      (by simpa [c] using hgaussCoretop)
      hetaTop hetaHalf (by simpa [c] using hpaper.1)
      hmix hmixTop hcombined

/-- Guard-free body-level version of `speedyToGaussian_of_paperStep_cv18`.
Positive finite volume and bounded convex geometry discharge every
normalization side condition. -/
theorem TVLe.speedyToGaussian_of_paperStep_of_body_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta sigma coreError : ℝ} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hcoreError0 : 0 < coreError) (hcoreError16 : coreError ≤ 1 / 16)
    (hstep : delta ≤
      1 / (8 * Real.sqrt
        ((n : ℝ) * Real.log ((n : ℝ) / coreError))))
    {mu : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu]
    {mixError : ENNReal}
    (hmix : Arlib.TVLe mu (ellGaussianProb K delta (sigma ^ 2)) mixError)
    (hmixTop : mixError ≠ ⊤)
    (hcombined : 8 * mixError + 4 * ENNReal.ofReal coreError ≤
      ENNReal.ofReal (1 / 4 : ℝ)) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (gaussianScaleAcceptance (sigma ^ 2) c)) Set.univ)
      (Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight (sigma ^ 2))) K)
      (64 * mixError + 32 * ENNReal.ofReal coreError) := by
  dsimp only
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hcoreM : MeasurableSet (c • K) :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
  have hsub : c • K ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem
      (hball (Metric.mem_closedBall_self zero_le_one)) hx ⟨hc0.le, hc1.le⟩
  have hcoreVol0 : volume (c • K) ≠ 0 := by
    rw [Arlib.volume_smul_euclidean hc0.le]
    exact mul_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 n)) hK0
  have hcoreVoltop : volume (c • K) ≠ ⊤ := by
    rw [Arlib.volume_smul_euclidean hc0.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin
  have hgaussCore0 :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K) (c • K) ≠ 0 := by
    rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
    exact withDensity_gaussianWeight_ne_zero _ hcoreVol0
  have hgaussCoretop :
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2))).restrict K) (c • K) ≠ ⊤ := by
    rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
    exact withDensity_gaussianWeight_ne_top (by positivity) hcoreM hcoreVoltop
  have hspeedy0 : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hKcl.measurableSet hKc hKb hK0 hdelta _
  have hspeedytop : ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKfin delta (by positivity)
  have hscaled : 0 < sigma ^ 2 / c ^ 2 := by positivity
  have hproposal0 :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2 / c ^ 2))) K ≠ 0 :=
    withDensity_gaussianWeight_ne_zero _ hK0
  have hproposaltop :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (sigma ^ 2 / c ^ 2))) K ≠ ⊤ :=
    withDensity_gaussianWeight_ne_top hscaled hKcl.measurableSet hKfin
  exact TVLe.speedyToGaussian_of_paperStep_cv18
    hn hKc hKcl hKfin hball hdelta hsigma hcoreError0 hcoreError16 hstep
      (by simpa [c] using hgaussCore0)
      (by simpa [c] using hgaussCoretop)
      hspeedy0 hspeedytop
      (by simpa [c] using hproposal0)
      (by simpa [c] using hproposaltop)
      hmix hmixTop hcombined

end Arlib.MarkovChains
