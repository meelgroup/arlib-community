/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.PrekopaLeindler
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofWarmStart

open MeasureTheory
open scoped ENNReal

namespace ArlibCommunity.Algorithms.CV18

/-! # Gaussian partition log-concavity

This file supplies the geometric input used by the sharp fixed-rate moment
bound.  The proof is routed through the finite-dimensional
Prékopa--Leindler inequality, transported from coordinate functions to
`EuclideanSpace`.
-/

/-- Prékopa--Leindler on the Euclidean-space spelling used by CV18. -/
theorem prekopaLeindler_euclidean {n : ℕ}
    {f g h : AmbientSpace n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hle : ∀ x y : AmbientSpace n,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have he : MeasurableEmbedding (@WithLp.toLp 2 (Fin n → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hPL := AsymptoticStatistics.prekopaLeindler
    (hf.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    (hg.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    (hh.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    ht ht1 (fun x y => by
      simpa [map_add, map_smul] using
        hle (WithLp.toLp 2 x) (WithLp.toLp 2 y))
  simpa only [Function.comp_apply,
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb he f,
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb he g,
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb he h] using hPL

/-- The perspective density whose marginal in the precision parameter is
`a^(n+1) * Z(1/a)`. -/
noncomputable def gaussianPerspective {n : ℕ}
    (K : Set (AmbientSpace n)) (a : ℝ) (x : AmbientSpace n) : ℝ :=
  {x | a⁻¹ • x ∈ K}.indicator (fun y => a * gaussianDensity a y) x

theorem gaussianPerspective_nonneg {n : ℕ} (K : Set (AmbientSpace n))
    {a : ℝ} (ha : 0 ≤ a) (x : AmbientSpace n) :
    0 ≤ gaussianPerspective K a x := by
  unfold gaussianPerspective
  exact Set.indicator_nonneg (fun y _ => mul_nonneg ha (by
    unfold gaussianDensity
    exact (Real.exp_pos _).le)) x

theorem measurable_gaussianPerspective {n : ℕ} (K : Set (AmbientSpace n))
    (hK : MeasurableSet K) (a : ℝ) :
    Measurable (gaussianPerspective K a) := by
  unfold gaussianPerspective
  apply Measurable.indicator
  · exact measurable_const.mul (by unfold gaussianDensity; fun_prop)
  · exact ((measurable_const : Measurable fun _ : AmbientSpace n => (a⁻¹ : ℝ)).smul
      measurable_id) hK

/-- The Gaussian perspective is log-concave at midpoints before restricting
to the perspective cone of a convex set. -/
theorem gaussianPerspectiveDensity_mul_le_sq {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : AmbientSpace n) :
    (a * gaussianDensity a x) * (b * gaussianDensity b y) ≤
      (((a + b) / 2) *
        gaussianDensity ((a + b) / 2) ((2 : ℝ)⁻¹ • (x + y))) ^ 2 := by
  have hab : 0 < a + b := add_pos ha hb
  have hm : 0 < (a + b) / 2 := by positivity
  have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have htri_sq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
  have hweighted : (‖x‖ + ‖y‖) ^ 2 ≤
      (a + b) * (‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b) := by
    rw [← sub_nonneg]
    have hid :
        (a + b) * (‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b) -
            (‖x‖ + ‖y‖) ^ 2 =
          (b * ‖x‖ - a * ‖y‖) ^ 2 / (a * b) := by
      field_simp [ha.ne', hb.ne']
      ring
    rw [hid]
    positivity
  have hnorm : ‖x + y‖ ^ 2 ≤
      (a + b) * (‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b) :=
    htri_sq.trans hweighted
  have hmidnorm : ‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ((a + b) / 2) =
      ‖x + y‖ ^ 2 / (2 * (a + b)) := by
    rw [norm_smul]
    norm_num [Real.norm_eq_abs]
    field_simp [hab.ne']
  have hexponent :
      -‖x‖ ^ 2 / (2 * a) + -‖y‖ ^ 2 / (2 * b) ≤
        2 * (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / (2 * ((a + b) / 2))) := by
    have hscaled : ‖x + y‖ ^ 2 / (2 * (a + b)) ≤
        (‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b) / 2 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * (a + b))]
      nlinarith
    have hdouble : 2 * (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 /
          (2 * ((a + b) / 2))) =
        -‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ((a + b) / 2) := by
      field_simp [hab.ne']
    have hmidnorm_neg : -‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ((a + b) / 2) =
        -(‖x + y‖ ^ 2 / (2 * (a + b))) := by
      rw [neg_div, hmidnorm]
    have hlhs : -‖x‖ ^ 2 / (2 * a) + -‖y‖ ^ 2 / (2 * b) =
        -((‖x‖ ^ 2 / a + ‖y‖ ^ 2 / b) / 2) := by ring
    rw [hdouble, hmidnorm_neg]
    rw [hlhs]
    exact neg_le_neg hscaled
  have hprefactor : a * b ≤ ((a + b) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  rw [gaussianDensity_eq, gaussianDensity_eq, gaussianDensity_eq]
  calc
    (a * Real.exp (-‖x‖ ^ 2 / (2 * a))) *
          (b * Real.exp (-‖y‖ ^ 2 / (2 * b))) =
        (a * b) * Real.exp
          (-‖x‖ ^ 2 / (2 * a) + -‖y‖ ^ 2 / (2 * b)) := by
      rw [Real.exp_add]
      ring
    _ ≤ ((a + b) / 2) ^ 2 * Real.exp
          (-‖x‖ ^ 2 / (2 * a) + -‖y‖ ^ 2 / (2 * b)) := by
      gcongr
    _ ≤ ((a + b) / 2) ^ 2 * Real.exp
          (2 * (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 /
            (2 * ((a + b) / 2)))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (sq_nonneg _)
    _ = (((a + b) / 2) *
          Real.exp (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 /
            (2 * ((a + b) / 2)))) ^ 2 := by
      rw [show 2 * (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 /
          (2 * ((a + b) / 2))) =
        (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / (2 * ((a + b) / 2))) +
          (-‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / (2 * ((a + b) / 2))) by ring,
        Real.exp_add]
      ring

/-- Restricting the perspective density to the perspective cone of a convex
set preserves its midpoint log-concavity. -/
theorem gaussianPerspective_mul_le_sq {n : ℕ} {K : Set (AmbientSpace n)}
    (hK : Convex ℝ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : AmbientSpace n) :
    gaussianPerspective K a x * gaussianPerspective K b y ≤
      gaussianPerspective K ((a + b) / 2)
        ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ^ 2 := by
  let z : AmbientSpace n := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hab : 0 < a + b := add_pos ha hb
  have hm : 0 < (a + b) / 2 := by positivity
  by_cases hx : a⁻¹ • x ∈ K
  · by_cases hy : b⁻¹ • y ∈ K
    · have hwa : 0 ≤ a / (a + b) := by positivity
      have hwb : 0 ≤ b / (a + b) := by positivity
      have hw : a / (a + b) + b / (a + b) = 1 := by
        field_simp [hab.ne']
      have hconv := hK hx hy hwa hwb hw
      have hzEq : ((a + b) / 2)⁻¹ • z =
          (a / (a + b)) • (a⁻¹ • x) +
            (b / (a + b)) • (b⁻¹ • y) := by
        ext i
        change ((a + b) / 2)⁻¹ * ((1 / 2) * x i + (1 / 2) * y i) =
          (a / (a + b)) * (a⁻¹ * x i) +
            (b / (a + b)) * (b⁻¹ * y i)
        field_simp [ha.ne', hb.ne', hab.ne']
      have hz : ((a + b) / 2)⁻¹ • z ∈ K := hzEq ▸ hconv
      unfold gaussianPerspective
      rw [Set.indicator_of_mem (show x ∈ {x | a⁻¹ • x ∈ K} from hx),
        Set.indicator_of_mem (show y ∈ {x | b⁻¹ • x ∈ K} from hy),
        Set.indicator_of_mem
          (show z ∈ {x | ((a + b) / 2)⁻¹ • x ∈ K} from hz)]
      have hz' : z = (2 : ℝ)⁻¹ • (x + y) := by
        ext i
        simp [z, PiLp.smul_apply]
      rw [hz']
      exact gaussianPerspectiveDensity_mul_le_sq ha hb x y
    · unfold gaussianPerspective
      rw [Set.indicator_of_notMem
        (show y ∉ {x | b⁻¹ • x ∈ K} from hy), mul_zero]
      exact sq_nonneg _
  · unfold gaussianPerspective
    rw [Set.indicator_of_notMem
      (show x ∉ {x | a⁻¹ • x ∈ K} from hx), zero_mul]
    exact sq_nonneg _

/-- ENNReal half-power form of the preceding squared inequality, matching
the pointwise premise of Prékopa--Leindler at `t = 1/2`. -/
theorem gaussianPerspective_geomMean_le {n : ℕ} {K : Set (AmbientSpace n)}
    (hK : Convex ℝ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : AmbientSpace n) :
    ENNReal.ofReal (gaussianPerspective K a x) ^ ((1 : ℝ) / 2) *
        ENNReal.ofReal (gaussianPerspective K b y) ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (gaussianPerspective K ((a + b) / 2)
        ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) := by
  have hFa := gaussianPerspective_nonneg K ha.le x
  have hFb := gaussianPerspective_nonneg K hb.le y
  have hFm := gaussianPerspective_nonneg K (by positivity : 0 ≤ (a + b) / 2)
    ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  have hsqReal := gaussianPerspective_mul_le_sq hK ha hb x y
  have hsq :
      ENNReal.ofReal (gaussianPerspective K a x) *
          ENNReal.ofReal (gaussianPerspective K b y) ≤
        ENNReal.ofReal (gaussianPerspective K ((a + b) / 2)
          ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ^ 2 := by
    rw [← ENNReal.ofReal_mul hFa, ← ENNReal.ofReal_pow hFm]
    exact ENNReal.ofReal_le_ofReal hsqReal
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have htaken := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsimp :
      (ENNReal.ofReal (gaussianPerspective K ((a + b) / 2)
          ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ^ 2) ^ ((1 : ℝ) / 2) =
        ENNReal.ofReal (gaussianPerspective K ((a + b) / 2)
          ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rw [hsimp] at htaken
  exact htaken

theorem integrable_gaussianPerspective {n : ℕ} (K : Set (AmbientSpace n))
    (hK : MeasurableSet K) {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianPerspective K a) := by
  unfold gaussianPerspective
  exact ((integrable_gaussianDensity ha).const_mul a).indicator
    (((measurable_const : Measurable fun _ : AmbientSpace n => (a⁻¹ : ℝ)).smul
      measurable_id) hK)

/-- Prékopa--Leindler integrated form for the Gaussian perspective. -/
theorem integral_gaussianPerspective_mul_le_sq {n : ℕ}
    (K : Set (AmbientSpace n)) (hKmeas : MeasurableSet K)
    (hKconv : Convex ℝ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, gaussianPerspective K a x) *
        (∫ x, gaussianPerspective K b x) ≤
      (∫ x, gaussianPerspective K ((a + b) / 2) x) ^ 2 := by
  let F : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K a x)
  let G : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K b x)
  let H : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K ((a + b) / 2) x)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas a)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas b)
  have hH : Measurable H := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas ((a + b) / 2))
  have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hPL : (∫⁻ x, F x) ^ ((1 : ℝ) / 2) *
        (∫⁻ x, G x) ^ ((1 : ℝ) / 2) ≤ ∫⁻ x, H x := by
    have h := prekopaLeindler_euclidean hF hG hH
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (fun x y => by
        rw [hone]
        exact gaussianPerspective_geomMean_le hKconv ha hb x y)
    rw [hone] at h
    exact h
  let A : ℝ≥0∞ := ∫⁻ x, F x
  let B : ℝ≥0∞ := ∫⁻ x, G x
  let C : ℝ≥0∞ := ∫⁻ x, H x
  have hAhalf : A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, ENNReal.rpow_one]
  have hBhalf : B ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) = B := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, ENNReal.rpow_one]
  have hsqENN : A * B ≤ C ^ 2 := by
    have hmul := mul_le_mul hPL hPL (by positivity) (by positivity)
    change (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) *
        (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) ≤ C * C at hmul
    calc
      A * B =
          (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) *
            (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
        rw [mul_mul_mul_comm, hAhalf, hBhalf]
      _ ≤ C * C := hmul
      _ = C ^ 2 := by ring
  have hIa := integrable_gaussianPerspective K hKmeas ha
  have hIb := integrable_gaussianPerspective K hKmeas hb
  have hm : 0 < (a + b) / 2 := by positivity
  have hIm := integrable_gaussianPerspective K hKmeas hm
  have hIa0 : 0 ≤ ∫ x, gaussianPerspective K a x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K ha.le x
  have hIb0 : 0 ≤ ∫ x, gaussianPerspective K b x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K hb.le x
  have hIm0 : 0 ≤ ∫ x, gaussianPerspective K ((a + b) / 2) x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K hm.le x
  have hsqRealLift :
      ENNReal.ofReal (∫ x, gaussianPerspective K a x) *
          ENNReal.ofReal (∫ x, gaussianPerspective K b x) ≤
        ENNReal.ofReal (∫ x, gaussianPerspective K ((a + b) / 2) x) ^ 2 := by
    simpa [A, B, C, F, G, H,
      ← ofReal_integral_eq_lintegral_ofReal hIa
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K ha.le x),
      ← ofReal_integral_eq_lintegral_ofReal hIb
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K hb.le x),
      ← ofReal_integral_eq_lintegral_ofReal hIm
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K hm.le x)] using hsqENN
  rw [← ENNReal.ofReal_mul hIa0, ← ENNReal.ofReal_pow hIm0] at hsqRealLift
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hsqRealLift

theorem gaussianDensity_precision_scale {n : ℕ} {a : ℝ} (ha : 0 < a)
    (x : AmbientSpace n) :
    gaussianDensity a (a • x) = gaussianDensity (1 / a) x := by
  rw [gaussianDensity_eq, gaussianDensity_eq, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  congr 1
  field_simp [ha.ne']

/-- Change of variables `y = a x`: the perspective marginal is precisely
`a^(n+1) Z(1/a)`. -/
theorem integral_gaussianPerspective_eq {n : ℕ}
    (K : Set (AmbientSpace n)) {a : ℝ} (ha : 0 < a) :
    (∫ y, gaussianPerspective K a y) =
      a ^ (n + 1) * gaussianIntegral K (1 / a) := by
  have hpoint : ∀ x : AmbientSpace n,
      gaussianPerspective K a (a • x) =
        a * unnormGaussian K (1 / a) x := by
    intro x
    unfold gaussianPerspective unnormGaussian
    have hcancel : a⁻¹ • (a • x) = x := by
      rw [← mul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    have hmem : a • x ∈ {y | a⁻¹ • y ∈ K} ↔ x ∈ K := by
      change a⁻¹ • (a • x) ∈ K ↔ x ∈ K
      rw [hcancel]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx,
        gaussianDensity_precision_scale ha, gaussianDensity_eq]
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)),
        Set.indicator_of_notMem hx, mul_zero]
  have hleft : (∫ x, gaussianPerspective K a (a • x)) =
      a * gaussianIntegral K (1 / a) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_const_mul]
    rfl
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (gaussianPerspective K a) a (hR := ha.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchange
  rw [hleft] at hchange
  have hapow : a ^ n ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp [hapow] at hchange
  calc
    (∫ y, gaussianPerspective K a y) =
        a ^ n * (a * gaussianIntegral K (1 / a)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hchange.symm
    _ = a ^ (n + 1) * gaussianIntegral K (1 / a) := by
      rw [pow_succ]
      ring

/-- Midpoint log-concavity in Gaussian precision, in exactly the weighted
form cited as `lem:z-logconcave` by CV18. -/
def GaussianPartitionMidpointLogConcave {n : ℕ}
    (K : Set (AmbientSpace n)) : Prop :=
  ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b →
    (a ^ (n + 1) * gaussianIntegral K (1 / a)) *
        (b ^ (n + 1) * gaussianIntegral K (1 / b)) ≤
      (((a + b) / 2) ^ (n + 1) *
        gaussianIntegral K (2 / (a + b))) ^ 2

/-- Prékopa--Leindler proves the weighted Gaussian partition midpoint
inequality for every measurable convex set. -/
theorem gaussianPartitionMidpointLogConcave {n : ℕ}
    (K : Set (AmbientSpace n)) (hKmeas : MeasurableSet K)
    (hKconv : Convex ℝ K) : GaussianPartitionMidpointLogConcave K := by
  intro a b ha hb
  have hm : 0 < (a + b) / 2 := by positivity
  have h := integral_gaussianPerspective_mul_le_sq K hKmeas hKconv ha hb
  rw [integral_gaussianPerspective_eq K ha,
    integral_gaussianPerspective_eq K hb,
    integral_gaussianPerspective_eq K hm] at h
  have hvariance : 1 / ((a + b) / 2) = 2 / (a + b) := by
    field_simp [(add_pos ha hb).ne']
  rw [hvariance] at h
  exact h

theorem truncatedBody_gaussianPartitionMidpointLogConcave
    (q : VolumeParams) (I : VolumeInput q.n) :
    GaussianPartitionMidpointLogConcave (truncatedBody q I) :=
  gaussianPartitionMidpointLogConcave (truncatedBody q I)
    (truncatedBody_measurable q I) (truncatedVolumeInput q I).body.convex

end ArlibCommunity.Algorithms.CV18
