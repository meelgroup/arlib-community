/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable def gaussianDensity {n : ℕ} (s : ℝ) (x : AmbientSpace n) : ℝ :=
  Real.exp (- (1 / (2 * s)) * ‖x‖ ^ 2)

theorem gaussianDensity_eq (s : ℝ) (x : AmbientSpace n) :
    gaussianDensity s x = Real.exp (-‖x‖ ^ 2 / (2 * s)) := by
  unfold gaussianDensity
  congr 1
  field_simp

theorem integral_gaussianDensity {n : ℕ} {s : ℝ} (hs : 0 < s) :
    ∫ x : AmbientSpace n, gaussianDensity s x =
      Real.rpow (2 * Real.pi * s) ((n : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := AmbientSpace n) (b := (1 / (2 * s) : ℝ)) (by positivity)
  rw [show (Real.pi / (1 / (2 * s))) = 2 * Real.pi * s by field_simp] at h
  simpa [gaussianDensity, finrank_euclideanSpace_fin] using h

theorem integrable_gaussianDensity {n : ℕ} {s : ℝ} (hs : 0 < s) :
    Integrable (gaussianDensity (n := n) s) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianDensity hs]
  exact (Real.rpow_pos_of_pos (by positivity) _).ne'

theorem gaussianIntegral_univ {n : ℕ} {s : ℝ} (hs : 0 < s) :
    gaussianIntegral (Set.univ : Set (AmbientSpace n)) s =
      Real.rpow (2 * Real.pi * s) ((n : ℝ) / 2) := by
  simp only [gaussianIntegral, unnormGaussian, Set.indicator_univ]
  simpa [gaussianDensity, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (integral_gaussianDensity (n := n) hs)

lemma gaussianDensity_tail_pointwise {n : ℕ} {s : ℝ} (hs : 0 < s)
    {x : AmbientSpace n} (hx : x ∈ (unitBall n)ᶜ) :
    gaussianDensity s x ≤ Real.exp (-1 / (4 * s)) * gaussianDensity (2 * s) x := by
  have hxnorm : 1 < ‖x‖ := by
    simpa [unitBall, Metric.mem_closedBall, dist_zero_right] using hx
  have hx_sq : 1 ≤ ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg x]
  rw [gaussianDensity, gaussianDensity, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  field_simp
  nlinarith

lemma gaussianDensity_tail_le {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (∫ x in (unitBall n)ᶜ, gaussianDensity s x) ≤
      Real.exp (-1 / (4 * s)) *
        Real.rpow (4 * Real.pi * s) ((n : ℝ) / 2) := by
  let c : ℝ := Real.exp (-1 / (4 * s))
  have hf := integrable_gaussianDensity (n := n) hs
  have hg := integrable_gaussianDensity (n := n) (show 0 < 2 * s by positivity)
  calc
    (∫ x in (unitBall n)ᶜ, gaussianDensity s x) ≤
        ∫ x in (unitBall n)ᶜ, c * gaussianDensity (2 * s) x := by
      apply MeasureTheory.setIntegral_mono_on hf.integrableOn
        (hg.const_mul c).integrableOn (Metric.isClosed_closedBall.measurableSet.compl)
      intro x hx
      exact gaussianDensity_tail_pointwise hs hx
    _ ≤ ∫ x : AmbientSpace n in Set.univ, c * gaussianDensity (2 * s) x := by
      apply MeasureTheory.setIntegral_mono_set (hg.const_mul c).integrableOn
      · filter_upwards with x
        exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      · filter_upwards with x
        intro _
        exact Set.mem_univ x
    _ = ∫ x : AmbientSpace n, c * gaussianDensity (2 * s) x := by simp
    _ = c * Real.rpow (4 * Real.pi * s) ((n : ℝ) / 2) := by
      rw [MeasureTheory.integral_const_mul, integral_gaussianDensity (show 0 < 2 * s by positivity)]
      congr 2
      ring
    _ = _ := rfl

lemma exp_neg_six_le_one_div_64 : Real.exp (-6) ≤ (1 : ℝ) / 64 := by
  rw [show (-6 : ℝ) = (6 : ℕ) * (-1 : ℝ) by norm_num, Real.exp_nat_mul]
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le 6
  norm_num at hpow ⊢
  exact hpow

lemma initial_tail_coefficient_le (q : VolumeParams) :
    Real.exp (-1 / (4 * initialVariance q)) *
        Real.rpow 2 ((q.n : ℝ) / 2) ≤ q.eps / 64 := by
  have he0 : 0 < q.eps := q.heps.1
  have he1 : q.eps < 1 := q.heps.2
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hlog : Real.log 2 ≤ 1 := by
    exact (Real.log_le_iff_le_exp (by norm_num)).2 Real.exp_one_gt_two.le
  have hfirst : Real.exp (-1 / q.eps) ≤ q.eps := by
    have hlarge : 1 / q.eps ≤ Real.exp (1 / q.eps) :=
      (show 1 / q.eps ≤ 1 / q.eps + 1 by linarith).trans
        (Real.add_one_le_exp (1 / q.eps))
    have hinv := one_div_le_one_div_of_le (by positivity : 0 < 1 / q.eps) hlarge
    rw [show -1 / q.eps = -(1 / q.eps) by ring, Real.exp_neg]
    simpa [div_eq_mul_inv] using hinv
  have hrest :
      -1 / (4 * initialVariance q) + (q.n : ℝ) / 2 + 1 / q.eps ≤ -6 := by
    rw [initialVariance]
    field_simp
    nlinarith
  change Real.exp (-1 / (4 * initialVariance q)) *
      (2 : ℝ) ^ ((q.n : ℝ) / 2) ≤ q.eps / 64
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  calc
    Real.exp (-1 / (4 * initialVariance q) + Real.log 2 * ((q.n : ℝ) / 2)) ≤
        Real.exp (-1 / (4 * initialVariance q) + (q.n : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      have hn0 : 0 ≤ (q.n : ℝ) / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hlog hn0]
    _ = Real.exp (-1 / q.eps) *
        Real.exp (-1 / (4 * initialVariance q) + (q.n : ℝ) / 2 + 1 / q.eps) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ q.eps * ((1 : ℝ) / 64) := by
      exact mul_le_mul hfirst
        ((Real.exp_le_exp.mpr hrest).trans exp_neg_six_le_one_div_64)
        (Real.exp_pos _).le he0.le
    _ = q.eps / 64 := by ring

lemma initialVariance_pos (q : VolumeParams) : 0 < initialVariance q := by
  unfold initialVariance
  have hn : (0 : ℝ) < q.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) q.dim_ok)
  exact div_pos q.heps.1 (by positivity)

lemma initial_tail_mass_le (q : VolumeParams) :
    (∫ x in (unitBall q.n)ᶜ, gaussianDensity (initialVariance q) x) ≤
      q.eps / 64 * initialGaussianIntegral q := by
  have hs := initialVariance_pos q
  have htail := gaussianDensity_tail_le (n := q.n) hs
  rw [show 4 * Real.pi * initialVariance q =
      2 * (2 * Real.pi * initialVariance q) by ring] at htail
  have hrpow : Real.rpow (2 * (2 * Real.pi * initialVariance q)) ((q.n : ℝ) / 2) =
      Real.rpow 2 ((q.n : ℝ) / 2) *
        Real.rpow (2 * Real.pi * initialVariance q) ((q.n : ℝ) / 2) :=
    Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num)
      (show 0 ≤ 2 * Real.pi * initialVariance q by positivity)
  rw [hrpow] at htail
  calc
    (∫ x in (unitBall q.n)ᶜ, gaussianDensity (initialVariance q) x) ≤
        (Real.exp (-1 / (4 * initialVariance q)) *
          Real.rpow 2 ((q.n : ℝ) / 2)) *
          Real.rpow (2 * Real.pi * initialVariance q) ((q.n : ℝ) / 2) := by
      convert htail using 1
      ring
    _ ≤ (q.eps / 64) *
          Real.rpow (2 * Real.pi * initialVariance q) ((q.n : ℝ) / 2) := by
      have hz : 0 ≤ Real.rpow (2 * Real.pi * initialVariance q) ((q.n : ℝ) / 2) := by
        exact Real.rpow_nonneg (by positivity) _
      exact mul_le_mul_of_nonneg_right (initial_tail_coefficient_le q) hz
    _ = q.eps / 64 * initialGaussianIntegral q := rfl

lemma gaussianIntegral_eq_setIntegral {n : ℕ} {K : Set (AmbientSpace n)}
    (hK : MeasurableSet K) (s : ℝ) :
    gaussianIntegral K s = ∫ x in K, gaussianDensity s x := by
  unfold gaussianIntegral unnormGaussian
  rw [MeasureTheory.integral_indicator hK]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact (gaussianDensity_eq s x).symm

theorem volume_proof_initial_tail :
    ∀ (q : VolumeParams) (I : VolumeInput q.n),
      RelativeApprox (q.eps / 32)
        (gaussianIntegral (I.body : Set (AmbientSpace q.n)) (initialVariance q))
        (initialGaussianIntegral q) := by
  intro q I
  have he0 : 0 < q.eps := q.heps.1
  have he1 : q.eps < 1 := q.heps.2
  have hs := initialVariance_pos q
  have hf := integrable_gaussianDensity (n := q.n) hs
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) := I.body.isClosed.measurableSet
  have hball : MeasurableSet (unitBall q.n) := Metric.isClosed_closedBall.measurableSet
  let Z := initialGaussianIntegral q
  let M := gaussianIntegral (I.body : Set (AmbientSpace q.n)) (initialVariance q)
  have hZ_eq : (∫ x : AmbientSpace q.n, gaussianDensity (initialVariance q) x) = Z := by
    simpa [Z, initialGaussianIntegral] using (integral_gaussianDensity (n := q.n) hs)
  have hZpos : 0 < Z := by
    dsimp [Z, initialGaussianIntegral]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hM_eq : M = ∫ x in (I.body : Set (AmbientSpace q.n)),
      gaussianDensity (initialVariance q) x := gaussianIntegral_eq_setIntegral hK _
  have hMnonneg : 0 ≤ M := by
    rw [hM_eq]
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      (Real.exp_pos _).le)
  have hM_le_Z : M ≤ Z := by
    rw [hM_eq, ← hZ_eq]
    calc
      (∫ x in (I.body : Set (AmbientSpace q.n)), gaussianDensity (initialVariance q) x) ≤
          ∫ x : AmbientSpace q.n in Set.univ, gaussianDensity (initialVariance q) x := by
        apply MeasureTheory.setIntegral_mono_set hf.integrableOn
        · filter_upwards with x
          exact (Real.exp_pos _).le
        · filter_upwards with x
          intro _
          exact Set.mem_univ x
      _ = ∫ x : AmbientSpace q.n, gaussianDensity (initialVariance q) x := by simp
  have hball_le_M :
      (∫ x in unitBall q.n, gaussianDensity (initialVariance q) x) ≤ M := by
    rw [hM_eq]
    apply MeasureTheory.setIntegral_mono_set hf.integrableOn
    · filter_upwards with x
      exact (Real.exp_pos _).le
    · filter_upwards with x
      intro hx
      exact I.unitBall_subset hx
  have hdecomp := MeasureTheory.integral_add_compl hball hf
  have htail := initial_tail_mass_le q
  change (∫ x in (unitBall q.n)ᶜ, gaussianDensity (initialVariance q) x) ≤
    q.eps / 64 * Z at htail
  have hM_lower : (1 - q.eps / 64) * Z ≤ M := by
    calc
      (1 - q.eps / 64) * Z = Z - q.eps / 64 * Z := by ring
      _ ≤ Z - (∫ x in (unitBall q.n)ᶜ, gaussianDensity (initialVariance q) x) := by
        linarith
      _ = ∫ x in unitBall q.n, gaussianDensity (initialVariance q) x := by
        rw [hZ_eq] at hdecomp
        linarith
      _ ≤ M := hball_le_M
  unfold RelativeApprox Arlib.relErr
  constructor
  · calc
      (1 - q.eps / 32) * M ≤ M := by
        exact mul_le_of_le_one_left hMnonneg (by linarith)
      _ ≤ Z := hM_le_Z
  · have hscale :
        (1 + q.eps / 32) * ((1 - q.eps / 64) * Z) ≤
          (1 + q.eps / 32) * M :=
      mul_le_mul_of_nonneg_left hM_lower (by positivity)
    have hcoeff : (1 : ℝ) ≤ (1 + q.eps / 32) * (1 - q.eps / 64) := by
      nlinarith [mul_nonneg he0.le (show 0 ≤ 32 - q.eps by linarith)]
    have hzscale : Z ≤ (1 + q.eps / 32) * (1 - q.eps / 64) * Z :=
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff hZpos.le
    calc
      Z ≤ (1 + q.eps / 32) * (1 - q.eps / 64) * Z := hzscale
      _ = (1 + q.eps / 32) * ((1 - q.eps / 64) * Z) := by ring
      _ ≤ (1 + q.eps / 32) * M := hscale

end ArlibCommunity.Algorithms.CV18
