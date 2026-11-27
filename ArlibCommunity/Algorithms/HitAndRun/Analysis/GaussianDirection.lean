/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Prelude
import ArlibCommunity.Foundations.Convex.Basic.UniformOn

/-!
# A normalized Gaussian vector is uniform on the sphere

The sampler draws the direction of a hit-and-run step as `g / ‖g‖` for a standard
Gaussian vector `g`.  This file proves that this direction has the uniform law on the
unit sphere (`stdGaussian_map_direction`), the law the hit-and-run kernel draws its
direction from.  Ported from the charged CV18 development of TTC.

* `stdGaussian_apply`: the standard Gaussian on `ℝⁿ` has density `(2π)^{-n/2} e^{-‖x‖²/2}`;
* `stdGaussian_map_direction`: `g / ‖g‖` is uniform on the unit sphere, because the density
  depends only on the norm.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun.GaussianDirection

open ArlibCommunity.Foundations.MarkovChainTheory

/-- Tonelli for a product of one-variable functions on `ℝⁿ`. -/
theorem lintegral_pi_prod : ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i
  | 0, μ, _, f, _ => by simp
  | n + 1, μ, _, f, hf => by
      have hmp := measurePreserving_piFinSuccAbove μ 0
      rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp only [Fin.prod_univ_succ]
      have hsplit : ∀ p : ℝ × (Fin n → ℝ),
          f 0 (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p) 0) *
            ∏ i : Fin n, f i.succ (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p)
              i.succ) =
          f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [hsplit]
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
      rw [lintegral_pi_prod n (fun j => μ (Fin.succAbove 0 j)) (fun i => f i.succ)
        (fun i => hf i.succ)]
      simp

/-- Independent standard Gaussians in each coordinate have the product density. -/
theorem pi_gaussianReal_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    lintegral_pi_prod n _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (hs i)]

/-- The standard Gaussian density on `ℝⁿ`, as a function of the norm:
`φ(r) = (2π)^{-n/2} e^{-r²/2}`. -/
noncomputable def radialDensity (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ n * Real.exp (-r ^ 2 / 2))

theorem measurable_radialDensity (n : ℕ) : Measurable (radialDensity n) := by
  unfold radialDensity; fun_prop

theorem prod_gaussianPDF_eq (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ∏ i, gaussianPDF 0 1 (y i) = radialDensity n ‖y‖ := by
  rw [radialDensity, gaussianPDF_def,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    EuclideanSpace.real_norm_sq_eq, Finset.sum_neg_distrib, Finset.sum_div, neg_div]

/-- **The standard Gaussian has density `φ(‖x‖)`.** -/
theorem stdGaussian_apply (n : ℕ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) A = ∫⁻ y in A, radialDensity n ‖y‖ := by
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hA,
    pi_gaussianReal_eq_withDensity, withDensity_apply _ (by measurability)]
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage_emb hemb]
  refine setLIntegral_congr_fun (hemb.measurable hA) fun x _ => ?_
  rw [← prod_gaussianPDF_eq]

/-! ## The direction `g / ‖g‖` -/

variable {n : ℕ} [NeZero n]

/-- `g / ‖g‖` as a point of `ℝⁿ`, with an arbitrary unit vector at `g = 0` (a null event). -/
noncomputable def directionVal (n : ℕ) [NeZero n] (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if g = 0 then EuclideanSpace.single 0 1 else ‖g‖⁻¹ • g

theorem directionVal_mem (g : EuclideanSpace ℝ (Fin n)) :
    directionVal n g ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  unfold directionVal
  split_ifs with h
  · simp
  · simp [norm_smul, h]

/-- The direction `g / ‖g‖` of a vector, on the unit sphere. -/
noncomputable def direction (n : ℕ) [NeZero n] (g : EuclideanSpace ℝ (Fin n)) :
    sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨directionVal n g, directionVal_mem g⟩

theorem measurable_direction : Measurable (direction n) := by
  refine Measurable.subtype_mk ?_
  unfold directionVal
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem direction_eq_polar (y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    direction n y = (homeomorphUnitSphereProd _ y).1 := by
  have hy : (y : EuclideanSpace ℝ (Fin n)) ≠ 0 := y.2
  apply Subtype.ext
  simp [direction, directionVal, hy]

/-- The radial mass of the Gaussian density in polar coordinates. -/
noncomputable def radialMass (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, radialDensity n r.1
    ∂Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)

/-- **Polar coordinates.** The Gaussian mass of the cone over `s` is `toSphere s` times the
radial mass. -/
theorem stdGaussian_direction_preimage {s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : MeasurableSet s) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (direction n ⁻¹' s) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere s * radialMass n := by
  have hD : MeasurableSet (direction n ⁻¹' s) := measurable_direction hs
  have h0 : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    (measurableSet_singleton 0).compl
  rw [stdGaussian_apply n hD, ← lintegral_indicator hD]
  conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) 0,
    ← lintegral_subtype_comap h0]
  have hpt : ∀ y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      (direction n ⁻¹' s).indicator (fun y => radialDensity n ‖y‖) (y : EuclideanSpace ℝ (Fin n)) =
        (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ) =>
          s.indicator 1 p.1 * radialDensity n p.2.1) (homeomorphUnitSphereProd _ y) := by
    intro y
    have hnorm : ‖(y : EuclideanSpace ℝ (Fin n))‖ = ((homeomorphUnitSphereProd _ y).2 : ℝ) := by
      simp
    dsimp only
    by_cases hy : direction n y ∈ s
    · have hy' : (homeomorphUnitSphereProd _ y).1 ∈ s := direction_eq_polar y ▸ hy
      rw [Set.indicator_of_mem (show (y : EuclideanSpace ℝ (Fin n)) ∈ direction n ⁻¹' s from hy),
        Set.indicator_of_mem hy', hnorm, Pi.one_apply, one_mul]
    · have hy' : (homeomorphUnitSphereProd _ y).1 ∉ s := direction_eq_polar y ▸ hy
      rw [Set.indicator_of_notMem (show (y : EuclideanSpace ℝ (Fin n)) ∉ direction n ⁻¹' s from hy),
        Set.indicator_of_notMem hy', zero_mul]
  refine (lintegral_congr hpt).trans ?_
  refine ((Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℝ (Fin n)))).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _)
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ) =>
        s.indicator 1 p.1 * radialDensity n p.2.1)).trans ?_
  rw [lintegral_prod_mul (f := s.indicator 1) (g := fun r : Ioi (0 : ℝ) => radialDensity n r.1)
    (aemeasurable_const.indicator hs)
    ((measurable_radialDensity n).comp measurable_subtype_coe).aemeasurable,
    lintegral_indicator_one hs]
  rfl

/-- **A normalized standard Gaussian vector is uniform on the sphere.** -/
theorem stdGaussian_map_direction :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (direction n) =
      ArlibCommunity.Foundations.MarkovChainTheory.unifSphere n := by
  set T := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ
  have htotal : T * radialMass n = 1 := by
    rw [← stdGaussian_direction_preimage MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hK : radialMass n = T⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact htotal)
  ext s hs
  rw [Measure.map_apply measurable_direction hs, stdGaussian_direction_preimage hs, hK,
    ArlibCommunity.Foundations.MarkovChainTheory.unifSphere, Measure.smul_apply, smul_eq_mul,
    ArlibCommunity.Foundations.MarkovChainTheory.sphereArea, mul_comm]


end ArlibCommunity.Algorithms.HitAndRun.GaussianDirection
