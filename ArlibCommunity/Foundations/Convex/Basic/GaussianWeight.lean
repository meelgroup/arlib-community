/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import ArlibCommunity.Foundations.Convex.Prelude
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The unnormalised Gaussian weight

The function `x ↦ e^{-‖x‖²/(2s)}` on `EuclideanSpace ℝ (Fin n)`, in real and in `ℝ≥0∞` form.
It is the density, with respect to Lebesgue measure, of the unnormalised Gaussian measure
whose restriction to a convex body is the target law of Gaussian cooling and of the
Metropolis-filtered ball walk ([CV18]).

The definitions sit on their own, below both the geometry that integrates the weight and the
Markov chains that use it as a stationary density, so that neither layer depends on the other
for it.

## Main definitions

* `gaussianWeightReal s x` — `e^{-‖x‖²/(2s)}` as a real number.
* `gaussianWeight s x` — the same weight in `ℝ≥0∞`.

The basic facts — positivity, the bound by `1`, continuity and measurability — follow.
-/

namespace ArlibCommunity.Foundations.Convex

open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## The Gaussian weight -/

theorem gaussianWeightReal_pos (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < gaussianWeightReal s x := Real.exp_pos _

theorem gaussianWeightReal_ne_zero (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s x ≠ 0 := (gaussianWeightReal_pos s x).ne'

@[simp] theorem gaussianWeightReal_zero (s : ℝ) :
    gaussianWeightReal s (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  simp [gaussianWeightReal]

theorem continuous_gaussianWeightReal (s : ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal s x :=
  Real.continuous_exp.comp (((continuous_norm.pow 2).neg).div_const _)

/-- For `s > 0` the Gaussian weight is at most its value `1` at the origin. -/
theorem gaussianWeightReal_le_one {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeightReal s x ≤ 1 := by
  rw [gaussianWeightReal, Real.exp_le_one_iff, neg_div]
  exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith))

/-- For `s > 0` the Gaussian weight is *strictly* below `1` away from the origin.  This is
what makes the acceptance filter non-trivial. -/
theorem gaussianWeightReal_lt_one {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : gaussianWeightReal s x < 1 := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [gaussianWeightReal, Real.exp_lt_one_iff, neg_div]
  exact neg_neg_iff_pos.2 (div_pos (by positivity) (by linarith))

/-- **A uniform lower bound on the Gaussian weight over a bounded region**: on `‖x‖ ≤ r`
the weight is at least `e^{-r²/(2s)}`, which is strictly positive. -/
theorem exp_le_gaussianWeightReal {s : ℝ} (hs : 0 < s) {r : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ r) :
    Real.exp (-r ^ 2 / (2 * s)) ≤ gaussianWeightReal s x := by
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have hsq : ‖x‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg x]
  have hinv : (0 : ℝ) < (2 * s)⁻¹ := inv_pos.2 h2
  rw [gaussianWeightReal, Real.exp_le_exp, div_eq_mul_inv, div_eq_mul_inv]
  nlinarith

theorem gaussianWeight_pos (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : 0 < gaussianWeight s x :=
  ENNReal.ofReal_pos.2 (gaussianWeightReal_pos s x)

theorem gaussianWeight_ne_zero (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≠ 0 := (gaussianWeight_pos s x).ne'

theorem gaussianWeight_ne_top (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≠ ⊤ := ENNReal.ofReal_ne_top

@[simp] theorem gaussianWeight_zero (s : ℝ) :
    gaussianWeight s (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  rw [gaussianWeight, gaussianWeightReal_zero, ENNReal.ofReal_one]

theorem measurable_gaussianWeight (s : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => gaussianWeight s x :=
  (continuous_gaussianWeightReal s).measurable.ennreal_ofReal

theorem gaussianWeight_le_one {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight s x ≤ 1 := by
  rw [gaussianWeight, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (gaussianWeightReal_le_one hs x)

theorem gaussianWeight_lt_one {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    gaussianWeight s x < 1 := by
  rw [gaussianWeight, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (gaussianWeightReal_lt_one hs hx)

/-- The `n`-dimensional Gaussian is integrable: it is a product of one-dimensional ones. -/
theorem integrable_gaussian_pi {n : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / c)) := by
  have h1 : (fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / c))
      = fun t : Fin n → ℝ => ∏ i, Real.exp (-(1 / c) * (t i) ^ 2) := by
    funext t
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    field_simp
  rw [h1, MeasureTheory.volume_pi]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by positivity))

/-- The `n`-dimensional gaussian weight is integrable on `EuclideanSpace ℝ (Fin n)`.
Transported from `integrable_gaussian_pi` along the volume-preserving identification with
`Fin n → ℝ`. -/
theorem integrable_gaussian_eucl {n : ℕ} {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * s))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  have hcomp : ((fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * s)))
        ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)))
      = fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / (2 * s)) := by
    funext t
    simp only [Function.comp_apply]
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hcomp]
  exact integrable_gaussian_pi (by positivity)

end ArlibCommunity.Foundations.Convex
