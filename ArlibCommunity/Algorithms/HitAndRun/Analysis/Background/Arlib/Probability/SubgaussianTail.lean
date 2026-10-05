/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A sub-Gaussian tail bound for linear forms in independent bounded variables

Let `Y : Fin n → Ω → ℝ` be a family of independent, mean-zero random variables,
each supported in `[-1, 1]`, and let `A : Fin n → ℝ` be a coefficient vector with
Euclidean norm `‖A‖ = √(∑ k, A k ^ 2)`. This file proves

  `Pr[ κ‖A‖ ≤ ∑ k, A k * Y k ] ≤ exp(-κ² / 2)`   for every `κ ≥ 0`,

together with a specialisation at a particular `κ` and a routine union bound.

## Contents

* `coeffNorm` / `coeffNorm_sq` — the Euclidean norm of a coefficient vector.
* `hasSubgaussianMGF_coeff_mul` — each scaled coordinate `A k * Y k` is
  sub-Gaussian with variance proxy `A k ^ 2` (Hoeffding's lemma for bounded
  mean-zero variables).
* `rounding_tail_bound` — the tail estimate displayed above.
* `rounding_tail_bound_kappa` — the same at
  `κ = √(2 log(4/η)) + √(2 log r)`, which yields the bound `η / (4r)`.
* `rounding_union_bound` — summing an `η / (4r)` bound over at most `r` indices
  gives `η / 4`.

## Motivating application

This is the concentration input to the Azuma/martingale step of Kannan–Vempala's
Theorem 2, where `Y` is the displacement produced by a coordinatewise randomized
rounding of a point (so the coordinates are independent, mean zero and supported
in `[-1, 1]`) and `A` is the coefficient vector of a facet. The quantity to
control is exactly `Pr[A · Y ≥ κ‖A‖]`.

### A missing square in the printed exponent

Kannan–Vempala's Theorem 2 displays the bound

  `Pr(A · Y ≥ κ) ≤ 2 exp(-κ² ‖A‖ / (2 ∑_{k} |A k|²))`.

Since `∑_k |A k|² = ‖A‖²`, that exponent is `-κ² / (2‖A‖)`, which is not
scale-invariant. The correct exponent — and the one Hoeffding's inequality
actually yields for the event `A · Y ≥ κ‖A‖` — is

  `-(κ‖A‖)² / (2 ∑_k |A k|²) = -κ² / 2`,

i.e. the numerator needs `‖A‖²`, not `‖A‖`. With the square restored the argument
goes through, and `rounding_tail_bound` below is the corrected statement.

Note also that the event is one-sided, so the leading factor `2` in the printed
display is unnecessary; that is the source of the slack between the `η / 4` of
`rounding_union_bound` and the `η / 2` the argument consumes.
-/

namespace Arlib.Probability

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Euclidean norm `‖A‖ = √(∑ k, A k ^ 2)` of a coefficient vector `A`. -/
noncomputable def coeffNorm {n : ℕ} (A : Fin n → ℝ) : ℝ := Real.sqrt (∑ k, A k ^ 2)

/-- The square of `coeffNorm A` is the sum of squares of the coefficients. -/
theorem coeffNorm_sq {n : ℕ} (A : Fin n → ℝ) : coeffNorm A ^ 2 = ∑ k, A k ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Each scaled coordinate `A k * Y k` is sub-Gaussian with variance proxy
`A k ^ 2`, by Hoeffding's lemma for bounded mean-zero variables. -/
theorem hasSubgaussianMGF_coeff_mul {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (k : Fin n) (hmeas : AEMeasurable (Y k) μ)
    (hbdd : ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1) (hmean : μ[Y k] = 0) :
    HasSubgaussianMGF (fun ω => A k * Y k ω) (‖A k‖₊ ^ 2) μ := by
  have hbdd' : ∀ᵐ ω ∂μ, (A k * Y k ω) ∈ Set.Icc (-|A k|) |A k| := by
    filter_upwards [hbdd] with ω hω
    rw [Set.mem_Icc, ← abs_le, abs_mul]
    have h1 : |Y k ω| ≤ 1 := abs_le.2 ⟨hω.1, hω.2⟩
    nlinarith [abs_nonneg (A k), abs_nonneg (Y k ω)]
  have hmean' : μ[fun ω => A k * Y k ω] = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun ω => A k * Y k ω) (a := -|A k|) (b := |A k|)
    (hmeas.const_mul _) hbdd' hmean'
  have hcoef : (‖|A k| - -|A k|‖₊ / 2) ^ 2 = ‖A k‖₊ ^ 2 := by
    rw [show |A k| - -|A k| = 2 * |A k| by ring]
    rw [show (2 : ℝ) * |A k| = |(2 : ℝ) * A k| by rw [abs_mul]; norm_num]
    simp [nnnorm_mul]
  rwa [hcoef] at h

/-- **Sub-Gaussian tail bound for a linear form in independent bounded variables.**

If `Y` has independent coordinates, each supported in `[-1, 1]` with mean zero,
then for any coefficient vector `A` with `∑ k, A k ^ 2 > 0` and any `κ ≥ 0`,

  `Pr[ κ‖A‖ ≤ ∑ k, A k * Y k ] ≤ exp(-κ² / 2)`.

This is Hoeffding's inequality. It is the corrected form of the Azuma step of
Kannan–Vempala's Theorem 2; see the module docstring for the missing square in
the printed exponent. -/
theorem rounding_tail_bound {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (hmeas : ∀ k, AEMeasurable (Y k) μ)
    (hindep : iIndepFun (fun k ω => A k * Y k ω) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[Y k] = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (hA : 0 < ∑ k, A k ^ 2) :
    μ.real {ω | κ * coeffNorm A ≤ ∑ k, A k * Y k ω} ≤ Real.exp (-κ ^ 2 / 2) := by
  have hsubG : ∀ k ∈ Finset.univ,
      HasSubgaussianMGF (fun ω => A k * Y k ω) (‖A k‖₊ ^ 2) μ :=
    fun k _ => hasSubgaussianMGF_coeff_mul Y A k (hmeas k) (hbdd k) (hmean k)
  have hNpos : 0 < coeffNorm A := Real.sqrt_pos.2 hA
  have hε : 0 ≤ κ * coeffNorm A := mul_nonneg hκ (le_of_lt hNpos)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep (s := Finset.univ) hsubG hε
  -- identify `∑ k, ‖A k‖₊ ^ 2` with `‖A‖²` and simplify the exponent
  have hsum : ((∑ k, ‖A k‖₊ ^ 2 : NNReal) : ℝ) = ∑ k, A k ^ 2 := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]
  refine le_trans h (le_of_eq ?_)
  congr 1
  rw [hsum, ← coeffNorm_sq A]
  have hNne : coeffNorm A ≠ 0 := ne_of_gt hNpos
  field_simp

/-- **The tail bound at `κ = √(2 log(4/η)) + √(2 log r)`.**

At this threshold the bound `exp(-κ² / 2)` of `rounding_tail_bound` is at most
`η / (4r)`, the per-index budget consumed by `rounding_union_bound`. -/
theorem rounding_tail_bound_kappa {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (hmeas : ∀ k, AEMeasurable (Y k) μ)
    (hindep : iIndepFun (fun k ω => A k * Y k ω) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[Y k] = 0)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hA : 0 < ∑ k, A k ^ 2) :
    μ.real {ω | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm A
        ≤ ∑ k, A k * Y k ω} ≤ η / (4 * r) := by
  set κ : ℝ := Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r) with hκdef
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlogη : 0 ≤ Real.log (4 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  -- `κ² ≥ 2 log(4/η) + 2 log r`
  have hκsq : 2 * Real.log (4 / η) + 2 * Real.log r ≤ κ ^ 2 := by
    rw [hκdef, add_sq, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have : 0 ≤ 2 * Real.sqrt (2 * Real.log (4 / η)) * Real.sqrt (2 * Real.log r) := by
      positivity
    linarith
  -- `exp(-κ²/2) ≤ η/(4r)`
  have hexp : Real.exp (-κ ^ 2 / 2) ≤ η / (4 * r) := by
    have hsplit : Real.log (4 * r / η) = Real.log (4 / η) + Real.log r := by
      rw [show (4 : ℝ) * r / η = (4 / η) * r by ring,
        Real.log_mul (by positivity) (by linarith)]
    have hle : -κ ^ 2 / 2 ≤ -Real.log (4 * r / η) := by
      rw [hsplit]; linarith
    calc Real.exp (-κ ^ 2 / 2) ≤ Real.exp (-Real.log (4 * r / η)) := Real.exp_le_exp.2 hle
      _ = (4 * r / η)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ = η / (4 * r) := by rw [inv_div]
  exact le_trans (rounding_tail_bound Y A hmeas hindep hbdd hmean hκ0 hA) hexp

/-- **Union bound.** Summing a per-index bound of `η / (4r)` over a finite index
set of cardinality at most `r` gives `η / 4`. -/
theorem rounding_union_bound {ι : Type*} (T : Finset ι) (pr : ι → ℝ)
    {η r : ℝ} (hr : 0 < r) (hcard : (T.card : ℝ) ≤ r)
    (hbound : ∀ i ∈ T, pr i ≤ η / (4 * r)) (hη : 0 ≤ η) :
    ∑ i ∈ T, pr i ≤ η / 4 := by
  calc ∑ i ∈ T, pr i ≤ ∑ _i ∈ T, η / (4 * r) := Finset.sum_le_sum hbound
    _ = (T.card : ℝ) * (η / (4 * r)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ r * (η / (4 * r)) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = η / 4 := by field_simp

end Arlib.Probability
