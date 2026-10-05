/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependence
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The dependent-product recurrence in CV18 Lemma 7.15

This module formalizes the recursive truncations used after Lemma 7.17(c).
With the paper's one-based indexing, `dependentPhaseMeanProduct mean i` is
`E(V₁) * ... * E(Vᵢ)` and `dependentTruncatedProduct alpha mean V i` is `Uᵢ`.
The definitions are kept model-independent so that the recurrence can be
instantiated directly on the complete history law of the executable walk.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic product `E(V₁) * ... * E(Vᵢ)` in CV18 Lemma 7.15. -/
def dependentPhaseMeanProduct (mean : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, mean (j + 1)

/-- The untruncated random product `W₁ * ... * Wᵢ`. -/
def dependentPhaseSampleProduct (W : ℕ → Omega → ℝ) (i : ℕ)
    (omega : Omega) : ℝ :=
  ∏ j ∈ Finset.range i, W (j + 1) omega

/-- The first truncation layer in CV18 Lemma 7.15:
`Vᵢ = min(W̄ᵢ, alpha * E(W̄ᵢ))`. -/
def dependentTruncatedPhase (alpha : ℝ) (rawMean : ℕ → ℝ)
    (W : ℕ → Omega → ℝ) (j : ℕ) (omega : Omega) : ℝ :=
  min (W j omega) (alpha * rawMean j)

@[simp]
theorem dependentPhaseMeanProduct_zero (mean : ℕ → ℝ) :
    dependentPhaseMeanProduct mean 0 = 1 := by
  simp [dependentPhaseMeanProduct]

theorem dependentPhaseMeanProduct_succ (mean : ℕ → ℝ) (i : ℕ) :
    dependentPhaseMeanProduct mean (i + 1) =
      dependentPhaseMeanProduct mean i * mean (i + 1) := by
  simp [dependentPhaseMeanProduct, Finset.prod_range_succ]

@[simp]
theorem dependentPhaseSampleProduct_zero (W : ℕ → Omega → ℝ) (omega : Omega) :
    dependentPhaseSampleProduct W 0 omega = 1 := by
  simp [dependentPhaseSampleProduct]

theorem dependentPhaseSampleProduct_succ (W : ℕ → Omega → ℝ)
    (i : ℕ) (omega : Omega) :
    dependentPhaseSampleProduct W (i + 1) omega =
      dependentPhaseSampleProduct W i omega * W (i + 1) omega := by
  simp [dependentPhaseSampleProduct, Finset.prod_range_succ]

theorem dependentPhaseMeanProduct_nonneg (mean : ℕ → ℝ)
    (hmean : ∀ j, 0 ≤ mean j) (i : ℕ) :
    0 ≤ dependentPhaseMeanProduct mean i := by
  exact Finset.prod_nonneg fun j _ => hmean (j + 1)

/-- The recursively truncated accumulated product `Uᵢ` from CV18 Lemma 7.15.
The phase variables `V` use the paper's one-based indexing. -/
def dependentTruncatedProduct (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) : ℕ → Omega → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun omega =>
      min (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega)
        (alpha * dependentPhaseMeanProduct mean (i + 1))

@[simp]
theorem dependentTruncatedProduct_zero (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V 0 omega = 1 := by
  rfl

theorem dependentTruncatedProduct_succ (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega =
      min (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega)
        (alpha * dependentPhaseMeanProduct mean (i + 1)) := by
  rfl

theorem measurable_dependentTruncatedProduct (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (hV : ∀ j, Measurable (V j)) :
    ∀ i, Measurable (dependentTruncatedProduct alpha mean V i)
  | 0 => measurable_const
  | i + 1 =>
      ((measurable_dependentTruncatedProduct alpha mean V hV i).mul
        (hV (i + 1))).min measurable_const

theorem dependentTruncatedProduct_nonneg (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 0 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hV : ∀ j omega, 0 ≤ V j omega) :
    ∀ i omega, 0 ≤ dependentTruncatedProduct alpha mean V i omega
  | 0, _ => by simp
  | i + 1, omega => by
      rw [dependentTruncatedProduct_succ]
      exact le_min
        (mul_nonneg
          (dependentTruncatedProduct_nonneg alpha mean V halpha hmean hV i omega)
          (hV (i + 1) omega))
        (mul_nonneg halpha (dependentPhaseMeanProduct_nonneg mean hmean (i + 1)))

/-- `Uᵢ Vᵢ₊₁` is the untruncated candidate for `Uᵢ₊₁`. -/
theorem dependentTruncatedProduct_succ_le_mul (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega ≤
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega := by
  rw [dependentTruncatedProduct_succ]
  exact min_le_left _ _

/-- The deterministic cap on `Uᵢ` used in equations (8)--(11). -/
theorem dependentTruncatedProduct_succ_le_cap (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega ≤
      alpha * dependentPhaseMeanProduct mean (i + 1) := by
  rw [dependentTruncatedProduct_succ]
  exact min_le_right _ _

/-- Uniform cap on `Uᵢ`, including `i = 0`.  The paper always chooses
`alpha ≥ 1`, so the base value `U₀ = 1` obeys the same formula. -/
theorem dependentTruncatedProduct_le_cap (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V i omega ≤
      alpha * dependentPhaseMeanProduct mean i := by
  cases i with
  | zero => simpa using halpha
  | succ i => exact dependentTruncatedProduct_succ_le_cap alpha mean V i omega

theorem integrable_dependentTruncatedProduct (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega) (i : ℕ) :
    Integrable (dependentTruncatedProduct alpha mean V i) mu := by
  apply Integrable.of_bound
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i).aestronglyMeasurable
    (alpha * dependentPhaseMeanProduct mean i)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  · exact dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i omega

theorem integrable_phase_of_le_two_mul_alpha_mean (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 0 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j) (j : ℕ) :
    Integrable (V j) mu := by
  apply Integrable.of_bound (hVmeas j).aestronglyMeasurable (2 * alpha * mean j)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (hV0 j omega)]
  exact hVcap j omega

theorem integrable_dependentTruncatedProduct_mul_phase (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) mu := by
  let a := alpha * dependentPhaseMeanProduct mean i
  let b := 2 * alpha * mean (i + 1)
  have hmeas : Measurable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) :=
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i).mul (hVmeas (i + 1))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (a * b)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUa := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  have hnext0 := hV0 (i + 1) omega
  have hnextb := hVcap (i + 1) omega
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hU0 hnext0)]
  exact mul_le_mul hUa hnextb hnext0 (mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i))

/-- Equation (8) of CV18 Lemma 7.15, with all measurability and boundedness
hypotheses exposed.  The factor `2` comes from
`Vᵢ₊₁ ≤ alpha * E(Wᵢ₊₁) ≤ 2 * alpha * E(Vᵢ₊₁)`. -/
theorem abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (i : ℕ) (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    |(∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          (∫ omega, V (i + 1) omega ∂mu)| ≤
      2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
  have h := ApproxIndepFun.abs_integral_mul_sub_mul_integral_le mu
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i)
    (hVmeas (i + 1))
    (mul_nonneg (zero_le_one.trans halpha)
      (dependentPhaseMeanProduct_nonneg mean hmean i))
    (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans halpha))
      (hmean (i + 1)))
    hepsilon
    (dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i)
    (dependentTruncatedProduct_le_cap alpha mean V halpha i)
    (hV0 (i + 1)) (hVcap (i + 1)) hind
  rw [dependentPhaseMeanProduct_succ]
  calc
    _ ≤ epsilon *
          (alpha * dependentPhaseMeanProduct mean i) *
          (2 * alpha * mean (i + 1)) := h
    _ = 2 * epsilon * alpha ^ 2 *
          (dependentPhaseMeanProduct mean i * mean (i + 1)) := by ring

/-- One-step upper recurrence extracted from equation (8). -/
theorem integral_dependentTruncatedProduct_succ_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (i : ℕ) (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) +
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
  have hnextInt := integrable_dependentTruncatedProduct mu alpha mean V halpha
    hmean hVmeas hV0 (i + 1)
  have hmulInt := integrable_dependentTruncatedProduct_mul_phase mu alpha mean V
    halpha hmean hVmeas hV0 hVcap i
  have hmono :
      (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
        ∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu :=
    integral_mono hnextInt hmulInt
      (dependentTruncatedProduct_succ_le_mul alpha mean V i)
  have hcov := abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcap i hind
  rw [hVmean (i + 1)] at hcov
  have hcovUpper :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) ≤
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) :=
    (le_abs_self _).trans hcov
  linarith

/-- Equation (9) of CV18 Lemma 7.15: the upper first-moment induction for
the recursively truncated product. -/
theorem integral_dependentTruncatedProduct_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (phases : ℕ)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    (∫ omega, dependentTruncatedProduct alpha mean V phases omega ∂mu) ≤
      (1 + 2 * epsilon * alpha ^ 2 * phases) *
        dependentPhaseMeanProduct mean phases := by
  induction phases with
  | zero => simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | succ i ih =>
      have hstep := integral_dependentTruncatedProduct_succ_le
        mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcap
          hVmean i (hind i (Nat.lt_succ_self i))
      have hstep' :
          (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
            (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
                mean (i + 1) +
              2 * epsilon * alpha ^ 2 *
                (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
        simpa only [dependentPhaseMeanProduct_succ] using hstep
      have hinduction := ih fun k hk =>
        hind k (lt_trans hk (Nat.lt_succ_self i))
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hmean (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) +
            2 * epsilon * alpha ^ 2 *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := hstep'
        _ ≤ ((1 + 2 * epsilon * alpha ^ 2 * i) *
              dependentPhaseMeanProduct mean i) * mean (i + 1) +
            2 * epsilon * alpha ^ 2 *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
          exact add_le_add hscaled (le_refl _)
        _ = (1 + 2 * epsilon * alpha ^ 2 * (i + 1)) *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
          ring

/-- Squaring preserves approximate independence and gives the covariance
estimate used for the second-moment recurrence (10)--(11) of Lemma 7.15. -/
theorem ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hepsilon : 0 ≤ epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXa : ∀ omega, X omega ≤ a)
    (hY0 : ∀ omega, 0 ≤ Y omega) (hYb : ∀ omega, Y omega ≤ b)
    (hind : ApproxIndepFun epsilon X Y mu) :
    |(∫ omega, X omega ^ 2 * Y omega ^ 2 ∂mu) -
        (∫ omega, X omega ^ 2 ∂mu) * (∫ omega, Y omega ^ 2 ∂mu)| ≤
      epsilon * a ^ 2 * b ^ 2 := by
  apply ApproxIndepFun.abs_integral_mul_sub_mul_integral_le mu
    (hX.pow_const 2) (hY.pow_const 2) (sq_nonneg a) (sq_nonneg b) hepsilon
  · intro omega
    exact sq_nonneg _
  · intro omega
    exact (sq_le_sq₀ (hX0 omega) ha).2 (hXa omega)
  · intro omega
    exact sq_nonneg _
  · intro omega
    exact (sq_le_sq₀ (hY0 omega) hb).2 (hYb omega)
  · have hsq : Measurable (fun x : ℝ => x ^ 2) :=
      measurable_id.pow_const 2
    have hsquared : ApproxIndepFun epsilon
        ((fun x : ℝ => x ^ 2) ∘ X) ((fun y : ℝ => y ^ 2) ∘ Y) mu :=
      ApproxIndepFun.comp hind hsq hsq
    simpa only [Function.comp_def] using hsquared

/-- Products of first moments squared are bounded by products of second
moments.  This is the finite-product form used between (10) and (11). -/
theorem dependentPhaseMeanProduct_sq_le (mean second : ℕ → ℝ)
    (hsecond0 : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j) (i : ℕ) :
    dependentPhaseMeanProduct mean i ^ 2 ≤
      dependentPhaseMeanProduct second i := by
  rw [dependentPhaseMeanProduct, dependentPhaseMeanProduct,
    ← Finset.prod_pow]
  exact Finset.prod_le_prod
    (fun j _ => sq_nonneg (mean (j + 1)))
    (fun j _ => hmeanSecond (j + 1))

/-- Squared form of the dependence error behind (10)--(11).  Unlike the
paper's word "similarly", this records the two estimates needed for the
constant `2`: the raw cap mean has square at most twice the truncated second
moment, and products of squared truncated means are bounded by products of
truncated second moments. -/
theorem abs_integral_dependentTruncatedProduct_sq_mul_phase_sq_sub_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (i : ℕ) (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    |(∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
          V (i + 1) omega ^ 2 ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          (∫ omega, V (i + 1) omega ^ 2 ∂mu)| ≤
      2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) := by
  have hcov := ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le mu
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i)
    (hVmeas (i + 1))
    (mul_nonneg (zero_le_one.trans halpha)
      (dependentPhaseMeanProduct_nonneg mean hmean i))
    (mul_nonneg (zero_le_one.trans halpha) (hrawMean (i + 1)))
    hepsilon
    (dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i)
    (dependentTruncatedProduct_le_cap alpha mean V halpha i)
    (hV0 (i + 1)) (hVcap (i + 1)) hind
  have hmeans := dependentPhaseMeanProduct_sq_le mean second hsecond
    hmeanSecond i
  have hpairsq :
      dependentPhaseMeanProduct mean i ^ 2 * rawMean (i + 1) ^ 2 ≤
        dependentPhaseMeanProduct second i * (2 * second (i + 1)) :=
    mul_le_mul hmeans (hrawSecond (i + 1)) (sq_nonneg _)
      (dependentPhaseMeanProduct_nonneg second hsecond i)
  rw [dependentPhaseMeanProduct_succ]
  calc
    _ ≤ epsilon *
          (alpha * dependentPhaseMeanProduct mean i) ^ 2 *
          (alpha * rawMean (i + 1)) ^ 2 := hcov
    _ = (epsilon * alpha ^ 4) *
          (dependentPhaseMeanProduct mean i ^ 2 * rawMean (i + 1) ^ 2) := by ring
    _ ≤ (epsilon * alpha ^ 4) *
          (dependentPhaseMeanProduct second i * (2 * second (i + 1))) := by
      exact mul_le_mul_of_nonneg_left hpairsq
        (mul_nonneg hepsilon (by positivity))
    _ = 2 * epsilon * alpha ^ 4 *
          (dependentPhaseMeanProduct second i * second (i + 1)) := by ring

theorem integrable_dependentTruncatedProduct_sq (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2) mu := by
  let cap := alpha * dependentPhaseMeanProduct mean i
  have hcap0 : 0 ≤ cap := mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i)
  apply Integrable.of_bound
    ((measurable_dependentTruncatedProduct alpha mean V hVmeas i).pow_const 2).aestronglyMeasurable
    (cap ^ 2)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUcap := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ hU0 hcap0).2 hUcap

theorem integrable_dependentTruncatedProduct_sq_mul_phase_sq
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (alpha : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hmean : ∀ j, 0 ≤ mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2) mu := by
  let a := alpha * dependentPhaseMeanProduct mean i
  let b := alpha * rawMean (i + 1)
  have ha0 : 0 ≤ a := mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i)
  have hb0 : 0 ≤ b := mul_nonneg (zero_le_one.trans halpha) (hrawMean (i + 1))
  have hmeas : Measurable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2) :=
    ((measurable_dependentTruncatedProduct alpha mean V hVmeas i).pow_const 2).mul
      ((hVmeas (i + 1)).pow_const 2)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (a ^ 2 * b ^ 2)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUa := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  have hnext0 := hV0 (i + 1) omega
  have hnextb := hVcap (i + 1) omega
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul ((sq_le_sq₀ hU0 ha0).2 hUa)
    ((sq_le_sq₀ hnext0 hb0).2 hnextb) (sq_nonneg _) (sq_nonneg _)

/-- Equation (11), with the sound successor index made explicit.  It is the
one-step second-moment estimate from which equation (10) follows. -/
theorem integral_dependentTruncatedProduct_sq_mul_phase_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (i : ℕ) (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2 ∂mu) ≤
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          second (i + 1) +
        2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) := by
  have hcov := abs_integral_dependentTruncatedProduct_sq_mul_phase_sq_sub_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap i hind
  rw [hVsecond (i + 1)] at hcov
  have hupper :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
          V (i + 1) omega ^ 2 ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          second (i + 1) ≤
        2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) :=
    (le_abs_self _).trans hcov
  linarith

/-- Equation (10) of CV18 Lemma 7.15. -/
theorem integral_dependentTruncatedProduct_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (phases : ℕ)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    (∫ omega, dependentTruncatedProduct alpha mean V phases omega ^ 2 ∂mu) ≤
      (1 + 2 * epsilon * alpha ^ 4 * phases) *
        dependentPhaseMeanProduct second phases := by
  induction phases with
  | zero => simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | succ i ih =>
      have hcandidate := integral_dependentTruncatedProduct_sq_mul_phase_sq_le
        mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
          hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond i
            (hind i (Nat.lt_succ_self i))
      have hnextInt := integrable_dependentTruncatedProduct_sq mu alpha mean V
        halpha hmean hVmeas hV0 (i + 1)
      have hcandidateInt := integrable_dependentTruncatedProduct_sq_mul_phase_sq
        mu alpha mean rawMean V halpha hmean hrawMean hVmeas hV0 hVcap i
      have hpoint : ∀ omega,
          dependentTruncatedProduct alpha mean V (i + 1) omega ^ 2 ≤
            dependentTruncatedProduct alpha mean V i omega ^ 2 *
              V (i + 1) omega ^ 2 := by
        intro omega
        rw [← mul_pow]
        exact (sq_le_sq₀
          (dependentTruncatedProduct_nonneg alpha mean V
            (zero_le_one.trans halpha) hmean hV0 (i + 1) omega)
          (mul_nonneg
            (dependentTruncatedProduct_nonneg alpha mean V
              (zero_le_one.trans halpha) hmean hV0 i omega)
            (hV0 (i + 1) omega))).2
          (dependentTruncatedProduct_succ_le_mul alpha mean V i omega)
      have hmono := integral_mono hnextInt hcandidateInt hpoint
      have hinduction := ih fun k hk =>
        hind k (lt_trans hk (Nat.lt_succ_self i))
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hsecond (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
              V (i + 1) omega ^ 2 ∂mu := hmono
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
              second (i + 1) +
            2 * epsilon * alpha ^ 4 *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by
          simpa only [dependentPhaseMeanProduct_succ] using hcandidate
        _ ≤ ((1 + 2 * epsilon * alpha ^ 4 * i) *
              dependentPhaseMeanProduct second i) * second (i + 1) +
            2 * epsilon * alpha ^ 4 *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by
          exact add_le_add hscaled (le_refl _)
        _ = (1 + 2 * epsilon * alpha ^ 4 * (i + 1)) *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by ring

/-- The candidate form of equations (10)--(11), prior to the paper's final
numerical estimate comparing the product of second moments with the square of
the product of first moments. -/
theorem integral_dependentTruncatedProduct_candidate_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (i : ℕ) (hind : ∀ k, k ≤ i → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V k) (V (k + 1)) mu) :
    (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
      (1 + 2 * epsilon * alpha ^ 4 * (i + 1)) *
        dependentPhaseMeanProduct second (i + 1) := by
  have hcandidate := integral_dependentTruncatedProduct_sq_mul_phase_sq_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond i
        (hind i le_rfl)
  have hinduction := integral_dependentTruncatedProduct_sq_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond i
        (fun k hk => hind k (Nat.le_trans (Nat.le_of_lt hk) le_rfl))
  have hscaled := mul_le_mul_of_nonneg_right hinduction (hsecond (i + 1))
  rw [dependentPhaseMeanProduct_succ]
  calc
    (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) =
        ∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
          V (i + 1) omega ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      ring
    _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          second (i + 1) +
        2 * epsilon * alpha ^ 4 *
          (dependentPhaseMeanProduct second i * second (i + 1)) := by
      simpa only [dependentPhaseMeanProduct_succ] using hcandidate
    _ ≤ ((1 + 2 * epsilon * alpha ^ 4 * i) *
          dependentPhaseMeanProduct second i) * second (i + 1) +
        2 * epsilon * alpha ^ 4 *
          (dependentPhaseMeanProduct second i * second (i + 1)) := by
      exact add_le_add hscaled (le_refl _)
    _ = (1 + 2 * epsilon * alpha ^ 4 * (i + 1)) *
          (dependentPhaseMeanProduct second i * second (i + 1)) := by ring

theorem dependentTruncatedProduct_candidateSecond_of_relativeProduct
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (phases : ℕ)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hrelative : ∀ i, i ≤ phases →
      (1 + 2 * epsilon * alpha ^ 4 * i) * dependentPhaseMeanProduct second i ≤
        2 * dependentPhaseMeanProduct mean i ^ 2) :
    ∀ i, i < phases →
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
          2 * dependentPhaseMeanProduct mean (i + 1) ^ 2 := by
  intro i hi
  have hrel := hrelative (i + 1) (Nat.succ_le_iff.mpr hi)
  norm_num only [Nat.cast_add, Nat.cast_one] at hrel
  exact (integral_dependentTruncatedProduct_candidate_sq_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond i
        (fun k hk => hind k (lt_of_le_of_lt hk hi))).trans
        hrel

/-- Equation (12), before inserting the second-moment estimate: truncating
the candidate `Uᵢ Vᵢ₊₁` at its deterministic cap loses at most its second
moment divided by four times that cap. -/
theorem integral_dependentTruncatedProduct_succ_ge
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hmean : ∀ j, 0 ≤ mean j)
    (hmeanPos : ∀ j, 0 < mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j) (i : ℕ) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega) ^ 2 ∂mu) /
          (4 * (alpha * dependentPhaseMeanProduct mean (i + 1))) := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have hcandidateInt := integrable_dependentTruncatedProduct_mul_phase
    mu alpha mean V halpha hmean hVmeas hV0 hVcapTwo i
  have hcandidateSqInt : Integrable (fun omega =>
      (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) ^ 2) mu := by
    simpa only [mul_pow] using
      integrable_dependentTruncatedProduct_sq_mul_phase_sq mu alpha mean rawMean V
        halpha hmean hrawMean hVmeas hV0 hVcap i
  have hcandidate0 : ∀ omega,
      0 ≤ dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega :=
    fun omega => mul_nonneg
      (dependentTruncatedProduct_nonneg alpha mean V
        (zero_le_one.trans halpha) hmean hV0 i omega)
      (hV0 (i + 1) omega)
  have hmeanProductPos : 0 < dependentPhaseMeanProduct mean (i + 1) := by
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  have hcapPos : 0 < alpha * dependentPhaseMeanProduct mean (i + 1) :=
    mul_pos (zero_lt_one.trans_le halpha) hmeanProductPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    hcandidateInt hcandidateSqInt hcandidate0 hcapPos
  simpa only [dependentTruncatedProduct_succ] using htrunc

/-- The one-step lower recurrence used in (14).  Its two error contributions
(dependence and truncation) are each charged `Mᵢ₊₁/(2 alpha)`. -/
theorem integral_dependentTruncatedProduct_succ_ge_sub
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (i : ℕ) (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hcandidateSecond :
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
          2 * dependentPhaseMeanProduct mean (i + 1) ^ 2) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) -
        dependentPhaseMeanProduct mean (i + 1) / alpha := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have htrunc := integral_dependentTruncatedProduct_succ_ge mu alpha mean rawMean V
    halpha hmean hmeanPos hrawMean hrawMean_le hVmeas hV0 hVcap i
  have hcov := abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcapTwo i hind
  rw [hVmean (i + 1)] at hcov
  let M := dependentPhaseMeanProduct mean (i + 1)
  have hMpos : 0 < M := by
    dsimp [M, dependentPhaseMeanProduct]
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  have halphaPos : 0 < alpha := zero_lt_one.trans_le halpha
  have hcoef : 2 * epsilon * alpha ^ 2 ≤ 1 / (2 * alpha) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) halphaPos)]
    nlinarith [hsmall]
  have hdepCharge : 2 * epsilon * alpha ^ 2 * M ≤ M / (2 * alpha) := by
    calc
      2 * epsilon * alpha ^ 2 * M ≤ (1 / (2 * alpha)) * M :=
        mul_le_mul_of_nonneg_right hcoef hMpos.le
      _ = M / (2 * alpha) := by ring
  have hcovLower :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) ≥
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
            mean (i + 1) - M / (2 * alpha) := by
    have hlower :
        -(2 * epsilon * alpha ^ 2 * M) ≤
          (∫ omega, dependentTruncatedProduct alpha mean V i omega *
              V (i + 1) omega ∂mu) -
            (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) :=
      (neg_le_of_abs_le hcov)
    linarith
  have htruncCharge :
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega) ^ 2 ∂mu) /
          (4 * (alpha * M)) ≤ M / (2 * alpha) := by
    calc
      _ ≤ (2 * M ^ 2) / (4 * (alpha * M)) := by
        exact div_le_div_of_nonneg_right hcandidateSecond
          (mul_nonneg (by norm_num) (mul_nonneg halphaPos.le hMpos.le))
      _ = M / (2 * alpha) := by
        field_simp [halphaPos.ne', hMpos.ne']
        ring
  change (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
      mean (i + 1) - M / alpha
  change (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
    (∫ omega, dependentTruncatedProduct alpha mean V i omega *
      V (i + 1) omega ∂mu) -
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) / (4 * (alpha * M)) at htrunc
  have hcombined :
      (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
            mean (i + 1) - M / (2 * alpha) - M / (2 * alpha) := by
    linarith
  calc
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) - M / alpha =
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) - M / (2 * alpha) - M / (2 * alpha) := by
      field_simp [halphaPos.ne']
      ring
    _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu :=
      hcombined

/-- Equation (14), in a slightly cleaner zero-based form:
`E(Uᵢ) ≥ (1 - i/alpha) * ∏ E(Vⱼ)`. -/
theorem integral_dependentTruncatedProduct_ge
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hcandidateSecond : ∀ i,
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
          2 * dependentPhaseMeanProduct mean (i + 1) ^ 2) :
    ∀ i,
      (1 - i / alpha) * dependentPhaseMeanProduct mean i ≤
        ∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu
  | 0 => by simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | i + 1 => by
      have hstep := integral_dependentTruncatedProduct_succ_ge_sub
        mu alpha epsilon mean rawMean V halpha hepsilon hsmall hmean hmeanPos
          hrawMean hrawMean_le hVmeas hV0 hVcap hVmean i (hind i)
          (hcandidateSecond i)
      have hinduction := integral_dependentTruncatedProduct_ge
        mu alpha epsilon mean rawMean V halpha hepsilon hsmall hmean hmeanPos
          hrawMean hrawMean_le hVmeas hV0 hVcap hVmean hind hcandidateSecond i
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hmean (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        (1 - (i + 1) / alpha) *
            (dependentPhaseMeanProduct mean i * mean (i + 1)) =
          ((1 - i / alpha) * dependentPhaseMeanProduct mean i) *
              mean (i + 1) -
            (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by ring
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) -
            (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by
          linarith
        _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu := by
          simpa only [dependentPhaseMeanProduct_succ] using hstep

/-- Equations (7), (9), (10), and (14) assembled from the phasewise moment
data and the single numerical relative-product estimate used by CV18. -/
theorem dependentTruncatedProduct_moment_bounds_of_relativeProduct
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (phases : ℕ)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hrelative : ∀ i, i ≤ phases →
      (1 + 2 * epsilon * alpha ^ 4 * i) * dependentPhaseMeanProduct second i ≤
        2 * dependentPhaseMeanProduct mean i ^ 2) :
    (1 - phases / alpha) * dependentPhaseMeanProduct mean phases ≤
        ∫ omega, dependentTruncatedProduct alpha mean V phases omega ∂mu ∧
    (∫ omega, dependentTruncatedProduct alpha mean V phases omega ∂mu) ≤
        (1 + 2 * epsilon * alpha ^ 2 * phases) *
          dependentPhaseMeanProduct mean phases ∧
    (∫ omega, dependentTruncatedProduct alpha mean V phases omega ^ 2 ∂mu) ≤
        (1 + 2 * epsilon * alpha ^ 4 * phases) *
          dependentPhaseMeanProduct second phases := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have hcandidate := dependentTruncatedProduct_candidateSecond_of_relativeProduct
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond phases hind hrelative
  have hlowerAll : ∀ n, n ≤ phases →
      (1 - n / alpha) * dependentPhaseMeanProduct mean n ≤
        ∫ omega, dependentTruncatedProduct alpha mean V n omega ∂mu := by
    intro n hn
    induction n with
    | zero => simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
    | succ i hi =>
        have hstep := integral_dependentTruncatedProduct_succ_ge_sub
          mu alpha epsilon mean rawMean V halpha hepsilon hsmall hmean hmeanPos
            hrawMean hrawMean_le hVmeas hV0 hVcap hVmean i
              (hind i (lt_of_lt_of_le (Nat.lt_succ_self i) hn))
            (hcandidate i (lt_of_lt_of_le (Nat.lt_succ_self i) hn))
        have hscaled := mul_le_mul_of_nonneg_right
          (hi (Nat.le_trans (Nat.le_succ i) hn)) (hmean (i + 1))
        rw [dependentPhaseMeanProduct_succ]
        norm_num only [Nat.cast_add, Nat.cast_one]
        calc
          (1 - (i + 1) / alpha) *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) =
            ((1 - i / alpha) * dependentPhaseMeanProduct mean i) *
                mean (i + 1) -
              (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by ring
          _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
                mean (i + 1) -
              (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by
            linarith
          _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu := by
            simpa only [dependentPhaseMeanProduct_succ] using hstep
  have hlower := hlowerAll phases le_rfl
  have hupper := integral_dependentTruncatedProduct_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcapTwo hVmean
      phases hind
  have hsquared := integral_dependentTruncatedProduct_sq_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond phases hind
  exact ⟨hlower, hupper, hsquared⟩

/-- Expanding a squared deviation from a deterministic target on a
probability space. -/
theorem integral_sub_const_sq_eq (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : MemLp X 2 mu) (target : ℝ) :
    (∫ omega, (X omega - target) ^ 2 ∂mu) =
      (∫ omega, X omega ^ 2 ∂mu) -
        2 * target * (∫ omega, X omega ∂mu) + target ^ 2 := by
  have hXint : Integrable X mu := hX.integrable (by norm_num)
  have hXsq : Integrable (fun omega => X omega ^ 2) mu := hX.integrable_sq
  have hlinear : Integrable (fun omega => 2 * target * X omega) mu :=
    hXint.const_mul (2 * target)
  have hconst : Integrable (fun _ : Omega => target ^ 2) mu := integrable_const _
  calc
    (∫ omega, (X omega - target) ^ 2 ∂mu) =
        ∫ omega, X omega ^ 2 - 2 * target * X omega + target ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      ring
    _ = (∫ omega, X omega ^ 2 ∂mu) -
          (∫ omega, 2 * target * X omega ∂mu) +
          (∫ _omega : Omega, target ^ 2 ∂mu) := by
      calc
        (∫ omega, X omega ^ 2 - 2 * target * X omega + target ^ 2 ∂mu) =
            (∫ omega, X omega ^ 2 - 2 * target * X omega ∂mu) +
              (∫ _omega : Omega, target ^ 2 ∂mu) :=
          integral_add (hXsq.sub hlinear) hconst
        _ = (∫ omega, X omega ^ 2 ∂mu) -
              (∫ omega, 2 * target * X omega ∂mu) +
              (∫ _omega : Omega, target ^ 2 ∂mu) := by
          rw [integral_sub hXsq hlinear]
    _ = (∫ omega, X omega ^ 2 ∂mu) -
          2 * target * (∫ omega, X omega ∂mu) + target ^ 2 := by
      rw [integral_const_mul, integral_const, probReal_univ]
      ring

/-- A target-centered second-moment tail bound.  Unlike the usual Chebyshev
form, the target need not equal the mean: a lower mean bias `eta` contributes
the additive charge `2 * eta`. -/
theorem measure_relativeDeviation_le_of_target_moments
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : MemLp X 2 mu)
    {target eps eta delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hmeanLower : (1 - eta) * target ≤ ∫ omega, X omega ∂mu)
    (hsecond : (∫ omega, X omega ^ 2 ∂mu) ≤
      (1 + delta) * target ^ 2) :
    mu {omega | eps * target ≤ |X omega - target|} ≤
      ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) := by
  let threshold := eps * target
  let deviationSq : Omega → ℝ := fun omega => (X omega - target) ^ 2
  have hthreshold : 0 < threshold := mul_pos heps htarget
  have hdevInt : Integrable deviationSq mu := by
    exact (hX.sub (memLp_const target)).integrable_sq
  have hdev0 : ∀ omega, 0 ≤ deviationSq omega := fun omega => sq_nonneg _
  have hdevBound :
      (∫ omega, deviationSq omega ∂mu) ≤
        (delta + 2 * eta) * target ^ 2 := by
    rw [show (∫ omega, deviationSq omega ∂mu) =
        (∫ omega, X omega ^ 2 ∂mu) -
          2 * target * (∫ omega, X omega ∂mu) + target ^ 2 by
      simpa [deviationSq] using integral_sub_const_sq_eq mu hX target]
    have hscale0 : 0 ≤ 2 * target :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htarget.le
    have hscaledMean := mul_le_mul_of_nonneg_left hmeanLower hscale0
    nlinarith [sq_nonneg target, hsecond, hscaledMean]
  have hevent : {omega | threshold ^ 2 ≤ deviationSq omega} =
      {omega | eps * target ≤ |X omega - target|} := by
    ext omega
    simp only [Set.mem_setOf_eq, threshold, deviationSq]
    have habsSq : (X omega - target) ^ 2 = |X omega - target| ^ 2 := by
      exact (sq_abs (X omega - target)).symm
    rw [habsSq]
    exact sq_le_sq₀ hthreshold.le (abs_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := mu) (Filter.Eventually.of_forall hdev0) hdevInt (threshold ^ 2)
  rw [hevent] at hmarkov
  have hreal :
      mu.real {omega | eps * target ≤ |X omega - target|} ≤
        (delta + 2 * eta) / eps ^ 2 := by
    have hraw := hmarkov.trans hdevBound
    calc
      mu.real {omega | eps * target ≤ |X omega - target|} ≤
          ((delta + 2 * eta) * target ^ 2) / threshold ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hthreshold)]
        simpa [mul_comm] using hraw
      _ = (delta + 2 * eta) / eps ^ 2 := by
        dsimp only [threshold]
        field_simp [heps.ne', htarget.ne']
  rw [← ENNReal.toReal_le_toReal (measure_ne_top mu _)
    ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (div_nonneg (add_nonneg hdelta (mul_nonneg (by norm_num) heta))
    (sq_nonneg eps))]
  exact hreal

/-- The Chebyshev/Markov conclusion of CV18 Lemma 7.15 for the recursively
truncated product.  The remaining inputs are exactly the two numerical
product estimates supplied by the cooling schedule. -/
theorem measure_dependentTruncatedProduct_relativeDeviation_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (phases : ℕ)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hrelative : ∀ i, i ≤ phases →
      (1 + 2 * epsilon * alpha ^ 4 * i) * dependentPhaseMeanProduct second i ≤
        2 * dependentPhaseMeanProduct mean i ^ 2)
    {tailDelta relativeEps : ℝ}
    (htailDelta : 0 ≤ tailDelta) (hrelativeEps : 0 < relativeEps)
    (htailSecond :
      (1 + 2 * epsilon * alpha ^ 4 * phases) *
          dependentPhaseMeanProduct second phases ≤
        (1 + tailDelta) * dependentPhaseMeanProduct mean phases ^ 2) :
    mu {omega | relativeEps * dependentPhaseMeanProduct mean phases ≤
        |dependentTruncatedProduct alpha mean V phases omega -
          dependentPhaseMeanProduct mean phases|} ≤
      ENNReal.ofReal ((tailDelta + 2 * (phases / alpha)) / relativeEps ^ 2) := by
  have hmoments := dependentTruncatedProduct_moment_bounds_of_relativeProduct
    mu alpha epsilon mean rawMean second V halpha hepsilon hsmall hmean hmeanPos
      hrawMean hrawMean_le hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap
      hVmean hVsecond phases hind hrelative
  have htarget : 0 < dependentPhaseMeanProduct mean phases := by
    dsimp [dependentPhaseMeanProduct]
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  have hUmem : MemLp (dependentTruncatedProduct alpha mean V phases) 2 mu := by
    apply (memLp_two_iff_integrable_sq
      (measurable_dependentTruncatedProduct alpha mean V hVmeas phases).aestronglyMeasurable).2
    exact integrable_dependentTruncatedProduct_sq mu alpha mean V halpha
      hmean hVmeas hV0 phases
  apply measure_relativeDeviation_le_of_target_moments mu hUmem htarget
    hrelativeEps (div_nonneg (Nat.cast_nonneg phases) (zero_le_one.trans halpha))
      htailDelta
  · exact hmoments.1
  · exact hmoments.2.2.trans htailSecond

/-- Markov's inequality in exactly the form needed by both truncation layers
of CV18 Lemma 7.15.  If a nonnegative random variable has mean at most
`factor * scale`, then truncating it at `alpha * scale` changes it with
probability at most `factor / alpha`. -/
theorem measure_min_ne_self_le_of_integral_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → ℝ) (alpha scale factor : ℝ)
    (hfmeas : Measurable f) (hf0 : ∀ omega, 0 ≤ f omega)
    (hfint : Integrable f mu)
    (halpha : 0 < alpha) (hscale : 0 < scale) (hfactor : 0 ≤ factor)
    (hintegral : (∫ omega, f omega ∂mu) ≤ factor * scale) :
    mu {omega | min (f omega) (alpha * scale) ≠ f omega} ≤
      ENNReal.ofReal (factor / alpha) := by
  let threshold := alpha * scale
  have hthreshold : 0 < threshold := mul_pos halpha hscale
  have hsubset :
      {omega | min (f omega) threshold ≠ f omega} ⊆
        {omega | threshold ≤ f omega} := by
    intro omega hchanged
    simp only [Set.mem_setOf_eq] at hchanged ⊢
    by_contra hnot
    exact hchanged (min_eq_left (le_of_not_ge hnot))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := mu) (Filter.Eventually.of_forall hf0) hfint threshold
  have hreal :
      mu.real {omega | threshold ≤ f omega} ≤ factor / alpha := by
    have hraw :
        threshold * mu.real {omega | threshold ≤ f omega} ≤
          factor * scale := hmarkov.trans hintegral
    rw [le_div_iff₀ halpha]
    exact le_of_mul_le_mul_left
      (by simpa [threshold, mul_assoc, mul_left_comm, mul_comm] using hraw)
      hscale
  have htail :
      mu {omega | threshold ≤ f omega} ≤ ENNReal.ofReal (factor / alpha) := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top mu _)
      ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal (div_nonneg hfactor halpha.le)]
    exact hreal
  exact (measure_mono hsubset).trans htail

/-- The paper's bound `Pr(Vᵢ ≠ W̄ᵢ) ≤ 1 / alpha` at the end of
Lemma 7.15. -/
theorem measure_dependentTruncatedPhase_ne_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha : ℝ) (rawMean : ℕ → ℝ) (W : ℕ → Omega → ℝ)
    (j : ℕ) (halpha : 0 < alpha) (hrawMeanPos : 0 < rawMean j)
    (hWmeas : Measurable (W j)) (hW0 : ∀ omega, 0 ≤ W j omega)
    (hWint : Integrable (W j) mu)
    (hWmean : (∫ omega, W j omega ∂mu) = rawMean j) :
    mu {omega | dependentTruncatedPhase alpha rawMean W j omega ≠ W j omega} ≤
      ENNReal.ofReal (1 / alpha) := by
  apply measure_min_ne_self_le_of_integral_le mu (W j) alpha (rawMean j) 1
    hWmeas hW0 hWint halpha hrawMeanPos (by norm_num)
  simpa using hWmean.le

/-- Equation (8) and the first-moment recurrence imply the expectation bound
used by the second Markov estimate, whenever the current numerical coefficient
is at most two. -/
theorem integral_dependentTruncatedProduct_mul_phase_le_two
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (i : ℕ) (hind : ∀ k, k ≤ i → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V k) (V (k + 1)) mu)
    (hcoefficient : 2 * epsilon * alpha ^ 2 * (i + 1) ≤ 1) :
    (∫ omega, dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega ∂mu) ≤
      2 * dependentPhaseMeanProduct mean (i + 1) := by
  have hcov := abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcap i
      (hind i le_rfl)
  rw [hVmean (i + 1)] at hcov
  have hcovUpper :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) ≤
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
            mean (i + 1) +
          2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
    linarith [le_abs_self
      ((∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1))]
  have hU := integral_dependentTruncatedProduct_le mu alpha epsilon mean V
    halpha hepsilon hmean hVmeas hV0 hVcap hVmean i
      (fun k hk => hind k (Nat.le_of_lt hk))
  have hscaled := mul_le_mul_of_nonneg_right hU (hmean (i + 1))
  have hproduct0 := dependentPhaseMeanProduct_nonneg mean hmean (i + 1)
  calc
    (∫ omega, dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega ∂mu) ≤
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) +
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) :=
      hcovUpper
    _ ≤ ((1 + 2 * epsilon * alpha ^ 2 * i) *
          dependentPhaseMeanProduct mean i) * mean (i + 1) +
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
      exact add_le_add hscaled (le_refl _)
    _ = (1 + 2 * epsilon * alpha ^ 2 * (i + 1)) *
        dependentPhaseMeanProduct mean (i + 1) := by
      rw [dependentPhaseMeanProduct_succ]
      ring
    _ ≤ 2 * dependentPhaseMeanProduct mean (i + 1) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hproduct0

/-- The paper's bound `Pr(Uᵢ₊₁ ≠ Uᵢ Vᵢ₊₁) ≤ 2 / alpha` at the
end of Lemma 7.15, from the already established candidate first-moment
bound. -/
theorem measure_dependentTruncatedProduct_succ_ne_mul_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ) (i : ℕ)
    (halpha : 1 ≤ alpha) (hmean : ∀ j, 0 ≤ mean j)
    (hmeanPos : ∀ j, 0 < mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hcandidateMean :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) ≤
        2 * dependentPhaseMeanProduct mean (i + 1)) :
    mu {omega |
        dependentTruncatedProduct alpha mean V (i + 1) omega ≠
          dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega} ≤
      ENNReal.ofReal (2 / alpha) := by
  let candidate : Omega → ℝ := fun omega =>
    dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega
  have hcandidateMeas : Measurable candidate :=
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i).mul
      (hVmeas (i + 1))
  have hcandidate0 : ∀ omega, 0 ≤ candidate omega := fun omega =>
    mul_nonneg
      (dependentTruncatedProduct_nonneg alpha mean V
        (zero_le_one.trans halpha) hmean hV0 i omega)
      (hV0 (i + 1) omega)
  have hcandidateInt : Integrable candidate mu :=
    integrable_dependentTruncatedProduct_mul_phase mu alpha mean V halpha
      hmean hVmeas hV0 hVcap i
  have hscalePos : 0 < dependentPhaseMeanProduct mean (i + 1) := by
    dsimp [dependentPhaseMeanProduct]
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  simpa only [dependentTruncatedProduct_succ, candidate] using
    (measure_min_ne_self_le_of_integral_le mu candidate alpha
      (dependentPhaseMeanProduct mean (i + 1)) 2 hcandidateMeas hcandidate0
      hcandidateInt (zero_lt_one.trans_le halpha) hscalePos (by norm_num)
      hcandidateMean)

/-- If neither level of truncation fires through phase `i`, the recursive
variable `Uᵢ` equals the original estimator product. -/
theorem dependentTruncatedProduct_eq_sampleProduct_of_eq
    (alpha : ℝ) (mean : ℕ → ℝ) (V W : ℕ → Omega → ℝ)
    (i : ℕ) (omega : Omega)
    (hphase : ∀ j, j < i → V (j + 1) omega = W (j + 1) omega)
    (haccum : ∀ j, j < i →
      dependentTruncatedProduct alpha mean V (j + 1) omega =
        dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega) :
    dependentTruncatedProduct alpha mean V i omega =
      dependentPhaseSampleProduct W i omega := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [haccum i (Nat.lt_succ_self i),
        ih (fun j hj => hphase j (hj.trans (Nat.lt_succ_self i)))
          (fun j hj => haccum j (hj.trans (Nat.lt_succ_self i))),
        hphase i (Nat.lt_succ_self i), dependentPhaseSampleProduct_succ]

/-- Union bound for the two truncation layers in Lemma 7.15. -/
theorem measure_dependentTruncatedProduct_ne_sampleProduct_le
    (mu : Measure Omega) (alpha : ℝ) (mean : ℕ → ℝ)
    (V W : ℕ → Omega → ℝ) (phases : ℕ) :
    mu {omega | dependentTruncatedProduct alpha mean V phases omega ≠
        dependentPhaseSampleProduct W phases omega} ≤
      ∑ j : Fin phases,
        (mu {omega | V (j + 1) omega ≠ W (j + 1) omega} +
          mu {omega |
            dependentTruncatedProduct alpha mean V (j + 1) omega ≠
              dependentTruncatedProduct alpha mean V j omega *
                V (j + 1) omega}) := by
  let phaseBad : Fin phases → Set Omega := fun j =>
    {omega | V (j + 1) omega ≠ W (j + 1) omega}
  let accumBad : Fin phases → Set Omega := fun j =>
    {omega | dependentTruncatedProduct alpha mean V (j + 1) omega ≠
      dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega}
  have hsubset :
      {omega | dependentTruncatedProduct alpha mean V phases omega ≠
          dependentPhaseSampleProduct W phases omega} ⊆
        ⋃ j : Fin phases, phaseBad j ∪ accumBad j := by
    intro omega hne
    by_contra hnot
    have hall : ∀ j : Fin phases, omega ∉ phaseBad j ∪ accumBad j := by
      intro j hj
      exact hnot (Set.mem_iUnion.2 ⟨j, hj⟩)
    have hphase : ∀ j, j < phases → V (j + 1) omega = W (j + 1) omega := by
      intro j hj
      have h := hall ⟨j, hj⟩
      have hboth :
          V (j + 1) omega = W (j + 1) omega ∧
            dependentTruncatedProduct alpha mean V (j + 1) omega =
              dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega := by
        simpa [phaseBad, accumBad] using h
      exact hboth.1
    have haccum : ∀ j, j < phases →
        dependentTruncatedProduct alpha mean V (j + 1) omega =
          dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega := by
      intro j hj
      have h := hall ⟨j, hj⟩
      have hboth :
          V (j + 1) omega = W (j + 1) omega ∧
            dependentTruncatedProduct alpha mean V (j + 1) omega =
              dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega := by
        simpa [phaseBad, accumBad] using h
      exact hboth.2
    exact hne (dependentTruncatedProduct_eq_sampleProduct_of_eq
      alpha mean V W phases omega hphase haccum)
  calc
    mu {omega | dependentTruncatedProduct alpha mean V phases omega ≠
        dependentPhaseSampleProduct W phases omega} ≤
      mu (⋃ j : Fin phases, phaseBad j ∪ accumBad j) := measure_mono hsubset
    _ ≤ ∑ j : Fin phases, mu (phaseBad j ∪ accumBad j) :=
      measure_iUnion_fintype_le mu _
    _ ≤ ∑ j : Fin phases, (mu (phaseBad j) + mu (accumBad j)) := by
      exact Finset.sum_le_sum fun j _ => measure_union_le _ _
    _ = ∑ j : Fin phases,
        (mu {omega | V (j + 1) omega ≠ W (j + 1) omega} +
          mu {omega |
            dependentTruncatedProduct alpha mean V (j + 1) omega ≠
              dependentTruncatedProduct alpha mean V j omega *
                V (j + 1) omega}) := rfl

/-- Transfer any tail bound for the recursively truncated product `Uₘ` to
the original estimator product.  This is the deterministic union-bound step
at the end of CV18 Lemma 7.15. -/
theorem measure_dependentPhaseSampleProduct_relativeDeviation_le_of_truncation_bounds
    (mu : Measure Omega) (alpha : ℝ) (mean : ℕ → ℝ)
    (V W : ℕ → Omega → ℝ) (phases : ℕ)
    (relativeEps target : ℝ) (tailBound phaseBound accumBound : ENNReal)
    (htail :
      mu {omega | relativeEps * target ≤
          |dependentTruncatedProduct alpha mean V phases omega - target|} ≤
        tailBound)
    (hphase : ∀ j, j < phases →
      mu {omega | V (j + 1) omega ≠ W (j + 1) omega} ≤ phaseBound)
    (haccum : ∀ j, j < phases →
      mu {omega |
          dependentTruncatedProduct alpha mean V (j + 1) omega ≠
            dependentTruncatedProduct alpha mean V j omega * V (j + 1) omega} ≤
        accumBound) :
    mu {omega | relativeEps * target ≤
        |dependentPhaseSampleProduct W phases omega - target|} ≤
      tailBound + ∑ _ : Fin phases, (phaseBound + accumBound) := by
  let truncatedBad : Set Omega :=
    {omega | relativeEps * target ≤
      |dependentTruncatedProduct alpha mean V phases omega - target|}
  let couplingBad : Set Omega :=
    {omega | dependentTruncatedProduct alpha mean V phases omega ≠
      dependentPhaseSampleProduct W phases omega}
  have hsubset :
      {omega | relativeEps * target ≤
          |dependentPhaseSampleProduct W phases omega - target|} ⊆
        truncatedBad ∪ couplingBad := by
    intro omega hbad
    by_cases heq : dependentTruncatedProduct alpha mean V phases omega =
        dependentPhaseSampleProduct W phases omega
    · left
      simpa [truncatedBad, heq] using hbad
    · right
      exact heq
  have hcoupling := measure_dependentTruncatedProduct_ne_sampleProduct_le
    mu alpha mean V W phases
  have hcouplingBound :
      mu couplingBad ≤ ∑ _ : Fin phases, (phaseBound + accumBound) := by
    calc
      mu couplingBad ≤
          ∑ j : Fin phases,
            (mu {omega | V (j + 1) omega ≠ W (j + 1) omega} +
              mu {omega |
                dependentTruncatedProduct alpha mean V (j + 1) omega ≠
                  dependentTruncatedProduct alpha mean V j omega *
                    V (j + 1) omega}) := by
        simpa [couplingBad] using hcoupling
      _ ≤ ∑ _ : Fin phases, (phaseBound + accumBound) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (hphase j j.isLt) (haccum j j.isLt)
  calc
    mu {omega | relativeEps * target ≤
        |dependentPhaseSampleProduct W phases omega - target|} ≤
      mu (truncatedBad ∪ couplingBad) := measure_mono hsubset
    _ ≤ mu truncatedBad + mu couplingBad := measure_union_le _ _
    _ ≤ tailBound + ∑ _ : Fin phases, (phaseBound + accumBound) :=
      add_le_add (by simpa [truncatedBad] using htail) hcouplingBound

/-- CV18 Lemma 7.15 in model-independent probability-space form.  It combines
the dependent-product moment recurrence, Chebyshev, both Markov truncation
bounds, and the final union bound, and concludes directly about the original
estimator product `W₁ ⋯ Wₘ`. -/
theorem measure_dependentPhaseSampleProduct_relativeDeviation_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V W : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMeanPos : ∀ j, 0 < rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (phases : ℕ)
    (hVeq : ∀ j, 1 ≤ j → j ≤ phases → ∀ omega,
      V j omega = dependentTruncatedPhase alpha rawMean W j omega)
    (hWmeas : ∀ j, 1 ≤ j → j ≤ phases → Measurable (W j))
    (hW0 : ∀ j, 1 ≤ j → j ≤ phases → ∀ omega, 0 ≤ W j omega)
    (hWint : ∀ j, 1 ≤ j → j ≤ phases → Integrable (W j) mu)
    (hWmean : ∀ j, 1 ≤ j → j ≤ phases →
      (∫ omega, W j omega ∂mu) = rawMean j)
    (hind : ∀ i, i < phases → ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hrelative : ∀ i, i ≤ phases →
      (1 + 2 * epsilon * alpha ^ 4 * i) * dependentPhaseMeanProduct second i ≤
        2 * dependentPhaseMeanProduct mean i ^ 2)
    (hcoefficient : ∀ i, i < phases →
      2 * epsilon * alpha ^ 2 * (i + 1) ≤ 1)
    {tailDelta relativeEps : ℝ}
    (htailDelta : 0 ≤ tailDelta) (hrelativeEps : 0 < relativeEps)
    (htailSecond :
      (1 + 2 * epsilon * alpha ^ 4 * phases) *
          dependentPhaseMeanProduct second phases ≤
        (1 + tailDelta) * dependentPhaseMeanProduct mean phases ^ 2) :
    mu {omega | relativeEps * dependentPhaseMeanProduct mean phases ≤
        |dependentPhaseSampleProduct W phases omega -
          dependentPhaseMeanProduct mean phases|} ≤
      ENNReal.ofReal ((tailDelta + 2 * (phases / alpha)) / relativeEps ^ 2) +
        ∑ _ : Fin phases,
          (ENNReal.ofReal (1 / alpha) + ENNReal.ofReal (2 / alpha)) := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have htail := measure_dependentTruncatedProduct_relativeDeviation_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hsmall hmean hmeanPos
      hrawMean hrawMean_le hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap
      hVmean hVsecond phases hind hrelative htailDelta hrelativeEps htailSecond
  apply measure_dependentPhaseSampleProduct_relativeDeviation_le_of_truncation_bounds
    mu alpha mean V W phases relativeEps (dependentPhaseMeanProduct mean phases)
      (ENNReal.ofReal
        ((tailDelta + 2 * (phases / alpha)) / relativeEps ^ 2))
      (ENNReal.ofReal (1 / alpha)) (ENNReal.ofReal (2 / alpha)) htail
  · intro j hj
    simpa only [hVeq (j + 1) (by omega) (by omega)] using
      (measure_dependentTruncatedPhase_ne_le mu alpha rawMean W (j + 1)
        (zero_lt_one.trans_le halpha) (hrawMeanPos (j + 1))
        (hWmeas (j + 1) (by omega) (by omega))
        (hW0 (j + 1) (by omega) (by omega))
        (hWint (j + 1) (by omega) (by omega))
        (hWmean (j + 1) (by omega) (by omega)))
  · intro j hj
    apply measure_dependentTruncatedProduct_succ_ne_mul_le mu alpha mean V j
      halpha hmean hmeanPos hVmeas hV0 hVcapTwo
    exact integral_dependentTruncatedProduct_mul_phase_le_two
      mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcapTwo
        hVmean j (fun k hk => hind k (lt_of_le_of_lt hk hj))
          (hcoefficient j hj)

#print axioms measurable_dependentTruncatedProduct
#print axioms dependentTruncatedProduct_nonneg
#print axioms abs_integral_dependentTruncatedProduct_mul_phase_sub_le
#print axioms integral_dependentTruncatedProduct_le
#print axioms integral_dependentTruncatedProduct_sq_le
#print axioms integral_dependentTruncatedProduct_succ_ge
#print axioms integral_dependentTruncatedProduct_ge
#print axioms dependentTruncatedProduct_moment_bounds_of_relativeProduct
#print axioms measure_relativeDeviation_le_of_target_moments
#print axioms measure_dependentTruncatedProduct_relativeDeviation_le
#print axioms measure_dependentTruncatedProduct_ne_sampleProduct_le
#print axioms measure_min_ne_self_le_of_integral_le
#print axioms measure_dependentTruncatedPhase_ne_le
#print axioms integral_dependentTruncatedProduct_mul_phase_le_two
#print axioms measure_dependentTruncatedProduct_succ_ne_mul_le
#print axioms measure_dependentPhaseSampleProduct_relativeDeviation_le_of_truncation_bounds
#print axioms measure_dependentPhaseSampleProduct_relativeDeviation_le
#print axioms ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le

end ArlibCommunity.Algorithms.CV18
