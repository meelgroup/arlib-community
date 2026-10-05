/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Cousins–Vempala accelerated-cooling variance bound (§5.1)

A port of §5.1 of

> Ben Cousins, Santosh Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and
> Gaussian Volume* (arXiv:1409.6011),

the variance analysis of the ratio estimator driving the Gaussian-cooling volume
algorithm.

With `g(x,s) = f(x) e^{-‖x‖²/(2s)}` and `G(s) = ∫ g(x,s) dx`, the algorithm draws `X` from
the density `∝ g(·, σᵢ²)` and averages `Y = g(X, σᵢ₊₁²)/g(X, σᵢ²)`. The file proves,
in order:

* the two moment identities `E(Y) = G(b)/G(a)`, `E(Y²) = G(c)/G(a)` and their combination
  `variance_ratio` (paper eqs. at `:1078`, `:1086`);
* `sq_var_le`, paper Lemma 5.5: `Var(X²) ≤ 4M² Var(X)` for `X` supported in `[-M,M]`;
* the one-dimensional exponential-needle moments `J k x = ∫_ℓ^u tᵏ e^{γt}e^{-t²x/(2σ²)}`,
  differentiation under the integral sign (`hasDerivAt_J`), and — via a single
  integration by parts — the needle form of **Brascamp–Lieb** (paper Theorem 4.1),
  `J₂J₀ − J₁² ≤ (σ²/x)J₀²` (`J_var_le`, `brascampLieb`). This is *proved*, not assumed;
* `v_deriv_ge` (Lemma 5.6) and `hFun_le_exp` (Lemma 5.7): `h(α) ≤ exp(2R²α²/σ²)`;
* the localization reduction's geometric content — every needle can be put in the
  normalized position `t ↦ p + t·w` (`exists_normalized_needle`), the offset factors out
  (`needleInt_factor`) and cancels in the ratio (`needle_ratio_eq`), so every needle obeys
  the bound (`needle_variance_bound`);
* the headline bounds `lc_variance_bound` (Lemma 5.8) and `fast_var_bound` (Claim 5.11),
  and the fixed-rate `fixed_var_bound` (Lemma 5.10).

## Two inputs that are assumed, not proved

Two cited results are outside Mathlib's reach and are **not** proved here. Neither is
introduced as an axiom; each is a `Prop`-valued predicate that appears as an *explicit
hypothesis* of the theorems that need it, so `#print axioms` on every declaration below is
clean and no statement silently depends on an unproved input:

* `LocalizationHypothesis` — the Localization Lemma (paper Theorem 5.3, from [KLS95]).
  Hypothesis of `variance_bound`, `lc_variance_bound`.
* `ZLogconcaveHypothesis` — paper Lemma 5.9, that `a ↦ aⁿ∫_K f(ax) dx` is logconcave (a
  Prékopa–Leindler consequence). Hypothesis of `G_mul_G_le_of_zLogconcave`,
  `fixed_var_bound`, `fixed_var_bound_ratio`.

Everything else in the file is unconditional.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real

/-- The ambient space `ℝⁿ`. -/
abbrev EuclSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## §5.1.1 The ratio estimator and its moments -/

section Ratio

variable {n : ℕ} {f : EuclSpace n → ℝ}

/-- `g(x, s) = f(x) e^{-‖x‖²/(2s)}` (`vol3_journal.tex:1067`). -/
noncomputable def gW (f : EuclSpace n → ℝ) (s : ℝ) (x : EuclSpace n) : ℝ :=
  f x * exp (-(‖x‖ ^ 2) / (2 * s))

/-- `G(s) = ∫_{ℝⁿ} g(x,s) dx` (`vol3_journal.tex:1071`). -/
noncomputable def G (f : EuclSpace n → ℝ) (s : ℝ) : ℝ := ∫ x, gW f s x

lemma gW_nonneg (hf : ∀ x, 0 ≤ f x) (s : ℝ) (x : EuclSpace n) : 0 ≤ gW f s x :=
  mul_nonneg (hf x) (exp_pos _).le

/-- **The key pointwise identity.** `g(x,b)²/g(x,a) = g(x, ab/(2a-b))`: squaring the
numerator and dividing by the base density again produces a Gaussian weight, with the
variance parameter transformed by the harmonic relation `1/c = 2/b - 1/a`.
This is the computation at `vol3_journal.tex:1085`. -/
theorem gW_sq_div {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : 2 * a - b ≠ 0)
    (x : EuclSpace n) :
    (gW f b x) ^ 2 / gW f a x = gW f (a * b / (2 * a - b)) x := by
  by_cases hfx : f x = 0
  · simp [gW, hfx]
  · have hc : a * b / (2 * a - b) ≠ 0 := div_ne_zero (mul_ne_zero ha hb) hab
    have hc2 : 2 * (a * b / (2 * a - b)) ≠ 0 := by
      simpa using mul_ne_zero (two_ne_zero) hc
    have key : -(‖x‖ ^ 2) / (2 * b) + -(‖x‖ ^ 2) / (2 * b)
        = -(‖x‖ ^ 2) / (2 * (a * b / (2 * a - b))) + -(‖x‖ ^ 2) / (2 * a) := by
      field_simp
      ring
    rw [gW, gW, gW, div_eq_iff (mul_ne_zero hfx (ne_of_gt (exp_pos _)))]
    calc (f x * exp (-(‖x‖ ^ 2) / (2 * b))) ^ 2
        = f x ^ 2 * (exp (-(‖x‖ ^ 2) / (2 * b)) * exp (-(‖x‖ ^ 2) / (2 * b))) := by ring
      _ = f x ^ 2 * exp (-(‖x‖ ^ 2) / (2 * b) + -(‖x‖ ^ 2) / (2 * b)) := by rw [exp_add]
      _ = f x ^ 2 * exp (-(‖x‖ ^ 2) / (2 * (a * b / (2 * a - b)))
            + -(‖x‖ ^ 2) / (2 * a)) := by rw [key]
      _ = f x * exp (-(‖x‖ ^ 2) / (2 * (a * b / (2 * a - b))))
            * (f x * exp (-(‖x‖ ^ 2) / (2 * a))) := by rw [exp_add]; ring

/-- The cooling substitution `a = σ²/(1+α)`, `b = σ²` sends `c = ab/(2a-b)` to
`σ²/(1-α)` (`vol3_journal.tex:1094`). -/
theorem cool_param {σ α : ℝ} (hσ : σ ≠ 0) (hα1 : 1 + α ≠ 0) (hα2 : 1 - α ≠ 0) :
    (σ ^ 2 / (1 + α)) * σ ^ 2 / (2 * (σ ^ 2 / (1 + α)) - σ ^ 2) = σ ^ 2 / (1 - α) := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hden : 2 * (σ ^ 2 / (1 + α)) - σ ^ 2 = σ ^ 2 * (1 - α) / (1 + α) := by
    field_simp; ring
  rw [hden]
  field_simp

/-- `2a - b ≠ 0` under the cooling substitution. -/
lemma cool_denom_ne {σ α : ℝ} (hσ : σ ≠ 0) (hα1 : 1 + α ≠ 0) (hα2 : 1 - α ≠ 0) :
    2 * (σ ^ 2 / (1 + α)) - σ ^ 2 ≠ 0 := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h : 2 * (σ ^ 2 / (1 + α)) - σ ^ 2 = σ ^ 2 * (1 - α) / (1 + α) := by
    field_simp; ring
  rw [h]
  exact div_ne_zero (mul_ne_zero hσ2 hα2) hα1

/-! ### The moment identities

`X` has density `g(·,a)/G(a)`, and `Y = g(X,b)/g(X,a)`. -/

/-- `E(Y) = G(b)/G(a)` (`vol3_journal.tex:1078`). -/
theorem expect_ratio {a b : ℝ} :
    ∫ x, (gW f b x / gW f a x) * (gW f a x / G f a) = G f b / G f a := by
  have hpt : ∀ x, (gW f b x / gW f a x) * (gW f a x / G f a) = gW f b x / G f a := by
    intro x
    by_cases hax : gW f a x = 0
    · have hfx : f x = 0 := by
        rcases mul_eq_zero.mp hax with h | h
        · exact h
        · exact absurd h (ne_of_gt (exp_pos _))
      simp [gW, hfx]
    · field_simp
  simp_rw [hpt]
  rw [integral_div]
  rfl

/-- `E(Y²) = G(c)/G(a)` with `c = ab/(2a-b)` (`vol3_journal.tex:1086`). -/
theorem expect_ratio_sq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : 2 * a - b ≠ 0) :
    ∫ x, (gW f b x / gW f a x) ^ 2 * (gW f a x / G f a)
      = G f (a * b / (2 * a - b)) / G f a := by
  have hpt : ∀ x, (gW f b x / gW f a x) ^ 2 * (gW f a x / G f a)
      = gW f (a * b / (2 * a - b)) x / G f a := by
    intro x
    rw [← gW_sq_div ha hb hab x]
    by_cases hax : gW f a x = 0
    · simp [hax]
    · have hkey : (gW f b x / gW f a x) ^ 2 * gW f a x = gW f b x ^ 2 / gW f a x := by
        field_simp
      calc (gW f b x / gW f a x) ^ 2 * (gW f a x / G f a)
          = ((gW f b x / gW f a x) ^ 2 * gW f a x) / G f a := by ring
        _ = (gW f b x ^ 2 / gW f a x) / G f a := by rw [hkey]
  simp_rw [hpt]
  rw [integral_div]
  rfl

/-- **The variance ratio of the estimator** (`vol3_journal.tex:1096`): with
`a = σ²/(1+α)` and `b = σ²`,

  `E(Y²)/E(Y)² = G(σ²/(1+α)) · G(σ²/(1-α)) / G(σ²)²`. -/
theorem variance_ratio {σ α : ℝ} (hσ : σ ≠ 0) (hα1 : 1 + α ≠ 0) (hα2 : 1 - α ≠ 0)
    (hGa : G f (σ ^ 2 / (1 + α)) ≠ 0) (hGb : G f (σ ^ 2) ≠ 0) :
    (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α))))
      / (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
          * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2
      = G f (σ ^ 2 / (1 + α)) * G f (σ ^ 2 / (1 - α)) / (G f (σ ^ 2)) ^ 2 := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have ha : σ ^ 2 / (1 + α) ≠ 0 := div_ne_zero hσ2 hα1
  have hab := cool_denom_ne hσ hα1 hα2
  rw [expect_ratio, expect_ratio_sq ha hσ2 hab, cool_param hσ hα1 hα2]
  field_simp

end Ratio

/-! ## §5.1.2 Paper Lemma 5.5: `Var(X²) ≤ 4M² Var(X)` on a bounded support

The paper's proof is a symmetrization: with `Y` an independent copy of `X`,
`2 Var(X²) = E((X+Y)²(X-Y)²) ≤ 4 max{a²,b²} E((X-Y)²) = 8 max{a²,b²} Var(X)`.
The formalization is the same argument, with the independent copy realized as the product
measure `μ ⊗ μ` and the pointwise inequality `0 ≤ (s-t)² (4M² - (s+t)²)` integrated over
the square.

Statements are *unnormalized* — in terms of `∫ tᵏ dμ` and the total mass — not of moments
of a probability distribution. That is the form Lemma 5.6 consumes, where `μ` is a
Gaussian weight on an interval which is nowhere normalized. -/

section Moments

variable {μ : Measure ℝ}

/-- On a finite measure whose support is bounded by `M`, every power is integrable. -/
lemma integrable_pow_of_bounded [IsFiniteMeasure μ] {M : ℝ}
    (hM : ∀ᵐ t ∂μ, |t| ≤ M) (k : ℕ) : Integrable (fun t => t ^ k) μ := by
  refine ⟨(measurable_id.pow_const k).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := |M| ^ k) ?_
  filter_upwards [hM] with t ht
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg t) (ht.trans (le_abs_self M)) k

/-- **Paper Lemma 5.5 (`vol3_journal.tex:1170`)**, in the weighted, unnormalized form the
rest of the development uses. Writing `mₖ = ∫ tᵏ w(t) dν` for a nonnegative weight `w`,

  `m₄ m₀ - m₂² ≤ 4M² (m₂ m₀ - m₁²)`

whenever `ν` is supported in `[-M, M]`. Dividing by `m₀²` gives the paper's
`E(X⁴) - E(X²)² ≤ 4M² Var(X)` for the distribution with density `∝ w`.

The weight is carried explicitly rather than absorbed into the measure because that is how
Section 5.1 uses it: `w` is the needle weight `s(x, ·)`, which is never normalized. -/
theorem sq_var_le [SFinite μ] {M : ℝ} {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hM : ∀ᵐ t ∂μ, |t| ≤ M) (hint : ∀ k : ℕ, Integrable (fun t => t ^ k * w t) μ) :
    (∫ t, t ^ 4 * w t ∂μ) * (∫ t, w t ∂μ) - (∫ t, t ^ 2 * w t ∂μ) ^ 2
      ≤ 4 * M ^ 2 * ((∫ t, t ^ 2 * w t ∂μ) * (∫ t, w t ∂μ) - (∫ t, t * w t ∂μ) ^ 2) := by
  have h0 : (∫ t, w t ∂μ) = ∫ t, t ^ (0:ℕ) * w t ∂μ := by simp
  -- `|z.1| ≤ M` and `|z.2| ≤ M` hold a.e. for the product measure
  have h1 : ∀ᵐ z : ℝ × ℝ ∂(μ.prod μ), |z.1| ≤ M :=
    Measure.quasiMeasurePreserving_fst.ae hM
  have h2 : ∀ᵐ z : ℝ × ℝ ∂(μ.prod μ), |z.2| ≤ M :=
    Measure.quasiMeasurePreserving_snd.ae hM
  -- the symmetrized integrand is pointwise nonnegative
  have hnn : 0 ≤ ∫ z : ℝ × ℝ,
      (z.1 - z.2) ^ 2 * (4 * M ^ 2 - (z.1 + z.2) ^ 2) * (w z.1 * w z.2) ∂(μ.prod μ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    have habs : |z.1 + z.2| ≤ 2 * M := (abs_add_le _ _).trans (by linarith)
    have hsq : (z.1 + z.2) ^ 2 ≤ 4 * M ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (z.1 + z.2)) habs 2
      rw [sq_abs] at h
      nlinarith
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
      (mul_nonneg (hw z.1) (hw z.2))
  -- expand `(s-t)²(4M² - (s+t)²) w(s) w(t)` into separable terms
  have hsplit : ∀ z : ℝ × ℝ,
      (z.1 - z.2) ^ 2 * (4 * M ^ 2 - (z.1 + z.2) ^ 2) * (w z.1 * w z.2)
      = 4 * M ^ 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
        + (-(8 * M ^ 2)) * ((z.1 ^ 1 * w z.1) * (z.2 ^ 1 * w z.2))
        + 4 * M ^ 2 * ((z.1 ^ (0:ℕ) * w z.1) * (z.2 ^ 2 * w z.2))
        + (-1) * ((z.1 ^ 4 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
        + 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ 2 * w z.2))
        + (-1) * ((z.1 ^ (0:ℕ) * w z.1) * (z.2 ^ 4 * w z.2)) := by
    intro z; simp only [pow_zero, pow_one, one_mul]; ring
  have hI : ∀ (c : ℝ) (i j : ℕ), Integrable
      (fun z : ℝ × ℝ => c * ((z.1 ^ i * w z.1) * (z.2 ^ j * w z.2))) (μ.prod μ) :=
    fun c i j => ((hint i).mul_prod (hint j)).const_mul c
  have hprod : ∀ i j : ℕ,
      ∫ z : ℝ × ℝ, (z.1 ^ i * w z.1) * (z.2 ^ j * w z.2) ∂(μ.prod μ)
        = (∫ t, t ^ i * w t ∂μ) * (∫ t, t ^ j * w t ∂μ) :=
    fun i j => integral_prod_mul (fun s => s ^ i * w s) (fun t => t ^ j * w t)
  have hexp : ∫ z : ℝ × ℝ,
      (z.1 - z.2) ^ 2 * (4 * M ^ 2 - (z.1 + z.2) ^ 2) * (w z.1 * w z.2) ∂(μ.prod μ)
      = 4 * M ^ 2 * ((∫ t, t ^ 2 * w t ∂μ) * (∫ t, t ^ (0:ℕ) * w t ∂μ))
        + (-(8 * M ^ 2)) * ((∫ t, t ^ 1 * w t ∂μ) * (∫ t, t ^ 1 * w t ∂μ))
        + 4 * M ^ 2 * ((∫ t, t ^ (0:ℕ) * w t ∂μ) * (∫ t, t ^ 2 * w t ∂μ))
        + (-1) * ((∫ t, t ^ 4 * w t ∂μ) * (∫ t, t ^ (0:ℕ) * w t ∂μ))
        + 2 * ((∫ t, t ^ 2 * w t ∂μ) * (∫ t, t ^ 2 * w t ∂μ))
        + (-1) * ((∫ t, t ^ (0:ℕ) * w t ∂μ) * (∫ t, t ^ 4 * w t ∂μ)) := by
    -- the five partial sums, each stated with an explicit lambda so that `integral_add`
    -- rewrites against the pointwise (not `Pi.add`) shape of the goal
    have p2 : Integrable (fun z : ℝ × ℝ =>
        4 * M ^ 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
          + (-(8 * M ^ 2)) * ((z.1 ^ 1 * w z.1) * (z.2 ^ 1 * w z.2)))
        (μ.prod μ) := (hI _ 2 0).add (hI _ 1 1)
    have p3 : Integrable (fun z : ℝ × ℝ =>
        4 * M ^ 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
          + (-(8 * M ^ 2)) * ((z.1 ^ 1 * w z.1) * (z.2 ^ 1 * w z.2))
          + 4 * M ^ 2 * ((z.1 ^ (0:ℕ) * w z.1) * (z.2 ^ 2 * w z.2)))
        (μ.prod μ) := p2.add (hI _ 0 2)
    have p4 : Integrable (fun z : ℝ × ℝ =>
        4 * M ^ 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
          + (-(8 * M ^ 2)) * ((z.1 ^ 1 * w z.1) * (z.2 ^ 1 * w z.2))
          + 4 * M ^ 2 * ((z.1 ^ (0:ℕ) * w z.1) * (z.2 ^ 2 * w z.2))
          + (-1) * ((z.1 ^ 4 * w z.1) * (z.2 ^ (0:ℕ) * w z.2)))
        (μ.prod μ) := p3.add (hI _ 4 0)
    have p5 : Integrable (fun z : ℝ × ℝ =>
        4 * M ^ 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
          + (-(8 * M ^ 2)) * ((z.1 ^ 1 * w z.1) * (z.2 ^ 1 * w z.2))
          + 4 * M ^ 2 * ((z.1 ^ (0:ℕ) * w z.1) * (z.2 ^ 2 * w z.2))
          + (-1) * ((z.1 ^ 4 * w z.1) * (z.2 ^ (0:ℕ) * w z.2))
          + 2 * ((z.1 ^ 2 * w z.1) * (z.2 ^ 2 * w z.2)))
        (μ.prod μ) := p4.add (hI _ 2 2)
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add p5 (hI _ 0 4), integral_add p4 (hI _ 2 2), integral_add p3 (hI _ 4 0),
      integral_add p2 (hI _ 0 2), integral_add (hI _ 2 0) (hI _ 1 1)]
    simp only [integral_const_mul, hprod]
  rw [hexp] at hnn
  rw [h0]
  simp only [pow_one] at hnn ⊢
  nlinarith [hnn]

end Moments

/-! ## §5.1.3 The exponential needle

The paper writes (`vol3_journal.tex:1228`) `s(x,t) = e^{γ t} · e^{-t² x/(2σ²)}` and studies
the moment integrals `∫_ℓ^u tᵏ s(x,t) dt` as functions of the parameter `x`. This section
sets those up (`nWeight`, `J`) and proves the fact everything else rests on:
differentiating under the integral sign in `x` lowers to the moment two degrees higher,

  `d/dx J k x = -(1/(2σ²)) · J (k+2) x`.

`x` ranges over all of `ℝ` here; the paper only ever uses `x ∈ [1-α, 1+α]`. -/

section Needle

open intervalIntegral

/-- The exponential-needle weight `s(x,t) = e^{γt} e^{-t²x/(2σ²)}`
(`vol3_journal.tex:1228`). -/
noncomputable def nWeight (γ σ : ℝ) (x t : ℝ) : ℝ :=
  exp (γ * t) * exp (-(t ^ 2 * x) / (2 * σ ^ 2))

/-- The `k`-th moment of the needle weight over `[ℓ, u]`. The paper's `v(x)` is
`J 2 x / J 0 x`. -/
noncomputable def J (γ σ ℓ u : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in ℓ..u, t ^ k * nWeight γ σ x t

variable {γ σ ℓ u : ℝ}

lemma nWeight_pos (x t : ℝ) : 0 < nWeight γ σ x t :=
  mul_pos (exp_pos _) (exp_pos _)

lemma continuous_nWeight (x : ℝ) : Continuous (nWeight γ σ x) := by
  unfold nWeight
  fun_prop

lemma continuous_pow_mul_nWeight (k : ℕ) (x : ℝ) :
    Continuous (fun t => t ^ k * nWeight γ σ x t) :=
  (continuous_pow k).mul (continuous_nWeight x)

lemma intervalIntegrable_J (k : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t => t ^ k * nWeight γ σ x t) volume ℓ u :=
  (continuous_pow_mul_nWeight k x).intervalIntegrable ℓ u

/-- Pointwise derivative of the needle weight in the parameter `x`. -/
lemma hasDerivAt_pow_mul_nWeight (hσ : σ ≠ 0) (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => t ^ k * nWeight γ σ x t)
      (-(1 / (2 * σ ^ 2)) * (t ^ (k + 2) * nWeight γ σ x t)) x := by
  have hσ2 : (2 : ℝ) * σ ^ 2 ≠ 0 := by positivity
  have hlin : HasDerivAt (fun x : ℝ => -(t ^ 2 * x)) (-(t ^ 2)) x := by
    simpa [neg_mul] using (hasDerivAt_id x).const_mul (-(t ^ 2))
  have h0 := hlin.div_const (2 * σ ^ 2)
  have h3 : HasDerivAt (fun y => t ^ k * nWeight γ σ y t)
      (t ^ k * (exp (γ * t)
        * (exp (-(t ^ 2 * x) / (2 * σ ^ 2)) * (-(t ^ 2) / (2 * σ ^ 2))))) x :=
    ((h0.exp).const_mul (exp (γ * t))).const_mul (t ^ k)
  refine h3.congr_deriv ?_
  simp only [nWeight]
  rw [pow_add]
  field_simp

/-- **Differentiation under the integral sign.** In the parameter `x`, the `k`-th needle
moment differentiates to `-(1/(2σ²))` times the `(k+2)`-nd. This is the computation the
paper performs at `vol3_journal.tex:1248` and again inside `v'`. -/
theorem hasDerivAt_J (hσ : σ ≠ 0) (k : ℕ) (x₀ : ℝ) :
    HasDerivAt (J γ σ ℓ u k) (-(1 / (2 * σ ^ 2)) * J γ σ ℓ u (k + 2) x₀) x₀ := by
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  set bound : ℝ → ℝ := fun t =>
    (1 / (2 * σ ^ 2)) *
      (|t| ^ (k + 2) * (exp (|γ| * |t|) * exp (t ^ 2 * (|x₀| + 1) / (2 * σ ^ 2))))
    with hbound
  have hbound_cont : Continuous bound := by
    rw [hbound]; fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := ℓ) (b := u)
    (F := fun x t => t ^ k * nWeight γ σ x t)
    (F' := fun x t => -(1 / (2 * σ ^ 2)) * (t ^ (k + 2) * nWeight γ σ x t))
    (x₀ := x₀) (bound := bound) (μ := volume) (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (continuous_pow_mul_nWeight k x).aestronglyMeasurable)
    (intervalIntegrable_J k x₀)
    ((continuous_const.mul (continuous_pow_mul_nWeight (k + 2) x₀)).aestronglyMeasurable)
    ?_ (hbound_cont.intervalIntegrable ℓ u)
    (Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_pow_mul_nWeight hσ k t x)
  · have hkey : HasDerivAt (J γ σ ℓ u k)
        (∫ t in ℓ..u, -(1 / (2 * σ ^ 2)) * (t ^ (k + 2) * nWeight γ σ x₀ t)) x₀ := key.2
    refine hkey.congr_deriv ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  · refine Filter.Eventually.of_forall fun t _ x hx => ?_
    rw [Real.norm_eq_abs, hbound]
    have hxb : |x| ≤ |x₀| + 1 := by
      have : |x - x₀| < 1 := by simpa [Real.dist_eq] using hx
      calc |x| = |x₀ + (x - x₀)| := by rw [add_sub_cancel]
        _ ≤ |x₀| + |x - x₀| := abs_add_le _ _
        _ ≤ |x₀| + 1 := by linarith
    have habs : |(-(1 / (2 * σ ^ 2)) * (t ^ (k + 2) * nWeight γ σ x t))|
        = (1 / (2 * σ ^ 2)) * (|t| ^ (k + 2) * nWeight γ σ x t) := by
      rw [abs_mul, abs_neg, abs_mul, abs_pow, abs_of_pos (nWeight_pos x t)]
      rw [abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * σ ^ 2))]
    rw [habs]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold nWeight
    refine mul_le_mul (exp_le_exp.mpr ?_) (exp_le_exp.mpr ?_) (exp_pos _).le (exp_pos _).le
    · calc γ * t ≤ |γ * t| := le_abs_self _
        _ = |γ| * |t| := abs_mul _ _
    · have hnum : -(t ^ 2 * x) ≤ t ^ 2 * (|x₀| + 1) :=
        calc -(t ^ 2 * x) ≤ |t ^ 2 * x| := neg_le_abs (t ^ 2 * x)
          _ = t ^ 2 * |x| := by rw [abs_mul, abs_pow, sq_abs]
          _ ≤ t ^ 2 * (|x₀| + 1) := by nlinarith [sq_nonneg t]
      rw [div_le_div_iff₀ hσ2 hσ2]
      nlinarith [sq_nonneg σ]

/-! ### The needle variance bound — Brascamp–Lieb in one dimension, proved

Paper Theorem 4.1 (`vol3_journal.tex:1407`) cites Brascamp–Lieb [BL76] for the fact that
the needle distribution at parameter `x` — the Gaussian of variance `σ²/x`, tilted by
`e^{γt}` and restricted to `[ℓ,u]` — has variance at most `σ²/x`. In this one-dimensional
setting the general theorem is not needed: the tilt only shifts the mean and the
restriction only shrinks the spread, and a single integration by parts sees both at once.

Write `A = J₀`, `B = J₁` and `g(t) = (tA − B)·s(x,t)`. Since `∂ₜ s = (γ − tx/σ²)s`
(`hasDerivAt_nWeight_t`),

  `∫_ℓ^u g′ = A² − (x/σ²)(J₂A − B²)`,

because the two `γ` terms cancel — that cancellation is what makes the tilt harmless.
The fundamental theorem of calculus equates this with `g(u) − g(ℓ)`, which is
`(uA − B)s(x,u) + (B − ℓA)s(x,ℓ) ≥ 0`, since `ℓ ≤ B/A ≤ u` says the mean lies inside the
interval (`J1_le_right`, `J1_ge_left`) — and that is where the restriction is spent. -/

/-- **Pointwise derivative of the needle weight in `t`**: `∂ₜ s(x,t) = (γ − tx/σ²)s(x,t)`.

The companion of `hasDerivAt_pow_mul_nWeight`, which differentiates in the parameter `x`.
Here the `t` in the exponent is what matters, and the resulting factor is what makes the
weight's logarithmic derivative linear — the sole input to the variance bound. -/
lemma hasDerivAt_nWeight_t (hσ : σ ≠ 0) (x t : ℝ) :
    HasDerivAt (nWeight γ σ x) ((γ - t * x / σ ^ 2) * nWeight γ σ x t) t := by
  have hσ2 : (2 : ℝ) * σ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => γ * s) γ t := by
    simpa using (hasDerivAt_id t).const_mul γ
  have hp : HasDerivAt (fun s : ℝ => -(s ^ 2 * x)) (-(2 * t * x)) t := by
    have h := ((hasDerivAt_pow 2 t).mul_const x).neg
    norm_num at h
    exact h
  have h2 : HasDerivAt (fun s : ℝ => -(s ^ 2 * x) / (2 * σ ^ 2)) (-(t * x / σ ^ 2)) t := by
    refine (hp.div_const (2 * σ ^ 2)).congr_deriv ?_
    field_simp
  have h : HasDerivAt (nWeight γ σ x)
      (exp (γ * t) * γ * exp (-(t ^ 2 * x) / (2 * σ ^ 2))
        + exp (γ * t) * (exp (-(t ^ 2 * x) / (2 * σ ^ 2)) * -(t * x / σ ^ 2))) t :=
    h1.exp.mul h2.exp
  refine h.congr_deriv ?_
  simp only [nWeight]
  ring

/-- `J₀` as a plain integral of the weight (the `t^0` factor removed). -/
lemma J_zero_eq (x : ℝ) : J γ σ ℓ u 0 x = ∫ t in ℓ..u, nWeight γ σ x t := by
  simp [J]

/-- `J₁` as a plain integral (the `t^1` factor flattened). -/
lemma J_one_eq (x : ℝ) : J γ σ ℓ u 1 x = ∫ t in ℓ..u, t * nWeight γ σ x t := by
  simp [J]

/-- **The needle's mean is at most `u`**, written without dividing: `J₁ ≤ u·J₀`. It is
`∫_ℓ^u (u − t)s(x,t) dt ≥ 0`. -/
lemma J1_le_right (hlu : ℓ ≤ u) (x : ℝ) : J γ σ ℓ u 1 x ≤ u * J γ σ ℓ u 0 x := by
  have hnn : 0 ≤ ∫ t in ℓ..u, (u - t) * nWeight γ σ x t := by
    refine intervalIntegral.integral_nonneg hlu fun t ht => ?_
    exact mul_nonneg (by linarith [ht.2]) (nWeight_pos (γ := γ) (σ := σ) x t).le
  have hsplit : (∫ t in ℓ..u, (u - t) * nWeight γ σ x t)
      = u * J γ σ ℓ u 0 x - J γ σ ℓ u 1 x := by
    have h0 : IntervalIntegrable (fun t : ℝ => u * nWeight γ σ x t) volume ℓ u :=
      (continuous_const.mul (continuous_nWeight (γ := γ) (σ := σ) x)).intervalIntegrable ℓ u
    have h1 : IntervalIntegrable (fun t : ℝ => t * nWeight γ σ x t) volume ℓ u :=
      ((continuous_id.mul (continuous_nWeight (γ := γ) (σ := σ) x))).intervalIntegrable ℓ u
    have hsub : (∫ t in ℓ..u, (u - t) * nWeight γ σ x t)
        = (∫ t in ℓ..u, u * nWeight γ σ x t) - ∫ t in ℓ..u, t * nWeight γ σ x t := by
      rw [← intervalIntegral.integral_sub h0 h1]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [hsub, intervalIntegral.integral_const_mul, ← J_zero_eq, ← J_one_eq]
  linarith [hsplit ▸ hnn]

/-- **The needle's mean is at least `ℓ`**: `ℓ·J₀ ≤ J₁`, from `∫_ℓ^u (t − ℓ)s(x,t) dt ≥ 0`. -/
lemma J1_ge_left (hlu : ℓ ≤ u) (x : ℝ) : ℓ * J γ σ ℓ u 0 x ≤ J γ σ ℓ u 1 x := by
  have hnn : 0 ≤ ∫ t in ℓ..u, (t - ℓ) * nWeight γ σ x t := by
    refine intervalIntegral.integral_nonneg hlu fun t ht => ?_
    exact mul_nonneg (by linarith [ht.1]) (nWeight_pos (γ := γ) (σ := σ) x t).le
  have hsplit : (∫ t in ℓ..u, (t - ℓ) * nWeight γ σ x t)
      = J γ σ ℓ u 1 x - ℓ * J γ σ ℓ u 0 x := by
    have h0 : IntervalIntegrable (fun t : ℝ => ℓ * nWeight γ σ x t) volume ℓ u :=
      (continuous_const.mul (continuous_nWeight (γ := γ) (σ := σ) x)).intervalIntegrable ℓ u
    have h1 : IntervalIntegrable (fun t : ℝ => t * nWeight γ σ x t) volume ℓ u :=
      ((continuous_id.mul (continuous_nWeight (γ := γ) (σ := σ) x))).intervalIntegrable ℓ u
    have hsub : (∫ t in ℓ..u, (t - ℓ) * nWeight γ σ x t)
        = (∫ t in ℓ..u, t * nWeight γ σ x t) - ∫ t in ℓ..u, ℓ * nWeight γ σ x t := by
      rw [← intervalIntegral.integral_sub h1 h0]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [hsub, intervalIntegral.integral_const_mul, ← J_zero_eq, ← J_one_eq]
  linarith [hsplit ▸ hnn]

/-- **The integration by parts.** With `A = J₀` and `B = J₁`, applying the fundamental
theorem of calculus to `g(t) = (tA − B)s(x,t)` gives

  `A² − (x/σ²)(J₂A − B²) = (uA − B)s(x,u) + (B − ℓA)s(x,ℓ)`.

Both `γ`-terms cancel on the left, which is why the exponential tilt costs nothing. -/
lemma J_var_ibp (hσ : σ ≠ 0) (_hlu : ℓ ≤ u) (x : ℝ) :
    (J γ σ ℓ u 0 x) ^ 2
        - (x / σ ^ 2) * (J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2)
      = (u * J γ σ ℓ u 0 x - J γ σ ℓ u 1 x) * nWeight γ σ x u
        + (J γ σ ℓ u 1 x - ℓ * J γ σ ℓ u 0 x) * nWeight γ σ x ℓ := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  set A : ℝ := J γ σ ℓ u 0 x with hA
  set B : ℝ := J γ σ ℓ u 1 x with hB
  set c₀ : ℝ := A - γ * B with hc₀
  set c₁ : ℝ := γ * A + x / σ ^ 2 * B with hc₁
  set c₂ : ℝ := -(x / σ ^ 2) * A with hc₂
  -- the derivative of `g(t) = (tA − B)s(x,t)`, arranged as a combination of `tᵏ s(x,t)`
  have hderiv : ∀ t ∈ Set.uIcc ℓ u,
      HasDerivAt (fun t : ℝ => (t * A - B) * nWeight γ σ x t)
        (c₀ * (t ^ 0 * nWeight γ σ x t) + c₁ * (t ^ 1 * nWeight γ σ x t)
          + c₂ * (t ^ 2 * nWeight γ σ x t)) t := by
    intro t _
    have hlin : HasDerivAt (fun t : ℝ => t * A - B) A t := by
      simpa using ((hasDerivAt_id t).mul_const A).sub_const B
    have h : HasDerivAt (fun t : ℝ => (t * A - B) * nWeight γ σ x t)
        (A * nWeight γ σ x t
          + (t * A - B) * ((γ - t * x / σ ^ 2) * nWeight γ σ x t)) t :=
      hlin.mul (hasDerivAt_nWeight_t (γ := γ) (σ := σ) hσ x t)
    refine h.congr_deriv ?_
    rw [hc₀, hc₁, hc₂]
    field_simp
    ring
  have hcont : Continuous fun t : ℝ =>
      c₀ * (t ^ 0 * nWeight γ σ x t) + c₁ * (t ^ 1 * nWeight γ σ x t)
        + c₂ * (t ^ 2 * nWeight γ σ x t) :=
    ((continuous_const.mul (continuous_pow_mul_nWeight (γ := γ) (σ := σ) 0 x)).add
        (continuous_const.mul (continuous_pow_mul_nWeight (γ := γ) (σ := σ) 1 x))).add
      (continuous_const.mul (continuous_pow_mul_nWeight (γ := γ) (σ := σ) 2 x))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable ℓ u)
  -- evaluate the left-hand integral term by term
  have hexp : (∫ t in ℓ..u, c₀ * (t ^ 0 * nWeight γ σ x t) + c₁ * (t ^ 1 * nWeight γ σ x t)
        + c₂ * (t ^ 2 * nWeight γ σ x t))
      = c₀ * J γ σ ℓ u 0 x + c₁ * J γ σ ℓ u 1 x + c₂ * J γ σ ℓ u 2 x := by
    rw [intervalIntegral.integral_add
        (((intervalIntegrable_J (γ := γ) (σ := σ) 0 x).const_mul c₀).add
          ((intervalIntegrable_J (γ := γ) (σ := σ) 1 x).const_mul c₁))
        ((intervalIntegrable_J (γ := γ) (σ := σ) 2 x).const_mul c₂),
      intervalIntegral.integral_add ((intervalIntegrable_J (γ := γ) (σ := σ) 0 x).const_mul c₀)
        ((intervalIntegrable_J (γ := γ) (σ := σ) 1 x).const_mul c₁),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [J]
  rw [hexp] at hftc
  rw [hc₀, hc₁, hc₂, ← hA, ← hB] at hftc
  -- `hftc : (A − γB)A + (γA + (x/σ²)B)B + (−(x/σ²)A)J₂ = (uA − B)s(x,u) − (ℓA − B)s(x,ℓ)`
  linear_combination hftc

/-- **Brascamp–Lieb for the exponential needle, proved rather than cited**
(paper Theorem 4.1, `vol3_journal.tex:1407`):

  `J₂J₀ − J₁² ≤ (σ²/x)·J₀²`,

i.e. the needle distribution at parameter `x` has variance at most `σ²/x`. -/
theorem J_var_le (hσ : σ ≠ 0) (hlu : ℓ ≤ u) {x : ℝ} (hx : 0 < x) :
    J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2
      ≤ (σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2 := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hibp := J_var_ibp (γ := γ) (σ := σ) hσ hlu x
  have hu : 0 ≤ (u * J γ σ ℓ u 0 x - J γ σ ℓ u 1 x) * nWeight γ σ x u :=
    mul_nonneg (by linarith [J1_le_right (γ := γ) (σ := σ) hlu x])
      (nWeight_pos (γ := γ) (σ := σ) x u).le
  have hl : 0 ≤ (J γ σ ℓ u 1 x - ℓ * J γ σ ℓ u 0 x) * nWeight γ σ x ℓ :=
    mul_nonneg (by linarith [J1_ge_left (γ := γ) (σ := σ) hlu x])
      (nWeight_pos (γ := γ) (σ := σ) x ℓ).le
  -- the boundary terms are both nonnegative, so `(x/σ²)·Var ≤ J₀²`
  have hkey : x / σ ^ 2 * (J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2)
      ≤ (J γ σ ℓ u 0 x) ^ 2 := by linarith
  have hcoef : (0 : ℝ) ≤ σ ^ 2 / x := by positivity
  have hcancel : σ ^ 2 / x * (x / σ ^ 2) = 1 := by
    field_simp
  calc J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2
      = σ ^ 2 / x * (x / σ ^ 2 * (J γ σ ℓ u 2 x * J γ σ ℓ u 0 x
          - (J γ σ ℓ u 1 x) ^ 2)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ σ ^ 2 / x * (J γ σ ℓ u 0 x) ^ 2 := mul_le_mul_of_nonneg_left hkey hcoef

end Needle

/-! ## §5.1.4 Paper Lemma 5.6: the derivative of the second-moment ratio

Differentiating under the integral sign (`hasDerivAt_J`),

  `v'(x) = (1/(2σ²)) · (J₂² - J₀J₄) / J₀²`,

which is `(1/(2σ²))(E(X²)² - E(X⁴))` for the needle distribution `X`. Lemma 5.5
(`sq_var_le`) bounds `E(X⁴) - E(X²)²` by `4R² Var(X)`, and Brascamp–Lieb (`J_var_le`)
bounds `Var(X)` by `σ²/x`. -/

section VDeriv

open intervalIntegral

variable {γ σ ℓ u R : ℝ}

lemma J_pos (hlu : ℓ < u) (k : ℕ) (x : ℝ) (hk : k = 0) : 0 < J γ σ ℓ u k x := by
  subst hk
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_J 0 x) ?_ hlu
  intro t _
  simpa using nWeight_pos (γ := γ) (σ := σ) x t

lemma J0_pos (hlu : ℓ < u) (x : ℝ) : 0 < J γ σ ℓ u 0 x := J_pos hlu 0 x rfl

/-- The interval integral of the needle moments, as an integral against
`volume.restrict (Ioc ℓ u)`; this is the form `sq_var_le` is stated in. -/
lemma J_eq_setIntegral (hlu : ℓ ≤ u) (k : ℕ) (x : ℝ) :
    J γ σ ℓ u k x = ∫ t, t ^ k * nWeight γ σ x t ∂(volume.restrict (Ioc ℓ u)) := by
  rw [J, intervalIntegral.integral_of_le hlu]

/-- **Paper Lemma 5.5 applied to the needle.** With `[ℓ,u] ⊆ [-R, R]`,
`J₄J₀ - J₂² ≤ 4R² (J₂J₀ - J₁²)`. -/
theorem J_sq_var_le (hlu : ℓ ≤ u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R) (x : ℝ) :
    J γ σ ℓ u 4 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 2 x) ^ 2
      ≤ 4 * R ^ 2 * (J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2) := by
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc ℓ u)), |t| ≤ R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hR t ht
  have hint : ∀ k : ℕ, Integrable (fun t => t ^ k * nWeight γ σ x t)
      (volume.restrict (Ioc ℓ u)) := fun k =>
    (continuous_pow_mul_nWeight k x).integrableOn_Ioc
  have key := sq_var_le (μ := volume.restrict (Ioc ℓ u)) (M := R)
    (w := nWeight γ σ x) (fun t => (nWeight_pos x t).le) hae hint
  have hw0 : (∫ t, nWeight γ σ x t ∂(volume.restrict (Ioc ℓ u)))
      = J γ σ ℓ u 0 x := by
    rw [J_eq_setIntegral hlu]
    simp
  have hw1 : (∫ t, t * nWeight γ σ x t ∂(volume.restrict (Ioc ℓ u)))
      = J γ σ ℓ u 1 x := by
    rw [J_eq_setIntegral hlu]
    simp
  rw [hw0, hw1, ← J_eq_setIntegral hlu 2, ← J_eq_setIntegral hlu 4] at key
  exact key

/-- The paper's `v(x)` (`vol3_journal.tex:1193`): the second moment of the needle
distribution at parameter `x`. -/
noncomputable def v (γ σ ℓ u : ℝ) (x : ℝ) : ℝ := J γ σ ℓ u 2 x / J γ σ ℓ u 0 x

/-- Differentiating `v` through the quotient rule, using `hasDerivAt_J` on numerator and
denominator. -/
theorem hasDerivAt_v (hσ : σ ≠ 0) (hlu : ℓ < u) (x : ℝ) :
    HasDerivAt (v γ σ ℓ u)
      ((1 / (2 * σ ^ 2)) *
        ((J γ σ ℓ u 2 x) ^ 2 - J γ σ ℓ u 0 x * J γ σ ℓ u 4 x) / (J γ σ ℓ u 0 x) ^ 2) x := by
  have h0 := hasDerivAt_J (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ 0 x
  have h2 := hasDerivAt_J (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ 2 x
  norm_num at h0 h2
  have hne : J γ σ ℓ u 0 x ≠ 0 := ne_of_gt (J0_pos hlu x)
  have hq : HasDerivAt (v γ σ ℓ u)
      ((-((σ ^ 2)⁻¹ * (1 / 2) * J γ σ ℓ u 4 x) * J γ σ ℓ u 0 x
        - J γ σ ℓ u 2 x * -((σ ^ 2)⁻¹ * (1 / 2) * J γ σ ℓ u 2 x))
        / (J γ σ ℓ u 0 x) ^ 2) x :=
    h2.div h0 hne
  refine hq.congr_deriv ?_
  have hσ2 : (2 : ℝ) * σ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The Brascamp–Lieb input (paper Theorem 4.1, `vol3_journal.tex:1407`, from [BL76]),
specialized to the needle: the distribution with density `∝ s(x, ·)` on `[ℓ,u]` — a
Gaussian of variance `σ²/x` restricted to an interval — has variance at most `σ²/x`.

Written unnormalized: `J₂J₀ - J₁² ≤ (σ²/x) J₀²`.

Kept as a named predicate because it is exactly the form the paper cites; it is **not** an
assumption of this development — `brascampLieb` proves it. -/
def BrascampLieb (γ σ ℓ u : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    J γ σ ℓ u 2 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 1 x) ^ 2 ≤ (σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2

/-- **The needle form of Brascamp–Lieb, proved.** The paper cites [BL76] for this; in one
dimension it follows from a single integration by parts (`J_var_le`), so it costs no
assumption here. This is what turns paper Theorem 4.1 from a cited input into a theorem of
the development. -/
theorem brascampLieb (hσ : σ ≠ 0) (hlu : ℓ ≤ u) : BrascampLieb γ σ ℓ u :=
  fun _ hx => J_var_le hσ hlu hx

/-- **Paper Lemma 5.6 (`vol3_journal.tex:1190`).** `v'(x) ≥ -2R²/x` for `x > 0`, when the
needle lives in `[-R, R]`. -/
theorem v_deriv_ge (hσ : 0 < σ) (hlu : ℓ < u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R)
    {x : ℝ} (hx : 0 < x) :
    -(2 * R ^ 2 / x) ≤ deriv (v γ σ ℓ u) x := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hJ0 : 0 < J γ σ ℓ u 0 x := J0_pos hlu x
  have hd := hasDerivAt_v (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ' hlu x
  rw [hd.deriv]
  -- `J₄J₀ - J₂² ≤ 4R² (J₂J₀ - J₁²) ≤ 4R² σ²/x · J₀²`
  have h1 := J_sq_var_le (γ := γ) (σ := σ) hlu.le hR x
  have h2 := brascampLieb (γ := γ) hσ' hlu.le x hx
  have hR2 : (0:ℝ) ≤ 4 * R ^ 2 := by positivity
  have h3 : J γ σ ℓ u 4 x * J γ σ ℓ u 0 x - (J γ σ ℓ u 2 x) ^ 2
      ≤ 4 * R ^ 2 * ((σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hR2)
  -- clear the (positive) denominator `J₀²` and compare numerators
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (J γ σ ℓ u 0 x) ^ 2)]
  have hdiv : 4 * R ^ 2 * ((σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2)
      = (4 * R ^ 2 * σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2 := by
    field_simp
  rw [hdiv] at h3
  have hstep : -(4 * R ^ 2 * σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2
      ≤ (J γ σ ℓ u 2 x) ^ 2 - J γ σ ℓ u 0 x * J γ σ ℓ u 4 x := by nlinarith [h3]
  calc -(2 * R ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2
      = 1 / (2 * σ ^ 2) * (-(4 * R ^ 2 * σ ^ 2 / x) * (J γ σ ℓ u 0 x) ^ 2) := by
        field_simp
        ring
    _ ≤ 1 / (2 * σ ^ 2) * ((J γ σ ℓ u 2 x) ^ 2 - J γ σ ℓ u 0 x * J γ σ ℓ u 4 x) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)

end VDeriv

/-! ## §5.1.5 Paper Claim 5.9 and Lemma 5.7: `h(α) ≤ exp(2R²α²/σ²)`

The exponential-needle ratio

  `h(α) = (∫_ℓ^u s(1+α,t) dt)(∫_ℓ^u s(1-α,t) dt) / (∫_ℓ^u s(1,t) dt)²`

satisfies `h'(α)/h(α) ≤ 4R²α/σ²` and hence `h(α) ≤ exp(2R²α²/σ²)` for `α ≤ 1/2`.

Two deviations from the paper's write-up:

* the paper reaches `h'/h ≤ 4R₁²α/σ²` through a displayed integration of `2R₁²/x` that
  antidifferentiates it as `-R₁²/x²` (i.e. as though the integrand were `2R₁²/x³`); the
  correct antiderivative gives `2R₁² log((1+α)/(1-α))`, and `log((1+α)/(1-α)) ≤ 4α` for
  `α ≤ 1/2` recovers the same conclusion. That is the route taken here.
* the paper integrates `h'/h` and `v'` by the fundamental theorem of calculus. Here both
  steps are run as monotonicity arguments (`monotoneOn_of_deriv_nonneg`,
  `antitoneOn_of_deriv_nonpos`), which need no integrability of the derivatives. -/

section ExpBound

variable {γ σ ℓ u R : ℝ}

/-- `log((1+α)/(1-α)) ≤ 4α` for `0 ≤ α ≤ 1/2`, because `(1+α)/(1-α) ≤ 1 + 4α ≤ e^{4α}`.
This replaces the paper's (mis-antidifferentiated) evaluation of `∫ 2R²/x`. -/
theorem log_ratio_le {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    log ((1 + α) / (1 - α)) ≤ 4 * α := by
  have h1 : (0:ℝ) < 1 - α := by linarith
  have h2 : (1 + α) / (1 - α) ≤ 1 + 4 * α := by
    rw [div_le_iff₀ h1]
    nlinarith
  have h3 : (1 : ℝ) + 4 * α ≤ exp (4 * α) := by
    linarith [Real.add_one_le_exp (4 * α)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  linarith

/-- `x ↦ v(x) + 2R² log x` is monotone on `[1/2, 3/2]`, since its derivative is
`v'(x) + 2R²/x ≥ 0` by Lemma 5.6. -/
lemma monotoneOn_v_add_log (hσ : 0 < σ) (hlu : ℓ < u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R) :
    MonotoneOn (fun x => v γ σ ℓ u x + 2 * R ^ 2 * log x) (Icc (1 / 2 : ℝ) (3 / 2)) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hpos : ∀ x ∈ interior (Icc (1 / 2 : ℝ) (3 / 2)), (0:ℝ) < x := by
    rw [interior_Icc]
    intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1.le
  have hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => v γ σ ℓ u x + 2 * R ^ 2 * log x)
      (deriv (v γ σ ℓ u) x + 2 * R ^ 2 / x) x := by
    intro x hx
    have h1 := (hasDerivAt_v (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ' hlu x)
    have h2 := (Real.hasDerivAt_log hx).const_mul (2 * R ^ 2)
    have h3 := h1.add h2
    rw [h1.deriv]
    refine h3.congr_deriv ?_
    field_simp
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      have : (0:ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
      exact ne_of_gt this
    exact ((hd x hx0).differentiableAt).continuousAt.continuousWithinAt
  · intro x hx
    exact ((hd x (ne_of_gt (hpos x hx))).differentiableAt).differentiableWithinAt
  · intro x hx
    have hx0 : (0:ℝ) < x := hpos x hx
    rw [(hd x (ne_of_gt hx0)).deriv]
    have hv := v_deriv_ge (γ := γ) hσ hlu hR hx0
    have hlin : 2 * R ^ 2 / x = -(-(2 * R ^ 2 / x)) := by ring
    linarith [hv]

/-- **The step of paper Claim 5.9.** `v(1-α) - v(1+α) ≤ 2R² log((1+α)/(1-α)) ≤ 8R²α`. -/
theorem v_diff_le (hσ : 0 < σ) (hlu : ℓ < u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    v γ σ ℓ u (1 - α) - v γ σ ℓ u (1 + α) ≤ 8 * R ^ 2 * α := by
  have hm := monotoneOn_v_add_log (γ := γ) hσ hlu hR
  have hmem1 : (1 - α) ∈ Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hmem2 : (1 + α) ∈ Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  have hle := hm hmem1 hmem2 (by linarith)
  -- `v(1-α) + 2R² log(1-α) ≤ v(1+α) + 2R² log(1+α)`
  have hlog : log (1 + α) - log (1 - α) = log ((1 + α) / (1 - α)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hbound := log_ratio_le hα0 hα
  have hR2 : (0:ℝ) ≤ 2 * R ^ 2 := by positivity
  have hmul : 2 * R ^ 2 * (log (1 + α) - log (1 - α)) ≤ 2 * R ^ 2 * (4 * α) := by
    rw [hlog]; exact mul_le_mul_of_nonneg_left hbound hR2
  simp only at hle
  linarith

/-- The paper's `h(α)` (`vol3_journal.tex:1233`). -/
noncomputable def hFun (γ σ ℓ u : ℝ) (α : ℝ) : ℝ :=
  J γ σ ℓ u 0 (1 + α) * J γ σ ℓ u 0 (1 - α) / (J γ σ ℓ u 0 1) ^ 2

lemma hFun_pos (hlu : ℓ < u) (α : ℝ) : 0 < hFun γ σ ℓ u α :=
  div_pos (mul_pos (J0_pos hlu _) (J0_pos hlu _)) (pow_pos (J0_pos hlu _) 2)

lemma hFun_zero (hlu : ℓ < u) : hFun γ σ ℓ u 0 = 1 := by
  have h : J γ σ ℓ u 0 1 ≠ 0 := ne_of_gt (J0_pos hlu 1)
  rw [hFun]
  norm_num
  rw [← pow_two]
  exact div_self (pow_ne_zero 2 h)

/-- The paper's computation of `h'(α)` (`vol3_journal.tex:1258`), in the form
`h'(α) = (1/(2σ²)) h(α) (v(1-α) - v(1+α))`. -/
theorem hasDerivAt_hFun (hσ : σ ≠ 0) (hlu : ℓ < u) (α : ℝ) :
    HasDerivAt (hFun γ σ ℓ u)
      (1 / (2 * σ ^ 2) * hFun γ σ ℓ u α *
        (v γ σ ℓ u (1 - α) - v γ σ ℓ u (1 + α))) α := by
  have hA : HasDerivAt (fun a : ℝ => J γ σ ℓ u 0 (1 + a))
      (-(1 / (2 * σ ^ 2)) * J γ σ ℓ u 2 (1 + α)) α := by
    have h := (hasDerivAt_J (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ 0 (1 + α)).comp α
      ((hasDerivAt_id α).const_add 1)
    norm_num at h ⊢
    exact h
  have hB : HasDerivAt (fun a : ℝ => J γ σ ℓ u 0 (1 - a))
      (1 / (2 * σ ^ 2) * J γ σ ℓ u 2 (1 - α)) α := by
    have h := (hasDerivAt_J (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ 0 (1 - α)).comp α
      ((hasDerivAt_id α).const_sub 1)
    norm_num at h ⊢
    refine h.congr_deriv ?_
    ring
  have hprod : HasDerivAt (hFun γ σ ℓ u)
      ((-(1 / (2 * σ ^ 2)) * J γ σ ℓ u 2 (1 + α) * J γ σ ℓ u 0 (1 - α)
        + J γ σ ℓ u 0 (1 + α) * (1 / (2 * σ ^ 2) * J γ σ ℓ u 2 (1 - α)))
        / (J γ σ ℓ u 0 1) ^ 2) α :=
    (hA.mul hB).div_const ((J γ σ ℓ u 0 1) ^ 2)
  refine hprod.congr_deriv ?_
  have h1 : J γ σ ℓ u 0 (1 + α) ≠ 0 := ne_of_gt (J0_pos hlu _)
  have h2 : J γ σ ℓ u 0 (1 - α) ≠ 0 := ne_of_gt (J0_pos hlu _)
  have h3 : J γ σ ℓ u 0 1 ≠ 0 := ne_of_gt (J0_pos hlu _)
  have hσ2 : (2:ℝ) * σ ^ 2 ≠ 0 := by positivity
  simp only [hFun, v]
  field_simp
  ring

/-- **Paper Claim 5.9 (`vol3_journal.tex:1238`).** `h'(α) ≤ 4R²α h(α)/σ²` for `α ≤ 1/2`. -/
theorem hFun_deriv_le (hσ : 0 < σ) (hlu : ℓ < u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    deriv (hFun γ σ ℓ u) α ≤ 4 * R ^ 2 * α * hFun γ σ ℓ u α / σ ^ 2 := by
  rw [(hasDerivAt_hFun (γ := γ) (ne_of_gt hσ) hlu α).deriv]
  have hv := v_diff_le (γ := γ) hσ hlu hR hα0 hα
  have hpos : 0 < hFun γ σ ℓ u α := hFun_pos hlu α
  have hc : (0:ℝ) < 1 / (2 * σ ^ 2) * hFun γ σ ℓ u α := by positivity
  calc 1 / (2 * σ ^ 2) * hFun γ σ ℓ u α * (v γ σ ℓ u (1 - α) - v γ σ ℓ u (1 + α))
      ≤ 1 / (2 * σ ^ 2) * hFun γ σ ℓ u α * (8 * R ^ 2 * α) :=
        mul_le_mul_of_nonneg_left hv hc.le
    _ = 4 * R ^ 2 * α * hFun γ σ ℓ u α / σ ^ 2 := by field_simp; ring

/-- **Paper Lemma 5.7 (`vol3_journal.tex:1218`).** For `0 ≤ α ≤ 1/2`,

  `h(α) ≤ exp(2R²α²/σ²)`.

Proved by showing `α ↦ log h(α) - 2R²α²/σ²` is antitone on `[0, 1/2]` and vanishes at
`0`. -/
theorem hFun_le_exp (hσ : 0 < σ) (hlu : ℓ < u) (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    hFun γ σ ℓ u α ≤ exp (2 * R ^ 2 * α ^ 2 / σ ^ 2) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  set φ : ℝ → ℝ := fun a => log (hFun γ σ ℓ u a) - 2 * R ^ 2 * a ^ 2 / σ ^ 2 with hφ
  have hdφ : ∀ a : ℝ, HasDerivAt φ
      (deriv (hFun γ σ ℓ u) a / hFun γ σ ℓ u a - 4 * R ^ 2 * a / σ ^ 2) a := by
    intro a
    have h1 := hasDerivAt_hFun (γ := γ) (σ := σ) (ℓ := ℓ) (u := u) hσ' hlu a
    have hlog := h1.log (ne_of_gt (hFun_pos hlu a))
    have hquad : HasDerivAt (fun a : ℝ => 2 * R ^ 2 * a ^ 2 / σ ^ 2)
        (4 * R ^ 2 * a / σ ^ 2) a := by
      refine (((hasDerivAt_pow 2 a).const_mul (2 * R ^ 2)).div_const (σ ^ 2)).congr_deriv ?_
      push_cast
      field_simp
      ring
    have hsub := hlog.sub hquad
    rw [h1.deriv]
    exact hsub
  -- `φ` is antitone on `[0, 1/2]`
  have hanti : AntitoneOn φ (Icc (0:ℝ) (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun a _ => ((hdφ a).differentiableAt).continuousAt.continuousWithinAt)
      (fun a _ => ((hdφ a).differentiableAt).differentiableWithinAt) ?_
    intro a ha
    rw [interior_Icc] at ha
    rw [(hdφ a).deriv]
    have hle := hFun_deriv_le (γ := γ) hσ hlu hR ha.1.le ha.2.le
    have hpos : 0 < hFun γ σ ℓ u a := hFun_pos hlu a
    have hdiv : deriv (hFun γ σ ℓ u) a / hFun γ σ ℓ u a ≤ 4 * R ^ 2 * a / σ ^ 2 := by
      rw [div_le_iff₀ hpos]
      refine hle.trans (le_of_eq ?_)
      field_simp
    linarith
  have hzero : φ 0 = 0 := by
    rw [hφ]
    simp [hFun_zero hlu]
  have hle : φ α ≤ 0 := by
    have h := hanti (left_mem_Icc.mpr (by norm_num)) ⟨hα0, hα⟩ hα0
    rw [hzero] at h
    exact h
  -- unwind the logarithm
  have hpos : 0 < hFun γ σ ℓ u α := hFun_pos hlu α
  have hlog : log (hFun γ σ ℓ u α) ≤ 2 * R ^ 2 * α ^ 2 / σ ^ 2 := by
    rw [hφ] at hle; simp only at hle; linarith
  exact (Real.log_le_iff_le_exp hpos).mp hlog

end ExpBound

/-! ## §5.1.6 The localization reduction

Paper Lemma 5.4 (`lem:exp-needle-simplify`, `vol3_journal.tex:1134`) and the headline
Lemma 3.2 (`lem:variance-bound`, `vol3_journal.tex:360`).

The `n`-dimensional inequality `G(σ²/(1+α)) G(σ²/(1-α)) ≤ c · G(σ²)²` is reduced by the
Localization Lemma to the same inequality along one-dimensional *exponential needles*. The
reduction has a concrete geometric content, which is what this section proves:

* every needle can be parameterized as `t ↦ p + t·w` with `p ⟂ w`, `‖w‖ = 1`
  (`exists_normalized_needle`), so that `‖p + t·w‖² = ‖p‖² + t²` (Pythagoras);
* consequently the needle integral factors as `e^{-‖p‖²/(2s)}` times a *one-dimensional*
  needle integral with no offset (`needleInt_factor`);
* and in the ratio the offset cancels exactly (`needle_ratio_eq`).

What remains is exactly Lemma 5.7 (`hFun_le_exp`), so every needle obeys the bound
`exp(2R²α²/σ²)` (`needle_variance_bound`).

The Localization Lemma itself (paper Theorem 5.3, `vol3_journal.tex:1106`, from [KLS95])
is **not** formalized: it is carried as the explicit hypothesis `LocalizationHypothesis`,
stated in the exact form the reduction consumes. -/

section Localization

open intervalIntegral

variable {n : ℕ} {f : EuclSpace n → ℝ}

/-- The Gaussian needle integral: the integral of `x ↦ e^{-‖x‖²/(2s)}` along the segment
`{p + t·w : t ∈ [ℓ,u]}`, against the needle's exponential weight `e^{γt}`
(`vol3_journal.tex:1101`). -/
noncomputable def needleInt (γ : ℝ) (p w : EuclSpace n) (ℓ u s : ℝ) : ℝ :=
  ∫ t in ℓ..u, exp (γ * t) * exp (-(‖p + t • w‖ ^ 2) / (2 * s))

/-- **Pythagoras.** If `p ⟂ w` and `‖w‖ = 1` then `‖p + t·w‖² = ‖p‖² + t²`: this is what
makes the offset `z = ‖p‖` factor out of the needle integral. -/
lemma norm_add_smul_sq {p w : EuclSpace n} (hpw : inner ℝ p w = 0) (hw : ‖w‖ = 1)
    (t : ℝ) : ‖p + t • w‖ ^ 2 = ‖p‖ ^ 2 + t ^ 2 := by
  rw [@norm_add_sq_real]
  rw [real_inner_smul_right, hpw, norm_smul, hw]
  simp [sq_abs]

/-- Every nondegenerate segment can be written as `t ↦ p + t·w` with `p ⟂ w` and
`‖w‖ = 1`; the paper's "`z` is the closest distance from the origin to the extension of
`I`" (`vol3_journal.tex:1155`). -/
theorem exists_normalized_needle (a b : EuclSpace n) (hab : a ≠ b) :
    ∃ (p w : EuclSpace n) (c : ℝ), inner ℝ p w = 0 ∧ ‖w‖ = 1 ∧
      ∀ τ : ℝ, a + τ • (b - a) = p + (c + τ * ‖b - a‖) • w := by
  have hne : ‖b - a‖ ≠ 0 := by
    simpa [sub_eq_zero] using fun h => hab (by rw [h])
  refine ⟨a - (inner ℝ a (‖b - a‖⁻¹ • (b - a))) • (‖b - a‖⁻¹ • (b - a)),
    ‖b - a‖⁻¹ • (b - a), (inner ℝ a (‖b - a‖⁻¹ • (b - a))), ?_, ?_, ?_⟩
  · set w : EuclSpace n := ‖b - a‖⁻¹ • (b - a) with hwdef
    have hw1 : ‖w‖ = 1 := by
      rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw1]
    ring
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
  · intro τ
    set w : EuclSpace n := ‖b - a‖⁻¹ • (b - a) with hwdef
    have hbw : (‖b - a‖ : ℝ) • w = b - a := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ hne, one_smul]
    calc a + τ • (b - a) = a + τ • ((‖b - a‖ : ℝ) • w) := by rw [hbw]
      _ = a - (inner ℝ a w) • w + ((inner ℝ a w) + τ * ‖b - a‖) • w := by module

/-- **The offset factors out.** `∫ e^{γt} e^{-‖p+t·w‖²/(2s)} dt = e^{-‖p‖²/(2s)} ∫ e^{γt}
e^{-t²/(2s)} dt` (`vol3_journal.tex:1157`). -/
theorem needleInt_factor {γ : ℝ} {p w : EuclSpace n} (hpw : inner ℝ p w = 0)
    (hw : ‖w‖ = 1) (ℓ u s : ℝ) (hs : s ≠ 0) :
    needleInt γ p w ℓ u s
      = exp (-(‖p‖ ^ 2) / (2 * s))
        * ∫ t in ℓ..u, exp (γ * t) * exp (-(t ^ 2) / (2 * s)) := by
  rw [needleInt, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [norm_add_smul_sq hpw hw t]
  have hsplit : -(‖p‖ ^ 2 + t ^ 2) / (2 * s)
      = -(‖p‖ ^ 2) / (2 * s) + -(t ^ 2) / (2 * s) := by
    field_simp
    ring
  rw [hsplit, exp_add]
  ring

/-- The offset-free needle integral is the `0`-th needle moment, at parameter `x` when
`s = σ²/x`. -/
lemma integral_eq_J {γ σ x : ℝ} (hσ : σ ≠ 0) (hx : x ≠ 0) (ℓ u : ℝ) :
    (∫ t in ℓ..u, exp (γ * t) * exp (-(t ^ 2) / (2 * (σ ^ 2 / x))))
      = J γ σ ℓ u 0 x := by
  rw [J]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  simp only [nWeight, pow_zero, one_mul]
  congr 2
  field_simp

/-- **Paper Lemma 5.4 (`vol3_journal.tex:1134`), the computation.** For a needle in
normalized position, the ratio the localization argument must bound equals the purely
one-dimensional `hFun` — the offset `z = ‖p‖` cancels because `(1+α) + (1-α) = 2`. -/
theorem needle_ratio_eq {γ σ α : ℝ} {p w : EuclSpace n} (hpw : inner ℝ p w = 0)
    (hw : ‖w‖ = 1) {ℓ u : ℝ} (hσ : σ ≠ 0)
    (hα1 : 1 + α ≠ 0) (hα2 : 1 - α ≠ 0) :
    needleInt γ p w ℓ u (σ ^ 2 / (1 + α)) * needleInt γ p w ℓ u (σ ^ 2 / (1 - α))
      / (needleInt γ p w ℓ u (σ ^ 2)) ^ 2 = hFun γ σ ℓ u α := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  -- rewrite each needle integral as `e^{-z²x/(2σ²)} · J₀(x)`
  have hrw : ∀ x : ℝ, x ≠ 0 → needleInt γ p w ℓ u (σ ^ 2 / x)
      = exp (-(‖p‖ ^ 2) / (2 * (σ ^ 2 / x))) * J γ σ ℓ u 0 x := by
    intro x hx
    rw [needleInt_factor hpw hw ℓ u _ (div_ne_zero hσ2 hx), integral_eq_J hσ hx]
  have e1 := hrw (1 + α) hα1
  have e2 := hrw (1 - α) hα2
  have e3 : needleInt γ p w ℓ u (σ ^ 2)
      = exp (-(‖p‖ ^ 2) / (2 * σ ^ 2)) * J γ σ ℓ u 0 1 := by
    simpa using hrw 1 one_ne_zero
  set E1 : ℝ := exp (-(‖p‖ ^ 2) / (2 * (σ ^ 2 / (1 + α)))) with hE1
  set E2 : ℝ := exp (-(‖p‖ ^ 2) / (2 * (σ ^ 2 / (1 - α)))) with hE2
  set E3 : ℝ := exp (-(‖p‖ ^ 2) / (2 * σ ^ 2)) with hE3
  -- the three exponential prefactors cancel: `(1+α) + (1-α) = 2`
  have hz : E1 * E2 = E3 ^ 2 := by
    have hsq : E3 ^ 2
        = exp (-(‖p‖ ^ 2) / (2 * σ ^ 2) + -(‖p‖ ^ 2) / (2 * σ ^ 2)) := by
      rw [exp_add, hE3]; ring
    rw [hsq, hE1, hE2, ← exp_add]
    congr 1
    field_simp
    ring
  have hE3ne : E3 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (by rw [hE3]; exact exp_pos _))
  rw [e1, e2, e3, hFun]
  calc E1 * J γ σ ℓ u 0 (1 + α) * (E2 * J γ σ ℓ u 0 (1 - α)) / (E3 * J γ σ ℓ u 0 1) ^ 2
      = E1 * E2 * (J γ σ ℓ u 0 (1 + α) * J γ σ ℓ u 0 (1 - α))
          / (E3 ^ 2 * (J γ σ ℓ u 0 1) ^ 2) := by rw [mul_pow]; ring_nf
    _ = E3 ^ 2 * (J γ σ ℓ u 0 (1 + α) * J γ σ ℓ u 0 (1 - α))
          / (E3 ^ 2 * (J γ σ ℓ u 0 1) ^ 2) := by rw [hz]
    _ = J γ σ ℓ u 0 (1 + α) * J γ σ ℓ u 0 (1 - α) / (J γ σ ℓ u 0 1) ^ 2 :=
        mul_div_mul_left _ _ hE3ne

/-- **Every needle obeys the variance bound.** Paper Lemma 5.4 composed with Lemma 5.7. -/
theorem needle_variance_bound {γ σ α R : ℝ} {p w : EuclSpace n} (hpw : inner ℝ p w = 0)
    (hw : ‖w‖ = 1) {ℓ u : ℝ} (hlu : ℓ < u) (hσ : 0 < σ)
    (hR : ∀ t ∈ Ioc ℓ u, |t| ≤ R) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    needleInt γ p w ℓ u (σ ^ 2 / (1 + α)) * needleInt γ p w ℓ u (σ ^ 2 / (1 - α))
      ≤ exp (2 * R ^ 2 * α ^ 2 / σ ^ 2) * (needleInt γ p w ℓ u (σ ^ 2)) ^ 2 := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hα1 : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have hα2 : (1:ℝ) - α ≠ 0 := ne_of_gt (by linarith)
  have hpos : 0 < needleInt γ p w ℓ u (σ ^ 2) := by
    rw [needleInt_factor hpw hw ℓ u _ (pow_ne_zero 2 hσ')]
    refine mul_pos (exp_pos _) ?_
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t _ => by positivity) hlu
    exact (Continuous.intervalIntegrable (by fun_prop) ℓ u)
  have heq := needle_ratio_eq (γ := γ) (ℓ := ℓ) (u := u) hpw hw hσ' hα1 hα2
  have hle := hFun_le_exp (γ := γ) hσ hlu hR hα0 hα
  rw [← heq, div_le_iff₀ (by positivity)] at hle
  linarith

/-- **The Localization Lemma, as an assumption** (paper Theorem 5.3,
`vol3_journal.tex:1106`, from [KLS95]).

**This predicate is never proved in this file.** It is stated only so that the theorems
that need it (`variance_bound`, `lc_variance_bound`) can carry it as an explicit,
clearly-named hypothesis rather than smuggling it in as an axiom. A user of those theorems
must supply a proof of it.

Content: if the four-function inequality holds along every exponential needle that meets
the support of `f`, it holds for `f` itself. Needles are quantified in the normalized
position `t ↦ p + t·w` supplied by `exists_normalized_needle`, and restricted to `[-R, R]`
because `f` vanishes outside `R·Bₙ` (`vol3_journal.tex:1155`). -/
def LocalizationHypothesis (f : EuclSpace n → ℝ) (σ α c R : ℝ) : Prop :=
  (∀ (γ : ℝ) (p w : EuclSpace n) (ℓ u : ℝ), inner ℝ p w = 0 → ‖w‖ = 1 → ℓ < u →
      (∀ t ∈ Ioc ℓ u, |t| ≤ R) →
      needleInt γ p w ℓ u (σ ^ 2 / (1 + α)) * needleInt γ p w ℓ u (σ ^ 2 / (1 - α))
        ≤ c * (needleInt γ p w ℓ u (σ ^ 2)) ^ 2) →
    G f (σ ^ 2 / (1 + α)) * G f (σ ^ 2 / (1 - α)) ≤ c * (G f (σ ^ 2)) ^ 2

/-- **Paper Lemma 3.2 (`vol3_journal.tex:360`) / Lemma 5.8 (`vol3_journal.tex:1304`).**
For a logconcave `f` supported in `R·Bₙ` and `α ≤ 1/2`,

  `G(σ²/(1+α)) · G(σ²/(1-α)) ≤ exp(2R²α²/σ²) · G(σ²)²`,

**given** the Localization Lemma as the hypothesis `hloc`. The needle side of the argument
(everything the hypothesis is applied to) is proved. -/
theorem variance_bound {σ α R : ℝ} (hσ : 0 < σ) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hloc : LocalizationHypothesis f σ α (exp (2 * R ^ 2 * α ^ 2 / σ ^ 2)) R) :
    G f (σ ^ 2 / (1 + α)) * G f (σ ^ 2 / (1 - α))
      ≤ exp (2 * R ^ 2 * α ^ 2 / σ ^ 2) * (G f (σ ^ 2)) ^ 2 :=
  hloc fun _ _ _ _ _ hpw hw hlu hR =>
    needle_variance_bound hpw hw hlu hσ hR hα0 hα

end Localization

/-! ## §5.1.7 The headline variance bounds

* `lc_variance_bound` — paper Lemma 5.8 (`vol3_journal.tex:1304`): for a logconcave `f`
  supported in `R·Bₙ`, the ratio estimator has `E(Y²)/E(Y)² ≤ exp(2R²α²/σ²)` for
  `α ≤ 1/2` (given the Localization Lemma as an explicit hypothesis).
* `fast_var_bound` — paper Claim 5.11 (`vol3_journal.tex:1447`): at the *accelerated*
  cooling rate `α = σ²/(2C²n)` of a body inside `C√n·Bₙ` (so `R = C√n`), the bound is
  `≤ 1 + σ²/(C²n)`, which is what makes `O(C²n/σ²)` phases per doubling of `σ²`
  affordable and yields the `O*(n³)` complexity.

The numeric heart of the second is `exp_le_one_add_two_mul`: `e^α ≤ 1 + 2α` for
`0 ≤ α ≤ 1/2`. -/

section Main

variable {n : ℕ} {f : EuclSpace n → ℝ}

/-- `e^α ≤ 1 + 2α` for `0 ≤ α ≤ 1/2`, via `e^α ≤ 1/(1-α) ≤ 1 + 2α`. -/
theorem exp_le_one_add_two_mul {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) :
    exp α ≤ 1 + 2 * α := by
  have h1 : (0:ℝ) < 1 - α := by linarith
  have hinv : exp α ≤ (1 - α)⁻¹ := by
    rw [le_inv_comm₀ (exp_pos α) h1, ← exp_neg]
    linarith [Real.add_one_le_exp (-α)]
  have h2 : (1 - α)⁻¹ ≤ 1 + 2 * α := by
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith
  linarith

/-- **Paper Lemma 5.8 (`vol3_journal.tex:1304`).** For a logconcave `f` supported in
`R·Bₙ`, with `X` drawn from the density `∝ g(·, σ²/(1+α))` and
`Y = g(X, σ²)/g(X, σ²/(1+α))`,

  `E(Y²)/E(Y)² ≤ exp(2R²α²/σ²)`.

The `E(Y²)/E(Y)²` on the left is the explicit integral ratio of `variance_ratio`; the one
cited result that is not proved here, the Localization Lemma, enters as the explicit
hypothesis `hloc`. -/
theorem lc_variance_bound {σ α R : ℝ} (hσ : 0 < σ) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2)
    (hGa : G f (σ ^ 2 / (1 + α)) ≠ 0) (hGb : G f (σ ^ 2) ≠ 0)
    (hloc : LocalizationHypothesis f σ α (exp (2 * R ^ 2 * α ^ 2 / σ ^ 2)) R) :
    (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α))))
      / (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
          * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2
      ≤ exp (2 * R ^ 2 * α ^ 2 / σ ^ 2) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hα1 : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have hα2 : (1:ℝ) - α ≠ 0 := ne_of_gt (by linarith)
  rw [variance_ratio hσ' hα1 hα2 hGa hGb]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (G f (σ ^ 2)) ^ 2)]
  exact variance_bound hσ hα0 hα hloc

/-- **Paper Claim 5.11 (`vol3_journal.tex:1447`).** At the accelerated cooling rate
`α = σ²/(2C²n)` for a body inside `C√n·Bₙ` (so the needle radius is `R = C√n`), the
variance bound `exp(2R²α²/σ²)` is at most `1 + σ²/(C²n) = 1 + 2α`.

This is the inequality that lets the second phase of the algorithm cool `C²n/σ²` times
faster than the first while keeping `O*(1)` samples per phase. -/
theorem fast_var_bound {σ C : ℝ} {α : ℝ} (hσ : 0 < σ) (hC : 0 < C) (hn : 0 < (n : ℝ))
    (hα : α = σ ^ 2 / (2 * C ^ 2 * n)) (hα2 : α ≤ 1 / 2) :
    exp (2 * (C * √n) ^ 2 * α ^ 2 / σ ^ 2) ≤ 1 + σ ^ 2 / (C ^ 2 * n) := by
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hsq : (C * √n) ^ 2 = C ^ 2 * n := by
    rw [mul_pow, Real.sq_sqrt hn.le]
  have hkey : 2 * (C * √n) ^ 2 * α ^ 2 / σ ^ 2 = α := by
    rw [hsq, hα]
    field_simp
  rw [hkey]
  have h2α : 2 * α = σ ^ 2 / (C ^ 2 * n) := by
    rw [hα]; field_simp
  rw [← h2α]
  exact exp_le_one_add_two_mul hα0 hα2

end Main

/-! ## §5.1.8 The fixed cooling rate — paper Lemma 5.10

Under the *fixed* cooling rate `σᵢ₊₁² = σᵢ²(1 + 1/n)` used in the first half of the
algorithm, where `σ ≤ 1` and the body may be arbitrarily large relative to `σ`:

  `E(Y²)/E(Y)² ≤ 1 + 2/n`   for `n ≥ 3`.

This is a *different* argument from the accelerated bound: it has no `K ⊆ C√n·Bₙ`
hypothesis, so the needle/Brascamp–Lieb route is unavailable. Instead it uses the
logconcavity of `a ↦ aⁿ ∫_K f(ax) dx` (paper Lemma 5.9, cited from [LV2]), which is a
Prékopa–Leindler consequence. Mathlib has neither Prékopa–Leindler nor Brunn–Minkowski, so
Lemma 5.9 enters as the explicit hypothesis `ZLogconcaveHypothesis`, stated in the midpoint
form the proof consumes. Everything downstream of it is proved here.

The numeric heart is `inv_one_sub_inv_sq_pow_le`: `(1 - 1/n²)^{-(n+1)} ≤ 1 + 2/n` for
`n ≥ 3`, which the paper reaches through `≤ e^{1/(n-1)} ≤ 1 + 2/n`. The chain
`e^{1/(n-1)} ≤ 1+2/n` is tight at `n = 3` (`e^{1/2} = 1.6487` against `1.6667`), so the
formalization splits: `n = 3` is a direct rational computation, and `n ≥ 4` goes through
`e^t ≤ (1-t)⁻¹`. -/

section FixedRate

variable {n : ℕ} {f : EuclSpace n → ℝ}

/-- `(1 - 1/n²)^{-(n+1)} ≤ 1 + 2/n` for `n ≥ 3` — the paper's chain at
`vol3_journal.tex:1376`, with the `n = 3` case computed rather than estimated. -/
theorem inv_one_sub_inv_sq_pow_le {n : ℕ} (hn : 3 ≤ n) :
    ((1 : ℝ) - (1 / (n : ℝ)) ^ 2)⁻¹ ^ (n + 1) ≤ 1 + 2 / (n : ℝ) := by
  rcases eq_or_lt_of_le hn with h3 | h4
  · -- `n = 3`: `(9/8)⁴ = 6561/4096 ≤ 5/3`
    subst h3
    norm_num
  · -- `n ≥ 4`
    have hn4 : 4 ≤ n := h4
    have hN : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hN2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hNsq : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    -- `(1 - 1/n²)⁻¹ = 1 + 1/(n²-1)`
    have hu : ((1 : ℝ) - (1 / (n : ℝ)) ^ 2)⁻¹ = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
      have h1 : (1 : ℝ) - (1 / (n : ℝ)) ^ 2 = ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2 := by
        field_simp
      rw [h1, inv_div]
      field_simp
      ring
    set u : ℝ := 1 / ((n : ℝ) ^ 2 - 1) with hudef
    have hu0 : 0 < u := by rw [hudef]; positivity
    -- `(1+u)^{n+1} ≤ e^{(n+1)u} = e^{1/(n-1)}`
    have hpow : (1 + u) ^ (n + 1) ≤ exp (((n : ℝ) + 1) * u) := by
      have hstep : (1 + u) ^ (n + 1) ≤ (exp u) ^ (n + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) (n + 1)
      refine hstep.trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexp : ((n : ℝ) + 1) * u = 1 / ((n : ℝ) - 1) := by
      rw [hudef]
      field_simp
      ring
    -- `e^t ≤ (1-t)⁻¹` for `t = 1/(n-1) ≤ 1/3`
    have ht : 1 / ((n : ℝ) - 1) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hN1 (by norm_num)]
      linarith
    have hlt : (0 : ℝ) < 1 - 1 / ((n : ℝ) - 1) := by linarith
    have hle : exp (1 / ((n : ℝ) - 1)) ≤ (1 - 1 / ((n : ℝ) - 1))⁻¹ := by
      rw [le_inv_comm₀ (exp_pos _) hlt, ← exp_neg]
      linarith [Real.add_one_le_exp (-(1 / ((n : ℝ) - 1)))]
    -- `(1 - 1/(n-1))⁻¹ = (n-1)/(n-2) ≤ 1 + 2/n` exactly when `n ≥ 4`
    have hfrac : (1 - 1 / ((n : ℝ) - 1))⁻¹ = ((n : ℝ) - 1) / ((n : ℝ) - 2) := by
      have h : (1 : ℝ) - 1 / ((n : ℝ) - 1) = ((n : ℝ) - 2) / ((n : ℝ) - 1) := by
        field_simp
        ring
      rw [h, inv_div]
    have hlast : ((n : ℝ) - 1) / ((n : ℝ) - 2) ≤ 1 + 2 / (n : ℝ) := by
      rw [div_le_iff₀ hN2]
      have hrw : (1 + 2 / (n : ℝ)) * ((n : ℝ) - 2)
          = ((n : ℝ) + 2) * ((n : ℝ) - 2) / (n : ℝ) := by
        field_simp
      rw [hrw, le_div_iff₀ hN0]
      nlinarith
    rw [hu]
    calc (1 + u) ^ (n + 1) ≤ exp (((n : ℝ) + 1) * u) := hpow
      _ = exp (1 / ((n : ℝ) - 1)) := by rw [hexp]
      _ ≤ (1 - 1 / ((n : ℝ) - 1))⁻¹ := hle
      _ = ((n : ℝ) - 1) / ((n : ℝ) - 2) := hfrac
      _ ≤ 1 + 2 / (n : ℝ) := hlast

/-- The paper's `z(a) = a^{n+1} ∫_K e^{-a‖x‖²/2} dx` (`vol3_journal.tex:1365`), written
against `G`: `∫_K e^{-a‖x‖²/2} dx = G f a⁻¹`. -/
noncomputable def zFun (f : EuclSpace n → ℝ) (a : ℝ) : ℝ := a ^ (n + 1) * G f a⁻¹

/-- **Paper Lemma 5.9 (`vol3_journal.tex:1342`, from [LV2]), as an assumption:** `aⁿ ∫_K
f(ax) dx` is a logconcave function of `a`, hence so is `z`. Stated in the midpoint form the
proof of Lemma 5.10 consumes, which is all that logconcavity is used for.

**This predicate is never proved in this file**, and is carried as an explicit,
clearly-named hypothesis of `G_mul_G_le_of_zLogconcave`, `fixed_var_bound` and
`fixed_var_bound_ratio`.

**⚠ It is FALSE for general logconcave `f`, so do not try to prove it in that
generality.** See `Arlib/Convexity/GaussianCooling/ZLogconcave.lean`.
Counterexample: `n = 1`, `f x = e^{−x}` (logconcave, positive, with `G f s` finite
for every `s > 0`). Then `z(A) = √(2π)·A^{3/2}·e^{1/(2A)}`, whose log is strictly
*convex* for `A < 2/3`; at `a = 1/10, b = 1/5` the inequality fails by a factor
≈ 1.93 (checked both in closed form and by quadrature).

The obstruction is structural, not a missing lemma: the proof route needs
`(A, y) ↦ f(y/A)` jointly logconcave, and a 0-homogeneous convex function is
constant on its domain. So up to a constant factor, **indicators of convex sets are
exactly the `f` for which this holds**.

What *is* available: `Arlib.GaussianCooling.zLogconcaveHypothesis_indicator` proves
it for `f = 1_K` with `K` convex and measurable (and `…_indicator_const` for
`c · 1_K`), which is the instance a volume oracle for a convex body needs — giving
the unconditional `fixed_var_bound_indicator` / `fixed_var_bound_ratio_indicator`.
The earlier remark here that this is "a Prékopa–Leindler consequence" pending
Mathlib support was doubly wrong: this repo now proves Prékopa–Leindler and
Brunn–Minkowski (`Arlib/Convexity/{PrekopaLeindler,PrekopaLeindlerN,BrunnSharp}.lean`),
and the general statement is false regardless. -/
def ZLogconcaveHypothesis (f : EuclSpace n → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → zFun f a * zFun f b ≤ (zFun f ((a + b) / 2)) ^ 2

/-- **The transport step (`vol3_journal.tex:1367`).** Logconcavity of `z` at the midpoint
of `(1±α)/σ²` gives

  `G(σ²/(1-α)) · G(σ²/(1+α)) ≤ (1-α²)^{-(n+1)} · G(σ²)²`. -/
theorem G_mul_G_le_of_zLogconcave (hz : ZLogconcaveHypothesis f) {σ α : ℝ} (hσ : 0 < σ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    G f (σ ^ 2 / (1 - α)) * G f (σ ^ 2 / (1 + α))
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) * (G f (σ ^ 2)) ^ 2 := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hm : (0 : ℝ) < 1 - α := by linarith
  have hp : (0 : ℝ) < 1 + α := by linarith
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  set a : ℝ := (1 - α) / σ ^ 2 with hadef
  set b : ℝ := (1 + α) / σ ^ 2 with hbdef
  set P : ℝ := ((1 : ℝ) / σ ^ 2) ^ (n + 1) with hPdef
  have ha : 0 < a := by rw [hadef]; positivity
  have hb : 0 < b := by rw [hbdef]; positivity
  have hP : 0 < P := by rw [hPdef]; positivity
  have hmid : (a + b) / 2 = 1 / σ ^ 2 := by rw [hadef, hbdef]; field_simp; ring
  have hainv : a⁻¹ = σ ^ 2 / (1 - α) := by rw [hadef, inv_div]
  have hbinv : b⁻¹ = σ ^ 2 / (1 + α) := by rw [hbdef, inv_div]
  have hmidinv : ((1 : ℝ) / σ ^ 2)⁻¹ = σ ^ 2 := by rw [one_div, inv_inv]
  have key := hz a b ha hb
  simp only [zFun] at key
  rw [hainv, hbinv, hmid, hmidinv, ← hPdef] at key
  -- `key : a^{n+1} G(σ²/(1-α)) · b^{n+1} G(σ²/(1+α)) ≤ (P · G(σ²))²`
  have hexpand : a ^ (n + 1) * b ^ (n + 1) = ((1 : ℝ) - α ^ 2) ^ (n + 1) * (P * P) := by
    have hab : a * b = ((1 : ℝ) - α ^ 2) * ((1 : ℝ) / σ ^ 2 * ((1 : ℝ) / σ ^ 2)) := by
      rw [hadef, hbdef]; field_simp; ring
    rw [← mul_pow, hab, mul_pow, mul_pow, hPdef]
  have hcoef : (0 : ℝ) < ((1 : ℝ) - α ^ 2) ^ (n + 1) := by positivity
  set Q : ℝ := G f (σ ^ 2 / (1 - α)) * G f (σ ^ 2 / (1 + α)) with hQdef
  -- cancel the common factor `P²`
  have hstep : ((1 : ℝ) - α ^ 2) ^ (n + 1) * Q ≤ (G f (σ ^ 2)) ^ 2 := by
    refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < P * P by positivity)
    calc P * P * (((1 : ℝ) - α ^ 2) ^ (n + 1) * Q)
        = ((1 : ℝ) - α ^ 2) ^ (n + 1) * (P * P) * Q := by ring
      _ = a ^ (n + 1) * b ^ (n + 1) * Q := by rw [← hexpand]
      _ = a ^ (n + 1) * G f (σ ^ 2 / (1 - α)) * (b ^ (n + 1) * G f (σ ^ 2 / (1 + α))) := by
          rw [hQdef]; ring
      _ ≤ (P * G f (σ ^ 2)) ^ 2 := key
      _ = P * P * (G f (σ ^ 2)) ^ 2 := by ring
  rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hcoef, mul_comm]
  exact hstep

/-- **Paper Lemma 5.10 (`vol3_journal.tex:1353`).** Under the fixed cooling rate
`σᵢ₊₁² = σᵢ²(1 + 1/n)` — i.e. `α = 1/n` — and for `n ≥ 3`,

  `G(σ²/(1+α)) · G(σ²/(1-α)) ≤ (1 + 2/n) · G(σ²)²`.

No roundness hypothesis on the body: unlike the accelerated bound, this one comes from
logconcavity of `z`, not from localization. -/
theorem fixed_var_bound (hz : ZLogconcaveHypothesis f) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    G f (σ ^ 2 / (1 + 1 / (n : ℝ))) * G f (σ ^ 2 / (1 - 1 / (n : ℝ)))
      ≤ (1 + 2 / (n : ℝ)) * (G f (σ ^ 2)) ^ 2 := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hα0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hα1 : 1 / (n : ℝ) < 1 := by
    rw [div_lt_one hN0]; linarith
  have hcore := G_mul_G_le_of_zLogconcave hz hσ hα0 hα1
  have hnum := inv_one_sub_inv_sq_pow_le (n := n) hn
  have hGsq : (0 : ℝ) ≤ (G f (σ ^ 2)) ^ 2 := sq_nonneg _
  have hstep : ((1 : ℝ) - (1 / (n : ℝ)) ^ 2)⁻¹ ^ (n + 1) * (G f (σ ^ 2)) ^ 2
      ≤ (1 + 2 / (n : ℝ)) * (G f (σ ^ 2)) ^ 2 :=
    mul_le_mul_of_nonneg_right hnum hGsq
  calc G f (σ ^ 2 / (1 + 1 / (n : ℝ))) * G f (σ ^ 2 / (1 - 1 / (n : ℝ)))
      = G f (σ ^ 2 / (1 - 1 / (n : ℝ))) * G f (σ ^ 2 / (1 + 1 / (n : ℝ))) := by ring
    _ ≤ ((1 : ℝ) - (1 / (n : ℝ)) ^ 2)⁻¹ ^ (n + 1) * (G f (σ ^ 2)) ^ 2 := hcore
    _ ≤ (1 + 2 / (n : ℝ)) * (G f (σ ^ 2)) ^ 2 := hstep

/-- **Lemma 5.10 in estimator form.** `E(Y²)/E(Y)² ≤ 1 + 2/n` for the fixed cooling rate,
matching `lc_variance_bound` for the accelerated rate. -/
theorem fixed_var_bound_ratio (hz : ZLogconcaveHypothesis f) {σ : ℝ} (hσ : 0 < σ)
    (hn : 3 ≤ n)
    (hGa : G f (σ ^ 2 / (1 + 1 / (n : ℝ))) ≠ 0) (hGb : G f (σ ^ 2) ≠ 0) :
    (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + 1 / (n : ℝ))) x) ^ 2
        * (gW f (σ ^ 2 / (1 + 1 / (n : ℝ))) x / G f (σ ^ 2 / (1 + 1 / (n : ℝ)))))
      / (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
          * (gW f (σ ^ 2 / (1 + 1 / (n : ℝ))) x / G f (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2
      ≤ 1 + 2 / (n : ℝ) := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hα1 : (1 : ℝ) + 1 / (n : ℝ) ≠ 0 := by positivity
  have hα2 : (1 : ℝ) - 1 / (n : ℝ) ≠ 0 := by
    have hlt : 1 / (n : ℝ) < 1 := by rw [div_lt_one hN0]; linarith
    intro h; linarith [hlt]
  rw [variance_ratio hσ' hα1 hα2 hGa hGb]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (G f (σ ^ 2)) ^ 2)]
  exact fixed_var_bound hz hσ hn

end FixedRate

end Arlib.GaussianCooling
