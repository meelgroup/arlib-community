/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.ZLogconcave

/-!
# The Cousins–Vempala per-phase variance bound, unconditional for a convex body

`Arlib.Convexity.GaussianCooling.Variance` proves the gaussian-cooling variance chain for a
general weight `f : ℝⁿ → ℝ` carrying `ZLogconcaveHypothesis f` as an explicit hypothesis, and
`Arlib.Convexity.GaussianCooling.ZLogconcave` shows that hypothesis is **false** for general
log-concave `f` but **true** for `f = 1_K` with `K` convex.

This file pushes the specialisation `f := 1_K` all the way to the shape the volume algorithm
consumes, so that no result below carries a `ZLogconcaveHypothesis` binder:

* `Arlib.GaussianCooling.G_indicator_pos` — `0 < G 1_K s` for `s > 0` whenever `K` is
  measurable with positive volume; this discharges the `G … ≠ 0` side conditions of
  `variance_ratio`, `lc_variance_bound` and `fixed_var_bound_ratio`.  No `volume K ≠ ⊤`
  guard is needed: `G 1_K s` is a *real* integral of a gaussian-dominated integrand and is
  finite for every `K` (`integrable_gW_indicator`).
* `Arlib.GaussianCooling.G_mul_G_le_exp_indicator` — for every convex measurable `K`, every
  `σ > 0` and every cooling rate `0 ≤ α < 1`,

    `G 1_K (σ²/(1-α)) · G 1_K (σ²/(1+α)) ≤ exp((n+1)α²/(1-α²)) · G 1_K (σ²)²`,

  the transport step `G_mul_G_le_of_zLogconcave` with its hypothesis discharged and the
  algebraic factor `(1-α²)^{-(n+1)}` replaced by an exponential *variance budget*.
* `Arlib.GaussianCooling.second_moment_le_exp_indicator` — the same bound in estimator form,
  `E(Y²) ≤ exp(phaseVarBudget) · E(Y)²`, which is literally the per-factor hypothesis `hc` of
  `Arlib.GaussianCooling.prod_sq_div_le` / `prod_sq_div_le_exp`.
* `Arlib.GaussianCooling.variance_le_exp_indicator` — the target shape,
  `Var(Y) ≤ (exp(phaseVarBudget) - 1) · E(Y)²`.
* `Arlib.GaussianCooling.phaseVarBudget_fixed_rate` and the `…_fixed_rate` corollaries — at
  the fixed cooling rate `α = 1/n` the budget is exactly `1/(n-1)`.

## The variance budget

`G_mul_G_le_of_zLogconcave` produces the factor `(1-α²)^{-(n+1)}`.  Writing
`(1-t)⁻¹ = 1 + t/(1-t) ≤ exp(t/(1-t))` at `t = α²` and raising to the power `n+1` gives

  `(1-α²)^{-(n+1)} ≤ exp((n+1)α²/(1-α²))`,

which is `phaseVarBudget n α`.  At `α = 1/n` this is `(n+1)/(n²-1) = 1/(n-1)`, matching the
paper's own chain at `vol3_journal.tex:1376` (`e^{1/(n-1)} ≤ 1 + 2/n`), and it is in fact
slightly *sharper* than the `1 + 2/n` of `fixed_var_bound_indicator` (at `n = 3`:
`e^{1/2} = 1.6487 < 5/3`).

## What is still assumed

Nothing here assumes `ZLogconcaveHypothesis`.  The standing hypotheses are only
`Convex ℝ K`, `MeasurableSet K`, `0 < volume K`, `0 < σ` and `0 ≤ α < 1`; the volume
hypothesis is exhibited as satisfiable by `Arlib.GaussianCooling.variance_le_exp_closedBall`.

`LocalizationHypothesis` (`Variance.lean:1095`) is a *different* assumption, feeding the
*accelerated* bounds `variance_bound` / `lc_variance_bound`; it is untouched here and is not
implied by anything in this file.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real

variable {n : ℕ}

/-! ## Finiteness and positivity of `G 1_K`

Everything in `Variance.lean` that turns a `G`-inequality into a statement about the
estimator needs `G f a ≠ 0`.  For `f = 1_K` this is exactly `0 < volume K`. -/

/-- The `n`-dimensional gaussian weight is integrable on `EuclideanSpace ℝ (Fin n)`.
Transported from `integrable_gaussian_pi` along the volume-preserving identification with
`Fin n → ℝ`. -/
theorem integrable_gaussian_eucl {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  have hcomp : ((fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s)))
        ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclSpace n))
      = fun t : Fin n → ℝ => Real.exp (-(∑ i, t i ^ 2) / (2 * s)) := by
    funext t
    simp only [Function.comp_apply]
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hcomp]
  exact integrable_gaussian_pi (by positivity)

/-- `g(·, s)` for `f = 1_K` is the indicator of `K` of the gaussian weight. -/
theorem gW_indicator_eq (K : Set (EuclSpace n)) (s : ℝ) :
    gW (Set.indicator K (1 : EuclSpace n → ℝ)) s
      = Set.indicator K (fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s))) := by
  funext x
  by_cases hx : x ∈ K <;>
    simp [gW, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- `g(·, s)` for `f = 1_K` is integrable for every `s > 0` — with **no** hypothesis on the
volume of `K`.  In particular `G 1_K s` is a genuine finite real number, so no
`volume K ≠ ⊤` guard is needed anywhere below. -/
theorem integrable_gW_indicator {K : Set (EuclSpace n)} (hKm : MeasurableSet K) {s : ℝ}
    (hs : 0 < s) : Integrable (gW (Set.indicator K (1 : EuclSpace n → ℝ)) s) := by
  rw [gW_indicator_eq]
  exact (integrable_gaussian_eucl hs).indicator hKm

/-- The support of `g(·, s)` for `f = 1_K` is `K` itself: the gaussian factor never
vanishes. -/
theorem support_gW_indicator (K : Set (EuclSpace n)) {s : ℝ} :
    Function.support (gW (Set.indicator K (1 : EuclSpace n → ℝ)) s) = K := by
  rw [gW_indicator_eq, Set.support_indicator]
  refine Set.inter_eq_left.mpr fun x _ => ?_
  simp only [Function.mem_support, ne_eq]
  exact (Real.exp_pos _).ne'

/-- `G 1_K s ≥ 0`. -/
theorem G_indicator_nonneg (K : Set (EuclSpace n)) (s : ℝ) :
    0 ≤ G (Set.indicator K (1 : EuclSpace n → ℝ)) s := by
  refine integral_nonneg fun x => ?_
  rw [gW_indicator_eq]
  exact Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x

/-- **`G 1_K s > 0` exactly when `K` has positive volume.**  This is what discharges the
`G … ≠ 0` side conditions of `variance_ratio` / `fixed_var_bound_ratio` for an indicator. -/
theorem G_indicator_pos {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hvol : 0 < volume K) {s : ℝ} (hs : 0 < s) :
    0 < G (Set.indicator K (1 : EuclSpace n → ℝ)) s := by
  rw [G, integral_pos_iff_support_of_nonneg _ (integrable_gW_indicator hKm hs),
    support_gW_indicator]
  · exact hvol
  · intro x
    rw [gW_indicator_eq]
    exact Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x

/-- `G 1_K s ≠ 0` for a body of positive volume. -/
theorem G_indicator_ne_zero {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hvol : 0 < volume K) {s : ℝ} (hs : 0 < s) :
    G (Set.indicator K (1 : EuclSpace n → ℝ)) s ≠ 0 :=
  (G_indicator_pos hKm hvol hs).ne'

/-! ## The variance budget

`G_mul_G_le_of_zLogconcave` produces the algebraic factor `(1-α²)^{-(n+1)}`.  The algorithm
wants it in the exponential form `exp(phaseVarBudget)`, so that `m` phases cost
`exp(m · phaseVarBudget)` (see `prod_sq_div_le_exp`). -/

/-- **The per-phase variance budget** of the cooling rate `α` in dimension `n`:
`phaseVarBudget n α = (n+1)α²/(1-α²)`.

This is a *closed-form abbreviation and nothing more* — it asserts no property.  Everything
it is claimed to bound is proved: `inv_one_sub_sq_pow_le_exp_phaseVarBudget` relates it to
the factor `(1-α²)^{-(n+1)}` coming out of the transport step, and
`phaseVarBudget_fixed_rate` computes it at the fixed cooling rate. -/
noncomputable def phaseVarBudget (n : ℕ) (α : ℝ) : ℝ := ((n : ℝ) + 1) * α ^ 2 / (1 - α ^ 2)

/-- **The budget bounds the algebraic factor:** `(1-α²)^{-(n+1)} ≤ exp(phaseVarBudget n α)`
for `0 ≤ α < 1`.  Proof: `(1-t)⁻¹ = 1 + t/(1-t) ≤ exp(t/(1-t))` at `t = α²`, raised to the power
`n+1`.  Assumes only `0 ≤ α` and `α < 1`. -/
theorem inv_one_sub_sq_pow_le_exp_phaseVarBudget {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ Real.exp (phaseVarBudget n α) := by
  have ht0 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  set u : ℝ := α ^ 2 / (1 - α ^ 2) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hinv : ((1 : ℝ) - α ^ 2)⁻¹ = 1 + u := by
    rw [hu]
    field_simp
    ring
  have hstep : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ (Real.exp u) ^ (n + 1) := by
    rw [hinv]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) (n + 1)
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  rw [hu, phaseVarBudget, mul_div_assoc]
  push_cast
  ring

/-- **The budget at the fixed cooling rate.**  `phaseVarBudget n (1/n) = 1/(n-1)` for
`n ≥ 2` — the paper's `e^{1/(n-1)}` at `vol3_journal.tex:1376`. -/
theorem phaseVarBudget_fixed_rate {n : ℕ} (hn : 2 ≤ n) :
    phaseVarBudget n (1 / (n : ℝ)) = 1 / ((n : ℝ) - 1) := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by intro h; rw [h] at hN; linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hsq : ((n : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hden : (1 : ℝ) - (1 / (n : ℝ)) ^ 2 = ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2 := by
    field_simp
  have hdenne : (1 : ℝ) - (1 / (n : ℝ)) ^ 2 ≠ 0 := by
    rw [hden]; exact div_ne_zero hsq (pow_ne_zero 2 hn0)
  rw [phaseVarBudget, div_eq_div_iff hdenne hn1]
  field_simp
  ring

/-! ## The transport step, unconditional for a convex body -/

/-- **`G_mul_G_le_of_zLogconcave` with its hypothesis discharged.**  For every convex
measurable `K ⊆ ℝⁿ`, every `σ > 0` and every `0 ≤ α < 1`,

  `G 1_K (σ²/(1-α)) · G 1_K (σ²/(1+α)) ≤ (1-α²)^{-(n+1)} · G 1_K (σ²)²`.

No `ZLogconcaveHypothesis`, no boundedness, no roundness, no `0 ∈ K`. -/
theorem G_mul_G_le_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) {σ α : ℝ} (hσ : 0 < σ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 - α))
        * G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α))
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2)) ^ 2 :=
  G_mul_G_le_of_zLogconcave (zLogconcaveHypothesis_indicator hK hKm) hσ hα0 hα1

/-- **The transport step in variance-budget form**, unconditional for a convex body:

  `G 1_K (σ²/(1-α)) · G 1_K (σ²/(1+α)) ≤ exp(phaseVarBudget n α) · G 1_K (σ²)²`

for every convex measurable `K`, every `σ > 0` and every cooling rate `0 ≤ α < 1`.
Assumes only `Convex ℝ K`, `MeasurableSet K`, `0 < σ`, `0 ≤ α`, `α < 1`. -/
theorem G_mul_G_le_exp_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) {σ α : ℝ} (hσ : 0 < σ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 - α))
        * G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α))
      ≤ Real.exp (phaseVarBudget n α)
        * (G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2)) ^ 2 :=
  (G_mul_G_le_indicator hK hKm hσ hα0 hα1).trans
    (mul_le_mul_of_nonneg_right (inv_one_sub_sq_pow_le_exp_phaseVarBudget hα0 hα1) (sq_nonneg _))

/-! ## From a `G`-bound to the estimator

`W = g(X, σ²)/g(X, σ²/(1+α))` with `X` drawn from the density `g(·, σ²/(1+α))/G(σ²/(1+α))`
is the per-phase ratio estimator: `E(W) = G(σ²)/G(σ²/(1+α))` is exactly the ratio of two
consecutive terms of the telescoping product.

The two lemmas here are pure bookkeeping on top of `expect_ratio` / `expect_ratio_sq`, hold
for an arbitrary `f`, and are **independent of `ZLogconcaveHypothesis`**: they convert any
`G`-bound with constant `c` into `E(W²) ≤ c·E(W)²` and `Var(W) ≤ (c-1)·E(W)²`. -/

/-- **`G`-bound ⟹ relative second moment.**  If
`G f (σ²/(1-α))·G f (σ²/(1+α)) ≤ c·G f (σ²)²` and `G f (σ²/(1+α)) > 0`, then the per-phase
estimator satisfies `E(W²) ≤ c·E(W)²`.  This is exactly the per-factor hypothesis `hc` of
`prod_sq_div_le` / `prod_sq_div_le_exp`.  Assumes nothing about `f` beyond the supplied
bound. -/
theorem second_moment_le_of_G_bound {f : EuclSpace n → ℝ} {σ α c : ℝ} (hσ : σ ≠ 0)
    (hα1 : (1 : ℝ) + α ≠ 0) (hα2 : (1 : ℝ) - α ≠ 0)
    (hGa : 0 < G f (σ ^ 2 / (1 + α)))
    (hbound : G f (σ ^ 2 / (1 - α)) * G f (σ ^ 2 / (1 + α)) ≤ c * (G f (σ ^ 2)) ^ 2) :
    (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α))))
      ≤ c * (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
          * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2 := by
  have hσ2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have ha : σ ^ 2 / (1 + α) ≠ 0 := div_ne_zero hσ2 hα1
  have hab := cool_denom_ne hσ hα1 hα2
  rw [expect_ratio, expect_ratio_sq ha hσ2 hab, cool_param hσ hα1 hα2]
  rw [div_le_iff₀ hGa]
  have hrw : c * (G f (σ ^ 2) / G f (σ ^ 2 / (1 + α))) ^ 2 * G f (σ ^ 2 / (1 + α))
      = c * (G f (σ ^ 2)) ^ 2 / G f (σ ^ 2 / (1 + α)) := by
    field_simp
  rw [hrw, le_div_iff₀ hGa]
  exact hbound

/-- **`G`-bound ⟹ variance bound.**  `Var(W) = E(W²) - E(W)² ≤ (c-1)·E(W)²`, the shape the
cooling schedule is designed around.  Same hypotheses as
`second_moment_le_of_G_bound`. -/
theorem variance_le_of_G_bound {f : EuclSpace n → ℝ} {σ α c : ℝ} (hσ : σ ≠ 0)
    (hα1 : (1 : ℝ) + α ≠ 0) (hα2 : (1 : ℝ) - α ≠ 0)
    (hGa : 0 < G f (σ ^ 2 / (1 + α)))
    (hbound : G f (σ ^ 2 / (1 - α)) * G f (σ ^ 2 / (1 + α)) ≤ c * (G f (σ ^ 2)) ^ 2) :
    (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α))))
        - (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
            * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2
      ≤ (c - 1) * (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
          * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2 := by
  have h := second_moment_le_of_G_bound hσ hα1 hα2 hGa hbound
  have hexp : (c - 1) * (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
        * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2
      = c * (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
          * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2
        - (∫ x, (gW f (σ ^ 2) x / gW f (σ ^ 2 / (1 + α)) x)
            * (gW f (σ ^ 2 / (1 + α)) x / G f (σ ^ 2 / (1 + α)))) ^ 2 := by ring
  rw [hexp]
  linarith

/-! ## The headline bounds for a convex body

No `ZLogconcaveHypothesis`, no `G ≠ 0` side condition: the only hypotheses are convexity,
measurability and `0 < volume K`. -/

/-- **`E(W²) ≤ exp(phaseVarBudget n α) · E(W)²` for the indicator of a convex body**, at
any cooling rate `0 ≤ α < 1`.

Hypotheses: `Convex ℝ K`, `MeasurableSet K`, `0 < volume K`, `0 < σ`, `0 ≤ α < 1`.
Nothing is assumed about `zFun`, log-concavity or localization. -/
theorem second_moment_le_exp_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hvol : 0 < volume K) {σ α : ℝ} (hσ : 0 < σ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α))))
      ≤ Real.exp (phaseVarBudget n α)
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)))) ^ 2 :=
  second_moment_le_of_G_bound hσ.ne' (by linarith) (by linarith)
    (G_indicator_pos hKm hvol (by positivity))
    (G_mul_G_le_exp_indicator hK hKm hσ hα0 hα1)

/-- **The target shape: `Var(W) ≤ (exp(phaseVarBudget n α) - 1)·E(W)²`** for the per-phase
ratio estimator between the consecutive gaussians `σ²/(1+α)` and `σ²`, when the weight is the
indicator of a convex body.

Hypotheses: `Convex ℝ K`, `MeasurableSet K`, `0 < volume K`, `0 < σ`, `0 ≤ α < 1`.
**No `ZLogconcaveHypothesis` and no `LocalizationHypothesis`.** -/
theorem variance_le_exp_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hvol : 0 < volume K) {σ α : ℝ} (hσ : 0 < σ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α))))
        - (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)))) ^ 2
      ≤ (Real.exp (phaseVarBudget n α) - 1)
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + α)))) ^ 2 :=
  variance_le_of_G_bound hσ.ne' (by linarith) (by linarith)
    (G_indicator_pos hKm hvol (by positivity))
    (G_mul_G_le_exp_indicator hK hKm hσ hα0 hα1)

/-! ## The fixed cooling rate `α = 1/n` -/

/-- **`E(W²) ≤ (1 + 2/n)·E(W)²` at the fixed cooling rate** `σᵢ₊₁² = σᵢ²(1+1/n)`, for a
convex body of positive volume and `n ≥ 3`.  This is `fixed_var_bound_indicator` in the
estimator form `prod_sq_div_le` consumes, with the `G ≠ 0` side conditions discharged. -/
theorem second_moment_le_fixed_rate_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hvol : 0 < volume K) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ)))))
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2 := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlt : 1 / (n : ℝ) < 1 := by rw [div_lt_one hN0]; linarith
  refine second_moment_le_of_G_bound hσ.ne' (by positivity) (by intro h; linarith)
    (G_indicator_pos hKm hvol (by positivity)) ?_
  rw [mul_comm]
  exact fixed_var_bound_indicator hK hKm hσ hn

/-- **`Var(W) ≤ (2/n)·E(W)²` at the fixed cooling rate**, for a convex body of positive
volume and `n ≥ 3`. -/
theorem variance_le_fixed_rate_indicator {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hvol : 0 < volume K) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ)))))
        - (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2
      ≤ (2 / (n : ℝ))
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2 := by
  have hN : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlt : 1 / (n : ℝ) < 1 := by rw [div_lt_one hN0]; linarith
  have h := variance_le_of_G_bound (f := Set.indicator K (1 : EuclSpace n → ℝ)) (σ := σ)
    (α := 1 / (n : ℝ)) (c := 1 + 2 / (n : ℝ)) hσ.ne' (by positivity)
    (by intro hz; linarith) (G_indicator_pos hKm hvol (by positivity))
    (by rw [mul_comm]; exact fixed_var_bound_indicator hK hKm hσ hn)
  have hc : (1 + 2 / (n : ℝ)) - 1 = 2 / (n : ℝ) := by ring
  rwa [hc] at h

/-- **Paper Lemma 5.10 in ratio form with *every* side condition discharged.**
`fixed_var_bound_ratio_indicator` still carries the two `G … ≠ 0` hypotheses; for the
indicator of a convex body they follow from `0 < volume K` by `G_indicator_ne_zero`, so the
only remaining hypotheses are `Convex ℝ K`, `MeasurableSet K`, `0 < volume K`, `0 < σ` and
`3 ≤ n`.

(The division-free `second_moment_le_fixed_rate_indicator` above says the same thing without
a quotient, and is the form `prod_sq_div_le` consumes.) -/
theorem fixed_var_bound_ratio_of_volume_pos {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hvol : 0 < volume K) {σ : ℝ} (hσ : 0 < σ) (hn : 3 ≤ n) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ)))))
      / (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
            / gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x)
          * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))) x
            / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + 1 / (n : ℝ))))) ^ 2
      ≤ 1 + 2 / (n : ℝ) :=
  fixed_var_bound_ratio_indicator hK hKm hσ hn
    (G_indicator_ne_zero hKm hvol (by positivity))
    (G_indicator_ne_zero hKm hvol (by positivity))

/-- **Non-vacuity witness.**  Every closed euclidean ball of positive radius is a convex
measurable set of positive volume, so the hypotheses of the bounds above are satisfiable and
the theorems are not vacuous. -/
theorem variance_le_exp_closedBall (c : EuclSpace n) {r : ℝ} (hr : 0 < r) {σ α : ℝ}
    (hσ : 0 < σ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ x, (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
              (σ ^ 2 / (1 + α)) x) ^ 2
        * (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
              (σ ^ 2 / (1 + α)) x
          / G (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
              (σ ^ 2 / (1 + α))))
        - (∫ x, (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)) x)
            * (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)) x
              / G (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)))) ^ 2
      ≤ (Real.exp (phaseVarBudget n α) - 1)
        * (∫ x, (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)) x)
            * (gW (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)) x
              / G (Set.indicator (Metric.closedBall c r) (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + α)))) ^ 2 :=
  variance_le_exp_indicator (convex_closedBall c r) Metric.isClosed_closedBall.measurableSet
    (Metric.measure_closedBall_pos volume c hr) hσ hα0 hα1

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms integrable_gaussian_eucl
#print axioms gW_indicator_eq
#print axioms integrable_gW_indicator
#print axioms support_gW_indicator
#print axioms G_indicator_nonneg
#print axioms G_indicator_pos
#print axioms G_indicator_ne_zero
#print axioms inv_one_sub_sq_pow_le_exp_phaseVarBudget
#print axioms phaseVarBudget_fixed_rate
#print axioms G_mul_G_le_indicator
#print axioms G_mul_G_le_exp_indicator
#print axioms second_moment_le_of_G_bound
#print axioms variance_le_of_G_bound
#print axioms second_moment_le_exp_indicator
#print axioms variance_le_exp_indicator
#print axioms second_moment_le_fixed_rate_indicator
#print axioms variance_le_fixed_rate_indicator
#print axioms fixed_var_bound_ratio_of_volume_pos
#print axioms variance_le_exp_closedBall

end Arlib.GaussianCooling
