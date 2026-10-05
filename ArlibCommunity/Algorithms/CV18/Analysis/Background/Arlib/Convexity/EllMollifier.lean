/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoIndicator
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.EllGaussianFacts

/-!
# The mollified `ℓ`-weighted Gaussian density `e^{−j·dist(x,K̄)}·ℓ·e^{−‖x‖²/(2σ²)}`

`Arlib.ellGaussian_isoperimetry_openClosed_logTwo` (`Arlib/Convexity/EllLogConcave.lean:474`)
is `thm:iso` for the **continuous** density `ℓ·γ`, `γ(x) = e^{−‖x‖²/(2σ²)}`, carrying **no**
indicator of `K`.  Bridging it to the **indicator** density `1_K·ℓ·γ` — the density of the
`ℓ`-weighted Gaussian restricted to the body — is a mollification argument: interpose the family

    g j x  =  e^{−j·dist(x, K̄)} · (ell K δ x).toReal · e^{−‖x‖²/(2σ²)},

which is continuous for every `j`, has a **log-concave** cofactor (so it discharges the
open/closed capstone's `hfc` binder), and decreases pointwise to `1_{K̄}·ℓ·γ`.  This file supplies
the analytic side conditions for `g j`, the two limits, and the two rewritings that land those
limits in the indicator density's own language.

**No `def` is introduced.**  Following `Arlib.ellGaussian_isoperimetry_openClosed_logTwo` and
`Arlib/Convexity/EllGaussianFacts.lean`, every statement takes the family as an opaque
`g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ` together with the explicit defining equation

    hg : ∀ (j : ℕ) (x : _), g j x
           = Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
               * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)),

so each lemma discharges a consumer binder verbatim and no name stands in for a proof
(CLAUDE.md §11).

## Main results

* `Arlib.exp_neg_natMul_infDist_le_one`, `Arlib.ell_toReal_le_one` — the two pointwise `≤ 1`
  facts every bound below rests on.
* `Arlib.isLogConcave_expNegInfDist_mul_ell` — `e^{−j·dist(x,K̄)}·ℓ` is **log-concave**, the
  cofactor binder of the open/closed capstone.
* `Arlib.hMoll_nonneg`, `Arlib.hMoll_le_one`, `Arlib.hMoll_continuous`,
  `Arlib.hMoll_integrable`, `Arlib.hMoll_integral_pos` — the mollified analogues of the five
  side conditions of `Arlib/Convexity/EllGaussianFacts.lean` (`h0`, `hhB` at `B = 1`, `hhc`,
  `hhi`, `hmass`).
* `Arlib.tendsto_setIntegral_hMoll` — **the deliverable.**  For **every** set `A`,
  measurable or not, `∫_A g j → ∫_{A ∩ K̄} ℓ·γ`.
* `Arlib.tendsto_integral_hMoll` — the same at `A = Set.univ`.
* `Arlib.setIntegral_closure_eq_setIntegral` — `∫_{A ∩ K̄} ℓ·γ = ∫_{A ∩ K} ℓ·γ` for convex `K`,
  the frontier being Lebesgue-null.
* `Arlib.setIntegral_eq_setIntegral_indicator` — `∫_A 1_K·(ℓ·γ) = ∫_{A ∩ K} ℓ·γ`, so the limit
  above is a statement about the indicator density.
* `Arlib.tendsto_setIntegral_hMoll_witness` — non-vacuity: the whole hypothesis bundle of
  `tendsto_setIntegral_hMoll`, plus its conclusion, at `n = 2`, `K = B(0,1)`, `δ = σ = 1`,
  `A = closedBall 0 (1/2)`.

## What was reused, not reproved

* `Arlib.tendsto_setIntegral_expNegInfDist_mul_weighted`
  (`Arlib/Convexity/IsoWeighted.lean:396`) — **the dominated-convergence engine.**  It is already
  stated for a general nonnegative continuous `f` with `f·γ` integrable, so
  `tendsto_setIntegral_hMoll` is its instantiation at `f := fun x => (ell K δ x).toReal` plus
  three mechanical rewritings (`neg_mul`; the `gaussianWeightReal` unfold; `setIntegral_indicator`
  to turn `∫_A 1_{K̄}·F` into `∫_{A ∩ K̄} F`).  The indicator-only
  `Arlib.tendsto_setIntegral_expNegInfDist_mul_gaussian` (`Arlib/Convexity/IsoIndicator.lean:329`)
  is the same statement at `f ≡ 1`; the weighted version supersedes it here.
* `Arlib.isLogConcave_exp_neg_infDist` (`Arlib/Convexity/IsoIndicator.lean:152`) and
  `Arlib.isLogConcave_ell_toReal` (`Arlib/Convexity/EllLogConcave.lean:262`), combined by
  `Arlib.IsLogConcave.mul` (`Arlib/Convexity/LogConcave.lean:152`) — which **does** exist, so no
  new product-of-log-concaves lemma was needed.  The term-mode pattern is copied from
  `Arlib.isLogConcave_indicator_mul_ell_toReal` (`Arlib/Convexity/EllLogConcave.lean:283`).
* `Arlib.setIntegral_indicator_closure_eq` (`Arlib/Convexity/IsoIndicator.lean:372`) — the
  frontier of a convex set is Lebesgue-null (`Convex.addHaar_frontier`).  **Null-ness of the
  boundary is not reproved here**; `setIntegral_closure_eq_setIntegral` is that lemma sandwiched
  between two applications of `MeasureTheory.setIntegral_indicator`.
* `Arlib.continuous_ell_toReal` (`Arlib/Convexity/EllLogConcave.lean:431`),
  `Arlib.MarkovChains.ell_le_one` (`Arlib/MarkovChains/Continuous/BallWalk.lean:151`),
  `Arlib.ellGaussian_integrable` (`Arlib/Convexity/EllGaussianFacts.lean:136`),
  `Arlib.integrable_gaussianWeightReal` (`Arlib/Convexity/IsoIndicator.lean:314`),
  `Arlib.integral_pos_of_continuous_of_pos` (`Arlib/Convexity/IsoWeighted.lean:380`),
  `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`
  (`Arlib/MarkovChains/Continuous/StarPolar.lean:426`).
* `Arlib.MarkovChains.gaussianWeightReal s x` is **by `def`**
  `Real.exp (-‖x‖ ^ 2 / (2 * s))` (`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean:150`),
  so at `s := σ ^ 2` it is definitionally the exponential written above; no bridge lemma exists
  or is needed, only `simp [gaussianWeightReal]`.

## One deviation from the obvious route

`hMoll_integral_pos` is **not** derived from `Arlib.ellGaussian_integral_pos`
(`Arlib/Convexity/EllGaussianFacts.lean:166`) by monotonicity: the domination
`g j ≤ ℓ·γ` runs the wrong way for a lower bound, and `ellGaussian_integral_pos` is an integral
over all of `ℝⁿ`, not over `K`.  Instead its proof is mirrored: `g j` is continuous, nonnegative
and integrable, and at any `x₀ ∈ K` one has `dist(x₀, K̄) = 0`, hence
`g j x₀ = ℓ(x₀)·γ(x₀) > 0`; `Arlib.integral_pos_of_continuous_of_pos` finishes.  This costs
`Convex ℝ K`, `Bornology.IsBounded K`, `volume K ≠ 0` (exactly `ellGaussian_integral_pos`'s
bundle) and **no** `MeasurableSet K`.

## What is assumed

**Nothing.**  There is no `def`, `structure`, `class` or `axiom` in this file; every declaration
is a `theorem`, and none of them takes `thm:iso`, a localization binder, or any part of either as
a hypothesis.  Nothing here is an isoperimetric, conductance or mixing statement: these are the
analytic side conditions and the two limits of a mollification, and nothing more.

The hypotheses actually needed, per lemma, are exactly those in the signatures below; notably
`tendsto_setIntegral_hMoll` needs only `n ≠ 0`, `0 ≤ δ`, `0 < σ` and `K.Nonempty` — no
measurability or convexity of `K`, and no measurability of `A`.
-/

open MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace Arlib

open MarkovChains

variable {n : ℕ}

/-! ### Two pointwise `≤ 1` facts -/

/-- `e^{−j·dist(x,C)} ≤ 1` for a natural number `j`: the exponent is nonpositive because both
`(j : ℝ)` and `Metric.infDist x C` are nonnegative. -/
theorem exp_neg_natMul_infDist_le_one {E : Type*} [PseudoMetricSpace E] (j : ℕ) (x : E)
    (C : Set E) : Real.exp (-(j : ℝ) * Metric.infDist x C) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have h : (0 : ℝ) ≤ (j : ℝ) * Metric.infDist x C :=
    mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
  linarith

/-- `(ell K δ x).toReal ≤ 1`, the real-valued form of `Arlib.MarkovChains.ell_le_one`. -/
theorem ell_toReal_le_one (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : (ell K δ x).toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
  simpa using this

/-! ### Log-concavity of the mollified cofactor -/

/-- **The mollified cofactor `e^{−j·dist(x,K̄)}·ℓ` is log-concave.**

A product of two log-concave functions (`Arlib.IsLogConcave.mul`):
`Arlib.isLogConcave_exp_neg_infDist` at the **closure** of `K` — which is convex
(`Convex.closure`), compact (bounded and closed) and nonempty — and
`Arlib.isLogConcave_ell_toReal`.

This is what the open/closed capstone
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` asks of the cofactor `f` of a density
`f·e^{−‖x‖²/(2σ²)}`; the point of mollifying at `closure K` rather than at `K` is precisely that
`Arlib.isLogConcave_exp_neg_infDist` needs a **compact** set. -/
theorem isLogConcave_expNegInfDist_mul_ell {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hKne : K.Nonempty)
    (δ : ℝ) (j : ℕ) :
    IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal) := by
  have hCconv : Convex ℝ (closure K) := hKc.closure
  have hCcomp : IsCompact (closure K) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hKb.closure
  have hCne : (closure K).Nonempty := hKne.closure
  have hexp : IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K))) := by
    have h := isLogConcave_exp_neg_infDist hCconv hCcomp hCne (c := (j : ℝ)) (Nat.cast_nonneg j)
    simpa only [neg_mul] using h
  exact IsLogConcave.mul hexp (isLogConcave_ell_toReal hK hKc δ)
    (fun _ => (Real.exp_pos _).le) (fun _ => ENNReal.toReal_nonneg)

/-! ### The four analytic side conditions, mirroring `EllGaussianFacts.lean` -/

/-- **Nonnegativity of the mollified density**, the capstone's `h0`.  No hypotheses: all three
factors are nonnegative outright. -/
theorem hMoll_nonneg {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), 0 ≤ g j x := by
  intro j x
  rw [hg]
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (Real.exp_pos _).le

/-- **The mollified density is bounded by `1`**, the capstone's `hhB` at `B = 1`.

Each of the three factors is at most `1`.  As in `Arlib.ellGaussian_le_one` no hypothesis on `σ`
is needed: at `σ = 0` Lean's `x / 0 = 0` convention makes the Gaussian factor `e⁰ = 1`. -/
theorem hMoll_le_one {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x ≤ 1 := by
  intro j x
  have hexp1 : Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) ≤ 1 :=
    exp_neg_natMul_infDist_le_one j x (closure K)
  have hell1 : (ell K δ x).toReal ≤ 1 := ell_toReal_le_one K δ x
  have hgle : Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by positivity))
  rw [hg]
  calc Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))
      ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul hexp1 hell1 ENNReal.toReal_nonneg zero_le_one) hgle
          (Real.exp_pos _).le (by norm_num)
    _ = 1 := by norm_num

/-- **The mollified density is continuous**, the capstone's `hhc`.

A product of `x ↦ e^{−j·dist(x,K̄)}` (continuous because `Metric.infDist · C` is), of
`Arlib.continuous_ell_toReal` — where all the work is — and of the Gaussian factor. -/
theorem hMoll_continuous (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ j : ℕ, Continuous (g j) := by
  intro j
  have hrw : g j = fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := funext (hg j)
  rw [hrw]
  have hcInf : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Metric.infDist x (closure K) := Metric.continuous_infDist_pt _
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) :=
    Real.continuous_exp.comp (continuous_const.mul hcInf)
  exact (hexpc.mul (continuous_ell_toReal hn hδ)).mul (by fun_prop)

/-- **The mollified density is integrable**, the capstone's `hhi`.

Domination by the Gaussian: `e^{−j·dist(x,K̄)} ≤ 1` and `ℓ ≤ 1`, so
`g j x ≤ e^{−‖x‖²/(2σ²)}` pointwise, and the latter is integrable by
`Arlib.integrable_gaussianWeightReal` (whose statement is about
`Arlib.MarkovChains.gaussianWeightReal (σ ^ 2)`, which **is** that exponential by `def`). -/
theorem hMoll_integrable (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 < σ) {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ j : ℕ, Integrable (g j) := by
  intro j
  have hgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    have := integrable_gaussianWeightReal (n := n) hσ
    simpa [gaussianWeightReal] using this
  refine hgi.mono' (hMoll_continuous hn hδ hg j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hMoll_nonneg hg j x), hg]
  have hprod : Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal ≤ 1 := by
    have h1 := exp_neg_natMul_infDist_le_one j x (closure K)
    have h2 := ell_toReal_le_one K δ x
    have h3 : (0 : ℝ) ≤ Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) :=
      (Real.exp_pos _).le
    nlinarith [ENNReal.toReal_nonneg (a := ell K δ x)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le hprod

/-- **The mollified density has positive total mass**, the capstone's `hmass`.

Not by monotonicity from `Arlib.ellGaussian_integral_pos`: the domination `g j ≤ ℓ·γ` runs the
wrong way.  Instead, `g j` is continuous, nonnegative and integrable, and at any `x₀ ∈ K` — which
exists because a null set has volume `0` — one has `x₀ ∈ closure K`, so `dist(x₀, K̄) = 0` and
`g j x₀ = ℓ(x₀)·e^{−‖x₀‖²/(2σ²)}`, which is strictly positive because
`Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex` gives `vol(B(x₀,δ) ∩ K) ≠ 0`.
`Arlib.integral_pos_of_continuous_of_pos` finishes.

**No `MeasurableSet K`** is required; the hypothesis bundle is exactly that of
`Arlib.ellGaussian_integral_pos`. -/
theorem hMoll_integral_pos (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ j : ℕ, 0 < ∫ x, g j x := by
  intro j
  obtain ⟨x₀, hx₀⟩ : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hK0 (by rw [hc]; exact measure_empty)
  have hpos : volume (ball x₀ δ ∩ K) ≠ 0 :=
    volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hx₀ hδ
  have hellpos : 0 < (ell K δ x₀).toReal := by
    refine ENNReal.toReal_pos ?_ (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x₀))
    rw [ell_apply]
    exact fun hz => hpos (by
      rcases (ENNReal.div_eq_zero_iff).1 hz with hnum | hden
      · exact hnum
      · exact absurd hden measure_ball_lt_top.ne)
  refine integral_pos_of_continuous_of_pos (hMoll_continuous hn hδ.le hg j)
    (hMoll_nonneg hg j) (hMoll_integrable hn hδ.le hσ hg j) (x₀ := x₀) ?_
  have hz : Metric.infDist x₀ (closure K) = 0 :=
    Metric.infDist_zero_of_mem (subset_closure hx₀)
  rw [hg, hz, mul_zero, Real.exp_zero, one_mul]
  exact mul_pos hellpos (Real.exp_pos _)

/-! ### The two rewritings into the indicator density's language -/

/-- **`∫_{A ∩ K̄} ℓ·γ = ∫_{A ∩ K} ℓ·γ`**, for a convex `K`.

Nothing about convex boundaries is proved here.  Both sides are turned into integrals of an
indicator over `A` by `MeasureTheory.setIntegral_indicator`, and the resulting identity is
exactly `Arlib.setIntegral_indicator_closure_eq` (`Arlib/Convexity/IsoIndicator.lean:372`), which
is where `Convex.addHaar_frontier` — `volume (frontier K) = 0` — is used. -/
theorem setIntegral_closure_eq_setIntegral {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {δ σ : ℝ}
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in A ∩ closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
      = ∫ x in A ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
  have h1 : (∫ x in A ∩ closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
      = ∫ x in A, Set.indicator (closure K)
          (fun y => (ell K δ y).toReal * Real.exp (-‖y‖ ^ 2 / (2 * σ ^ 2))) x :=
    (setIntegral_indicator isClosed_closure.measurableSet).symm
  have h2 : (∫ x in A ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
      = ∫ x in A, Set.indicator K
          (fun y => (ell K δ y).toReal * Real.exp (-‖y‖ ^ 2 / (2 * σ ^ 2))) x :=
    (setIntegral_indicator hK).symm
  rw [h1, h2]
  exact setIntegral_indicator_closure_eq hKc _ A

/-- **`∫_A 1_K·(ℓ·γ) = ∫_{A ∩ K} ℓ·γ`**, so that the limits below are statements about the
indicator density `1_K·ℓ·e^{−‖x‖²/(2σ²)}` itself.  This is `MeasureTheory.setIntegral_indicator`
at the `ℓ`-weighted Gaussian, recorded under a name the consumer can quote. -/
theorem setIntegral_eq_setIntegral_indicator {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ σ : ℝ} (A : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in A, Set.indicator K
        (fun y => (ell K δ y).toReal * Real.exp (-‖y‖ ^ 2 / (2 * σ ^ 2))) x)
      = ∫ x in A ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
  setIntegral_indicator hK

/-! ### The two limits -/

/-- **The deliverable: `∫_A g j → ∫_{A ∩ K̄} ℓ·γ` for every set `A`.**

`Arlib.tendsto_setIntegral_expNegInfDist_mul_weighted` (`Arlib/Convexity/IsoWeighted.lean:396`)
is already the dominated-convergence statement for a general nonnegative continuous cofactor `f`
with `f·γ` integrable, so this is its instantiation at `f := fun x => (ell K δ x).toReal`:
`hf0` is `ENNReal.toReal_nonneg`, `hfc` is `Arlib.continuous_ell_toReal`, and `hfi` is
`Arlib.ellGaussian_integrable`.  The only glue is `neg_mul`, the `gaussianWeightReal` unfold, and
`MeasureTheory.setIntegral_indicator` turning `∫_A 1_{K̄}·(ℓ·γ)` into `∫_{A ∩ K̄} ℓ·γ`.

`A` is **arbitrary** — not assumed measurable — and `K` is assumed neither measurable nor convex;
only `K.Nonempty` is used, to know that `dist(x, K̄) > 0` off `K̄`. -/
theorem tendsto_setIntegral_hMoll (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 < σ) (hKne : K.Nonempty)
    {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun j : ℕ => ∫ x in A, g j x) atTop
      (𝓝 (∫ x in A ∩ closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))) := by
  have hfi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x := by
    have := ellGaussian_integrable (n := n) (K := K) (δ := δ) (σ := σ) hn hδ hσ (fun _ => rfl)
    simpa [gaussianWeightReal] using this
  have hlim := tendsto_setIntegral_expNegInfDist_mul_weighted (σ := σ)
    (f := fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal)
    (fun _ => ENNReal.toReal_nonneg) (continuous_ell_toReal hn hδ) hfi
    (C := closure K) isClosed_closure hKne.closure A
  have htarget : (∫ x in A, Set.indicator (closure K)
        (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
      = ∫ x in A ∩ closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    rw [setIntegral_indicator isClosed_closure.measurableSet]
    simp [gaussianWeightReal]
  rw [htarget] at hlim
  have heq : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * (ell K δ x).toReal
        * gaussianWeightReal (σ ^ 2) x = g j x := by
    intro j x
    rw [hg, gaussianWeightReal, neg_mul]
  simpa only [heq] using hlim

/-- **The deliverable at `A = Set.univ`:** `∫ g j → ∫_{K̄} ℓ·γ`.  This is the capstone's `hmass`
factor in the limit; `Arlib.tendsto_setIntegral_hMoll` at `Set.univ`, with
`Set.univ ∩ closure K = closure K` and `MeasureTheory.setIntegral_univ`. -/
theorem tendsto_integral_hMoll (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 < σ) (hKne : K.Nonempty)
    {g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    Tendsto (fun j : ℕ => ∫ x, g j x) atTop
      (𝓝 (∫ x in closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))) := by
  have h := tendsto_setIntegral_hMoll hn hδ hσ hKne hg Set.univ
  simpa only [Set.univ_inter, MeasureTheory.setIntegral_univ] using h

/-! ### Non-vacuity -/

/-- **Non-vacuity for `Arlib.tendsto_setIntegral_hMoll`.**

Its whole hypothesis bundle — `n ≠ 0`, `0 ≤ δ`, `0 < σ`, `K.Nonempty` and the defining equation
for `g` — is discharged simultaneously at the concrete data

  `n = 2`,  `K = B(0,1)`,  `δ = 1`,  `σ = 1`,  `A = B̄(0, 1/2)`,

and the conclusion holds there.  So the binder bundle is satisfiable and the theorem is not
vacuous.  (`K.Nonempty` is `Metric.nonempty_ball`; the defining equation is `rfl`.) -/
theorem tendsto_setIntegral_hMoll_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ σ : ℝ)
      (g : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (A : Set (EuclideanSpace ℝ (Fin 2))),
      (2 : ℕ) ≠ 0 ∧ 0 ≤ δ ∧ 0 < σ ∧ K.Nonempty ∧
      (∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin 2)), g j x =
        Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
          * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Tendsto (fun j : ℕ => ∫ x in A, g j x) atTop
        (𝓝 (∫ x in A ∩ closure K,
          (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))) := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin 2)) 1, 1, 1,
    fun j x => Real.exp (-(j : ℝ)
        * Metric.infDist x (closure (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)))
      * (ell (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 x).toReal
      * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)),
    closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
    two_ne_zero, zero_le_one, one_pos, Metric.nonempty_ball.2 one_pos, fun _ _ => rfl, ?_⟩
  exact tendsto_setIntegral_hMoll (n := 2) two_ne_zero zero_le_one one_pos
    (Metric.nonempty_ball.2 one_pos) (fun _ _ => rfl) _

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`,
Mathlib's three standard foundational axioms — and nothing else. -/

#print axioms Arlib.exp_neg_natMul_infDist_le_one
#print axioms Arlib.ell_toReal_le_one
#print axioms Arlib.isLogConcave_expNegInfDist_mul_ell
#print axioms Arlib.hMoll_nonneg
#print axioms Arlib.hMoll_le_one
#print axioms Arlib.hMoll_continuous
#print axioms Arlib.hMoll_integrable
#print axioms Arlib.hMoll_integral_pos
#print axioms Arlib.setIntegral_closure_eq_setIntegral
#print axioms Arlib.setIntegral_eq_setIntegral_indicator
#print axioms Arlib.tendsto_setIntegral_hMoll
#print axioms Arlib.tendsto_integral_hMoll
#print axioms Arlib.tendsto_setIntegral_hMoll_witness
