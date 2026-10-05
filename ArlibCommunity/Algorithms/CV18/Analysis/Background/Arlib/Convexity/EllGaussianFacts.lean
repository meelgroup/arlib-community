/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoWeighted
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.StarPolar

/-!
# Side conditions for the `ℓ`-weighted Gaussian density, **without** an indicator of `K`

This file collects, as **named standalone lemmas**, the analytic side conditions that
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` (`Arlib/Convexity/OneDimSharp.lean:631`)
demands of its density `h`, at

    f x = (ell K δ x).toReal,   h x = f x · e^{−‖x‖²/(2σ²)}

— that is, at the density of `Arlib.ellGaussian_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/EllLogConcave.lean:474`), which carries **no `1_K`**.  Every statement is in
the `{h} (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))` style of that
theorem, so each one discharges a capstone binder verbatim.

## Main results

* `Arlib.ellGaussian_nonneg` — `∀ x, 0 ≤ h x`  (the capstone's `h0`; no hypotheses at all).
* `Arlib.ellGaussian_le_one` — `∀ x, h x ≤ 1`  (the capstone's `hhB` at `B = 1`; no hypotheses,
  not even `0 < σ`: at `σ = 0` the exponent is `x/0 = 0` and `e⁰ = 1 ≤ 1`).
* `Arlib.ellGaussian_continuous` — `Continuous h`  (the capstone's `hhc`).
* `Arlib.ellGaussian_integrable` — `Integrable h`  (the capstone's `hhi`).
* `Arlib.ellGaussian_integral_pos` — `0 < ∫ x, h x`  (the capstone's `hmass`), for a **bounded
  convex** `K` of positive volume, with **no measurability hypothesis on `K`**.
* `Arlib.ellGaussian_integral_pos_witness` — non-vacuity: the full hypothesis bundle of
  `ellGaussian_integral_pos` discharged at `n = 2`, `K = B(0,1)`, `δ = 1`, `σ = 1`.

## What was reused, and what did **not** already exist

None of the five facts existed anywhere in the tree as a standalone lemma for this
(indicator-free) `h`.  They existed only as **inline `have`s** inside a single proof,
`Arlib.ellGaussian_isoperimetry_openClosed_logTwo` (`Arlib/Convexity/EllLogConcave.lean:503`
for `hh0`, `:491` for `hhc`, `:506` for `hhB`, `:516` for `hhi`, `:530` for `hmass`), where they
are not accessible to any other file.  The proofs below are those `have`s, extracted and
generalised (notably: `hmass` here takes `Bornology.IsBounded K` and `volume K ≠ 0` rather than
a pre-supplied `volume (ball x₀ δ ∩ K) ≠ 0`, and needs no `MeasurableSet K`).

The nearest pre-existing relative of `ellGaussian_integrable` is
`Arlib.MarkovChains.integrableOn_ell_mul_gaussianWeightReal`
(`Arlib/MarkovChains/Continuous/SpeedyGaussianConductance.lean:118`), which is a strictly weaker
`IntegrableOn … A` for sets `A` of **finite volume** (and needs `MeasurableSet K`); it does not
give global `Integrable`, which is what the capstone asks for.  Likewise the nearest relative of
`ellGaussian_integral_pos` is `Arlib.MarkovChains.integral_ellGaussianIndicator_pos`
(`…/SpeedyGaussianConductance.lean:502`), which is about the **indicator** density
`1_K·ℓ·e^{−‖x‖²/(2σ²)}`, a strictly smaller integrand.

Genuinely reused, not reproved:

* `Arlib.continuous_ell_toReal` (`Arlib/Convexity/EllLogConcave.lean:431`) — continuity of `ℓ`.
* `Arlib.MarkovChains.ell_le_one` (`Arlib/MarkovChains/Continuous/BallWalk.lean:151`).
* `Arlib.integrable_gaussianWeightReal` (`Arlib/Convexity/IsoIndicator.lean:314`) — the
  dominating Gaussian.  **`Arlib.MarkovChains.gaussianWeightReal s x` is by definition
  `Real.exp (-‖x‖ ^ 2 / (2 * s))` (`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean:151`),
  so at `s := σ ^ 2` it is *definitionally* the exponential written above** — no bridge lemma is
  needed, only `simp [gaussianWeightReal]` to unfold the `def`.
* `Arlib.integral_pos_of_continuous_of_pos` (`Arlib/Convexity/IsoWeighted.lean:380`).
* `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`
  (`Arlib/MarkovChains/Continuous/StarPolar.lean:426`) — a bounded convex body of positive
  volume meets every proposal ball centred in it in positive volume.

## Scope

Nothing here is an isoperimetric, conductance or mixing statement; these are analytic side
conditions only.  There is no `def`, `structure`, `class` or `axiom` in this file; every
declaration is a `theorem`.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace Arlib

open MarkovChains

variable {n : ℕ}

/-- **Nonnegativity of the `ℓ`-weighted Gaussian density.**  `ℓ` is an `ℝ≥0∞`-valued quantity
read off through `toReal`, and the Gaussian factor is an exponential; no hypotheses needed.
This discharges the `h0`/`hf₀`-shaped side condition of
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`. -/
theorem ellGaussian_nonneg {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ x, 0 ≤ h x := by
  intro x
  rw [hh]
  exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le

/-- **The `ℓ`-weighted Gaussian density is bounded by `1`.**  This is the capstone's `hhB` at
`B = 1`: `ℓ ≤ 1` (`Arlib.MarkovChains.ell_le_one`) and `e^{−‖x‖²/(2σ²)} ≤ 1`.

No hypothesis on `σ` is needed: the exponent `−‖x‖²/(2σ²)` is nonpositive for every real `σ`,
including `σ = 0`, where Lean's `x / 0 = 0` convention makes it `0` and the factor `1`. -/
theorem ellGaussian_le_one {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    ∀ x, h x ≤ 1 := by
  intro x
  have hell1 : (ell K δ x).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  have hgle : Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by positivity))
  rw [hh]
  calc (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))
      ≤ 1 * 1 := mul_le_mul hell1 hgle (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- **The `ℓ`-weighted Gaussian density is continuous**, the capstone's `hhc`.  A product of
`Arlib.continuous_ell_toReal` (which is where all the work is: the annulus estimate) and the
manifestly continuous Gaussian factor.  No measurability or convexity of `K` is used. -/
theorem ellGaussian_continuous (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    Continuous h := by
  have hrw : h = fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := funext hh
  rw [hrw]
  exact (continuous_ell_toReal hn hδ).mul (by fun_prop)

/-- **The `ℓ`-weighted Gaussian density is integrable**, the capstone's `hhi`.

Domination by the Gaussian itself: `ℓ ≤ 1` gives `h x ≤ e^{−‖x‖²/(2σ²)}` pointwise, and the
latter is integrable by `Arlib.integrable_gaussianWeightReal`.  That lemma is stated for
`Arlib.MarkovChains.gaussianWeightReal (σ ^ 2)`, which **is** `Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))`
by `def` (`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean:151`), so the only step is to
unfold the definition — there is no bridge lemma to state. -/
theorem ellGaussian_integrable (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 < σ) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    Integrable h := by
  have hgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    have := integrable_gaussianWeightReal (n := n) hσ
    simpa [gaussianWeightReal] using this
  refine hgi.mono' (ellGaussian_continuous hn hδ hh).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hell1 : (ell K δ x).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  rw [Real.norm_eq_abs, abs_of_nonneg (ellGaussian_nonneg hh x), hh]
  exact mul_le_of_le_one_left (Real.exp_pos _).le hell1

/-- **The `ℓ`-weighted Gaussian density has positive total mass**, the capstone's `hmass`.

For a **bounded convex** `K` of positive volume: pick any `x₀ ∈ K` (nonempty because a null set
would have volume `0`); `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex` gives
`vol(B(x₀,δ) ∩ K) ≠ 0`, hence `ℓ(x₀) > 0` and `h x₀ > 0`; and a continuous, nonnegative,
integrable function that is positive at a point has positive integral
(`Arlib.integral_pos_of_continuous_of_pos`).

**No `MeasurableSet K`** is required: neither `Arlib.continuous_ell_toReal` (which uses only
monotonicity and subadditivity of `volume` as an outer measure) nor
`volume_ball_inter_ne_zero_of_convex` needs it.  This is where the indicator-free `h` is easier
than the indicator one: `Arlib.MarkovChains.integral_ellGaussianIndicator_pos`
(`Arlib/MarkovChains/Continuous/SpeedyGaussianConductance.lean:502`) must route through
`lintegral`s of the restricted measure and does need `hK` and `volume K ≠ ⊤`. -/
theorem ellGaussian_integral_pos (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))} {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :
    0 < ∫ x, h x := by
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
  refine integral_pos_of_continuous_of_pos (ellGaussian_continuous hn hδ.le hh)
    (ellGaussian_nonneg hh) (ellGaussian_integrable hn hδ.le hσ hh) (x₀ := x₀) ?_
  rw [hh]
  exact mul_pos hellpos (Real.exp_pos _)

/-- **Non-vacuity for `Arlib.ellGaussian_integral_pos`.**  Every hypothesis of that theorem —
`n ≠ 0`, `0 < δ`, `0 < σ`, `Convex ℝ K`, `Bornology.IsBounded K`, `volume K ≠ 0` and the
defining equation for `h` — is discharged simultaneously at the concrete instance

  `n = 2`,  `K = B(0,1)`,  `δ = 1`,  `σ = 1`,

and the conclusion `0 < ∫ h` holds there.  So the hypothesis bundle is satisfiable and the
theorem is not vacuous.  (`volume K ≠ 0` is Mathlib's `measure_ball_pos`; the defining equation
is `rfl`.) -/
theorem ellGaussian_integral_pos_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ σ : ℝ) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      (2 : ℕ) ≠ 0 ∧ 0 < δ ∧ 0 < σ ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧
        (∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
        0 < ∫ x, h x := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin 2)) 1, 1, 1,
    fun x => (ell (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 x).toReal
      * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)),
    two_ne_zero, one_pos, one_pos, convex_ball _ _, isBounded_ball,
    (measure_ball_pos volume 0 one_pos).ne', fun _ => rfl, ?_⟩
  exact ellGaussian_integral_pos (n := 2) two_ne_zero one_pos one_pos (convex_ball _ _)
    isBounded_ball (measure_ball_pos volume 0 one_pos).ne' (fun _ => rfl)

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.ellGaussian_nonneg
#print axioms Arlib.ellGaussian_le_one
#print axioms Arlib.ellGaussian_continuous
#print axioms Arlib.ellGaussian_integrable
#print axioms Arlib.ellGaussian_integral_pos
#print axioms Arlib.ellGaussian_integral_pos_witness
