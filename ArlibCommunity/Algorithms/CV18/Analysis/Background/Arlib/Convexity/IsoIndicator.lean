/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoOpenClosed
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisGaussian

/-!
# `thm:iso` for the **indicator** density `1_K·e^{−‖x‖²/(2σ²)}`, with `S₁ S₂ S₃` merely measurable

`Arlib.gaussianRestricted_isoperimetry_openClosed` (`Arlib/Convexity/IsoOpenClosed.lean:854`)
proves Cousins–Vempala's `thm:iso` with **no** localization binder, but only for `S₁, S₂` **open**,
`S₃` **closed**, and `h` **continuous**.  The Metropolis-ball-walk consumer
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
(`Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean:278`) needs it at

    h = Set.indicator K (gaussianWeightReal (σ ^ 2)),   K a convex body,

which is **discontinuous**, and for `S₁ S₂ S₃` merely `MeasurableSet`.  This file closes both
gaps.

## Main results

* `Arlib.convexOn_infDist_of_convex`, `Arlib.isLogConcave_exp_neg_infDist` — the approximating
  family.  `x ↦ dist(x, C)` is convex for convex `C`, so `x ↦ e^{−c·dist(x,C)}` is **log-concave**
  — which is what the capstone asks of the cofactor `f`.  It is continuous, `≤ 1`, and decreases
  pointwise to `1_C`.
* `Arlib.norm_sub_ge_of_densDist_gaussianIndicator` — **(B), the crux.**  *Inside* `K` the density
  branch of the separation hypothesis is no longer satisfiable at distance zero: for `u, v ∈ K`,
  `4(d/σ)√n ≤ d_h(u,v)` forces `‖u − v‖ ≥ 4σd√n/R`, hence `≥ 2√3·d` as soon as
  `√3·R ≤ 2σ√n`.  This is exactly the mechanism
  `Arlib.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean:1205`) exploits,
  neutralised: there the touching set lies in `{h = 0}`, which for the *indicator* density is
  `Kᶜ` — and `Kᶜ` is precisely what intersecting `S₁, S₂` with `K` removes.
* `Arlib.norm_sub_ge_of_mem_thickening`,
  `Arlib.exists_disjoint_open_enlargement_gaussianIndicator` — **(B), landed.**  At any
  `d' < d` the `√3(d−d')`-thickenings of `S₁ ∩ K` and `S₂ ∩ K` are disjoint open supersets on
  which the *metric* branch holds **unconditionally**, at the threshold `2√3·d'`.
* `Arlib.tendsto_setIntegral_expNegInfDist_mul_gaussian` — **(A), landed.**  Dominated
  convergence: `∫_S e^{−j·dist(x,C)}·e^{−‖x‖²/(2σ²)} → ∫_S 1_C·e^{−‖x‖²/(2σ²)}`, the Gaussian
  being the dominating function.
* `Arlib.gaussianIndicator_isoperimetry_measurable` — **the deliverable.**  `thm:iso` at the sharp
  constant `d/σ` for `h = 1_K·e^{−‖x‖²/(2σ²)}` and `S₁ S₂ S₃` merely measurable.
* `Arlib.hiso_metropolisGaussian_sharp_sqrt` — the same, spelled in the consumer's own notation
  at `d = δ·log 2/√n`.
* `Arlib.gaussianIndicator_isoperimetry_measurable_witness` — non-vacuity: every hypothesis is met
  outright, with a strictly positive left-hand side.
* `Arlib.metric_threshold_lt_openClosed_threshold` — the one residual mismatch against the
  consumer's binder, machine-checked; see "What does not match" below.

## How the two gaps are closed — and why the trap does not fire

The brief's trap for (A) is that `d_h` moves the wrong way under continuous approximation: if
`u ∉ K` sits at distance `ε` from `v ∈ K`, then `d_h(u,v) = 1` for the indicator density (one of
the two values is `0`), while for the smoothed `h_j` both values are close and `d_h ≈ 0`.  So the
separation hypothesis does **not** transfer from `h` to `h_j`.

It is never asked to.  The two gaps are closed in the opposite order.  **(B) first:** replace
`S₁, S₂` by `S₁ ∩ K`, `S₂ ∩ K` — which changes **no integral at all**, since `h` vanishes off `K`
— and observe that on `K` the density branch does have metric content, because there `h` is the
*continuous, strictly positive* Gaussian.  That gives a genuine positive separation, hence
disjoint open thickenings `U₁, U₂` on which

    2√3·d' ≤ ‖u − v‖   for **every** `u ∈ U₁`, `v ∈ U₂`,

at any `d' < d`.  **(A) second:** the capstone is now applied to `U₁, U₂` with the *metric* branch
supplied unconditionally — `d_h_j` never appears — so any continuous `h_j` will do.  Take
`h_j = e^{−j·dist(x, closure K)}·e^{−‖x‖²/(2σ²)}` and let `j → ∞` in the conclusion, which is an
integral inequality; the Gaussian dominates.  Finally `d' ↑ d`.

The frontier is free: `volume (frontier K) = 0` for convex `K` (`Convex.addHaar_frontier`), so
`1_{closure K}·g` and `1_K·g` have the same integrals.

## What is assumed

**Nothing.**  There is no `def`, `structure`, `class` or `axiom` in this file; every declaration
is a `theorem`, and none of them takes a localization binder, `thm:iso`, or any part of either as
a hypothesis.

Two hypotheses beyond what the consumer already carries are used, and both are load-bearing:

* `hRσ : √3·R ≤ 2σ√n` — the body must fit inside the Gaussian's effective radius.  It is what
  turns the density branch into metric separation; `R ≤ σ√n` implies it (since `√3 ≤ 2`), and that
  is the regime `Arlib.MarkovChains.acceptance_factor_ge_of_step_le` calls feasible.  The
  consumer's own non-vacuity witness runs at `R = 1/2`, `σ = 16`, `n = 2`.  Without it the route
  still works, but only at the reduced constant `min(d, 4σd√n/(2√3·R))`.
* `hK0 : volume K ≠ 0`, used only to know `K` is nonempty.

## What does not match the consumer's binder, and why

The consumer's `hiso` states its **metric** branch at threshold `δ·log 2/√n / log 2`, i.e. `d/log 2`
with `d = δ·log 2/√n`.  Everything proved here — and everything provable in this repository —
states it at `2√3·d`.  This is **not** a defect of this file: it is the known `(1d-2)` constant
gap recorded at `AUDIT.md:192` and `CV-ROADMAP.md:240`.  `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`
(`Arlib/Convexity/ConcaveProfileIso.lean:631`) discharges `(1d-2)` at `1/(2√3) ≈ 0.289`, not
Cousins–Vempala's `ln 2 ≈ 0.693`, so the separation threshold is larger by `2√3·ln 2 ≈ 2.401`.
`Arlib.metric_threshold_lt_openClosed_threshold` records the direction machine-checked:
`d/log 2 < 2√3·d` for `d > 0`, so the consumer's hypothesis is **strictly weaker** than the one
discharged here and cannot simply be `exact`-ed.  Closing that last gap means improving the
one-dimensional constant, which is a statement about `(1d-2)`, not about the indicator density.
Nothing here shows the consumer's binder is *false*.
-/

open MeasureTheory Set Filter Metric

open Arlib.MarkovChains

open scoped ENNReal Topology

namespace Arlib

/-! ### The continuous log-concave outer approximation of an indicator -/

section InfDist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`x ↦ dist(x, C)` is a convex function when `C` is convex.**

Mathlib has convexity of the norm and of `dist` in each variable separately, but not of the
distance to a convex *set*.  With `C` compact and nonempty the infimum is attained
(`IsCompact.exists_infDist_eq_dist`), so no `ε`-argument is needed: pick minimisers `p, q` for
`x, y`, note `a•p + b•q ∈ C`, and bound `‖a•(x−p) + b•(y−q)‖`. -/
theorem convexOn_infDist_of_convex {C : Set E} (hC : Convex ℝ C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) :
    ConvexOn ℝ (Set.univ : Set E) (fun x => Metric.infDist x C) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨p, hp, hxp⟩ := hCcomp.exists_infDist_eq_dist hCne x
  obtain ⟨q, hq, hyq⟩ := hCcomp.exists_infDist_eq_dist hCne y
  have hmem : a • p + b • q ∈ C := hC hp hq ha hb hab
  have hle : Metric.infDist (a • x + b • y) C ≤ dist (a • x + b • y) (a • p + b • q) :=
    Metric.infDist_le_dist_of_mem hmem
  have hd : dist (a • x + b • y) (a • p + b • q) ≤ a * dist x p + b * dist y q := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    have hrw : a • x + b • y - (a • p + b • q) = a • (x - p) + b • (y - q) := by
      module
    rw [hrw]
    calc ‖a • (x - p) + b • (y - q)‖ ≤ ‖a • (x - p)‖ + ‖b • (y - q)‖ := norm_add_le _ _
      _ = a * ‖x - p‖ + b * ‖y - q‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
  simp only [smul_eq_mul]
  rw [hxp, hyq]
  linarith

/-- **`x ↦ e^{−c·dist(x, C)}` is log-concave** for `c ≥ 0` and `C` a convex body.

This is the continuous outer approximation of `1_C` used below.  It decreases pointwise to `1_C`
as `c → ∞`, is bounded by `1`, and — the point — is log-concave, which is what
`Arlib.gaussianRestricted_isoperimetry_openClosed` asks of the cofactor `f`. -/
theorem isLogConcave_exp_neg_infDist {C : Set E} (hC : Convex ℝ C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) {c : ℝ} (hc : 0 ≤ c) :
    IsLogConcave (fun x : E => Real.exp (-(c * Metric.infDist x C))) := by
  have hconv : ConvexOn ℝ (Set.univ : Set E) (fun x => c * Metric.infDist x C) := by
    simpa only [smul_eq_mul] using (convexOn_infDist_of_convex hC hCcomp hCne).smul hc
  exact isLogConcave_exp hconv.neg

end InfDist

/-! ### (B) On `K`, the density branch forces genuine metric separation -/

section Separation

variable {n : ℕ}

/-- `1 − e^{−s} ≤ s`, from `s + 1 ≤ e^s` at `−s`. -/
theorem one_sub_exp_neg_le (s : ℝ) : 1 - Real.exp (-s) ≤ s := by
  have h := Real.add_one_le_exp (-s)
  linarith

/-- **The `densDist` of a Gaussian weight is at most the normalised gap of the exponents**, in the
ordered case `A ≤ B`.

`d(e^{−A/c}, e^{−B/c}) = 1 − e^{−(B−A)/c} ≤ (B−A)/c`. -/
theorem densDist_exp_div_le_of_le {c A B : ℝ} (hc : 0 < c) (hAB : A ≤ B) :
    |Real.exp (-A / c) - Real.exp (-B / c)| /
        max (Real.exp (-A / c)) (Real.exp (-B / c)) ≤ (B - A) / c := by
  have hxpos : (0 : ℝ) < Real.exp (-A / c) := Real.exp_pos _
  have hypos : (0 : ℝ) < Real.exp (-B / c) := Real.exp_pos _
  have hcne : c ≠ 0 := ne_of_gt hc
  have hexp : -B / c ≤ -A / c := by
    rw [div_le_iff₀ hc, div_mul_cancel₀ (-A) hcne]
    linarith
  have hyx : Real.exp (-B / c) ≤ Real.exp (-A / c) := Real.exp_le_exp.mpr hexp
  rw [max_eq_left hyx, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-A / c) - Real.exp (-B / c))]
  have hratio : Real.exp (-B / c) / Real.exp (-A / c) = Real.exp (-((B - A) / c)) := by
    rw [← Real.exp_sub]
    congr 1
    field_simp
    ring
  have hxne : Real.exp (-A / c) ≠ 0 := ne_of_gt hxpos
  have hsplit : (Real.exp (-A / c) - Real.exp (-B / c)) / Real.exp (-A / c)
      = 1 - Real.exp (-B / c) / Real.exp (-A / c) := by
    field_simp
  rw [hsplit, hratio]
  exact one_sub_exp_neg_le _

/-- **The `densDist` of a Gaussian weight is at most the normalised gap of the exponents.** -/
theorem densDist_exp_div_le {c A B : ℝ} (hc : 0 < c) :
    |Real.exp (-A / c) - Real.exp (-B / c)| /
        max (Real.exp (-A / c)) (Real.exp (-B / c)) ≤ |A - B| / c := by
  rcases le_total A B with h | h
  · rw [abs_of_nonpos (by linarith : A - B ≤ 0)]
    have := densDist_exp_div_le_of_le hc h
    have hrw : -(A - B) = B - A := by ring
    rw [hrw]
    exact this
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ A - B)]
    have h2 := densDist_exp_div_le_of_le hc h
    rwa [abs_sub_comm, max_comm] at h2

/-- **(B), the crux.  Inside `K` the density branch of the separation hypothesis has metric
content.**

`Arlib.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean:1205`) refutes the
uniform open-enlargement mechanism by exploiting the fact that `d_h(u,v) = 1` whenever exactly one
of `h u, h v` vanishes — so the density branch is satisfied at **distance zero** on `{h = 0}`.
For `h = 1_K·e^{−‖x‖²/(2σ²)}` the set `{h = 0}` is exactly `Kᶜ`, and on `K` itself `h` is the
Gaussian: continuous and strictly positive.  There the density branch reads

    4(d/σ)√n ≤ 1 − e^{−|‖u‖²−‖v‖²|/(2σ²)} ≤ |‖u‖²−‖v‖²|/(2σ²) ≤ 2R‖u − v‖/(2σ²),

so `‖u − v‖ ≥ 4σd√n/R`, which is at least `2√3·d` exactly when `√3·R ≤ 2σ√n`.

`R > 0` is not assumed: `u ≠ v` (they lie in disjoint parts) forces `0 < ‖u − v‖ ≤ 2R`. -/
theorem norm_sub_ge_of_densDist_gaussianIndicator {σ d R : ℝ} (hσ : 0 < σ) (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v)
    (hdens : 4 * (d / σ) * Real.sqrt n
      ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) :
    2 * Real.sqrt 3 * d ≤ ‖u - v‖ := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by
    have := pow_pos hσ 2
    linarith
  -- `R > 0`
  have hpos : 0 < ‖u - v‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hnormle : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
  have hR0 : 0 < R := by
    have h1 := hKR u hu
    have h2 := hKR v hv
    linarith
  -- the indicator equals the weight at `u` and `v`
  have hdd : densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v
      = |Real.exp (-‖u‖ ^ 2 / (2 * σ ^ 2)) - Real.exp (-‖v‖ ^ 2 / (2 * σ ^ 2))| /
          max (Real.exp (-‖u‖ ^ 2 / (2 * σ ^ 2))) (Real.exp (-‖v‖ ^ 2 / (2 * σ ^ 2))) := by
    rw [densDist, Set.indicator_of_mem hu, Set.indicator_of_mem hv, gaussianWeightReal,
      gaussianWeightReal]
  rw [hdd] at hdens
  have hbound := densDist_exp_div_le (c := 2 * σ ^ 2) (A := ‖u‖ ^ 2) (B := ‖v‖ ^ 2) hσ2
  have hstep : 4 * (d / σ) * Real.sqrt n ≤ |‖u‖ ^ 2 - ‖v‖ ^ 2| / (2 * σ ^ 2) :=
    le_trans hdens hbound
  rw [le_div_iff₀ hσ2] at hstep
  -- `4(d/σ)√n·2σ² = 8σd√n`
  have hlhs : 4 * (d / σ) * Real.sqrt n * (2 * σ ^ 2) = 8 * σ * d * Real.sqrt n := by
    field_simp
    ring
  rw [hlhs] at hstep
  -- `|‖u‖² − ‖v‖²| ≤ 2R‖u − v‖`
  have hgap : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * R * ‖u - v‖ := by
    have hfac : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖ + ‖v‖)]
    have h1 : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
    have h2 : ‖u‖ + ‖v‖ ≤ 2 * R := by
      have := hKR u hu
      have := hKR v hv
      linarith
    calc |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) ≤ ‖u - v‖ * (2 * R) :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
      _ = 2 * R * ‖u - v‖ := by ring
  -- combine with `√3·R ≤ 2σ√n`
  have hchain : 4 * Real.sqrt 3 * d * R ≤ 8 * σ * d * Real.sqrt n := by
    have h4d : (0:ℝ) ≤ 4 * d := by linarith
    have hdiff : (0:ℝ) ≤ 2 * σ * Real.sqrt n - Real.sqrt 3 * R := by linarith
    nlinarith [mul_nonneg h4d hdiff]
  have hfinal : 4 * Real.sqrt 3 * d * R ≤ 2 * R * ‖u - v‖ := by linarith
  by_contra hlt
  rw [not_le] at hlt
  have hmul := mul_lt_mul_of_pos_left hlt hR0
  nlinarith [hmul, hfinal]

/-- **Thickening degrades a metric separation by at most twice the radius.** -/
theorem norm_sub_ge_of_mem_thickening {E : Type*} [NormedAddCommGroup E]
    {A₁ A₂ : Set E} {D ρ : ℝ} (hsep : ∀ u ∈ A₁, ∀ v ∈ A₂, D ≤ ‖u - v‖)
    {u v : E} (hu : u ∈ Metric.thickening ρ A₁) (hv : v ∈ Metric.thickening ρ A₂) :
    D - 2 * ρ ≤ ‖u - v‖ := by
  obtain ⟨p, hp, hup⟩ := Metric.mem_thickening_iff.mp hu
  obtain ⟨q, hq, hvq⟩ := Metric.mem_thickening_iff.mp hv
  rw [dist_eq_norm] at hup hvq
  have hpq := hsep p hp q hq
  have hsplit : p - q = (p - u) + (u - v) + (v - q) := by abel
  have h1 : ‖p - q‖ ≤ ‖p - u‖ + ‖u - v‖ + ‖v - q‖ := by
    rw [hsplit]
    exact le_trans (norm_add_le _ _)
      (by linarith [norm_add_le (p - u) (u - v)])
  have h2 : ‖p - u‖ = ‖u - p‖ := norm_sub_rev _ _
  have h3 : ‖v - q‖ = ‖v - q‖ := rfl
  rw [h2] at h1
  linarith

end Separation

/-! ### (A) Dominated convergence for the continuous outer approximations -/

section Approximation

variable {n : ℕ}

/-- The Gaussian weight is integrable on `EuclideanSpace ℝ (Fin n)`. -/
theorem integrable_gaussianWeightReal {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) := by
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x)
      = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * σ ^ 2)) := by
    funext x
    rw [gaussianWeightReal]
  rw [heq]
  exact Arlib.GaussianCooling.integrable_gaussian_eucl (pow_pos hσ 2)

/-- **(A), landed.**  The continuous outer approximations converge in every set integral.

`e^{−j·dist(x,C)}` decreases pointwise to `1_C` (`C` closed and nonempty), so
`e^{−j·dist(x,C)}·e^{−‖x‖²/(2σ²)}` converges pointwise to `1_C·e^{−‖x‖²/(2σ²)}` dominated by the
Gaussian itself.  No hypothesis about `S` beyond nothing at all: the statement is an identity of
limits of integrals over the restricted measure. -/
theorem tendsto_setIntegral_expNegInfDist_mul_gaussian {σ : ℝ} (hσ : 0 < σ)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCcl : IsClosed C) (hCne : C.Nonempty)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun j : ℕ => ∫ x in S,
        Real.exp (-((j : ℝ) * Metric.infDist x C)) * gaussianWeightReal (σ ^ 2) x)
      atTop (𝓝 (∫ x in S, Set.indicator C (gaussianWeightReal (σ ^ 2)) x)) := by
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hcInf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x C) :=
    Metric.continuous_infDist_pt C
  have hInf0 : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ Metric.infDist x C :=
    fun x => Metric.infDist_nonneg
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => gaussianWeightReal (σ ^ 2) x) (fun j => ?_) hgi.restrict (fun j => ?_) ?_
  · exact ((Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)).mul
      (continuous_gaussianWeightReal _)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hle : Real.exp (-((j : ℝ) * Metric.infDist x C)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (Nat.cast_nonneg j) (hInf0 x)
    have h0 : 0 < Real.exp (-((j : ℝ) * Metric.infDist x C)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0.le (hgpos x).le)]
    nlinarith [hgpos x]
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ C
    · have hz : Metric.infDist x C = 0 := Metric.infDist_zero_of_mem hx
      rw [Set.indicator_of_mem hx]
      simp only [hz, mul_zero, neg_zero, Real.exp_zero, one_mul]
      exact tendsto_const_nhds
    · have hz : 0 < Metric.infDist x C := (hCcl.notMem_iff_infDist_pos hCne).mp hx
      rw [Set.indicator_of_notMem hx]
      have hbot : Tendsto (fun j : ℕ => -((j : ℝ) * Metric.infDist x C)) atTop atBot := by
        have h1 : Tendsto (fun j : ℕ => (j : ℝ) * Metric.infDist x C) atTop atTop :=
          Filter.Tendsto.atTop_mul_const hz tendsto_natCast_atTop_atTop
        exact tendsto_neg_atTop_atBot.comp h1
      have h2 : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) * Metric.infDist x C))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hbot
      simpa using h2.mul_const (gaussianWeightReal (σ ^ 2) x)

/-- **The frontier of a convex body is Lebesgue-null**, so `1_{closure K}` and `1_K` have the same
set integrals.  (`Convex.addHaar_frontier`.) -/
theorem setIntegral_indicator_closure_eq {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (S : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in S, Set.indicator (closure K) g x) = ∫ x in S, Set.indicator K g x := by
  refine integral_congr_ae (Filter.EventuallyEq.restrict ?_)
  have hnull : volume (frontier K) = 0 := hKc.addHaar_frontier volume
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∉ frontier K := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  filter_upwards [hae] with x hx
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem (subset_closure hxK), Set.indicator_of_mem hxK]
  · rw [Set.indicator_of_notMem hxK]
    refine Set.indicator_of_notMem ?_ _
    intro hxc
    exact hx ⟨hxc, fun hint => hxK (interior_subset hint)⟩

end Approximation

/-! ### (B), landed: disjoint open enlargements at any strictly smaller `d` -/

section Enlargement

variable {n : ℕ}

/-- **(B), landed.**

Given the separation hypothesis at `d > 0` for the indicator density and `√3·R ≤ 2σ√n`, the
`√3(d−d')`-thickenings of `S₁ ∩ K` and `S₂ ∩ K` are **disjoint open** supersets of them on which
the *metric* branch holds for **every** pair, at the threshold `2√3·d'`.

This is the exact converse of `Arlib.exists_separated_no_disjoint_open_enlargement`: there `S₁`
and `S₂` touch, and they touch inside `{h = 0}`.  Intersecting with `K` deletes `{h = 0}` — and
deletes no mass, since `h` vanishes there — after which the density branch is no longer free. -/
theorem exists_disjoint_open_enlargement_gaussianIndicator {σ d d' R : ℝ} (hσ : 0 < σ)
    (hd : 0 < d) (hd'0 : 0 < d') (hd'd : d' < d)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin n))} (hdisj : Disjoint S₁ S₂)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ S₁ ∩ K ⊆ U₁ ∧ S₂ ∩ K ⊆ U₂ ∧
        ∀ u ∈ U₁, ∀ v ∈ U₂, 2 * Real.sqrt 3 * d' ≤ ‖u - v‖ := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- the cores are genuinely separated
  have hAsep : ∀ u ∈ S₁ ∩ K, ∀ v ∈ S₂ ∩ K, 2 * Real.sqrt 3 * d ≤ ‖u - v‖ := by
    intro u hu v hv
    rcases hsep u hu.1 v hv.1 with hmetric | hdens
    · exact hmetric
    · refine norm_sub_ge_of_densDist_gaussianIndicator hσ hd hKR hRσ hu.2 hv.2 ?_ hdens
      rintro rfl
      exact (Set.disjoint_left.mp hdisj hu.1) hv.1
  set ρ : ℝ := Real.sqrt 3 * (d - d') with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact mul_pos hs3 (by linarith)
  refine ⟨Metric.thickening ρ (S₁ ∩ K), Metric.thickening ρ (S₂ ∩ K),
    Metric.isOpen_thickening, Metric.isOpen_thickening, ?_,
    Metric.self_subset_thickening hρ _, Metric.self_subset_thickening hρ _, ?_⟩
  · rw [Set.disjoint_left]
    intro a ha hb
    have hcontr := norm_sub_ge_of_mem_thickening hAsep ha hb
    rw [sub_self, norm_zero] at hcontr
    have harith : 2 * Real.sqrt 3 * d - 2 * ρ = 2 * Real.sqrt 3 * d' := by
      rw [hρdef]; ring
    rw [harith] at hcontr
    have : 0 < 2 * Real.sqrt 3 * d' := by positivity
    linarith
  · intro u hu v hv
    have hcontr := norm_sub_ge_of_mem_thickening hAsep hu hv
    have harith : 2 * Real.sqrt 3 * d - 2 * ρ = 2 * Real.sqrt 3 * d' := by
      rw [hρdef]; ring
    rw [harith] at hcontr
    exact hcontr

end Enlargement

/-! ### The deliverable -/

section Main

variable {n : ℕ}

/-- **`thm:iso` for the indicator density `1_K·e^{−‖x‖²/(2σ²)}`, with `S₁ S₂ S₃` merely
measurable.**

This is `Arlib.gaussianRestricted_isoperimetry_openClosed` with both of its topological
restrictions removed at the density the Metropolis-ball-walk consumer actually carries: `h` is the
**discontinuous** indicator density, and `S₁, S₂, S₃` are only `MeasurableSet`.

The two extra hypotheses are `hRσ : √3·R ≤ 2σ√n` (implied by `R ≤ σ√n`, since `√3 ≤ 2`) and
`hK0 : volume K ≠ 0` (used only for `K.Nonempty`); see the module docstring.

**Proof outline.**  `h` vanishes off `K`, so intersecting `S₁, S₂` with `K` changes no integral,
and on `K` the density branch has metric content
(`Arlib.norm_sub_ge_of_densDist_gaussianIndicator`).  At any `d' < d` this yields disjoint open
`U₁ ⊇ S₁ ∩ K`, `U₂ ⊇ S₂ ∩ K` with `2√3·d' ≤ ‖u − v‖` for **all** pairs
(`Arlib.exists_disjoint_open_enlargement_gaussianIndicator`), so the capstone applies to `U₁, U₂,
(U₁ ∪ U₂)ᶜ` and any continuous log-concave-cofactored density — in particular to
`h_j = e^{−j·dist(x, closure K)}·e^{−‖x‖²/(2σ²)}`, whose separation hypothesis is supplied by the
*metric* branch alone, so that `densDist h_j` never has to be compared with `densDist h`.
Let `j → ∞` (dominated convergence), then `d' ↑ d`. -/
theorem gaussianIndicator_isoperimetry_measurable (hn : 2 ≤ n) {σ d R : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (_hS₂ : MeasurableSet S₂) (_hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) :
    d / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
      ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
  classical
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hσsq : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hh0 : ∀ x, 0 ≤ Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    fun x => Set.indicator_nonneg (fun y _ => (hgpos y).le) x
  have hhi : Integrable (Set.indicator K (gaussianWeightReal (σ ^ 2))) := hgi.indicator hK
  have hm₁ : 0 ≤ ∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hm₂ : 0 ≤ ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hm₃ : 0 ≤ ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  have hM : 0 ≤ ∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
    integral_nonneg fun x => hh0 x
  rcases le_or_gt d 0 with hdle | hd
  · have hds : d / σ ≤ 0 := by
      rw [div_le_iff₀ hσ]
      linarith
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hds (mul_nonneg hm₁ hm₂))
      (mul_nonneg hM hm₃)
  -- from here `0 < d`
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hEq
    rw [hEq] at hK0
    exact hK0 measure_empty
  -- `closure K`: compact, convex, nonempty
  have hCne : (closure K).Nonempty := hKne.closure
  have hCconv : Convex ℝ (closure K) := hKc.closure
  have hCbdd : Bornology.IsBounded (closure K) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := R)).subset ?_
    refine (closure_minimal ?_ Metric.isClosed_closedBall)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hCcomp : IsCompact (closure K) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hCbdd
  -- `(S₁ ∪ S₂)ᶜ = S₃`
  have hS₃eq : (S₁ ∪ S₂)ᶜ = S₃ := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      have hmem : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; trivial
      rcases hmem with (h1 | h2) | h3
      · exact absurd (Or.inl h1) hx
      · exact absurd (Or.inr h2) hx
      · exact h3
    · intro x hx hmem
      rcases hmem with h1 | h2
      · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) hx
      · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) hx
  -- the main estimate, for every `d' ∈ (0, d)`
  have key : ∀ d' : ℝ, 0 < d' → d' < d →
      d' / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
    intro d' hd'0 hd'd
    obtain ⟨U₁, U₂, hU₁, hU₂, hUdisj, hsub₁, hsub₂, hUsep⟩ :=
      exists_disjoint_open_enlargement_gaussianIndicator hσ hd hd'0 hd'd hKR hRσ
        hpart.disjoint₁₂ hsep
    -- the capstone, applied to the continuous approximations on `U₁, U₂, (U₁ ∪ U₂)ᶜ`
    have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
      { union := Set.union_compl_self (U₁ ∪ U₂)
        disjoint₁₂ := hUdisj
        disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
        disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
    have hcap : ∀ j : ℕ,
        d' / σ * ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
          ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x := by
      intro j
      have hcInf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x (closure K)) :=
        Metric.continuous_infDist_pt _
      have hfc : Continuous
          (fun x : EuclideanSpace ℝ (Fin n) =>
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))) :=
        Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)
      have hjc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x) :=
        hfc.mul (continuous_gaussianWeightReal _)
      have hf1 : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) ≤ 1 := by
        intro x
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
      have hf0 : ∀ x : EuclideanSpace ℝ (Fin n),
          0 < Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := fun x => Real.exp_pos _
      have hjB : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x ≤ 1 := by
        intro x
        have h1 := hf1 x
        have h2 : gaussianWeightReal (σ ^ 2) x ≤ 1 :=
          gaussianWeightReal_le_one hσsq x
        nlinarith [hf0 x, hgpos x]
      have hji : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x) := by
        refine hgi.mono' hjc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x).le (hgpos x).le)]
        nlinarith [hf1 x, hf0 x, hgpos x]
      have hjmass : 0 < ∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
          * gaussianWeightReal (σ ^ 2) x := by
        obtain ⟨z₀, hz₀⟩ := hCne
        have hz₀R : ‖z₀‖ ≤ R := by
          have hsub : closure K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
            refine closure_minimal ?_ Metric.isClosed_closedBall
            intro x hx
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hKR x hx
          have := hsub hz₀
          rwa [Metric.mem_closedBall, dist_zero_right] at this
        have hlow : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            Real.exp (-((j : ℝ) * (1 + R))) * Real.exp (-(1 : ℝ) / (2 * σ ^ 2))
              ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
                * gaussianWeightReal (σ ^ 2) x := by
          intro x hx
          rw [Metric.mem_ball, dist_zero_right] at hx
          have hdist : Metric.infDist x (closure K) ≤ 1 + R := by
            refine le_trans (Metric.infDist_le_dist_of_mem hz₀) ?_
            rw [dist_eq_norm]
            have := norm_sub_le x z₀
            linarith
          have h1 : Real.exp (-((j : ℝ) * (1 + R)))
              ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := by
            refine Real.exp_le_exp.mpr ?_
            have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            nlinarith
          have h2 : Real.exp (-(1 : ℝ) / (2 * σ ^ 2)) ≤ gaussianWeightReal (σ ^ 2) x := by
            rw [gaussianWeightReal]
            refine Real.exp_le_exp.mpr ?_
            have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
            have hpos2 : (0 : ℝ) < 2 * σ ^ 2 := by linarith
            rw [div_le_iff₀ hpos2, div_mul_cancel₀ (-(‖x‖ ^ 2)) (ne_of_gt hpos2)]
            linarith
          have h3 : (0 : ℝ) < Real.exp (-((j : ℝ) * (1 + R))) := Real.exp_pos _
          have h4 : (0 : ℝ) < Real.exp (-(1 : ℝ) / (2 * σ ^ 2)) := Real.exp_pos _
          exact mul_le_mul h1 h2 h4.le (hf0 x).le
        have hpos := setIntegral_pos_of_ball_le (g := fun x =>
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x)
          hji (fun x => mul_nonneg (hf0 x).le (hgpos x).le) (S := Set.univ)
          (z := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
          (c := Real.exp (-((j : ℝ) * (1 + R))) * Real.exp (-(1 : ℝ) / (2 * σ ^ 2)))
          one_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Set.subset_univ _) hlow
        rwa [setIntegral_univ] at hpos
      exact gaussianRestricted_isoperimetry_openClosed hn hσ
        (f := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))))
        (h := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
          * gaussianWeightReal (σ ^ 2) x)
        (B := 1)
        (fun x => (hf0 x).le)
        (isLogConcave_exp_neg_infDist hCconv hCcomp hCne (Nat.cast_nonneg j))
        (fun x => rfl) hjc hjB hji hpart' hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hjmass
        (fun u hu v hv => Or.inl (hUsep u hu v hv))
    -- pass to the limit `j → ∞`
    have hlim : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        Tendsto (fun j : ℕ => ∫ x in S,
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * gaussianWeightReal (σ ^ 2) x)
          atTop (𝓝 (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) := by
      intro S
      have h := tendsto_setIntegral_expNegInfDist_mul_gaussian (n := n) hσ
        (C := closure K) isClosed_closure hCne S
      rwa [setIntegral_indicator_closure_eq hKc _ S] at h
    have hlimU : Tendsto (fun j : ℕ => ∫ x,
        Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * gaussianWeightReal (σ ^ 2) x)
        atTop (𝓝 (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) := by
      have h := hlim Set.univ
      simpa only [MeasureTheory.setIntegral_univ] using h
    have hLHS : Tendsto (fun j : ℕ => d' / σ *
        ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)) atTop
        (𝓝 (d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x))) :=
      ((hlim U₁).mul (hlim U₂)).const_mul (d' / σ)
    have hRHS : Tendsto (fun j : ℕ =>
        (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
            * gaussianWeightReal (σ ^ 2) x) atTop
        (𝓝 ((∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)) :=
      hlimU.mul (hlim _)
    have hUineq : d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
      le_of_tendsto_of_tendsto' hLHS hRHS hcap
    -- monotonicity back to `S₁, S₂, S₃`
    have hcut : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          = ∫ x in S ∩ K, gaussianWeightReal (σ ^ 2) x := fun S => setIntegral_indicator hK
    have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
        (∫ x in S, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          ≤ ∫ x in T, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      intro S T hST
      exact setIntegral_mono_set hhi.integrableOn
        (Filter.Eventually.of_forall hh0) hST.eventuallyLE
    have hcore₁ : (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₁ ∩ K, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut S₁, hcut (S₁ ∩ K), Set.inter_assoc, Set.inter_self]
    have hcore₂ : (∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₂ ∩ K, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut S₂, hcut (S₂ ∩ K), Set.inter_assoc, Set.inter_self]
    have hsetiii : ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ ∩ K = S₃ ∩ K := by
      ext x
      constructor
      · rintro ⟨hnot, hxK⟩
        refine ⟨?_, hxK⟩
        rw [← hS₃eq]
        intro hmem
        rcases hmem with h1 | h2
        · exact hnot (Or.inl ⟨h1, hxK⟩)
        · exact hnot (Or.inr ⟨h2, hxK⟩)
      · rintro ⟨h3, hxK⟩
        refine ⟨?_, hxK⟩
        rintro (⟨h1, -⟩ | ⟨h2, -⟩)
        · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) h3
        · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) h3
    have hcore₃ : (∫ x in ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ,
          Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        = ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcut _, hcut S₃, hsetiii]
    have hU₃sub : (U₁ ∪ U₂)ᶜ ⊆ ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ := by
      refine Set.compl_subset_compl.mpr ?_
      exact Set.union_subset_union hsub₁ hsub₂
    have hle₁ : (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcore₁]; exact hmono hsub₁
    have hle₂ : (∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [hcore₂]; exact hmono hsub₂
    have hle₃ : (∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := by
      rw [← hcore₃]; exact hmono hU₃sub
    have hd'σ : 0 ≤ d' / σ := (div_pos hd'0 hσ).le
    calc d' / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ d' / σ * ((∫ x in U₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in U₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hle₁ hle₂ hm₂ (le_trans hm₁ hle₁)) hd'σ
      _ ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Set.indicator K (gaussianWeightReal (σ ^ 2)) x := hUineq
      _ ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
          mul_le_mul_of_nonneg_left hle₃ hM
  -- let `d' ↑ d`
  by_contra hcon
  rw [not_le] at hcon
  set P : ℝ := (∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x with hPdef
  set Q : ℝ := (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
    * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x with hQdef
  have hQ0 : 0 ≤ Q := mul_nonneg hM hm₃
  have hPnn : 0 ≤ P := mul_nonneg hm₁ hm₂
  have hP : 0 < P := by
    rcases hPnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, mul_zero] at hcon
      linarith
  have hcd : σ * Q / P < d := by
    rw [div_lt_iff₀ hP]
    have hstep : Q * σ < d / σ * P * σ := mul_lt_mul_of_pos_right hcon hσ
    have hrw : d / σ * P * σ = d * P := by field_simp
    rw [hrw] at hstep
    linarith
  set d' : ℝ := (max (σ * Q / P) (d / 2) + d) / 2 with hd'def
  have hmaxlt : max (σ * Q / P) (d / 2) < d := max_lt hcd (by linarith)
  have hd'lt : d' < d := by rw [hd'def]; linarith
  have hd'gt : max (σ * Q / P) (d / 2) < d' := by rw [hd'def]; linarith
  have hhalf : d / 2 < d' := lt_of_le_of_lt (le_max_right _ _) hd'gt
  have hd'pos : 0 < d' := by linarith
  have hcc : σ * Q / P < d' := lt_of_le_of_lt (le_max_left _ _) hd'gt
  rw [div_lt_iff₀ hP] at hcc
  have hkey := key d' hd'pos hd'lt
  have hstep2 : d' / σ * P * σ ≤ Q * σ := mul_le_mul_of_nonneg_right hkey hσ.le
  have hrw2 : d' / σ * P * σ = d' * P := by field_simp
  rw [hrw2] at hstep2
  linarith

end Main

/-! ### The consumer's shape, and the one residual mismatch -/

section Consumer

variable {n : ℕ}

/-- **The mismatch against the consumer's binder, machine-checked.**

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge` states the *metric* branch of
its `hiso` binder at threshold `d / log 2`; everything provable in this repository states it at
`2√3·d`, and `d/log 2 < 2√3·d` for `d > 0`.  So the consumer's separation hypothesis is
**strictly weaker** than the one discharged here and cannot be `exact`-ed into it.

This is the `(1d-2)` constant gap already recorded at `AUDIT.md:192` and `CV-ROADMAP.md:240`:
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` proves `(1d-2)` at `1/(2√3) ≈ 0.289`,
not Cousins–Vempala's `ln 2 ≈ 0.693`.  It has nothing to do with the indicator density; nothing
here shows the consumer's binder is false. -/
theorem metric_threshold_lt_openClosed_threshold {d : ℝ} (hd : 0 < d) :
    d / Real.log 2 < 2 * Real.sqrt 3 * d := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h : Real.log (2:ℝ)⁻¹ ≤ (2:ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_inv] at h
    linarith
  have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
  have hs3 : (1.7 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  rw [div_lt_iff₀ hlogpos]
  have h2 : (0 : ℝ) < 2 * (Real.sqrt 3 * Real.log 2) - 1 := by nlinarith
  nlinarith [mul_pos hd h2]

/-- **`hiso` for the Metropolis-filtered Gaussian ball walk, in the consumer's own notation.**

This is the binder of `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`
(`Arlib/MarkovChains/Continuous/MetropolisOverlapSqrt.lean:284`) at `d = δ·log 2/√n`, verbatim,
with exactly **one** subterm changed: the metric branch reads `2√3·(δ·log 2/√n)` where the
consumer writes `δ·log 2/√n / log 2`.  Everything else — the partition, the measurability
hypotheses, the density branch `4(δ·log 2/√n/σ)√n ≤ d_h(u,v)`, and the conclusion
`(δ·log 2/√n/σ)·π(S₁)π(S₂) ≤ π(1)·π(S₃)` at `h = 1_K·gaussianWeightReal σ²` — is character for
character the consumer's.

`Arlib.metric_threshold_lt_openClosed_threshold` records that the two thresholds are genuinely
different and in which direction; see the module docstring.  `hKtop` is accepted and unused, so
that the argument list is the one the consumer has to hand. -/
theorem hiso_metropolisGaussian_sharp_sqrt (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (_hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n) :
    ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * (δ * Real.log 2 / Real.sqrt n) ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x :=
  fun _S₁ _S₂ _S₃ hpart hS₁ hS₂ hS₃ hsep =>
    gaussianIndicator_isoperimetry_measurable hn hσ hK hKc hKR hK0 hRσ hpart hS₁ hS₂ hS₃ hsep

end Consumer

/-! ### Non-vacuity -/

section Witness

variable {n : ℕ}

/-- **Non-vacuity for `Arlib.gaussianIndicator_isoperimetry_measurable`.**

Every hypothesis is satisfied outright — not vacuously — at data whose left-hand side is
*strictly positive*, so the theorem is not the trivial `0 ≤ something`:

  `K = closedBall 0 (1/2)`, `σ = 1`, `R = 1/2`, `d = 1/32`,
  `S₁ = {⟪e,x⟫ < −1/8}`, `S₂ = {1/8 < ⟪e,x⟫}`, `S₃` the closed slab between them.

`hRσ` reads `√3/2 ≤ 2√n`, true since `√3 ≤ 2 ≤ 2√n` for `n ≥ 2`; the separation fires on the
*metric* branch, `2√3·(1/32) ≤ 1/4 ≤ ‖u − v‖`, using `√3 ≤ 4`.  The two masses are positive
because balls of radius `1/16` about `∓(1/4)e` lie inside `K ∩ S₁` and `K ∩ S₂`, where the
Gaussian is at least `e^{−1/2}`.

The two clauses `(S₁ ∩ K).Nonempty`, `(S₂ ∩ K).Nonempty` are there so that the (B) step is not
vacuous on this data: the sets that
`Arlib.exists_disjoint_open_enlargement_gaussianIndicator` separates and thickens really do have
points (`∓(1/4)·e`), so the disjoint open enlargement it produces is a statement about two
*nonempty* sets, not about `∅` riding through `Metric.thickening_empty`. -/
theorem gaussianIndicator_isoperimetry_measurable_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d R : ℝ),
      0 < σ ∧ 0 < d ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
      Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨
          4 * (d / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) ∧
      (S₁ ∩ K).Nonempty ∧ (S₂ ∩ K).Nonempty ∧
      0 < d / σ * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (1/2) with hKdef
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1/2 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0:ℝ) < 1/2))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hsn : (1 : ℝ) ≤ Real.sqrt n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1
  have hRσ : Real.sqrt 3 * (1/2 : ℝ) ≤ 2 * (1 : ℝ) * Real.sqrt n := by nlinarith
  -- the slab partition
  have hme : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | inner ℝ e x < -(1/8 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1/8 : ℝ) < inner ℝ e x} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | -(1/8 : ℝ) ≤ inner ℝ e x ∧ (inner ℝ e x : ℝ) ≤ 1/8} with hS₃def
  have hS₁meas : MeasurableSet S₁ := (isOpen_lt hme continuous_const).measurableSet
  have hS₂meas : MeasurableSet S₂ := (isOpen_lt continuous_const hme).measurableSet
  have hS₃meas : MeasurableSet S₃ :=
    ((isClosed_le continuous_const hme).inter (isClosed_le hme continuous_const)).measurableSet
  -- the indicator density
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal ((1:ℝ) ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal ((1:ℝ) ^ 2) x) :=
    integrable_gaussianWeightReal one_pos
  have hhi : Integrable (Set.indicator K (gaussianWeightReal ((1:ℝ) ^ 2))) :=
    hgi.indicator hKmeas
  have hh0 : ∀ x, 0 ≤ Set.indicator K (gaussianWeightReal ((1:ℝ) ^ 2)) x :=
    fun x => Set.indicator_nonneg (fun y _ => (hgpos y).le) x
  -- balls of radius `1/16` about `r·e` with `|r| ≤ 1/4` sit inside `K`
  have hballs : ∀ r : ℝ, |r| ≤ 1/4 → ∀ x ∈ Metric.ball (r • e) (1/16),
      ‖x‖ ≤ 1/2 ∧ |(inner ℝ e x : ℝ) - r| < 1/16 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1/4 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| ≤ 1/4 → ∀ x ∈ Metric.ball (r • e) (1/16),
      Real.exp (-(1:ℝ)/2) ≤ Set.indicator K (gaussianWeightReal ((1:ℝ) ^ 2)) x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    have hmem : x ∈ K := by
      rw [hKdef, Metric.mem_closedBall, dist_zero_right]
      exact hx1
    rw [Set.indicator_of_mem hmem, gaussianWeightReal]
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2:ℝ) * (1:ℝ) ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hp1 : 0 < ∫ x in S₁, Set.indicator K (gaussianWeightReal ((1:ℝ) ^ 2)) x := by
    refine setIntegral_pos_of_ball_le (z := (-(1/4 : ℝ) • e)) (r := 1/16)
      (c := Real.exp (-(1:ℝ)/2)) hhi hh0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1/4)) (by rw [abs_le]; norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1/4)) (by rw [abs_le]; norm_num) x hx
    rw [hS₁def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.2]
  have hp2 : 0 < ∫ x in S₂, Set.indicator K (gaussianWeightReal ((1:ℝ) ^ 2)) x := by
    refine setIntegral_pos_of_ball_le (z := ((1/4 : ℝ) • e)) (r := 1/16)
      (c := Real.exp (-(1:ℝ)/2)) hhi hh0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1/4) (by rw [abs_le]; norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (1/4) (by rw [abs_le]; norm_num) x hx
    rw [hS₂def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.1]
  have hcore₁ne : (S₁ ∩ K).Nonempty := by
    refine ⟨(-(1/4 : ℝ)) • e, ?_, ?_⟩
    · have hval : (inner ℝ e ((-(1/4 : ℝ)) • e) : ℝ) = -(1/4) := by
        rw [real_inner_smul_right, hee, mul_one]
      rw [hS₁def]
      simp only [Set.mem_setOf_eq, hval]
      norm_num
    · have hnrm : ‖(-(1/4 : ℝ)) • e‖ = 1/4 := by
        rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_neg,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
      rw [hKdef, Metric.mem_closedBall, dist_zero_right, hnrm]
      norm_num
  have hcore₂ne : (S₂ ∩ K).Nonempty := by
    refine ⟨((1/4 : ℝ)) • e, ?_, ?_⟩
    · have hval : (inner ℝ e (((1/4 : ℝ)) • e) : ℝ) = 1/4 := by
        rw [real_inner_smul_right, hee, mul_one]
      rw [hS₂def]
      simp only [Set.mem_setOf_eq, hval]
      norm_num
    · have hnrm : ‖((1/4 : ℝ)) • e‖ = 1/4 := by
        rw [norm_smul, Real.norm_eq_abs, he, mul_one,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
      rw [hKdef, Metric.mem_closedBall, dist_zero_right, hnrm]
      norm_num
  refine ⟨K, S₁, S₂, S₃, 1, 1/32, 1/2, one_pos, by norm_num, hKmeas, hKconv, hKR, hK0, hRσ,
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1/8), hS₁meas, hS₂meas, hS₃meas, ?_,
    hcore₁ne, hcore₂ne, ?_⟩
  · intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1/8 : ℝ)) hu hv
    linarith
  · have h1 : (0:ℝ) < (1/32 : ℝ) / 1 := by norm_num
    exact mul_pos h1 (mul_pos hp1 hp2)

end Witness

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`,
Mathlib's three standard foundational axioms — and nothing else. -/

#print axioms Arlib.convexOn_infDist_of_convex
#print axioms Arlib.isLogConcave_exp_neg_infDist
#print axioms Arlib.one_sub_exp_neg_le
#print axioms Arlib.densDist_exp_div_le_of_le
#print axioms Arlib.densDist_exp_div_le
#print axioms Arlib.norm_sub_ge_of_densDist_gaussianIndicator
#print axioms Arlib.norm_sub_ge_of_mem_thickening
#print axioms Arlib.integrable_gaussianWeightReal
#print axioms Arlib.tendsto_setIntegral_expNegInfDist_mul_gaussian
#print axioms Arlib.setIntegral_indicator_closure_eq
#print axioms Arlib.exists_disjoint_open_enlargement_gaussianIndicator
#print axioms Arlib.gaussianIndicator_isoperimetry_measurable
#print axioms Arlib.metric_threshold_lt_openClosed_threshold
#print axioms Arlib.hiso_metropolisGaussian_sharp_sqrt
#print axioms Arlib.gaussianIndicator_isoperimetry_measurable_witness
