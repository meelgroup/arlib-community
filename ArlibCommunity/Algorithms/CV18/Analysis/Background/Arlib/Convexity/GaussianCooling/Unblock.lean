/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoBall

/-!
# Isoperimetry for a bounded density on a convex body, and the Gaussian-cooling instance

`Arlib.uniformOn_iso_of_convex` (`Arlib/Convexity/IsoBall.lean`) proves the three-set
isoperimetric inequality for the **uniform** measure on a bounded convex body, outright, at
`κ = 2⁻ⁿ/D`.  Cousins–Vempala §3 needs the same inequality for the **Gaussian-restricted**
measure `∝ 1_K(x)·e^{-‖x‖²/(2s)}`, because that — not the uniform measure — is the
stationary law of the walk each cooling phase samples from.  This file bridges the two by
the crudest available device, a density sandwich:

> If `m ≤ g ≤ M` on `K`, then every isoperimetric inequality for Lebesgue measure on `K`
> holds for `volume.withDensity g` with the constant degraded by `(m/M)²`.

That is all this file does, and it is deliberately elementary: `ν A ≤ M·vol A`,
`ν B ≤ M·vol B`, `ν C ≥ m·vol C`, `ν K ≥ m·vol K`, then quote
`Arlib.volume_mul_volume_le_of_separated`.

## The honest cost, stated once and repeated in every theorem below

Two exponentials multiply here, and **neither is an artefact of an incomplete proof**; both
are genuine features of what is being proved.

1. `Arlib.uniformOn_iso_of_convex` gives `κ = 2⁻ⁿ/D`, exponentially worse in `n` than the
   truth `2/D` (Lovász–Simonovits), because it replaces localization by a chord argument.
2. The density sandwich costs `(m/M)²`.  For `g(x) = e^{-‖x‖²/(2s)}` on `K ⊆ R·Bₙ` this is
   `e^{-R²/s}`, and the Cousins–Vempala schedule runs with `R ≍ √n` and `s` as small as
   `Θ(1/n)`, so `(m/M)² = e^{-Θ(n²)}` at the cold end of the schedule — worse still than
   the `2⁻ⁿ`.

So the constant proved below is exponentially small in `n`, any conductance bound it feeds
is exponentially small, and any mixing time is exponentially large.  **Nothing here yields a
polynomial-time volume algorithm, and no statement below may be quoted as if it did.**  What
it does yield is an *unconditional* isoperimetric inequality for the Gaussian-restricted
measure on a convex body, where previously this development had none at any constant.

## Main results

* `Arlib.Convexity.measure_withDensity_le_mul`,
  `Arlib.Convexity.mul_le_measure_withDensity` — the density sandwich, one side each.
* `Arlib.Convexity.withDensity_mul_le_of_separated` — the isoperimetric inequality in volume
  form for `volume.withDensity g`, for any `g` sandwiched between `m` and `M` on a bounded
  convex `K`.  No positivity hypotheses at all: every step is `ℝ≥0∞`-monotone, and at `m = 0`
  the statement is trivially true.
* `Arlib.Convexity.uniformOn_withDensity_iso_of_convex` — the same, normalized, in the
  `hiso` shape that `Arlib.MarkovChains.conductance_ballWalk_ge` consumes.
* `Arlib.Convexity.uniformOn_gaussian_iso_of_convex`,
  `Arlib.Convexity.uniformOn_gaussian_iso_kappa` — the instance the volume algorithm needs:
  the Gaussian-restricted measure on a convex `K ⊆ R·Bₙ`, at `κ = e^{-R²/s}·2⁻ⁿ/(2R)`.
* `Arlib.Convexity.ball_smul_subset`, `Arlib.Convexity.norm_le_of_mem_of_convex`,
  `Arlib.Convexity.exists_closedBall_superset_of_convex` — a convex body containing the unit
  ball and of finite volume is bounded, with the explicit radius `2·vol K/vol B(0,1/2)`,
  proved by a ball-packing count rather than by compactness.  This exists because the
  radius `R` above is *not* available from the hypotheses the volume-oracle interface
  supplies; this manufactures it.
* `Arlib.Convexity.exists_uniformOn_gaussian_iso_of_convex` — the capstone: for **every**
  convex measurable `K` containing the unit ball with `volume K ≠ ⊤`, and every `s > 0`, a
  strictly positive `κ` for which the Gaussian-restricted measure on `K` satisfies the
  three-set isoperimetric inequality.  No radius, no roundness, no localization.

## What is assumed

Nothing.  Every declaration below is a theorem with its hypotheses written inline; no `def`,
`structure`, `class` or named `Prop` in this file asserts an isoperimetric inequality, a
conductance bound, or a mixing rate.  There are no `def`s in this file at all — the Gaussian
weight is written out inline at every use precisely so that no name can drift from what is
proved about it.

## What this does *not* unblock

`Arlib.MarkovChains.conductance_ballWalk_ge` and everything downstream of it are hard-wired
to `Arlib.uniformOn volume K` — the *uniform* ball walk, whose stationary law is the uniform
measure on `K`.  A walk whose stationary law is `Arlib.uniformOn (volume.withDensity g) K`
is a Metropolis-filtered (or ball-walk-with-rejection) chain, and no such kernel is built in
this library.  So the theorems below supply the §3 input in the shape §4 wants, but §4 is
not yet stated at that generality.  See the module docstring of
`Arlib/MarkovChains/Continuous/BallWalkConductance.lean`.
-/

namespace Arlib.Convexity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-! ### The density sandwich -/

/-- **Upper half of the density sandwich.**  If `g ≤ M` on `K` and `S ⊆ K` is measurable,
then `(μ.withDensity g) S ≤ M · μ S`.

Nothing is assumed about `g` beyond the pointwise bound on `K` — in particular no
measurability, since `MeasureTheory.withDensity_apply` needs none. -/
theorem measure_withDensity_le_mul {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {g : E → ℝ≥0∞} {K S : Set E} (hS : MeasurableSet S) (hSK : S ⊆ K) {M : ℝ≥0∞}
    (hM : ∀ x ∈ K, g x ≤ M) :
    (μ.withDensity g) S ≤ M * μ S := by
  rw [withDensity_apply _ hS]
  calc ∫⁻ x in S, g x ∂μ ≤ ∫⁻ _ in S, M ∂μ :=
        setLIntegral_mono' hS fun x hx => hM x (hSK hx)
    _ = M * μ S := setLIntegral_const _ _

/-- **Lower half of the density sandwich.**  If `m ≤ g` on `K` and `S ⊆ K` is measurable,
then `m · μ S ≤ (μ.withDensity g) S`.  Assumes nothing else about `g`. -/
theorem mul_le_measure_withDensity {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {g : E → ℝ≥0∞} {K S : Set E} (hS : MeasurableSet S) (hSK : S ⊆ K) {m : ℝ≥0∞}
    (hm : ∀ x ∈ K, m ≤ g x) :
    m * μ S ≤ (μ.withDensity g) S := by
  rw [withDensity_apply _ hS]
  calc m * μ S = ∫⁻ _ in S, m ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in S, g x ∂μ := setLIntegral_mono' hS fun x hx => hm x (hSK hx)

/-! ### Isoperimetry for a sandwiched density, in volume form -/

/-- **The three-set isoperimetric inequality for `volume.withDensity g` on a bounded convex
body**, for any `g` with `m ≤ g ≤ M` on `K`:

    m²·(d/D)·ν A·ν B  ≤  M²·2ⁿ·ν (K \ A \ B)·ν K,    ν = volume.withDensity g.

**Assumed: nothing.**  This is `Arlib.volume_mul_volume_le_of_separated` composed with the
two halves of the density sandwich.  The hypotheses are exactly that theorem's (`K` convex
and measurable, `A, B ⊆ K` measurable and `d`-separated, `K` of diameter `≤ D`) plus the two
pointwise bounds on `g`.  There is no positivity requirement on `m`, `M` or `D`: every step
is `ℝ≥0∞`-monotone, and at `m = 0` the statement is trivially true.

**Cost.**  The effective constant is `(m/M)²·2⁻ⁿ/D`.  The `2⁻ⁿ` is inherited from
`Arlib.uniformOn_iso_of_convex` (the price of avoiding localization); the `(m/M)²` is the
price of the sandwich.  Both are exponentially small for the densities Cousins–Vempala uses;
see the module docstring. -/
theorem withDensity_mul_le_of_separated
    {K A B : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {d D : ℝ} {m M : ℝ≥0∞} (hd : 0 < d)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hm : ∀ x ∈ K, m ≤ g x) (hM : ∀ x ∈ K, g x ≤ M) :
    m ^ 2 * ENNReal.ofReal (d / D)
        * (volume.withDensity g) A * (volume.withDensity g) B
      ≤ M ^ 2 * 2 ^ n * (volume.withDensity g) ((K \ A) \ B)
          * (volume.withDensity g) K := by
  have hCm : MeasurableSet ((K \ A) \ B) := (hKm.diff hA).diff hB
  have hCK : ((K \ A) \ B) ⊆ K := Set.Subset.trans Set.sdiff_subset Set.sdiff_subset
  have hAup : (volume.withDensity g) A ≤ M * volume A :=
    measure_withDensity_le_mul hA hAK hM
  have hBup : (volume.withDensity g) B ≤ M * volume B :=
    measure_withDensity_le_mul hB hBK hM
  have hClo : m * volume ((K \ A) \ B) ≤ (volume.withDensity g) ((K \ A) \ B) :=
    mul_le_measure_withDensity hCm hCK hm
  have hKlo : m * volume K ≤ (volume.withDensity g) K :=
    mul_le_measure_withDensity hKm (subset_refl K) hm
  have hmain := volume_mul_volume_le_of_separated (D := D) hd hK hKm hA hB hAK hBK hsep hdiam
  calc m ^ 2 * ENNReal.ofReal (d / D)
          * (volume.withDensity g) A * (volume.withDensity g) B
      ≤ m ^ 2 * ENNReal.ofReal (d / D) * (M * volume A) * (M * volume B) := by gcongr
    _ = M ^ 2 * (m ^ 2 * (ENNReal.ofReal (d / D) * volume A * volume B)) := by ring
    _ ≤ M ^ 2 * (m ^ 2 * (2 ^ n * volume ((K \ A) \ B) * volume K)) := by gcongr
    _ = M ^ 2 * 2 ^ n * (m * volume ((K \ A) \ B)) * (m * volume K) := by ring
    _ ≤ M ^ 2 * 2 ^ n * (volume.withDensity g) ((K \ A) \ B)
          * (volume.withDensity g) K := by gcongr

/-! ### The same, normalized, in `hiso` shape -/

/-- **The isoperimetric inequality for a sandwiched density, normalized**, in the shape of
the `hiso` argument of `Arlib.MarkovChains.conductance_ballWalk_ge`, with
`π = uniformOn (volume.withDensity g) K`:

    m²·(d/D)·π A·π B  ≤  M²·2ⁿ·π (K \ A \ B).

**Assumed: nothing.**  This is `Arlib.Convexity.withDensity_mul_le_of_separated` divided
through by `(ν K)³`.  The two extra hypotheses `hν0`, `hνtop` are the non-degeneracy that
makes `π` a probability measure; they are discharged for the Gaussian weight in
`Arlib.Convexity.uniformOn_gaussian_iso_of_convex` below.

**Cost.**  `κ = (m/M)²·2⁻ⁿ/D`, exponentially small in `n`; see the module docstring. -/
theorem uniformOn_withDensity_iso_of_convex
    {K : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {D : ℝ} {m M : ℝ≥0∞}
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hν0 : (volume.withDensity g) K ≠ 0) (hνtop : (volume.withDensity g) K ≠ ⊤)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hm : ∀ x ∈ K, m ≤ g x) (hM : ∀ x ∈ K, g x ≤ M) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      m ^ 2 * ENNReal.ofReal (d / D)
          * Arlib.uniformOn (volume.withDensity g) K A
          * Arlib.uniformOn (volume.withDensity g) K B
        ≤ M ^ 2 * 2 ^ n
            * Arlib.uniformOn (volume.withDensity g) K ((K \ A) \ B) := by
  intro d hd A B hA hB hAK hBK hsep
  set ν : Measure (EuclideanSpace ℝ (Fin n)) := volume.withDensity g with hνdef
  have hVinv : ν K * (ν K)⁻¹ = 1 := ENNReal.mul_inv_cancel hν0 hνtop
  have hCK : ((K \ A) \ B) ⊆ K := Set.Subset.trans Set.sdiff_subset Set.sdiff_subset
  have hCm : MeasurableSet ((K \ A) \ B) := (hKm.diff hA).diff hB
  have eA : Arlib.uniformOn ν K A = ν A * (ν K)⁻¹ := by
    rw [Arlib.uniformOn_apply ν hKm hA, Set.inter_eq_self_of_subset_left hAK, div_eq_mul_inv]
  have eB : Arlib.uniformOn ν K B = ν B * (ν K)⁻¹ := by
    rw [Arlib.uniformOn_apply ν hKm hB, Set.inter_eq_self_of_subset_left hBK, div_eq_mul_inv]
  have eC : Arlib.uniformOn ν K ((K \ A) \ B) = ν ((K \ A) \ B) * (ν K)⁻¹ := by
    rw [Arlib.uniformOn_apply ν hKm hCm, Set.inter_eq_self_of_subset_left hCK, div_eq_mul_inv]
  have hmain := withDensity_mul_le_of_separated (D := D) (g := g) (m := m) (M := M)
    hd hK hKm hA hB hAK hBK hsep hdiam hm hM
  rw [eA, eB, eC]
  calc m ^ 2 * ENNReal.ofReal (d / D) * (ν A * (ν K)⁻¹) * (ν B * (ν K)⁻¹)
      = (m ^ 2 * ENNReal.ofReal (d / D) * ν A * ν B) * ((ν K)⁻¹) ^ 2 := by ring
    _ ≤ (M ^ 2 * 2 ^ n * ν ((K \ A) \ B) * ν K) * ((ν K)⁻¹) ^ 2 := by gcongr
    _ = M ^ 2 * 2 ^ n * (ν ((K \ A) \ B) * (ν K)⁻¹) * (ν K * (ν K)⁻¹) := by ring
    _ = M ^ 2 * 2 ^ n * (ν ((K \ A) \ B) * (ν K)⁻¹) := by rw [hVinv, mul_one]

/-! ### The Gaussian weight

The Cousins–Vempala cooling schedule carries the weight `e^{-‖x‖²/(2s)}`, in the `ℝ≥0∞`
form `ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s)))` (the same exponent convention as
`Arlib.GaussianCooling.gW`).  It is written out inline everywhere rather than named, so that
no definition can drift from what these theorems prove about it. -/

/-- The Gaussian weight is at most `1` for `s > 0`: its exponent is nonpositive. -/
theorem gaussianWeight_le_one {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))) ≤ 1 := by
  refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * s)]
  nlinarith [sq_nonneg ‖x‖]

/-- The Gaussian weight is at least `e^{-R²/(2s)}` at every point of norm at most `R`. -/
theorem gaussianWeight_ge {s R : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ≤ R) :
    ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * s)))
      ≤ ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have h2s : (0:ℝ) < 2 * s := by linarith
  have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith
  rw [div_le_div_iff₀ h2s h2s]
  nlinarith

/-- **The Gaussian-weighted measure of a body of finite volume is finite**, because the
weight is bounded by `1`.  This is one of the two non-degeneracy inputs of
`Arlib.Convexity.uniformOn_withDensity_iso_of_convex`. -/
theorem gaussianMeasure_ne_top {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    {s : ℝ} (hs : 0 < s) (hfin : volume K ≠ ⊤) :
    (volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K ≠ ⊤ := by
  have h := measure_withDensity_le_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g := fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s)))) (K := K) (S := K)
    hKm (subset_refl K) (M := 1) (fun x _ => gaussianWeight_le_one hs x)
  rw [one_mul] at h
  exact ne_top_of_le_ne_top hfin h

/-- **The Gaussian-weighted measure of a body of positive volume inside `R·Bₙ` is
positive**, because the weight is bounded below by `e^{-R²/(2s)} > 0` there.  This is the
other non-degeneracy input of `Arlib.Convexity.uniformOn_withDensity_iso_of_convex`. -/
theorem gaussianMeasure_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    {s R : ℝ} (hs : 0 < s) (hK0 : volume K ≠ 0)
    (hR : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :
    (volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K ≠ 0 := by
  have h := mul_le_measure_withDensity (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g := fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s)))) (K := K) (S := K)
    hKm (subset_refl K) (m := ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * s))))
    (fun x hx => gaussianWeight_ge hs (by
      have hxb := hR hx; rwa [mem_closedBall_zero_iff] at hxb))
  intro hzero
  rw [hzero] at h
  rcases mul_eq_zero.mp (nonpos_iff_eq_zero.mp h) with h1 | h1
  · rw [ENNReal.ofReal_eq_zero] at h1
    exact absurd h1 (not_le.mpr (Real.exp_pos _))
  · exact hK0 h1

/-! ### The Gaussian-cooling instance -/

/-- **An unconditional isoperimetric inequality for the Gaussian-restricted measure on a
convex body** — the Cousins–Vempala §3 input, in weakened but *proved* form.

For `K` convex, measurable, of positive finite volume, contained in `R·Bₙ`, and any variance
`s > 0`, put `π = uniformOn (volume.withDensity e^{-‖·‖²/(2s)}) K` — the law each cooling
phase samples from.  Then for every `d > 0` and every pair of `d`-separated measurable
`A, B ⊆ K`:

    e^{-R²/s}·(d/(2R))·π A·π B  ≤  2ⁿ·π (K \ A \ B).

**Assumed: nothing.**  This is `Arlib.Convexity.uniformOn_withDensity_iso_of_convex` at
`m = e^{-R²/(2s)}`, `M = 1`, `D = 2R`, with the two non-degeneracy hypotheses discharged by
`gaussianMeasure_ne_zero` and `gaussianMeasure_ne_top`.

**Cost — read this before quoting the result.**  The effective constant is
`e^{-R²/s}·2⁻ⁿ/(2R)`.  Cousins–Vempala run with `R ≍ √n` and `s` as small as `Θ(1/n)`, so
`e^{-R²/s}` is `e^{-Θ(n²)}`: the constant is *exponentially small in the dimension*, worse
even than the `2⁻ⁿ` it inherits from `Arlib.uniformOn_iso_of_convex`.  Any conductance and
mixing bound built on it is correspondingly exponential.  This is not, and must not be
presented as, the polynomial-time isoperimetric inequality of the paper, which needs
localization. -/
theorem uniformOn_gaussian_iso_of_convex
    {K : Set (EuclideanSpace ℝ (Fin n))} {s R : ℝ} (hs : 0 < s)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hR : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal (Real.exp (-(R ^ 2) / s)) * ENNReal.ofReal (d / (2 * R))
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K A
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K B
        ≤ 2 ^ n * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K
              ((K \ A) \ B) := by
  intro d hd A B hA hB hAK hBK hsep
  have hnorm : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxb := hR hx
    rwa [mem_closedBall_zero_iff] at hxb
  have hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := by
    intro x hx y hy
    have h1 := hnorm x hx
    have h2 := hnorm y hy
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * R := by linarith
  have h := uniformOn_withDensity_iso_of_convex (D := 2 * R)
    (g := fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))
    (m := ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * s)))) (M := 1)
    hK hKm (gaussianMeasure_ne_zero hKm hs hK0 hR) (gaussianMeasure_ne_top hKm hs hKtop)
    hdiam (fun x hx => gaussianWeight_ge hs (hnorm x hx))
    (fun x _ => gaussianWeight_le_one hs x) d hd A B hA hB hAK hBK hsep
  have hexp : Real.exp (-(R ^ 2) / (2 * s)) ^ 2 = Real.exp (-(R ^ 2) / s) := by
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hsq : (ENNReal.ofReal (Real.exp (-(R ^ 2) / (2 * s)))) ^ 2
      = ENNReal.ofReal (Real.exp (-(R ^ 2) / s)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, hexp]
  rw [hsq, one_pow, one_mul] at h
  exact h

/-- **The same in the `κ` normalization** used by `Arlib.uniformOn_iso_of_convex`:

    κ·d·π A·π B  ≤  π (K \ A \ B),    κ = e^{-R²/s}·(1/2)ⁿ/(2R),

with `π = uniformOn (volume.withDensity e^{-‖·‖²/(2s)}) K`.

**Assumed: nothing.**  A restatement of `Arlib.Convexity.uniformOn_gaussian_iso_of_convex`
with the `2ⁿ` moved to the left as `(1/2)ⁿ`, so the shape matches the `hiso` argument of
`Arlib.MarkovChains.conductance_ballWalk_ge` verbatim — modulo that theorem's `π` being the
*uniform* measure, which is exactly the gap recorded under "what this does not unblock" in
the module docstring.

**Cost.**  `κ = e^{-R²/s}·2⁻ⁿ/(2R)` is exponentially small in `n`.  This is not a
polynomial-time result; see the module docstring. -/
theorem uniformOn_gaussian_iso_kappa
    {K : Set (EuclideanSpace ℝ (Fin n))} {s R : ℝ} (hs : 0 < s)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hR : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R))
          * ENNReal.ofReal d
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K A
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K B
        ≤ Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K
              ((K \ A) \ B) := by
  intro d hd A B hA hB hAK hBK hsep
  have h := uniformOn_gaussian_iso_of_convex hs hK hKm hK0 hKtop hR d hd A B hA hB hAK hBK
    hsep
  -- If either part is empty the claim is trivial; otherwise `R > 0`, which the
  -- rearrangement of the constant needs.
  rcases Set.eq_empty_or_nonempty A with rfl | hAne
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hBne
  · simp
  obtain ⟨u, hu⟩ := hAne
  obtain ⟨v, hv⟩ := hBne
  have hRpos : 0 < R := by
    have h1 : ‖u‖ ≤ R := by
      have hb := hR (hAK hu); rwa [mem_closedBall_zero_iff] at hb
    have h3 : ‖v‖ ≤ R := by
      have hb := hR (hBK hv); rwa [mem_closedBall_zero_iff] at hb
    have h2 : (0:ℝ) < dist u v := lt_of_lt_of_le hd (hsep u hu v hv)
    have h4 : dist u v ≤ ‖u‖ + ‖v‖ := by
      rw [dist_eq_norm]; exact norm_sub_le u v
    linarith
  have hhalfpow : ((2 : ℝ≥0∞) ^ n)⁻¹ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1 / 2),
      show ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]; norm_num,
      ← ENNReal.inv_pow]
  have hkappa : ENNReal.ofReal (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R))
        * ENNReal.ofReal d
      = ((2 : ℝ≥0∞) ^ n)⁻¹
        * (ENNReal.ofReal (Real.exp (-(R ^ 2) / s)) * ENNReal.ofReal (d / (2 * R))) := by
    rw [hhalfpow,
      ← ENNReal.ofReal_mul (Real.exp_pos (-(R ^ 2) / s)).le,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1 / 2 : ℝ) ^ n),
      ← ENNReal.ofReal_mul
        (by positivity : (0:ℝ) ≤ Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R))]
    congr 1
    field_simp
  have htwo : ((2 : ℝ≥0∞) ^ n)⁻¹ * 2 ^ n = 1 :=
    ENNReal.inv_mul_cancel (by positivity) (by simp)
  rw [hkappa]
  calc ((2 : ℝ≥0∞) ^ n)⁻¹
        * (ENNReal.ofReal (Real.exp (-(R ^ 2) / s)) * ENNReal.ofReal (d / (2 * R)))
        * Arlib.uniformOn (volume.withDensity
            (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K A
        * Arlib.uniformOn (volume.withDensity
            (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K B
      = ((2 : ℝ≥0∞) ^ n)⁻¹
        * (ENNReal.ofReal (Real.exp (-(R ^ 2) / s)) * ENNReal.ofReal (d / (2 * R))
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K A
          * Arlib.uniformOn (volume.withDensity
              (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K B) := by
        ring
    _ ≤ ((2 : ℝ≥0∞) ^ n)⁻¹
        * (2 ^ n * Arlib.uniformOn (volume.withDensity
            (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K
            ((K \ A) \ B)) := by gcongr
    _ = (((2 : ℝ≥0∞) ^ n)⁻¹ * 2 ^ n)
        * Arlib.uniformOn (volume.withDensity
            (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K
            ((K \ A) \ B) := by ring
    _ = _ := by rw [htwo, one_mul]

/-! ### Removing the radius hypothesis

`Arlib.Convexity.uniformOn_gaussian_iso_of_convex` needs `K ⊆ R·Bₙ`, and the interface that
would consume it — `Ttc.VolumeAlgorithm.correct` — supplies no such `R`: it quantifies over
every convex `K` with `Metric.ball 0 1 ⊆ K` and `volume K ≠ ⊤`.  Those three facts do force
boundedness, with an explicit radius, and this section proves it.

The argument is a ball-packing count, not a compactness argument, so it yields a *number*.
If `x ∈ K` and `t = ‖x‖`, then for every `λ ∈ [0, 1/2]` the ball `B(λx, 1-λ) ⊆ K` by
convexity; taking `λ = k/t` for `k = 0, …, ⌊t/2⌋` gives `⌊t/2⌋+1` balls of radius `1/2`
whose centres are at mutual distance `≥ 1`, hence pairwise disjoint.  So
`(⌊t/2⌋+1)·vol(B(0,1/2)) ≤ vol K`, and `t < 2(⌊t/2⌋+1) ≤ 2·vol K/vol(B(0,1/2))`. -/

/-- **The dilated ball around `λx` lies in `K`.**  If `K` is convex, contains the unit ball
and contains `x`, then `B(λ·x, 1-λ) ⊆ K` for every `λ ∈ [0,1)`: a point of that ball is the
convex combination `(1-λ)·z + λ·x` with `‖z‖ < 1`.  Assumes only convexity and the two
memberships. -/
theorem ball_smul_subset {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) :
    Metric.ball (lam • x) (1 - lam) ⊆ K := by
  intro y hy
  have h1 : (0:ℝ) < 1 - lam := by linarith
  have hy' : ‖y - lam • x‖ < 1 - lam := by
    rw [← dist_eq_norm]; exact hy
  have hznorm : ‖(1 - lam)⁻¹ • (y - lam • x)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h1), ← div_eq_inv_mul,
      div_lt_one h1]
    exact hy'
  have hzK : (1 - lam)⁻¹ • (y - lam • x) ∈ K := by
    refine hball ?_
    rwa [Metric.mem_ball, dist_zero_right]
  have hy2 : y = (1 - lam) • ((1 - lam)⁻¹ • (y - lam • x)) + lam • x := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h1), one_smul]
    abel
  rw [hy2]
  exact hK hzK hx h1.le hlam0 (by ring)

/-- **A convex body containing the unit ball and of finite volume is bounded**, with the
explicit radius `2·vol(K)/vol(B(0,1/2))`.

**Assumed: nothing.**  Proof: the ball-packing count described in the section header.  The
bound is exponentially large in `n` (because `vol(B(0,1/2)) = 2⁻ⁿ·vol(B(0,1))`), which is
unavoidable for a bound of this shape — a simplex containing the unit ball really does have
diameter exponential in its volume. -/
theorem norm_le_of_mem_of_convex {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) :
    ‖x‖ ≤ 2 * (volume K).toReal
        / (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal := by
  have hb0 : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) :=
    Metric.measure_ball_pos volume 0 (by norm_num)
  have hbtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hbR : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal :=
    ENNReal.toReal_pos hb0.ne' hbtop
  have hKR : (0:ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le (norm_nonneg x) with htz | htpos
  · rw [← htz]
    positivity
  -- `t = ‖x‖ > 0`; pack `N+1` disjoint balls of radius `1/2` along the segment `[0, x/2]`
  set t : ℝ := ‖x‖ with ht
  set N : ℕ := ⌊t / 2⌋₊ with hN
  set c : ℕ → EuclideanSpace ℝ (Fin n) := fun k => ((k : ℝ) / t) • x with hc
  have hNle : (N : ℝ) ≤ t / 2 := Nat.floor_le (by positivity)
  have hlam : ∀ k ∈ Finset.range (N + 1), (k : ℝ) / t ≤ 1 / 2 := by
    intro k hk
    have hkN : (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [div_le_div_iff₀ htpos (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have hsub : ∀ k ∈ Finset.range (N + 1), Metric.ball (c k) (1 / 2) ⊆ K := by
    intro k hk
    have h2 : (k : ℝ) / t ≤ 1 / 2 := hlam k hk
    have h0 : (0:ℝ) ≤ (k : ℝ) / t := by positivity
    have hstep : Metric.ball (c k) (1 / 2)
        ⊆ Metric.ball (((k : ℝ) / t) • x) (1 - (k : ℝ) / t) := by
      simp only [hc]
      exact Metric.ball_subset_ball (by linarith)
    exact subset_trans hstep (ball_smul_subset hK hball hx h0 (by linarith))
  have hdist : ∀ k j : ℕ, k ≠ j → (1:ℝ) / 2 + 1 / 2 ≤ dist (c k) (c j) := by
    intro k j hkj
    have habs : (1:ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      rcases Nat.lt_or_ge k j with h | h
      · have hle : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have hlt : j < k := Nat.lt_of_le_of_ne h (Ne.symm hkj)
        have hle : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hsubv : c k - c j = (((k : ℝ) - (j : ℝ)) / t) • x := by
      simp only [hc, ← sub_smul]
      congr 1
      field_simp
    have hd : dist (c k) (c j) = |((k : ℝ) - (j : ℝ)) / t| * t := by
      rw [dist_eq_norm, hsubv, norm_smul, Real.norm_eq_abs, ← ht]
    rw [hd, abs_div, abs_of_pos htpos, div_mul_cancel₀ _ (ne_of_gt htpos)]
    linarith
  have hpd : (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint
      fun k => Metric.ball (c k) (1 / 2) := by
    intro k _ j _ hkj
    exact Metric.ball_disjoint_ball (hdist k j hkj)
  have hcount : ((N : ℝ≥0∞) + 1)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ volume K := by
    have hun : (⋃ k ∈ Finset.range (N + 1), Metric.ball (c k) (1 / 2)) ⊆ K := by
      refine Set.iUnion₂_subset ?_
      intro k hk
      exact hsub k hk
    have heq : volume (⋃ k ∈ Finset.range (N + 1), Metric.ball (c k) (1 / 2))
        = ∑ _k ∈ Finset.range (N + 1),
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
      rw [measure_biUnion_finset hpd fun k _ => measurableSet_ball]
      exact Finset.sum_congr rfl fun k _ => Measure.addHaar_ball_center volume (c k) (1 / 2)
    have hle := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hun
    rw [heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    simpa using hle
  have hcountR : ((N : ℝ) + 1)
      * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal
      ≤ (volume K).toReal := by
    have h := ENNReal.toReal_mono hfin hcount
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
      ENNReal.toReal_one] at h
  have hfloor : t / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one (t / 2)
  rw [le_div_iff₀ hbR]
  nlinarith

/-- **Every convex body containing the unit ball and of finite volume sits in a closed ball
of an explicit positive radius.**  The `∃ R` form of `norm_le_of_mem_of_convex`, which is
what `Arlib.Convexity.exists_uniformOn_gaussian_iso_of_convex` consumes. -/
theorem exists_closedBall_superset_of_convex {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Convex ℝ K) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
  refine ⟨max 1 (2 * (volume K).toReal
      / (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun x hx => ?_⟩
  rw [mem_closedBall_zero_iff]
  exact le_trans (norm_le_of_mem_of_convex hK hball hfin hx) (le_max_right _ _)

/-- **The Gaussian isoperimetric inequality with no geometric hypothesis at all.**

For *every* convex measurable `K ⊆ ℝⁿ` containing the unit ball and of finite volume — which
is exactly the class `Ttc.VolumeAlgorithm.correct` quantifies over — and every variance
`s > 0`, there is a **positive** constant `κ` with

    κ·d·π A·π B  ≤  π (K \ A \ B),    π = uniformOn (volume.withDensity e^{-‖·‖²/(2s)}) K,

for all `d > 0` and all `d`-separated measurable `A, B ⊆ K`.

**Assumed: nothing.**  This composes `Arlib.Convexity.uniformOn_gaussian_iso_kappa` with
`Arlib.Convexity.exists_closedBall_superset_of_convex`, which manufactures the radius the
first one needs out of convexity, the inscribed unit ball and finiteness of the volume.

**Cost.**  The `κ` produced is `e^{-R²/s}·2⁻ⁿ/(2R)` with `R = max 1 (2·vol K/vol B(0,1/2))`,
so it is doubly exponentially bad in `n` in the worst case.  The statement is an existential
precisely because no useful uniform constant is claimed: what is claimed is *positivity*,
which is what makes a conductance bound non-trivial, and nothing more.  This is not a
polynomial-time result. -/
theorem exists_uniformOn_gaussian_iso_of_convex
    {K : Set (EuclideanSpace ℝ (Fin n))} {s : ℝ} (hs : 0 < s)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
        MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
        (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
        ENNReal.ofReal kappa * ENNReal.ofReal d
            * Arlib.uniformOn (volume.withDensity
                (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K A
            * Arlib.uniformOn (volume.withDensity
                (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K B
          ≤ Arlib.uniformOn (volume.withDensity
                (fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))))) K
                ((K \ A) \ B) := by
  obtain ⟨R, hRpos, hR⟩ := exists_closedBall_superset_of_convex hK hball hKtop
  have hK0 : volume K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos) (measure_mono hball))
  refine ⟨Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R), by positivity, ?_⟩
  exact uniformOn_gaussian_iso_kappa hs hK hKm hK0 hKtop hR

/-! ### Axiom audit

Every declaration in this file is `sorry`-free and depends only on Lean's three standard
axioms.  Re-check with `lake build Arlib.Convexity.GaussianCooling.Unblock`. -/

#print axioms measure_withDensity_le_mul
#print axioms mul_le_measure_withDensity
#print axioms withDensity_mul_le_of_separated
#print axioms uniformOn_withDensity_iso_of_convex
#print axioms gaussianWeight_le_one
#print axioms gaussianWeight_ge
#print axioms gaussianMeasure_ne_top
#print axioms gaussianMeasure_ne_zero
#print axioms uniformOn_gaussian_iso_of_convex
#print axioms uniformOn_gaussian_iso_kappa
#print axioms ball_smul_subset
#print axioms norm_le_of_mem_of_convex
#print axioms exists_closedBall_superset_of_convex
#print axioms exists_uniformOn_gaussian_iso_of_convex

end Arlib.Convexity
