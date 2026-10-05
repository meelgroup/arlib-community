/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.HitAndRunConductanceUncond
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunUncond

/-!
# Theorem 1.1 of Lovász–Vempala for the lazy hit-and-run walk, with no mathematical hypothesis

`Arlib.conductance_hitAndRun_ge_uncond` (`Convexity/HitAndRunConductanceUncond.lean`) made
Theorem 4.2 unconditional:

    Φ(hit-and-run on K)  ≥  (1/8000)/(245760·n·D)  ≥  1/(2³¹·n·D)

for `n ≥ 1100` and a convex, closed, measurable, bounded `K ⊆ ℝⁿ` with a unit inball and
`diam K ≤ D`.  This file pushes that through the mixing theorem.

`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_param` (`HitAndRunUncond.lean:145`) is Theorem
1.1 with the conductance value a free parameter `phi` and deadline `4·lsThreshold M phi ε`.
Instantiating it at `phi = 1/(2³¹·n·D)` and feeding `conductance_hitAndRun_ge_uncond_pow` for
`hphi` gives

    `Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond`,

in which **no conductance, isoperimetry or overlap hypothesis remains**.

## The deadline

`lsThreshold M phi ε = log(8M/ε²)/phi²`, and `1/phi² = 2⁶²·n²·D²`, so `4·lsThreshold` is

    `hrDeadlineUncond n D M ε  =  2⁶⁴ · n² · D² · log(8M/ε²)`,

recorded as a definition and identified with `4 · lsThreshold M (1/(2³¹·n·D)) ε` by
`hrDeadlineUncond_eq`.  This is the paper's `O(n²D²·log(M/ε))` shape.

## Contents

| name | content |
|---|---|
| `hrDeadlineUncond` | `2⁶⁴·n²D²·log(8M/ε²)`, the deadline in closed form |
| `hrDeadlineUncond_eq` | it **is** `4 · lsThreshold M (1/(2³¹·n·D)) ε` |
| `tvLe_iterate_lazy_hitAndRun_uncond` | Theorem 1.1, no conductance/isoperimetry/overlap binder |
| `tvLe_iterate_lazy_hitAndRun_uncond_ball` | the same for `K ⊆ closedBall zout R`, deadline `2⁶⁶·n²R²·log(8M/ε²)` |
| `tvLe_iterate_lazy_hitAndRun_uncond_witness` | a concrete instance of every hypothesis at once |

## What remains, and why

The **warm-start data** `M`, `S`, `hM`, `hS`, `hdom` stays.  It is Lovász–Vempala Theorem 1.1's
own `(M, S)` clause — "the density `dσ/dπ_K` is bounded by `M` except on a set `S` with
`σ(S) ≤ ε/2`" — not a lemma this repository failed to prove; a mixing theorem without *some*
hypothesis on the start distribution is false (a point mass never mixes in a bounded number of
steps under a fixed bound).  Beyond that only `0 < ε ≤ 1`, `1100 ≤ n` and the geometry of `K`
remain, exactly as in Theorem 4.2.

`hM : 1 ≤ M` is not a restriction: `M = 1` with `S = ∅` is the stationary start, and the witness
below uses it.

## The exact form is stronger

The composition is done at the power-of-two conductance bound `1/(2³¹·n·D)` because it makes the
deadline a clean `2⁶⁴·n²D²·log(8M/ε²)`.  `Arlib.conductance_hitAndRun_ge_uncond`'s exact value
`(1/8000)/(245760·n·D) = 1/(1966080000·n·D)` is strictly larger, hence gives a strictly shorter
deadline (by a factor `(2³¹/1966080000)² ≈ 1.19`); `lsThreshold_anti` would carry it across.  No
second theorem is stated for it.

## Non-vacuity

`tvLe_iterate_lazy_hitAndRun_uncond_witness` discharges **every** hypothesis simultaneously:
`K = closedBall 0 1` in `ℝ¹¹⁰⁰`, `D = 2`, `σ = uniformOn volume K`, `M = 1`, `S = ∅`, `ε = 1/2`,
and an explicit step count past the deadline.  The conclusion is a genuine `1/2`-total-variation
bound, not the trivial `ε = 1` one.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

/-! ## 1. The deadline in closed form -/

/-- **The unconditional hit-and-run mixing deadline**: `2⁶⁴ · n² · D² · log(8M/ε²)`.

This is `4 · lsThreshold M phi ε` at the conductance `phi = 1/(2³¹·n·D)` that
`Arlib.conductance_hitAndRun_ge_uncond_pow` delivers: `lsThreshold M phi ε = log(8M/ε²)/phi²`
and `1/phi² = 2⁶²·n²D²`, and the factor `4` is `conductance_lazy` (laziness halves the
conductance and the deadline is quadratic in `1/phi`).  Identified with that product by
`hrDeadlineUncond_eq`.

`D` is a bound on the **diameter** of `K`, not on its circumradius; see
`tvLe_iterate_lazy_hitAndRun_uncond_ball` for the `R`-form, which costs a further `4`. -/
noncomputable def hrDeadlineUncond (n : ℕ) (D M eps : ℝ) : ℝ :=
  2 ^ 64 * (n : ℝ) ^ 2 * D ^ 2 * Real.log (8 * M / eps ^ 2)

/-- **`hrDeadlineUncond` is `4 · lsThreshold M (1/(2³¹·n·D)) ε`.**  Pure arithmetic:
`(1/(2³¹nD))² = 1/(2⁶²n²D²)`, and `4 · 2⁶² = 2⁶⁴`.  Stated as an equation so that a caller
holding either form of the deadline hypothesis holds the other. -/
theorem hrDeadlineUncond_eq {n : ℕ} {D M eps : ℝ} (hn : (n : ℝ) ≠ 0) (hD : D ≠ 0) :
    hrDeadlineUncond n D M eps = 4 * lsThreshold M (1 / (2 ^ 31 * (n : ℝ) * D)) eps := by
  rw [hrDeadlineUncond, lsThreshold, div_pow, one_pow]
  field_simp
  ring

/-! ## 2. Theorem 1.1, unconditional -/

/-- **Theorem 1.1 of Lovász–Vempala for the lazy hit-and-run walk, with no conductance,
isoperimetry or overlap hypothesis.**

For `n ≥ 1100` and a convex, closed, measurable, bounded `K ⊆ ℝⁿ` containing a unit ball, of
diameter at most `D`, the lazy hit-and-run walk started at any `(M, S)`-warm `σ` is within `ε`
in total variation of the uniform measure on `K` after

    `hrDeadlineUncond n D M ε  =  2⁶⁴ · n² · D² · log(8M/ε²)`

steps.

Every binder that used to carry mathematics is discharged: `hphi` is
`Arlib.conductance_hitAndRun_ge_uncond_pow`, which in turn absorbed `hIso`, `hLem41`, `htrans`
and `hloc`.  What is left is the geometry of `K`, `0 < ε ≤ 1`, and the warm-start data
`M`, `S`, `hM`, `hS`, `hdom` — Theorem 1.1's own hypothesis on the starting distribution, which
no mixing theorem can drop.  See the module docstring.

`volume K ≠ 0` and `volume K ≠ ⊤`, which the parametric form asks for, are derived here from
`hball` and `hKb` rather than assumed, exactly as in
`Arlib.conductance_hitAndRun_ge_uncond`. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    {m : ℕ} (hm : hrDeadlineUncond n D M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn1 hKb hball) hD
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  have hphi0 : 0 < 1 / (2 ^ 31 * (n : ℝ) * D) := by positivity
  have hphi1 : 1 / (2 ^ 31 * (n : ℝ) * D) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  refine tvLe_iterate_lazy_hitAndRun_param hn1 hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom (Arlib.conductance_hitAndRun_ge_uncond_pow hn hKc hKcl hKm hKb hball hD) ?_
  rwa [hrDeadlineUncond_eq (by positivity) (by positivity)] at hm

/-! ## 3. The circumradius form -/

/-- **Theorem 1.1, unconditional, for a body inside a ball of radius `R`.**

`K ⊆ closedBall zout R` gives `diam K ≤ 2R` by the triangle inequality, so §2 applies at
`D = 2R`, where the conductance bound reads `Φ ≥ 1/(2³²·n·R)` and the deadline is

    `hrDeadlineUncond n (2R) M ε  =  2⁶⁶ · n² · R² · log(8M/ε²)`

— a factor `4` worse than the diameter form, which is the price of measuring a body by its
circumradius.  This is the shape of the original `tvLe_iterate_lazy_hitAndRun_unitBall`, whose
deadline `4 · lvThreshold n 1 R M ε = 2⁵⁸·n²R²·log(8M/ε²)` this exceeds by exactly
`(8000/500)² = 256`, the square of the corrected Lemma 4.1 constant.  The rounding of the
conductance denominator to a power of two costs the same factor `16` on both routes
(`245760000 → 2²⁸` and `3932160000 → 2³²`), so it cancels from the comparison.

No hypothesis on `R` is needed: `0 ≤ R` follows from `hball` and `hout` (the body is
nonempty), and `1 ≤ 2R` from `one_le_diam_of_unitBall` inside §2.  Like §2, this statement has
no conductance, isoperimetry or overlap binder. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond_ball {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    {m : ℕ}
    (hm : 2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2) ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hout
  have hzK : z ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
  have hRnn : (0 : ℝ) ≤ R := le_trans dist_nonneg (Metric.mem_closedBall.1 (hout hzK))
  have hD : Metric.diam K ≤ 2 * R := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.1 (hout hx)
    have hy' := Metric.mem_closedBall.1 (hout hy)
    calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
      _ = dist x zout + dist y zout := by rw [dist_comm zout y]
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  refine tvLe_iterate_lazy_hitAndRun_uncond hn hKc hKcl hKm hKb hball hD hM heps0 heps1 hSm hS
    hdom ?_
  rwa [hrDeadlineUncond, show (2 : ℝ) ^ 64 * (n : ℝ) ^ 2 * (2 * R) ^ 2 = 2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2
    from by ring]

/-! ## 4. Non-vacuity

Every hypothesis of §2 at once, on a body that satisfies them all: the unit ball of `ℝ¹¹⁰⁰`,
started at its own uniform measure.  `M = 1` with `S = ∅` is the stationary start — the
smallest legal warm-start datum — and `ε = 1/2` keeps the conclusion a real bound (at `ε = 1`
`TVLe` holds between any two probability measures for trivial reasons).

The step count `2⁶⁴ · 150040000` is past the deadline because
`hrDeadlineUncond 1100 2 1 (1/2) = 2⁶⁴ · 1100² · 2² · log 32` and `log 32 ≤ 31`. -/

/-- **A concrete instance discharging every hypothesis of
`tvLe_iterate_lazy_hitAndRun_uncond` simultaneously.**

`K = closedBall 0 1 ⊆ ℝ¹¹⁰⁰`, `n = 1100`, `D = 2`, `σ = uniformOn volume K`, `M = 1`,
`S = ∅`, `ε = 1/2`, `m = 2⁶⁴·150040000`.

The geometry is immediate (`convex_closedBall`, `Metric.isClosed_closedBall`,
`measurableSet_closedBall`, `Metric.isBounded_closedBall`, `hball` is `subset_rfl`, and
`Metric.diam_closedBall` gives `diam K ≤ 2`).  The warm start is the stationary one:
`σ(∅) = 0 ≤ ε/2` and `σ(A \ ∅) = σ A = 1 · π_K(A)`, so `hS` and `hdom` hold with `M = 1`.

Without this the theorem above could be vacuous. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond_witness :
    Arlib.TVLe
      (iterate (lazy (hitAndRun (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1)))
        (uniformOn volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
        (2 ^ 64 * 150040000))
      (uniformOn volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
      (ENNReal.ofReal (1 / 2)) := by
  set K : Set (EuclideanSpace ℝ (Fin 1100)) := Metric.closedBall 0 1 with hK
  have hK0 : volume K ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hD : Metric.diam K ≤ 2 := by
    simpa using Metric.diam_closedBall (x := (0 : EuclideanSpace ℝ (Fin 1100)))
      (zero_le_one' ℝ)
  have hlog : Real.log (8 * 1 / ((1 : ℝ) / 2) ^ 2) ≤ 31 := by
    have h32 : (8 : ℝ) * 1 / ((1 : ℝ) / 2) ^ 2 = 32 := by norm_num
    have := Real.log_le_sub_one_of_pos (x := (32 : ℝ)) (by norm_num)
    rw [h32]
    linarith
  refine tvLe_iterate_lazy_hitAndRun_uncond (n := 1100) (by norm_num) (convex_closedBall 0 1)
    Metric.isClosed_closedBall measurableSet_closedBall Metric.isBounded_closedBall
    (z := 0) subset_rfl hD (M := 1) (eps := 1 / 2) le_rfl (by norm_num) (by norm_num)
    (S := ∅) MeasurableSet.empty (by simp)
    (fun A _ => by rw [Set.sdiff_empty, ENNReal.ofReal_one, one_mul]) ?_
  rw [hrDeadlineUncond]
  push_cast
  nlinarith [hlog, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8 * 1 / ((1 : ℝ) / 2) ^ 2)]

/-! ## Axiom profile -/

section AxiomCheck

#print axioms hrDeadlineUncond_eq
#print axioms tvLe_iterate_lazy_hitAndRun_uncond
#print axioms tvLe_iterate_lazy_hitAndRun_uncond_ball
#print axioms tvLe_iterate_lazy_hitAndRun_uncond_witness

end AxiomCheck

end Arlib.MarkovChains
