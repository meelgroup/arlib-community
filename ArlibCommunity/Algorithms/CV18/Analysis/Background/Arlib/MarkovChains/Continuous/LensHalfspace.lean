/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.StarPolar

/-!
# The separation `δ/n` of `volume_lens_inter_ge_max` is optimal — a counterexample

`Arlib/MarkovChains/Continuous/StarPolar.lean` proves the overlap estimate

    (1 − 1/n)ⁿ · max{vol(K ∩ B(u,δ)), vol(K ∩ B(v,δ))}  ≤  vol(K ∩ B(u,δ) ∩ B(v,δ))

(`Arlib.MarkovChains.volume_lens_inter_ge_max`) at separation `‖u − v‖ ≤ δ/n`, and its module
docstring (`StarPolar.lean:98–111`) proposes to reach the paper's `δ/√n` by combining the
direction-dependent contraction `Arlib.MarkovChains.volume_lens_inter_ge_halfspace` with a
single missing inequality: for convex `K ∋ u,v`, with `H_u = {x | 0 ≤ ⟪x−u, v−u⟫}` and
`H_v = {x | 0 ≤ ⟪x−v, u−v⟫}`,

    max{vol(K ∩ B_u ∩ H_u), vol(K ∩ B_v ∩ H_v)}  ≥  c · max{vol(K ∩ B_u), vol(K ∩ B_v)}.  (★)

**This file shows (★) is false, and that the obstruction is not the proof technique but the
statement.**  Three results, all `[propext, Classical.choice, Quot.sound]`:

* `exists_halfspace_max_lt` — for **every** `c > 0` there are `n`, a bounded convex body
  `K ⊆ ℝⁿ` of positive volume and `u, v ∈ K` at separation `‖u − v‖ ≤ 1/√n` for which (★)
  fails, *and* for which the `max`-form lens bound itself fails with constant `c`.
* `volume_halfspace_max_le_apexConeBody`, `volume_lens_le_apexConeBody` — the **rate**: at
  separation `t` and `δ = 1` the best possible constant is `≤ (1 + t/4)^{-n}`.  A constant `c`
  therefore forces `t = O(δ/n)`: **`volume_lens_inter_ge_max`'s hypothesis `‖u−v‖ ≤ δ/n` is
  optimal up to the constant**, and no `δ/n^α` with `α < 1` — in particular not `δ/√n` — is
  available for the `max` form.
* `exists_overlap_speedyWalk_sqrt_dim_counterexample` — **the conclusion** of
  `Arlib.MarkovChains.overlap_speedyWalk_convex`, `1 ≤ 20·(P_u(Tᶜ) + P_v(T))`, is false at
  separation `δ/√n`, with every one of that theorem's other hypotheses satisfied.  So the gap
  is not closable by any lemma of that binder shape, and the `√n` in
  `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex` /
  `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` cannot be recovered this way.

## The counterexample

`apexConeBody u v` is the solid circular cone with **apex `v`**, axis `(u−v)/‖u−v‖` and
half-angle `60°`, truncated to `closedBall v 4`; `δ = 1`, `t = ‖u − v‖ < 1/2`.  It is convex,
bounded, of positive volume, and contains both `u` and `v`.  Three facts drive everything:

* `K ⊆ H_v`, so the `v`-side half-space slice is the whole apex slice `K ∩ B(v,1)`;
* `K ∩ H_u ⊆ B(v, 2t)`, so the `u`-side half-space slice is *also* inside `K ∩ B(v,1)`;
* since `K` is a cone with apex `v` opening towards `u`, the homothety about `v` of ratio
  `1 + t/4 > 1` carries `K ∩ B(v,1)` into `K ∩ B(u,1)`, whence
  `(1 + t/4)ⁿ · vol(K ∩ B(v,1)) ≤ vol(K ∩ B(u,1))` (`volume_apexConeBody_ball_left_ge`).

At `t = 1/√n` the gain is `(1 + 1/(4√n))ⁿ ≈ e^{√n/4}`.  Both `B(u,1)` and `B(v,1)` slices are
of positive finite volume, so the refutations are quantitative, not `0`-vs-`0`.

This is the *same* configuration `StarPolar.lean:90–96` already identified as defeating the
`max` form at `δ/√n` — a thin body whose mass sits far from `v` on the `u` side — made
explicit, formal, and quantitative.  What that docstring got wrong is only the hope that (★)
would nevertheless survive: (★) implies the `max` form at `δ/√n` via
`volume_lens_inter_ge_halfspace`, so it is refuted by the very example already recorded there.

## What is *not* refuted, and what the paper's route actually needs

Nothing here contradicts KLS Lemma 3.5 in its **`min`** form,

    vol(K ∩ B_u ∩ B_v)  ≥  c · min{vol(K ∩ B_u), vol(K ∩ B_v)}   at `‖u−v‖ ≤ δ/√n`,

and on `apexConeBody` that form holds with constant `1` — `volume_lens_eq_min_apexConeBody`
proves the lens *equals* the `min`.  The `min` form in general is neither proved nor assumed
anywhere in this repository; no theorem below carries it as a binder.

But the `min` form alone does **not** give `overlap_speedyWalk_convex`'s conclusion: the two
one-step laws are normalised by `vol(K ∩ B_u)` and `vol(K ∩ B_v)` separately, so
`P_u(Tᶜ) + P_v(T) ≥ vol(lens)/max{vol(K ∩ B_u), vol(K ∩ B_v)}`, and passing from the `min` to
the `max` needs the local conductances to be comparable — precisely the `d_ℓ(u,v) < 1/3`
hypothesis of Cousins–Vempala's `lem:overlap` that `overlap_speedyWalk_convex` deletes.
`exists_overlap_speedyWalk_sqrt_dim_counterexample` is exactly a configuration where
`ell K 1 v` is more than `20×` smaller than `ell K 1 u`.  Restoring the `√n` therefore requires
changing the shape of `hoverlap` in `Arlib.MarkovChains.conductance_speedyGaussian_ge`
(a file this one does not touch), not strengthening `volume_lens_inter_ge_max`.

## Scope

No mixing-time or `O*(n³)` claim is made or implied here; `thm:iso` remains unproved in this
repository, and this file proves only negative geometric facts.  Nothing is `sorry`ed and no
axiom is declared.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped InnerProductSpace

variable {n : ℕ}

/-! ## 1. The body: a truncated circular cone with apex at `v`, opening towards `u` -/

/-- **The counterexample body.**  With `t = ‖u − v‖`, this is the (solid, circular) cone with
apex `v`, axis the direction `(u − v)/t` and half-angle `60°` (`cos α = 1/2`), truncated to
`closedBall v 4`:

    apexConeBody u v = {x | ‖x − v‖·‖u − v‖ ≤ 2⟪x − v, u − v⟫} ∩ closedBall v 4.

Writing `y = x − v` and `w = (u − v)/t`, the defining inequality is `‖y‖ ≤ 2⟪y, w⟫`, i.e.
`cos∠(y, w) ≥ 1/2`.  It is a plain set-level definition: no semantic identity is asserted by
the name. -/
noncomputable def apexConeBody (u v : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x - v‖ * ‖u - v‖ ≤ 2 * ⟪x - v, u - v⟫_ℝ} ∩ Metric.closedBall v 4

theorem mem_apexConeBody_iff {u v x : EuclideanSpace ℝ (Fin n)} :
    x ∈ apexConeBody u v ↔
      ‖x - v‖ * ‖u - v‖ ≤ 2 * ⟪x - v, u - v⟫_ℝ ∧ ‖x - v‖ ≤ 4 := by
  simp [apexConeBody, Metric.mem_closedBall, dist_eq_norm]

theorem convex_apexConeBody (u v : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (apexConeBody u v) := by
  refine Convex.inter ?_ (convex_closedBall v 4)
  intro x hx y hy p q hp hq hpq
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hvv : p • v + q • v = v := by rw [← add_smul, hpq, one_smul]
  have key : p • x + q • y - v = p • (x - v) + q • (y - v) := by
    rw [smul_sub, smul_sub]
    conv_lhs => rw [← hvv]
    abel
  rw [key]
  have hnorm : ‖p • (x - v) + q • (y - v)‖ ≤ p * ‖x - v‖ + q * ‖y - v‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp,
      abs_of_nonneg hq]
  have hinner : ⟪p • (x - v) + q • (y - v), u - v⟫_ℝ
      = p * ⟪x - v, u - v⟫_ℝ + q * ⟪y - v, u - v⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [hinner]
  have h0 : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hnorm h0, mul_le_mul_of_nonneg_left hx hp,
    mul_le_mul_of_nonneg_left hy hq]

theorem isBounded_apexConeBody (u v : EuclideanSpace ℝ (Fin n)) :
    Bornology.IsBounded (apexConeBody u v) :=
  Metric.isBounded_closedBall.subset Set.inter_subset_right

theorem measurableSet_apexConeBody (u v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (apexConeBody u v) := by
  refine MeasurableSet.inter ?_ measurableSet_closedBall
  refine measurableSet_le ?_ ?_
  · exact ((continuous_id.sub continuous_const).norm.mul continuous_const).measurable
  · exact (continuous_const.mul
      ((continuous_id.sub continuous_const).inner continuous_const)).measurable

theorem apex_mem_apexConeBody (u v : EuclideanSpace ℝ (Fin n)) : v ∈ apexConeBody u v := by
  rw [mem_apexConeBody_iff]
  simp

theorem mem_apexConeBody_of_left {u v : EuclideanSpace ℝ (Fin n)} (ht : ‖u - v‖ ≤ 4) :
    u ∈ apexConeBody u v := by
  rw [mem_apexConeBody_iff]
  refine ⟨?_, ht⟩
  rw [real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (u - v)]

/-! ## 2. The two half-spaces -/

/-- The whole cone lies in the half-space through `v` facing `u` — the half-space
`H_v = {x | 0 ≤ ⟪x − v, u − v⟫}` of `volume_lens_inter_ge_halfspace`.  So intersecting with
`H_v` costs the body **nothing**. -/
theorem apexConeBody_subset_halfspace_right {u v : EuclideanSpace ℝ (Fin n)} :
    apexConeBody u v ⊆ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ} := by
  intro x hx
  rw [mem_apexConeBody_iff] at hx
  have h1 : (0 : ℝ) ≤ ‖x - v‖ * ‖u - v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  simp only [Set.mem_setOf_eq]
  linarith [hx.1]

/-- **The cone meets the half-space through `u` facing `v` only in a ball of radius `2t`
about the apex.**  For `x` in the cone with `0 ≤ ⟪x − u, v − u⟫` one has `‖x − v‖ ≤ 2‖u − v‖`:
the cone opens *away* from `v`, so its part on the `v`-side of `u` is squeezed into the tip. -/
theorem norm_sub_le_of_mem_apexConeBody_halfspace_left {u v x : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (hx : x ∈ apexConeBody u v) (hh : 0 ≤ ⟪x - u, v - u⟫_ℝ) :
    ‖x - v‖ ≤ 2 * ‖u - v‖ := by
  rw [mem_apexConeBody_iff] at hx
  have hsplit : ⟪x - v, u - v⟫_ℝ = ⟪x - u, u - v⟫_ℝ + ⟪u - v, u - v⟫_ℝ := by
    rw [← inner_add_left]
    congr 1
    abel
  have hneg : ⟪x - u, u - v⟫_ℝ = -⟪x - u, v - u⟫_ℝ := by
    rw [← inner_neg_right]
    congr 1
    abel
  have hself : ⟪u - v, u - v⟫_ℝ = ‖u - v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hle : ⟪x - v, u - v⟫_ℝ ≤ ‖u - v‖ ^ 2 := by rw [hsplit, hneg, hself]; linarith
  nlinarith [hx.1]

/-! ## 3. The cone within `1 + t/4` of its apex is inside `B(u,1)` -/

/-- **The key inclusion.**  Because the cone opens towards `u`, every one of its points at
distance `≤ 1 + t/4` from the apex `v` is at distance `< 1` from `u` — even though
`1 + t/4 > 1`.  The computation is
`‖x − u‖² = ‖x − v‖² − 2⟪x − v, u − v⟫ + t² ≤ ρ² − ρt + t²` with `ρ = ‖x − v‖ ≤ 1 + t/4`, and
the quadratic `ρ ↦ ρ² − ρt + t²` is `≤ 1 − t/2 + 13t²/16 < 1` on `[0, 1 + t/4]` for
`0 < t < 1/2`. -/
theorem mem_ball_left_of_mem_apexConeBody {u v x : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) (hx : x ∈ apexConeBody u v)
    (hρ : ‖x - v‖ ≤ 1 + ‖u - v‖ / 4) :
    x ∈ Metric.ball u 1 := by
  rw [mem_apexConeBody_iff] at hx
  set t : ℝ := ‖u - v‖ with htdef
  set ρ : ℝ := ‖x - v‖ with hrdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hsq : ‖x - u‖ ^ 2 = ρ ^ 2 - 2 * ⟪x - v, u - v⟫_ℝ + t ^ 2 := by
    have hxu : x - u = (x - v) - (u - v) := by abel
    rw [hxu, norm_sub_sq_real]
  have hbound : ‖x - u‖ ^ 2 ≤ ρ ^ 2 - ρ * t + t ^ 2 := by
    rw [hsq]; linarith [hx.1]
  have hquad : ρ ^ 2 - ρ * t + t ^ 2 < 1 := by
    nlinarith [mul_nonneg hρ0 (by linarith : (0:ℝ) ≤ 1 + t / 4 - ρ)]
  have : ‖x - u‖ ^ 2 < 1 := by linarith
  rw [Metric.mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (x - u)]

/-! ## 4. Expanding the apex-slice by the factor `1 + t/4` -/

/-- **The expanding homothety.**  `apexConeBody u v` is a cone with apex `v`, so the
homothety about `v` of ratio `R = 1 + t/4 > 1` maps it into itself; combined with
`mem_ball_left_of_mem_apexConeBody` the image of the `B(v,1)`-slice lands in the
`B(u,1)`-slice.  This is the reverse of the contraction of
`Arlib.MarkovChains.homothety_image_subset_lens`: the ratio is `> 1`, so it *gains* volume. -/
theorem homothety_apexConeBody_image_subset {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    AffineMap.homothety v (1 + ‖u - v‖ / 4) '' (Metric.ball v 1 ∩ apexConeBody u v)
      ⊆ Metric.ball u 1 ∩ apexConeBody u v := by
  set t : ℝ := ‖u - v‖ with htdef
  set R : ℝ := 1 + t / 4 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  rintro _ ⟨x, ⟨hxb, hxK⟩, rfl⟩
  have hxv : ‖x - v‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hxb
  have hdiff : AffineMap.homothety v R x - v = R • (x - v) := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
  have hnorm : ‖AffineMap.homothety v R x - v‖ = R * ‖x - v‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
  have hinner : ⟪AffineMap.homothety v R x - v, u - v⟫_ℝ = R * ⟪x - v, u - v⟫_ℝ := by
    rw [hdiff, real_inner_smul_left]
  rw [mem_apexConeBody_iff] at hxK
  have hle : ‖AffineMap.homothety v R x - v‖ ≤ R := by
    rw [hnorm]
    nlinarith [norm_nonneg (x - v)]
  have hmem : AffineMap.homothety v R x ∈ apexConeBody u v := by
    rw [mem_apexConeBody_iff, hnorm, hinner]
    constructor
    · nlinarith [hxK.1]
    · rw [← hnorm]; linarith [hle]
  exact ⟨mem_ball_left_of_mem_apexConeBody ht0 ht hmem (by rw [← hRdef]; exact hle), hmem⟩

/-- **The volume gain.**  `(1 + t/4)ⁿ · vol(K ∩ B(v,1)) ≤ vol(K ∩ B(u,1))`: the slice at the
apex is exponentially (in `n·t`) *smaller* than the slice one step away along the axis. -/
theorem volume_apexConeBody_ball_left_ge {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) * volume (Metric.ball v 1 ∩ apexConeBody u v)
      ≤ volume (Metric.ball u 1 ∩ apexConeBody u v) := by
  have hR0 : (0 : ℝ) < 1 + ‖u - v‖ / 4 := by linarith [norm_nonneg (u - v)]
  have himg := Measure.addHaar_image_homothety
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) v (1 + ‖u - v‖ / 4)
    (Metric.ball v 1 ∩ apexConeBody u v)
  rw [finrank_euclideanSpace_fin,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + ‖u - v‖ / 4) ^ n)] at himg
  calc ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) * volume (Metric.ball v 1 ∩ apexConeBody u v)
      = volume (AffineMap.homothety v (1 + ‖u - v‖ / 4) ''
          (Metric.ball v 1 ∩ apexConeBody u v)) := himg.symm
    _ ≤ _ := measure_mono (homothety_apexConeBody_image_subset ht0 ht)

/-! ## 5. Non-degeneracy -/

/-- The apex slice has **positive** volume: the ball of radius `1/8` about the axis point
`v + (u − v)/(2t)` sits inside `apexConeBody u v ∩ B(v,1)`. -/
theorem volume_apexConeBody_ball_right_pos {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    0 < volume (Metric.ball v 1 ∩ apexConeBody u v) := by
  set t : ℝ := ‖u - v‖ with htdef
  set p : EuclideanSpace ℝ (Fin n) := v + (1 / (2 * t)) • (u - v) with hpdef
  have hpv : p - v = (1 / (2 * t)) • (u - v) := by rw [hpdef]; abel
  have hpvnorm : ‖p - v‖ = 1 / 2 := by
    rw [hpv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← htdef]
    field_simp
  have hpvinner : ⟪p - v, u - v⟫_ℝ = t / 2 := by
    rw [hpv, real_inner_smul_left, real_inner_self_eq_norm_sq, ← htdef]
    field_simp
  have hsub : Metric.ball p (1 / 8) ⊆ Metric.ball v 1 ∩ apexConeBody u v := by
    intro x hx
    have hxp : ‖x - p‖ < 1 / 8 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have hxv : ‖x - v‖ < 5 / 8 := by
      have : x - v = (x - p) + (p - v) := by abel
      calc ‖x - v‖ ≤ ‖x - p‖ + ‖p - v‖ := by rw [this]; exact norm_add_le _ _
        _ < 5 / 8 := by rw [hpvnorm]; linarith
    have hcs : |⟪x - p, u - v⟫_ℝ| ≤ ‖x - p‖ * t := by
      rw [htdef]; exact abs_real_inner_le_norm _ _
    have hxvinner : ⟪x - v, u - v⟫_ℝ = ⟪x - p, u - v⟫_ℝ + t / 2 := by
      rw [← hpvinner, ← inner_add_left]
      congr 1
      abel
    refine ⟨by rw [Metric.mem_ball, dist_eq_norm]; linarith, ?_⟩
    rw [mem_apexConeBody_iff]
    refine ⟨?_, by linarith⟩
    rw [hxvinner]
    have h1 : ⟪x - p, u - v⟫_ℝ ≥ -(‖x - p‖ * t) := by
      have := abs_le.1 hcs
      linarith [this.1]
    nlinarith [norm_nonneg (x - p)]
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume p (by norm_num)) (measure_mono hsub)

/-! ## 6. Theorem A — the half-space inequality is false, with a rate -/

/-- **Theorem A (parametrised).**  On `apexConeBody u v`, with `t = ‖u − v‖ ∈ (0, 1/2)` and
`δ = 1`,

    (1 + t/4)ⁿ · max{vol(K ∩ B(u,1) ∩ H_u), vol(K ∩ B(v,1) ∩ H_v)}
        ≤ max{vol(K ∩ B(u,1)), vol(K ∩ B(v,1))},

where `H_u = {x | 0 ≤ ⟪x − u, v − u⟫}` and `H_v = {x | 0 ≤ ⟪x − v, u − v⟫}` are exactly the
half-spaces of `Arlib.MarkovChains.volume_lens_inter_ge_halfspace`.

Both half-space slices are trapped inside the **apex** slice `K ∩ B(v,1)`: the `v`-slice
because `K ⊆ H_v` outright, the `u`-slice because `K ∩ H_u ⊆ B(v, 2t)`.  And the apex slice is
`(1 + t/4)ⁿ` times smaller than the `u`-slice, because `K` is a cone with apex `v` opening
towards `u`.

So the inequality
`max{vol(K ∩ B_u ∩ H_u), vol(K ∩ B_v ∩ H_v)} ≥ c·max{vol(K ∩ B_u), vol(K ∩ B_v)}`
forces `c ≤ (1 + t/4)^{-n}`.  At the separation `t = δ/√n` that is `≈ e^{-√n/4}`: **no
constant `c` works**, and even a *dimension-dependent* `c` degrades exponentially.  See
`exists_halfspace_max_lt` for the packaged refutation. -/
theorem volume_halfspace_max_le_apexConeBody {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) *
        max (volume (Metric.ball u 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}))
            (volume (Metric.ball v 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}))
      ≤ max (volume (Metric.ball u 1 ∩ apexConeBody u v))
            (volume (Metric.ball v 1 ∩ apexConeBody u v)) := by
  have hright : Metric.ball v 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}
      = Metric.ball v 1 ∩ apexConeBody u v :=
    Set.inter_eq_self_of_subset_left fun x hx => apexConeBody_subset_halfspace_right hx.2
  have hleft : Metric.ball u 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}
      ⊆ Metric.ball v 1 ∩ apexConeBody u v := by
    rintro x ⟨⟨_, hxK⟩, hxh⟩
    refine ⟨?_, hxK⟩
    have := norm_sub_le_of_mem_apexConeBody_halfspace_left ht0 hxK hxh
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hmax : max (volume (Metric.ball u 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}))
      (volume (Metric.ball v 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}))
      ≤ volume (Metric.ball v 1 ∩ apexConeBody u v) := by
    refine max_le (measure_mono hleft) ?_
    rw [hright]
  calc ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) *
        max (volume (Metric.ball u 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}))
            (volume (Metric.ball v 1 ∩ apexConeBody u v ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}))
      ≤ ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n)
          * volume (Metric.ball v 1 ∩ apexConeBody u v) := by gcongr
    _ ≤ volume (Metric.ball u 1 ∩ apexConeBody u v) :=
        volume_apexConeBody_ball_left_ge ht0 ht
    _ ≤ _ := le_max_left _ _

/-- **The `max`-form lens bound of `Arlib.MarkovChains.volume_lens_inter_ge_max` fails at any
separation better than `δ/n`.**  On `apexConeBody u v`,

    (1 + t/4)ⁿ · vol((B(u,1) ∩ B(v,1)) ∩ K)  ≤  max{vol(K ∩ B(u,1)), vol(K ∩ B(v,1))},

simply because the lens is contained in the apex slice.  So the constant in
`volume_lens_inter_ge_max` at separation `t` is at most `(1 + t/4)^{-n}`: its hypothesis
`‖u − v‖ ≤ δ/n` is **optimal up to the constant** — no `δ/n^α` with `α < 1` is possible for
the `max` form, and in particular not `δ/√n`.  (The *paper's* `min` form is untouched by
this: here `vol(K ∩ B(v,1))` is the smaller of the two, and the lens is comparable to it.) -/
theorem volume_lens_le_apexConeBody {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n)
        * volume (Metric.ball u 1 ∩ Metric.ball v 1 ∩ apexConeBody u v)
      ≤ max (volume (Metric.ball u 1 ∩ apexConeBody u v))
            (volume (Metric.ball v 1 ∩ apexConeBody u v)) := by
  have hsub : Metric.ball u 1 ∩ Metric.ball v 1 ∩ apexConeBody u v
      ⊆ Metric.ball v 1 ∩ apexConeBody u v := fun x hx => ⟨hx.1.2, hx.2⟩
  calc ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n)
        * volume (Metric.ball u 1 ∩ Metric.ball v 1 ∩ apexConeBody u v)
      ≤ ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n)
          * volume (Metric.ball v 1 ∩ apexConeBody u v) := by gcongr
    _ ≤ volume (Metric.ball u 1 ∩ apexConeBody u v) := volume_apexConeBody_ball_left_ge ht0 ht
    _ ≤ _ := le_max_left _ _

/-- **The `min` form is untouched — on this body it holds with constant `1`.**  The whole apex
slice `K ∩ B(v,1)` lies inside `B(u,1)`, so the lens *is* the apex slice, which is also the
smaller of the two slices:

    vol((B(u,1) ∩ B(v,1)) ∩ K) = min{vol(K ∩ B(u,1)), vol(K ∩ B(v,1))}.

So this counterexample refutes the `max` form and (★) without saying anything against KLS
Lemma 3.5 as the paper states it. -/
theorem volume_lens_eq_min_apexConeBody {u v : EuclideanSpace ℝ (Fin n)}
    (ht0 : 0 < ‖u - v‖) (ht : ‖u - v‖ < 1 / 2) :
    volume (Metric.ball u 1 ∩ Metric.ball v 1 ∩ apexConeBody u v)
      = min (volume (Metric.ball u 1 ∩ apexConeBody u v))
            (volume (Metric.ball v 1 ∩ apexConeBody u v)) := by
  have hR1 : (1 : ℝ) ≤ (1 + ‖u - v‖ / 4) ^ n :=
    one_le_pow₀ (by linarith [norm_nonneg (u - v)])
  have hba : volume (Metric.ball v 1 ∩ apexConeBody u v)
      ≤ volume (Metric.ball u 1 ∩ apexConeBody u v) := by
    refine le_trans ?_ (volume_apexConeBody_ball_left_ge ht0 ht)
    calc volume (Metric.ball v 1 ∩ apexConeBody u v)
        = 1 * volume (Metric.ball v 1 ∩ apexConeBody u v) := (one_mul _).symm
      _ ≤ _ := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hR1
  have hset : Metric.ball u 1 ∩ Metric.ball v 1 ∩ apexConeBody u v
      = Metric.ball v 1 ∩ apexConeBody u v := by
    refine Set.Subset.antisymm (fun x hx => ⟨hx.1.2, hx.2⟩) ?_
    rintro x ⟨hxb, hxK⟩
    have hxv : ‖x - v‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hxb
    exact ⟨⟨mem_ball_left_of_mem_apexConeBody ht0 ht hxK
      (by linarith [norm_nonneg (u - v)]), hxb⟩, hxK⟩
  rw [hset, min_eq_right hba]

/-! ## 7. The packaged refutation -/

/-- **The half-space inequality of the brief is FALSE.**  For *every* constant `c > 0` there
is a dimension `n`, a bounded convex `K ⊆ ℝⁿ` and `u, v ∈ K` with `0 < ‖u − v‖ ≤ 1/√n = δ/√n`,
`0 < vol(K ∩ B(v,1))` and `vol(K ∩ B(u,1)) < ∞`, for which

    max{vol(K ∩ B_u ∩ H_u), vol(K ∩ B_v ∩ H_v)}  <  c · max{vol(K ∩ B_u), vol(K ∩ B_v)}.

Both sides are finite and the right-hand side is positive, so this is a genuine quantitative
refutation, not a `0 ≤ 0` artifact.

Consequently **the half-space route cannot deliver a `δ/√n` analogue of
`Arlib.MarkovChains.volume_lens_inter_ge_max`**, since
`Arlib.MarkovChains.volume_lens_inter_ge_halfspace` plus such an inequality is exactly that
route.  `volume_halfspace_max_le_apexConeBody` gives the rate: the best possible `c` at
separation `t` is `≤ (1 + t/4)^{-n}`, so a constant `c` demands `t = O(1/n)` — the separation
`δ/n` of `volume_lens_inter_ge_max` is **optimal for this statement shape**, not an artefact
of the homothety argument. -/
theorem exists_halfspace_max_lt (c : ℝ) (hc : 0 < c) :
    ∃ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ u ∈ K ∧ v ∈ K ∧
      0 < ‖u - v‖ ∧ ‖u - v‖ ≤ 1 / Real.sqrt n ∧
      0 < volume (Metric.ball v 1 ∩ K) ∧ volume (Metric.ball u 1 ∩ K) ≠ ⊤ ∧
      (max (volume (Metric.ball u 1 ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}))
          (volume (Metric.ball v 1 ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}))
        < ENNReal.ofReal c
            * max (volume (Metric.ball u 1 ∩ K)) (volume (Metric.ball v 1 ∩ K))) ∧
      volume (Metric.ball u 1 ∩ Metric.ball v 1 ∩ K)
        < ENNReal.ofReal c
            * max (volume (Metric.ball u 1 ∩ K)) (volume (Metric.ball v 1 ∩ K)) := by
  classical
  obtain ⟨N, hN5, hNc⟩ : ∃ N : ℕ, 5 ≤ N ∧ 1 < c * (1 + (N : ℝ) / 4) := by
    refine ⟨⌈4 / c⌉₊ + 5, by omega, ?_⟩
    have h1 : 4 / c ≤ (⌈4 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : c * (4 / c) = 4 := by field_simp
    have h3 : (4 : ℝ) ≤ c * (⌈4 / c⌉₊ : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 hc.le
      linarith [h2]
    push_cast
    nlinarith [h3, hc]
  have hN0 : 0 < N := by omega
  have hNR : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
  set n : ℕ := N ^ 2 with hndef
  have hnpos : 0 < n := by rw [hndef]; exact pow_pos hN0 2
  have hncast : ((n : ℕ) : ℝ) = (N : ℝ) ^ 2 := by rw [hndef]; push_cast; ring
  have hsqrt : Real.sqrt ((n : ℕ) : ℝ) = (N : ℝ) := by
    rw [hncast, Real.sqrt_sq (by positivity)]
  set t : ℝ := 1 / (N : ℝ) with htdef
  have ht0' : 0 < t := by rw [htdef]; positivity
  have ht' : t < 1 / 2 := by
    rw [htdef, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  set u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hnpos⟩ t with hudef
  set v : EuclideanSpace ℝ (Fin n) := 0 with hvdef
  have hnormuv : ‖u - v‖ = t := by
    rw [hvdef, sub_zero, hudef, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht0']
  have ht0 : 0 < ‖u - v‖ := by rw [hnormuv]; exact ht0'
  have ht : ‖u - v‖ < 1 / 2 := by rw [hnormuv]; exact ht'
  set K : Set (EuclideanSpace ℝ (Fin n)) := apexConeBody u v with hKdef
  have hb0 : 0 < volume (Metric.ball v 1 ∩ K) := volume_apexConeBody_ball_right_pos ht0 ht
  have hbtop : volume (Metric.ball v 1 ∩ K) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top)
  have hatop : volume (Metric.ball u 1 ∩ K) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top)
  -- Bernoulli: `(1 + t/4)ⁿ ≥ 1 + n·t/4 = 1 + N/4`
  have hbern : 1 + (N : ℝ) / 4 ≤ (1 + ‖u - v‖ / 4) ^ n := by
    have h := one_add_mul_le_pow (a := t / 4) (by linarith) n
    have hnt : (n : ℝ) * (t / 4) = (N : ℝ) / 4 := by
      rw [hncast, htdef]; field_simp
    rw [hnt] at h
    rwa [hnormuv]
  have hcpow : 1 < c * (1 + ‖u - v‖ / 4) ^ n := by
    nlinarith [hbern, hc, hNc]
  have hstep : volume (Metric.ball v 1 ∩ K)
      < ENNReal.ofReal (c * (1 + ‖u - v‖ / 4) ^ n) * volume (Metric.ball v 1 ∩ K) := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (c * (1 + ‖u - v‖ / 4) ^ n) := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2 hcpow
    calc volume (Metric.ball v 1 ∩ K) = volume (Metric.ball v 1 ∩ K) * 1 := (mul_one _).symm
      _ < volume (Metric.ball v 1 ∩ K) * ENNReal.ofReal (c * (1 + ‖u - v‖ / 4) ^ n) :=
          ENNReal.mul_lt_mul_right hb0.ne' hbtop h1
      _ = _ := mul_comm _ _
  have hfin : ENNReal.ofReal (c * (1 + ‖u - v‖ / 4) ^ n) * volume (Metric.ball v 1 ∩ K)
      ≤ ENNReal.ofReal c * max (volume (Metric.ball u 1 ∩ K)) (volume (Metric.ball v 1 ∩ K)) := by
    rw [ENNReal.ofReal_mul hc.le, mul_assoc]
    gcongr
    exact le_trans (volume_apexConeBody_ball_left_ge ht0 ht) (le_max_left _ _)
  have hbmax : volume (Metric.ball v 1 ∩ K)
      < ENNReal.ofReal c * max (volume (Metric.ball u 1 ∩ K))
          (volume (Metric.ball v 1 ∩ K)) := lt_of_lt_of_le hstep hfin
  have hright : Metric.ball v 1 ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ} = Metric.ball v 1 ∩ K :=
    Set.inter_eq_self_of_subset_left fun x hx => apexConeBody_subset_halfspace_right hx.2
  have hleft : Metric.ball u 1 ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ} ⊆ Metric.ball v 1 ∩ K := by
    rintro x ⟨⟨_, hxK⟩, hxh⟩
    refine ⟨?_, hxK⟩
    have := norm_sub_le_of_mem_apexConeBody_halfspace_left ht0 hxK hxh
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hlens : Metric.ball u 1 ∩ Metric.ball v 1 ∩ K ⊆ Metric.ball v 1 ∩ K :=
    fun x hx => ⟨hx.1.2, hx.2⟩
  refine ⟨n, K, u, v, measurableSet_apexConeBody u v, convex_apexConeBody u v,
    isBounded_apexConeBody u v, mem_apexConeBody_of_left (by linarith), apex_mem_apexConeBody u v,
    ht0, by rw [hnormuv, hsqrt, htdef], hb0, hatop, lt_of_le_of_lt ?_ hbmax,
    lt_of_le_of_lt (measure_mono hlens) hbmax⟩
  refine max_le (measure_mono hleft) ?_
  rw [hright]

/-! ## 8. Two generic speedy-walk bounds -/

/-- If `u ∈ T`, the holding atom of `speedyWalk` contributes nothing to `P_u(Tᶜ)`, so the
one-step mass of `Tᶜ` is bounded by any superset of `Tᶜ ∩ B(u,δ) ∩ K`. -/
theorem speedyWalk_compl_le_of_mem {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) {u : EuclideanSpace ℝ (Fin n)} {T S : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) (hu : u ∈ T) (hsub : Tᶜ ∩ (Metric.ball u δ ∩ K) ⊆ S) :
    speedyWalk K δ u Tᶜ ≤ (volume (Metric.ball u δ ∩ K))⁻¹ * volume S := by
  have hind : Tᶜ.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) u = 0 :=
    Set.indicator_of_notMem (by simpa using hu) _
  rw [speedyWalk_apply_set hK δ u hT.compl, hind, mul_zero, add_zero]
  gcongr

/-- If `v ∉ T` and `T` is null inside `B(v,δ) ∩ K`, the walk from `v` never enters `T`. -/
theorem speedyWalk_eq_zero_of_null {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) {v : EuclideanSpace ℝ (Fin n)} {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) (hv : v ∉ T) (hnull : volume (T ∩ (Metric.ball v δ ∩ K)) = 0) :
    speedyWalk K δ v T = 0 := by
  have hind : T.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) v = 0 :=
    Set.indicator_of_notMem hv _
  rw [speedyWalk_apply_set hK δ v hT, hnull, mul_zero, hind, mul_zero, add_zero]

/-! ## 9. Theorem B — the *conclusion* of `overlap_speedyWalk_convex` fails at `δ/√n` -/

/-- **Theorem B (parametrised).**  On `apexConeBody u v`, as soon as the apex slice is more
than `20` times smaller than the `u`-slice, the overlap conclusion
`1 ≤ 20·(P_u(Tᶜ) + P_v(T))` of `Arlib.MarkovChains.overlap_speedyWalk_convex` **fails**, for
the explicit witness `T = ((B(u,1) ∩ K) \ B(v,1)) ∪ {u}`.

`T` contains everything the walk from `u` can reach except the lens, and meets the reach of
the walk from `v` only in the single point `u`.  Both holding atoms drop out by membership
alone (`u ∈ T` kills the `Tᶜ` indicator, `v ∉ T` kills the `T` indicator), so

    P_u(Tᶜ) ≤ vol(K ∩ B_u)⁻¹ · vol(K ∩ B_v),    P_v(T) = 0. -/
theorem exists_overlap_speedyWalk_fails_apexConeBody (hn : 0 < n)
    {u v : EuclideanSpace ℝ (Fin n)} (ht0 : 0 < ‖u - v‖)
    (hgap : (20 : ℝ≥0∞) * volume (Metric.ball v 1 ∩ apexConeBody u v)
      < volume (Metric.ball u 1 ∩ apexConeBody u v)) :
    ∃ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T ∧ u ∈ T ∧ v ∉ T ∧
      ¬ (1 ≤ 20 * (speedyWalk (apexConeBody u v) 1 u Tᶜ
          + speedyWalk (apexConeBody u v) 1 v T)) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set K : Set (EuclideanSpace ℝ (Fin n)) := apexConeBody u v with hKdef
  have hK : MeasurableSet K := measurableSet_apexConeBody u v
  have huv : u ≠ v := by
    intro hc
    rw [hc, sub_self, norm_zero] at ht0
    exact lt_irrefl _ ht0
  set T : Set (EuclideanSpace ℝ (Fin n)) :=
    ((Metric.ball u 1 ∩ K) \ Metric.ball v 1) ∪ {u} with hTdef
  have hTm : MeasurableSet T :=
    ((measurableSet_ball.inter hK).diff measurableSet_ball).union (measurableSet_singleton u)
  have huT : u ∈ T := Or.inr rfl
  have hvT : v ∉ T := by
    rintro (⟨_, hnv⟩ | hv)
    · exact hnv (Metric.mem_ball_self one_pos)
    · exact huv (Set.mem_singleton_iff.1 hv).symm
  have ha0 : volume (Metric.ball u 1 ∩ K) ≠ 0 := by
    intro hc
    rw [hc] at hgap
    exact absurd hgap (by simp)
  have hatop : volume (Metric.ball u 1 ∩ K) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top)
  have hu1 : speedyWalk K 1 u Tᶜ
      ≤ (volume (Metric.ball u 1 ∩ K))⁻¹ * volume (Metric.ball v 1 ∩ K) := by
    refine speedyWalk_compl_le_of_mem hK 1 hTm huT ?_
    rintro x ⟨hxT, hxb, hxK⟩
    refine ⟨?_, hxK⟩
    by_contra hxv
    exact hxT (Or.inl ⟨⟨hxb, hxK⟩, hxv⟩)
  have hv1 : speedyWalk K 1 v T = 0 := by
    refine speedyWalk_eq_zero_of_null hK 1 hTm hvT (measure_mono_null ?_ (measure_singleton u))
    rintro x ⟨hxT, hxb, _⟩
    rcases hxT with ⟨_, hnv⟩ | hxu
    · exact absurd hxb hnv
    · exact hxu
  refine ⟨T, hTm, huT, hvT, ?_⟩
  rw [not_le]
  calc (20 : ℝ≥0∞) * (speedyWalk K 1 u Tᶜ + speedyWalk K 1 v T)
      ≤ 20 * ((volume (Metric.ball u 1 ∩ K))⁻¹ * volume (Metric.ball v 1 ∩ K)) := by
        rw [hv1, add_zero]; gcongr
    _ = (volume (Metric.ball u 1 ∩ K))⁻¹ * (20 * volume (Metric.ball v 1 ∩ K)) := by ring
    _ < (volume (Metric.ball u 1 ∩ K))⁻¹ * volume (Metric.ball u 1 ∩ K) :=
        ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 hatop) (ENNReal.inv_ne_top.2 ha0) hgap
    _ = 1 := ENNReal.inv_mul_cancel ha0 hatop

/-! ## 10. Theorem C — the packaged refutation of `overlap_speedyWalk_convex` at `δ/√n` -/

/-- **`Arlib.MarkovChains.overlap_speedyWalk_convex` is FALSE with `δ/n` replaced by `δ/√n`.**

Explicitly, at `n = 23409`, `δ = 1`, `K = apexConeBody u v` (a bounded convex body of positive
volume), `‖u − v‖ = 1/306 < 1/153 = δ/√n`, `h ≡ 1` (so `densDist h u v = 0 < 1/4`), and
`T = ((B(u,1) ∩ K) \ B(v,1)) ∪ {u}`:

    1 ≤ 20·(P_u(Tᶜ) + P_v(T))   is false.

**Every** other hypothesis of `overlap_speedyWalk_convex` holds — `K` measurable, convex,
bounded, of positive volume, `hpos` (via `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`),
`u ∈ T`, `u, v ∈ K`, `v ∉ T`, `densDist h u v < 1/4` — so the failure is attributable to the
separation alone.

Combined with `exists_halfspace_max_lt` this settles the `√n` question negatively at the level
of the *conclusion*, not merely of the proof technique: no lemma of this binder shape can hold
at separation `δ/√n`, so the `√n` in `conductance_speedyWalk_ge_of_convex` /
`conductance_metropolisGaussian_sharp_ge` cannot be recovered by strengthening
`volume_lens_inter_ge_max`.  The paper's route needs, in addition, the local-conductance
comparability hypothesis (`d_ℓ(u,v) < 1/3` in `lem:overlap`) that `overlap_speedyWalk_convex`
deletes: here `ell K 1 v` is `≈ 20×` smaller than `ell K 1 u`. -/
theorem exists_overlap_speedyWalk_sqrt_dim_counterexample :
    ∃ (n : ℕ) (K T : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n))
      (h : EuclideanSpace ℝ (Fin n) → ℝ),
      2 ≤ n ∧ MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, volume (Metric.ball x 1 ∩ K) ≠ 0) ∧
      MeasurableSet T ∧ u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < 1 / Real.sqrt n ∧ densDist h u v < 1 / 4 ∧
      ¬ (1 ≤ 20 * (speedyWalk K 1 u Tᶜ + speedyWalk K 1 v T)) := by
  classical
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = 23409 := ⟨23409, rfl⟩
  have hnpos : 0 < n := by omega
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 1 / 306 := ⟨1 / 306, rfl⟩
  set u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hnpos⟩ t with hudef
  set v : EuclideanSpace ℝ (Fin n) := 0 with hvdef
  have hnormuv : ‖u - v‖ = t := by
    rw [hvdef, sub_zero, hudef, PiLp.norm_single, Real.norm_eq_abs, htdef]
    norm_num
  have ht0 : 0 < ‖u - v‖ := by rw [hnormuv, htdef]; norm_num
  have ht : ‖u - v‖ < 1 / 2 := by rw [hnormuv, htdef]; norm_num
  set K : Set (EuclideanSpace ℝ (Fin n)) := apexConeBody u v with hKdef
  have hKc : Convex ℝ K := convex_apexConeBody u v
  have hKm : MeasurableSet K := measurableSet_apexConeBody u v
  have hKb : Bornology.IsBounded K := isBounded_apexConeBody u v
  have hb0 : 0 < volume (Metric.ball v 1 ∩ K) := volume_apexConeBody_ball_right_pos ht0 ht
  have hbtop : volume (Metric.ball v 1 ∩ K) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top)
  have hKvol : volume K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hb0 (measure_mono Set.inter_subset_right))
  -- Bernoulli: `(1 + t/4)ⁿ ≥ 1 + n·t/4 = 1 + 153/8 = 161/8 > 20`
  have hbern : (161 / 8 : ℝ) ≤ (1 + ‖u - v‖ / 4) ^ n := by
    have h := one_add_mul_le_pow (a := t / 4) (by rw [htdef]; norm_num) n
    have hnt : (n : ℝ) * (t / 4) = 153 / 8 := by rw [hndef, htdef]; norm_num
    rw [hnt] at h
    rw [hnormuv]
    linarith
  have hgap : (20 : ℝ≥0∞) * volume (Metric.ball v 1 ∩ K)
      < volume (Metric.ball u 1 ∩ K) := by
    have h1 : (20 : ℝ≥0∞) < ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) := by
      rw [show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2 (by linarith)
    calc (20 : ℝ≥0∞) * volume (Metric.ball v 1 ∩ K)
        = volume (Metric.ball v 1 ∩ K) * 20 := mul_comm _ _
      _ < volume (Metric.ball v 1 ∩ K) * ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) :=
          ENNReal.mul_lt_mul_right hb0.ne' hbtop h1
      _ = ENNReal.ofReal ((1 + ‖u - v‖ / 4) ^ n) * volume (Metric.ball v 1 ∩ K) := mul_comm _ _
      _ ≤ _ := volume_apexConeBody_ball_left_ge ht0 ht
  obtain ⟨T, hTm, huT, hvT, hfail⟩ :=
    exists_overlap_speedyWalk_fails_apexConeBody hnpos ht0 hgap
  refine ⟨n, K, T, u, v, fun _ => 1, by omega, hKm, hKc, hKb, hKvol,
    fun x hx => volume_ball_inter_ne_zero_of_convex hKc hKb hKvol hx one_pos,
    hTm, huT, mem_apexConeBody_of_left (by linarith), apex_mem_apexConeBody u v, hvT, ?_,
    by simp [densDist], hfail⟩
  have hsq : Real.sqrt ((n : ℕ) : ℝ) = 153 := by
    rw [hndef, show (((23409 : ℕ) : ℝ)) = (153 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hnormuv, hsq, htdef]
  norm_num

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.convex_apexConeBody
#print axioms Arlib.MarkovChains.isBounded_apexConeBody
#print axioms Arlib.MarkovChains.measurableSet_apexConeBody
#print axioms Arlib.MarkovChains.apex_mem_apexConeBody
#print axioms Arlib.MarkovChains.mem_apexConeBody_of_left
#print axioms Arlib.MarkovChains.apexConeBody_subset_halfspace_right
#print axioms Arlib.MarkovChains.norm_sub_le_of_mem_apexConeBody_halfspace_left
#print axioms Arlib.MarkovChains.mem_ball_left_of_mem_apexConeBody
#print axioms Arlib.MarkovChains.homothety_apexConeBody_image_subset
#print axioms Arlib.MarkovChains.volume_apexConeBody_ball_left_ge
#print axioms Arlib.MarkovChains.volume_apexConeBody_ball_right_pos
#print axioms Arlib.MarkovChains.volume_halfspace_max_le_apexConeBody
#print axioms Arlib.MarkovChains.volume_lens_le_apexConeBody
#print axioms Arlib.MarkovChains.volume_lens_eq_min_apexConeBody
#print axioms Arlib.MarkovChains.exists_halfspace_max_lt
#print axioms Arlib.MarkovChains.speedyWalk_compl_le_of_mem
#print axioms Arlib.MarkovChains.speedyWalk_eq_zero_of_null
#print axioms Arlib.MarkovChains.exists_overlap_speedyWalk_fails_apexConeBody
#print axioms Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample
