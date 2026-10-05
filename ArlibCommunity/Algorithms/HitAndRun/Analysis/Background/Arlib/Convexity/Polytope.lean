/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Polytopes cut out by linear inequalities, and the cost of inflating them

A **polytope** here is the solution set of a finite (or arbitrary) system of
linear inequalities in `EuclideanSpace ℝ (Fin n)`,

  `body A b = {x | ∀ i, ⟪A i, x⟫ ≤ b i}`,

and its **`κ`-inflation** is the body obtained by pushing every facet outwards by
a *metric* distance `κ`:

  `inflate A b κ = {x | ∀ i, ⟪A i, x⟫ ≤ b i + κ‖A i‖}`.

The displacement `κ‖A i‖` (rather than `κ`) is exactly what makes `inflate A b κ`
the set of points within distance `κ` of every facet hyperplane in the *ambient*
metric, so that inflating is a geometric, not a coordinate-dependent, operation.

## Main results

* `Arlib.Polytope.convex_body`, `Arlib.Polytope.isClosed_body`,
  `Arlib.Polytope.measurableSet_body` — the body is a closed convex measurable
  set (and likewise for every inflation).
* `Arlib.Polytope.inflate_zero` — `inflate A b 0 = body A b`.
* `Arlib.Polytope.inflate_mono`, `Arlib.Polytope.body_subset_inflate` — inflation
  is monotone in `κ` and contains the body for `κ ≥ 0`.
* `Arlib.Polytope.inner_center_le_of_ball_subset` — an inscribed ball
  `Metric.ball c γ ⊆ body A b` forces every facet to satisfy
  `⟪A i, c⟫ + γ‖A i‖ ≤ b i`. This is the one place the geometry enters.
* `Arlib.Polytope.inflate_subset_homothety` and its unbundled restatement
  `Arlib.Polytope.inflate_subset_vadd_smul` — **the homothety bound**: the
  `κ`-inflation sits inside the `(1 + κ/γ)`-homothety of the body *about the
  centre of the inscribed ball*.
* `Arlib.Polytope.volume_inflate_le` — the volume consequence,
  `vol (inflate A b κ) ≤ (1 + κ/γ)ⁿ · vol (body A b)`.

The last statement is the engine of Kannan–Vempala's Lemma 1: it bounds the
acceptance probability of the rejection sampler that samples the inflated body
and keeps the points landing in the body itself.

## Implementation notes

Nothing here needs `Fintype ι`: all the statements are intersections over an
arbitrary index type, and the volume bound goes through the homothety, not
through any facet-by-facet count. The centre `c` of the inscribed ball is a free
parameter — no relation between different polytopes' centres is used, so the
bound applies verbatim to each member of a family of disjoint polytopes.
-/

namespace Arlib

open MeasureTheory Set Pointwise
open scoped InnerProductSpace

namespace Polytope

variable {n : ℕ} {ι : Type*}

/-- The polytope `{x | ∀ i, ⟪A i, x⟫ ≤ b i}` cut out by the linear inequalities
with normals `A i` and offsets `b i`. -/
def body (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i}

/-- The `κ`-**inflation** of `body A b`: every facet hyperplane is displaced
outwards by the metric distance `κ`, i.e. its offset grows by `κ‖A i‖`.
Negative `κ` deflates. -/
def inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i + κ * ‖A i‖}

@[simp]
theorem mem_body {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} : x ∈ body A b ↔ ∀ i, ⟪A i, x⟫_ℝ ≤ b i :=
  Iff.rfl

@[simp]
theorem mem_inflate {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ} {κ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ inflate A b κ ↔ ∀ i, ⟪A i, x⟫_ℝ ≤ b i + κ * ‖A i‖ :=
  Iff.rfl

/-! ## The inflation as an intersection of half-spaces -/

/-- `inflate A b κ` is the intersection of the closed half-spaces it is defined
by. This is the form in which convexity, closedness and measurability are read
off. -/
theorem inflate_eq_iInter (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    inflate A b κ = ⋂ i, {x | ⟪A i, x⟫_ℝ ≤ b i + κ * ‖A i‖} := by
  ext x
  simp [inflate]

/-- `body A b` is the intersection of the closed half-spaces it is defined by. -/
theorem body_eq_iInter (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    body A b = ⋂ i, {x | ⟪A i, x⟫_ℝ ≤ b i} := by
  ext x
  simp [body]

/-- `x ↦ ⟪a, x⟫_ℝ` is a linear map, in the bundled-free `IsLinearMap` form that
`convex_halfSpace_le` consumes. -/
theorem isLinearMap_inner_right (a : EuclideanSpace ℝ (Fin n)) :
    IsLinearMap ℝ (fun x : EuclideanSpace ℝ (Fin n) => ⟪a, x⟫_ℝ) :=
  ⟨fun x y => inner_add_right a x y, fun r x => real_inner_smul_right a x r⟩

/-- Every inflation of a polytope is convex: it is an intersection of
half-spaces. -/
theorem convex_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    Convex ℝ (inflate A b κ) := by
  rw [inflate_eq_iInter]
  exact convex_iInter fun i => convex_halfSpace_le (isLinearMap_inner_right (A i)) _

/-- A polytope is convex. -/
theorem convex_body (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    Convex ℝ (body A b) := by
  rw [body_eq_iInter]
  exact convex_iInter fun i => convex_halfSpace_le (isLinearMap_inner_right (A i)) _

/-- Every inflation of a polytope is closed. -/
theorem isClosed_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    IsClosed (inflate A b κ) := by
  rw [inflate_eq_iInter]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- A polytope is closed. -/
theorem isClosed_body (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    IsClosed (body A b) := by
  rw [body_eq_iInter]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Every inflation of a polytope is measurable. -/
theorem measurableSet_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ) :
    MeasurableSet (inflate A b κ) :=
  (isClosed_inflate A b κ).measurableSet

/-- A polytope is measurable. -/
theorem measurableSet_body (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    MeasurableSet (body A b) :=
  (isClosed_body A b).measurableSet

/-! ## Elementary properties of the inflation -/

/-- Inflating by `0` does nothing. -/
@[simp]
theorem inflate_zero (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) :
    inflate A b 0 = body A b := by
  ext x
  simp [inflate, body]

/-- The inflation is monotone in the inflation parameter. -/
theorem inflate_mono (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {κ₁ κ₂ : ℝ}
    (h : κ₁ ≤ κ₂) : inflate A b κ₁ ⊆ inflate A b κ₂ := by
  intro x hx i
  have := hx i
  nlinarith [norm_nonneg (A i)]

/-- For `κ ≥ 0` the inflation contains the body. -/
theorem body_subset_inflate (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) : body A b ⊆ inflate A b κ := by
  rw [← inflate_zero A b]
  exact inflate_mono A b hκ

/-! ## The inscribed ball -/

/-- **An inscribed ball bounds every facet away from its centre.**

If `Metric.ball c γ ⊆ body A b` with `γ > 0`, then for every constraint `i` the
centre satisfies `⟪A i, c⟫ + γ‖A i‖ ≤ b i` — that is, `c` has slack at least
`γ‖A i‖` in the `i`-th inequality.

This is the only geometric input to the homothety bound below. -/
theorem inner_center_le_of_ball_subset {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ body A b) (i : ι) :
    ⟪A i, c⟫_ℝ + γ * ‖A i‖ ≤ b i := by
  -- the closed ball is still inside the body, since the body is closed
  have hclosed : Metric.closedBall c γ ⊆ body A b := by
    rw [← closure_ball c hγ.ne']
    exact (isClosed_body A b).closure_subset_iff.2 hball
  rcases eq_or_ne (A i) 0 with h0 | h0
  · -- degenerate facet: the constraint reads `0 ≤ b i`, and `c` itself witnesses it
    have hc : c ∈ body A b := hclosed (Metric.mem_closedBall_self hγ.le)
    simpa [h0] using hc i
  · -- the point of the closed ball farthest in the direction `A i`
    have hnorm : 0 < ‖A i‖ := norm_pos_iff.2 h0
    set y : EuclideanSpace ℝ (Fin n) := c + (γ / ‖A i‖) • A i with hy
    have hmem : y ∈ Metric.closedBall c γ := by
      rw [Metric.mem_closedBall, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ γ / ‖A i‖)]
      have h1 : γ / ‖A i‖ * ‖A i‖ = γ := by field_simp
      exact h1.le
    have hinner : ⟪A i, y⟫_ℝ = ⟪A i, c⟫_ℝ + γ * ‖A i‖ := by
      rw [hy, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    calc ⟪A i, c⟫_ℝ + γ * ‖A i‖ = ⟪A i, y⟫_ℝ := hinner.symm
      _ ≤ b i := hclosed hmem i

/-! ## The homothety bound -/

/-- The image of a set under `AffineMap.homothety c k`, written with the
pointwise translation/dilation operations. -/
theorem homothety_image_eq (c : EuclideanSpace ℝ (Fin n)) (k : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    AffineMap.homothety c k '' S = c +ᵥ (k • ((-c) +ᵥ S)) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_vadd, Set.image_image,
    Set.image_image]
  refine Set.image_congr' (fun x => ?_)
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
  module

/-- **The homothety bound (set form).**

If `Metric.ball c γ ⊆ body A b` with `γ > 0` and `κ ≥ 0`, then the `κ`-inflation
of the body is contained in the homothety of the body about `c` with ratio
`1 + κ/γ`.

The witness for `x` in the inflation is `y = c + (x − c)/(1 + κ/γ)`: each
constraint gives
`⟪A i, y⟫ = ⟪A i, c⟫ + (⟪A i, x⟫ − ⟪A i, c⟫)/(1 + κ/γ) ≤ b i`, because the
inscribed ball forces `⟪A i, c⟫ ≤ b i − γ‖A i‖`
(`Arlib.Polytope.inner_center_le_of_ball_subset`). -/
theorem inflate_subset_homothety {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : Metric.ball c γ ⊆ body A b) :
    inflate A b κ ⊆ AffineMap.homothety c (1 + κ / γ) '' body A b := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  intro x hx
  refine ⟨AffineMap.homothety c (1 + κ / γ)⁻¹ x, fun i => ?_, ?_⟩
  · -- abbreviations: `B` is the slack of the centre in constraint `i`
    set B : ℝ := b i - ⟪A i, c⟫_ℝ with hB
    have hballi : γ * ‖A i‖ ≤ B := by
      have := inner_center_le_of_ball_subset hγ hball i
      rw [hB]; linarith
    have hlin : ⟪A i, AffineMap.homothety c (1 + κ / γ)⁻¹ x⟫_ℝ
        = (1 + κ / γ)⁻¹ * (⟪A i, x⟫_ℝ - ⟪A i, c⟫_ℝ) + ⟪A i, c⟫_ℝ := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
        inner_add_right, inner_sub_right, real_inner_smul_right]
    have hx' : ⟪A i, x⟫_ℝ - ⟪A i, c⟫_ℝ ≤ B + κ * ‖A i‖ := by
      have := hx i; rw [hB]; linarith
    -- `B + κ‖A i‖ ≤ (1 + κ/γ)·B`, since `γ‖A i‖ ≤ B` and `κ ≥ 0`
    have hkey : B + κ * ‖A i‖ ≤ (1 + κ / γ) * B := by
      have hrw : (1 + κ / γ) * B = B + (κ * B) / γ := by field_simp
      have h3 : κ * ‖A i‖ ≤ (κ * B) / γ := by
        rw [le_div_iff₀ hγ]; nlinarith
      linarith [hrw]
    have hstep : (1 + κ / γ)⁻¹ * (⟪A i, x⟫_ℝ - ⟪A i, c⟫_ℝ)
        ≤ (1 + κ / γ)⁻¹ * ((1 + κ / γ) * B) :=
      mul_le_mul_of_nonneg_left (hx'.trans hkey) (inv_nonneg.2 hk.le)
    have hcancel : (1 + κ / γ)⁻¹ * ((1 + κ / γ) * B) = B := by field_simp
    rw [hcancel] at hstep
    rw [hlin, hB] at *
    linarith
  · rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hk), one_smul, sub_add_cancel]

/-- **The homothety bound, unbundled.** Same statement as
`Arlib.Polytope.inflate_subset_homothety`, with the homothety written out as
translate–dilate–translate. -/
theorem inflate_subset_vadd_smul {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : Metric.ball c γ ⊆ body A b) :
    inflate A b κ ⊆ c +ᵥ ((1 + κ / γ) • ((-c) +ᵥ body A b)) := by
  rw [← homothety_image_eq]
  exact inflate_subset_homothety hγ hκ hball

/-- **The volume cost of inflating.**

`vol (inflate A b κ) ≤ (1 + κ/γ)ⁿ · vol (body A b)` whenever the body contains a
ball of radius `γ > 0` and `κ ≥ 0`. Immediate from
`Arlib.Polytope.inflate_subset_homothety` and the scaling law of Haar measure
under a homothety.

This is the engine of Kannan–Vempala's Lemma 1: it lower-bounds the acceptance
probability `vol (body) / vol (inflate)` of the rejection sampler by
`(1 + κ/γ)^{-n}`. -/
theorem volume_inflate_le {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hball : Metric.ball c γ ⊆ body A b) :
    volume (inflate A b κ) ≤ ENNReal.ofReal ((1 + κ / γ) ^ n) * volume (body A b) := by
  have hk : (0:ℝ) < 1 + κ / γ := by
    have : (0:ℝ) ≤ κ / γ := div_nonneg hκ hγ.le
    linarith
  have hmono := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (inflate_subset_homothety hγ hκ hball)
  rwa [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hk.le n)] at hmono

end Polytope

end Arlib
