/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.StarPolar
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.StepLength

/-!
# Lemma 3.5 of [KLS95] at separation `δ/√n`, in the `min` form — proved

For a convex `K ∋ u, v` in `ℝⁿ` (`n ≥ 2`) and `‖u − v‖ ≤ δ/√n`,

    vol(K ∩ B(u,δ) ∩ B(v,δ))  ≥  (1/40) · min{ℓ(u), ℓ(v)} · vol(δBₙ)

(`kls_lemma35_at_sep_sqrt_dim`), where `ℓ(x) = vol(K ∩ B(x,δ))/vol(B(x,δ))` is the local
conductance of `Arlib/MarkovChains/Continuous/BallWalk.lean`.  This is Lemma 3.5 of [KLS95] as
cited by Cousins–Vempala at `1409.6011/vol3_journal.tex:592`, with the constant `1/40` in place
of the paper's `1/(e+1)`; no attempt is made to sharpen it.  Nothing is `sorry`ed and no
hypothesis beyond the paper's is carried — see the axiom audit at the bottom.

This closes the `δ/n` → `δ/√n` gap left open by
`Arlib/MarkovChains/Continuous/StarPolar.lean` (`kls_lemma35_at_sep_div_dim`), and it does so
**without** the inequality that file proposed, which
`Arlib/MarkovChains/Continuous/LensHalfspace.lean` refutes.

## The proof, and why it needs the `min`

Write `t = ‖u − v‖`, `A = K ∩ B(u,δ)`, `B = K ∩ B(v,δ)`, and split each along the half-space
through its own centre facing the other centre:

    A₊ = A ∩ {⟪x−u, v−u⟫ ≥ 0},  A₋ = A ∩ {⟪x−u, v−u⟫ ≤ 0},
    B₋ = B ∩ {⟪x−v, u−v⟫ ≥ 0},  B₊ = B ∩ {⟪x−v, u−v⟫ ≤ 0}.

Three bounds on `Λ = vol(K ∩ B(u,δ) ∩ B(v,δ))`, all with the same factor `c = (1 − 1/n)ⁿ ≥ 1/20`
(`Arlib.MarkovChains.inv_twenty_le_one_sub_inv_pow`):

* `c · vol A₊ ≤ Λ` and `c · vol B₋ ≤ Λ` — the direction-dependent contraction
  `Arlib.MarkovChains.volume_lens_inter_ge_halfspace`, already in `StarPolar.lean`, run from
  each centre.  (Its side condition `λ²δ² + t² ≤ δ²` holds at `λ = 1 − 1/n` because
  `t² ≤ δ²/n`.)
* `c · min{vol A₋, vol B₊} ≤ Λ` — **the new ingredient**, in three steps:
  - `midpoint_mem_ball_inter`: for `x ∈ A₋` and `y ∈ B₊` the midpoint `½(x+y)` lies in `K` and
    within `δ + t²/(4δ)` of *both* centres.  The sign conditions kill the two `t`-linear terms
    (`‖(x−u) + (v−u)‖² ≤ δ² + t²`), so the excess over `δ` is quadratic in `t`, i.e. `δ/(4n)` at
    `t = δ/√n` — **not** the `δ/(2√n)` a bare triangle inequality gives.  This is the whole
    reason the argument reaches `δ/√n`: an excess of `δ/(4n)` is what a `(1 − 1/n)` homothety
    can absorb at constant cost, and a `δ/√n` excess is not.
  - `min_volume_le_volume_midpoint_sum`: Brunn–Minkowski
    (`Arlib.brunn_minkowski_sharp_euclidean`) gives `min{vol A₋, vol B₊} ≤ vol(½A₋ + ½B₊)`.
  - `homothety_image_subset_lens_of_dilate`: the `(1 − 1/n)`-homothety about `u` carries the
    `(δ + δ/(4n))`-lens into the `δ`-lens.
* Since `A = A₊ ∪ A₋` and `B = B₋ ∪ B₊`, writing `m = min{vol A, vol B}`:
  `c·m ≤ Λ + c·vol A₋` and `c·m ≤ Λ + c·vol B₊`, hence `c·m ≤ Λ + c·min{vol A₋, vol B₊} ≤ 2Λ`.

**The `min` is essential and is used exactly once**, in that last line: the argument pairs the
*backward* half of `A` with the *forward* half of `B`, and can only conclude about whichever of
`vol A`, `vol B` is smaller.  It therefore does **not** prove the `max` form — which is false,
by `Arlib.MarkovChains.exists_halfspace_max_lt`.  On that refutation's witness
`apexConeBody u v` the set `B₊` is null and the third bound is vacuous, the second bound alone
giving `c·vol B ≤ Λ`, in agreement with `Arlib.MarkovChains.volume_lens_eq_min_apexConeBody`.

## What is assumed, and what is not

Nothing is assumed: `volume_lens_ge_min_ball_inter` and `kls_lemma35_at_sep_sqrt_dim` carry
exactly the hypotheses `2 ≤ n`, `Convex ℝ K`, `u ∈ K`, `v ∈ K`, `0 < δ`, `‖u−v‖ ≤ δ/√n`.  In
particular **no measurability hypothesis on `K`** (convex sets are null-measurable,
`Convex.nullMeasurableSet`), no bound on `ℓ`, and no comparability hypothesis such as
Cousins–Vempala's `d_ℓ(u,v) < 1/3`.  The separation hypothesis is used only through
`n·‖u−v‖² ≤ δ²`, so the result holds verbatim for any `‖u−v‖ ≤ δ/√n`.

## What is *not* done here

* The constant `1/40` is not optimised; the paper's `1/(e+1)` is presumably reachable by
  replacing `(1 − 1/n)ⁿ` with the sharper `√(1 − 1/n)ⁿ` available in the half-space step and by
  a tighter final combination.
* **This file does not close `cor:overlap` at `δ/√n`.**  As
  `LensHalfspace.lean`'s docstring explains, the `min` form does not by itself give
  `1 ≤ 20·(P_u(Tᶜ) + P_v(T))`: the two one-step laws are normalised by `ℓ(u)` and `ℓ(v)`
  separately, and passing from the `min` to the `max` needs the local conductances to be
  comparable — precisely the `d_ℓ(u,v) < 1/3` hypothesis that
  `Arlib.MarkovChains.overlap_speedyWalk_convex` deletes.
  `Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample` remains a genuine
  counterexample to that conclusion at `δ/√n`, and is not contradicted by anything here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal
open scoped InnerProductSpace
open scoped Pointwise

section LensMin

variable {n : ℕ}

/-! ### 1. The midpoint step -/

/-- **The crux.**  Let `x` lie in `B(u,δ) ∩ K` on the far side of `u` from `v`
(`⟪x − u, v − u⟫ ≤ 0`) and let `y` lie in `B(v,δ) ∩ K` on the far side of `v` from `u`
(`⟪y − v, u − v⟫ ≤ 0`).  Then their midpoint lies in `K` and within `δ + t²/(4δ)` of **both**
centres, where `t = ‖u − v‖`.

The point is the size of the excess.  A naive triangle inequality gives only `δ + t/2`; here
the sign conditions make the two `t`-linear terms cancel — `‖(x−u) + (v−u)‖² ≤ δ² + t²` — and
the excess drops to `t²/(4δ)`, which at `t = δ/√n` is `δ/(4n)`.  That is what a `(1 − 1/n)`
homothety can absorb; a `δ/√n`-sized excess is not. -/
theorem midpoint_mem_ball_inter {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {u v x y : EuclideanSpace ℝ (Fin n)} {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Metric.ball u δ ∩ K) (hxh : ⟪x - u, v - u⟫_ℝ ≤ 0)
    (hy : y ∈ Metric.ball v δ ∩ K) (hyh : ⟪y - v, u - v⟫_ℝ ≤ 0) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈
      (Metric.ball u (δ + ‖u - v‖ ^ 2 / (4 * δ))
        ∩ Metric.ball v (δ + ‖u - v‖ ^ 2 / (4 * δ))) ∩ K := by
  set t : ℝ := ‖u - v‖ with ht
  set z : EuclideanSpace ℝ (Fin n) := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hz
  have hxu : ‖x - u‖ < δ := by
    have := hx.1; rwa [Metric.mem_ball, dist_eq_norm] at this
  have hyv : ‖y - v‖ < δ := by
    have := hy.1; rwa [Metric.mem_ball, dist_eq_norm] at this
  have htnn : 0 ≤ t := norm_nonneg _
  have hvu : ‖v - u‖ = t := by rw [ht, norm_sub_rev]
  -- the two "corrected" vectors have norm at most `√(δ² + t²) ≤ δ + t²/(2δ)`
  have hbound : ∀ a w : EuclideanSpace ℝ (Fin n), ‖a‖ < δ → ‖w‖ = t →
      ⟪a, w⟫_ℝ ≤ 0 → ‖a + w‖ ≤ δ + t ^ 2 / (2 * δ) := by
    intro a w ha hw hip
    have hsq : ‖a + w‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, w⟫_ℝ + ‖w‖ ^ 2 := norm_add_sq_real a w
    have h1 : ‖a + w‖ ^ 2 ≤ δ ^ 2 + t ^ 2 := by
      rw [hsq, hw]; nlinarith [norm_nonneg a]
    have h2 : (0 : ℝ) ≤ δ + t ^ 2 / (2 * δ) := by positivity
    have hds : 2 * δ * (t ^ 2 / (2 * δ)) = t ^ 2 := by field_simp
    by_contra hcon
    rw [not_le] at hcon
    have h3 : (δ + t ^ 2 / (2 * δ)) ^ 2 < ‖a + w‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg (t ^ 2 / (2 * δ))]
  -- `z − u = ½((x−u) + (v−u)) + ½(y−v)`
  have hzu : z - u = (1 / 2 : ℝ) • ((x - u) + (v - u)) + (1 / 2 : ℝ) • (y - v) := by
    rw [hz]; module
  have hzv : z - v = (1 / 2 : ℝ) • ((y - v) + (u - v)) + (1 / 2 : ℝ) • (x - u) := by
    rw [hz]; module
  have hipx : ⟪x - u, v - u⟫_ℝ ≤ 0 := hxh
  have hipy : ⟪y - v, u - v⟫_ℝ ≤ 0 := hyh
  have hbx : ‖(x - u) + (v - u)‖ ≤ δ + t ^ 2 / (2 * δ) := hbound _ _ hxu hvu hipx
  have hby : ‖(y - v) + (u - v)‖ ≤ δ + t ^ 2 / (2 * δ) := hbound _ _ hyv ht hipy
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, hzu]
    have := norm_add_le ((1 / 2 : ℝ) • ((x - u) + (v - u))) ((1 / 2 : ℝ) • (y - v))
    rw [norm_smul, norm_smul, Real.norm_eq_abs] at this
    simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at this
    have h4 : t ^ 2 / (4 * δ) = (1 / 2) * (t ^ 2 / (2 * δ)) := by ring
    rw [h4]; linarith
  · rw [Metric.mem_ball, dist_eq_norm, hzv]
    have := norm_add_le ((1 / 2 : ℝ) • ((y - v) + (u - v))) ((1 / 2 : ℝ) • (x - u))
    rw [norm_smul, norm_smul, Real.norm_eq_abs] at this
    simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at this
    have h4 : t ^ 2 / (4 * δ) = (1 / 2) * (t ^ 2 / (2 * δ)) := by ring
    rw [h4]; linarith
  · exact hKc hx.2 hy.2 (by norm_num) (by norm_num) (by norm_num)

/-! ### 2. Contracting a slightly-too-large lens back into the true one -/

/-- If `K` is star-shaped about `u` and `λ(ζ − t) ≤ δ − t` with `λ ≤ 1`, the homothety of ratio
`λ` about `u` carries the `ζ`-lens into the `δ`-lens. -/
theorem homothety_image_subset_lens_of_dilate {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ ζ lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hcond : lam * (ζ - ‖u - v‖) ≤ δ - ‖u - v‖) :
    AffineMap.homothety u lam '' ((Metric.ball u ζ ∩ Metric.ball v ζ) ∩ K)
      ⊆ (Metric.ball u δ ∩ Metric.ball v δ) ∩ K := by
  rintro _ ⟨z, ⟨⟨hzu, hzv⟩, hzK⟩, rfl⟩
  have hzu' : ‖z - u‖ < ζ := by rwa [Metric.mem_ball, dist_eq_norm] at hzu
  have hzv' : ‖z - v‖ < ζ := by rwa [Metric.mem_ball, dist_eq_norm] at hzv
  have htnn : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hlz : lam * ζ ≤ δ := by nlinarith
  have hval : AffineMap.homothety u lam z = (1 - lam) • u + lam • z := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have hdu : AffineMap.homothety u lam z - u = lam • (z - u) := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
  have hdv : AffineMap.homothety u lam z - v = lam • (z - v) - (1 - lam) • (v - u) := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, hdu, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlam0]
    nlinarith
  · rw [Metric.mem_ball, dist_eq_norm, hdv]
    have h1 := norm_sub_le (lam • (z - v)) ((1 - lam) • (v - u))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlam0,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), norm_sub_rev v u] at h1
    nlinarith
  · rw [hval]
    exact hKc hzK (by linarith) hlam0.le (by ring)

/-! ### 3. Brunn–Minkowski: the midpoint body is at least the smaller of the two -/

/-- `min(vol X, vol Y) ≤ vol(½X + ½Y)` for convex `X`, `Y`.

No measurability hypothesis is needed (convex sets are null-measurable, and Brunn–Minkowski is
applied to measurable subsets of full measure), and no nonemptiness hypothesis either: if
either set is empty the left-hand side is `0`. -/
theorem min_volume_le_volume_midpoint_sum (hn : n ≠ 0)
    {X Y : Set (EuclideanSpace ℝ (Fin n))} (hX : Convex ℝ X) (hY : Convex ℝ Y) :
    min (volume X) (volume Y) ≤ volume ((1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y) := by
  obtain ⟨X', hX'sub, hX'meas, hX'eq⟩ :=
    (hX.nullMeasurableSet (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).exists_measurable_subset_ae_eq
  obtain ⟨Y', hY'sub, hY'meas, hY'eq⟩ :=
    (hY.nullMeasurableSet (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).exists_measurable_subset_ae_eq
  have hXvol : volume X' = volume X := measure_congr hX'eq
  have hYvol : volume Y' = volume Y := measure_congr hY'eq
  rcases Set.eq_empty_or_nonempty X' with hXe | hX'ne
  · simp [hXe] at hXvol
    simp [← hXvol]
  rcases Set.eq_empty_or_nonempty Y' with hYe | hY'ne
  · simp [hYe] at hYvol
    simp [← hYvol]
  have key := brunn_minkowski_sharp_euclidean (n := n) hn (lam := 1 / 2)
    (by norm_num) (by norm_num) hX'meas hY'meas hX'ne hY'ne
  norm_num at key
  set m : ℝ≥0∞ := min (volume X) (volume Y) with hm
  have hmX : m ^ ((n : ℝ))⁻¹ ≤ volume X' ^ ((n : ℝ))⁻¹ := by
    rw [hXvol]; exact ENNReal.rpow_le_rpow (min_le_left _ _) (by positivity)
  have hmY : m ^ ((n : ℝ))⁻¹ ≤ volume Y' ^ ((n : ℝ))⁻¹ := by
    rw [hYvol]; exact ENNReal.rpow_le_rpow (min_le_right _ _) (by positivity)
  have hsub : ((1 / 2 : ℝ) • X' + (1 / 2 : ℝ) • Y') ⊆ ((1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y) := by
    exact Set.add_subset_add (Set.smul_set_mono hX'sub) (Set.smul_set_mono hY'sub)
  have hstep : m ^ ((n : ℝ))⁻¹
      ≤ volume ((1 / 2 : ℝ) • X' + (1 / 2 : ℝ) • Y') ^ ((n : ℝ))⁻¹ := by
    refine le_trans ?_ key
    have : m ^ ((n : ℝ))⁻¹ = ENNReal.ofReal (1 / 2) * m ^ ((n : ℝ))⁻¹
        + ENNReal.ofReal (1 / 2) * m ^ ((n : ℝ))⁻¹ := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [this]
    exact add_le_add (mul_le_mul_right hmX _) (mul_le_mul_right hmY _)
  have hfin : m ≤ volume ((1 / 2 : ℝ) • X' + (1 / 2 : ℝ) • Y') := by
    have hpos : (0 : ℝ) < ((n : ℝ))⁻¹ := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
    exact (ENNReal.rpow_le_rpow_iff hpos).mp hstep
  exact hfin.trans (measure_mono hsub)

/-! ### 4. The `min` form of Lemma 3.5 at separation `δ/√n` -/

/-- The half-space `{x | ⟪x − c, w⟫ ≤ 0}` is convex. -/
lemma convex_inner_sub_le_zero (c w : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ⟪x - c, w⟫_ℝ ≤ 0} := by
  intro x hx y hy a b ha hb hab
  have hx' : ⟪x - c, w⟫_ℝ ≤ 0 := hx
  have hy' : ⟪y - c, w⟫_ℝ ≤ 0 := hy
  have hsplit : ⟪a • x + b • y - c, w⟫_ℝ = a * ⟪x - c, w⟫_ℝ + b * ⟪y - c, w⟫_ℝ := by
    have : a • x + b • y - c = a • (x - c) + b • (y - c) := by
      rw [smul_sub, smul_sub]
      rw [show (a • x - a • c) + (b • y - b • c) = a • x + b • y - (a • c + b • c) by abel,
        ← add_smul, hab, one_smul]
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  show ⟪a • x + b • y - c, w⟫_ℝ ≤ 0
  rw [hsplit]
  have := mul_nonpos_of_nonneg_of_nonpos ha hx'
  have := mul_nonpos_of_nonneg_of_nonpos hb hy'
  linarith

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`, in the `min` form**, stated with the two
ball-slices in place of the local conductances. -/
theorem volume_lens_ge_min_ball_inter (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 40) *
        min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have htnn : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  -- the separation, cleared of the square root
  have ht2 : (n : ℝ) * ‖u - v‖ ^ 2 ≤ δ ^ 2 := by
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    have h1 : ‖u - v‖ * Real.sqrt (n : ℝ) ≤ δ := by
      rw [← le_div_iff₀ hsn]; exact hsep
    have h2 : (‖u - v‖ * Real.sqrt (n : ℝ)) ^ 2 ≤ δ ^ 2 := by
      nlinarith [mul_nonneg htnn hsn.le]
    rw [mul_pow, hsq] at h2
    linarith
  have ht34 : ‖u - v‖ ≤ 3 * δ / 4 := by nlinarith
  -- the contraction factor
  set lam : ℝ := 1 - 1 / (n : ℝ) with hlamdef
  have hrpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hrhalf : 1 / (n : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hnR
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlamdef]; linarith
  have hc20 : (1 : ℝ) / 20 ≤ lam ^ n := inv_twenty_le_one_sub_inv_pow hn
  have hlamn0 : (0 : ℝ) ≤ lam ^ n := pow_nonneg hlam0.le n
  -- the half-space side condition
  have hhs : lam ^ 2 * δ ^ 2 + ‖u - v‖ ^ 2 ≤ δ ^ 2 := by
    have hlin : lam * δ ^ 2 + ‖u - v‖ ^ 2 ≤ δ ^ 2 := by
      have he : lam * δ ^ 2 = δ ^ 2 - δ ^ 2 / (n : ℝ) := by
        rw [hlamdef]; field_simp
      have hle : ‖u - v‖ ^ 2 ≤ δ ^ 2 / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]; linarith [ht2]
      rw [he]; linarith
    nlinarith [sq_nonneg δ, hlam0, hlam1]
  -- the two half-space bounds
  have hAp : ENNReal.ofReal (lam ^ n) *
      volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) :=
    volume_lens_inter_ge_halfspace (hKc.starConvex hu) hδ hlam0 hlam1 hhs
  have hBm : ENNReal.ofReal (lam ^ n) *
      volume (Metric.ball v δ ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ})
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
    have hhs' : lam ^ 2 * δ ^ 2 + ‖v - u‖ ^ 2 ≤ δ ^ 2 := by rwa [norm_sub_rev]
    have := volume_lens_inter_ge_halfspace (K := K) (u := v) (v := u)
      (hKc.starConvex hv) hδ hlam0 hlam1 hhs'
    rwa [Set.inter_comm (Metric.ball v δ) (Metric.ball u δ)] at this
  -- the Brunn–Minkowski bound on the two complementary half-spaces
  set Am : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.ball u δ ∩ K ∩ {x | ⟪x - u, v - u⟫_ℝ ≤ 0} with hAmdef
  set Bp : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.ball v δ ∩ K ∩ {x | ⟪x - v, u - v⟫_ℝ ≤ 0} with hBpdef
  have hmid : ENNReal.ofReal (lam ^ n) * min (volume Am) (volume Bp)
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
    rcases Set.eq_empty_or_nonempty Am with hAe | hAne
    · simp [hAe]
    rcases Set.eq_empty_or_nonempty Bp with hBe | hBne
    · simp [hBe]
    set ζ : ℝ := δ + δ / (4 * (n : ℝ)) with hζdef
    have hball : ∀ w : EuclideanSpace ℝ (Fin n),
        Metric.ball w (δ + ‖u - v‖ ^ 2 / (4 * δ)) ⊆ Metric.ball w ζ := by
      intro w
      refine Metric.ball_subset_ball ?_
      rw [hζdef]
      have he : δ / (4 * (n : ℝ)) - ‖u - v‖ ^ 2 / (4 * δ)
          = (δ ^ 2 - (n : ℝ) * ‖u - v‖ ^ 2) / (4 * δ * (n : ℝ)) := by
        field_simp
      have h0 : 0 ≤ δ / (4 * (n : ℝ)) - ‖u - v‖ ^ 2 / (4 * δ) := by
        rw [he]; exact div_nonneg (by linarith) (by positivity)
      linarith
    have hS : ((1 / 2 : ℝ) • Am + (1 / 2 : ℝ) • Bp)
        ⊆ (Metric.ball u ζ ∩ Metric.ball v ζ) ∩ K := by
      rintro z ⟨a, ⟨x, hxAm, rfl⟩, b, ⟨y, hyBp, rfl⟩, rfl⟩
      have hmem := midpoint_mem_ball_inter hKc hδ hxAm.1 hxAm.2 hyBp.1 hyBp.2
      exact ⟨⟨hball u hmem.1.1, hball v hmem.1.2⟩, hmem.2⟩
    have hcond : lam * (ζ - ‖u - v‖) ≤ δ - ‖u - v‖ := by
      rw [hlamdef, hζdef]
      have hdn : δ / (4 * (n : ℝ)) = δ * (1 / (n : ℝ)) / 4 := by ring
      rw [hdn]
      nlinarith [mul_nonneg hrpos.le
        (by nlinarith [hrpos, hδ] : (0:ℝ) ≤ 3 * δ / 4 - ‖u - v‖ + δ * (1 / (n : ℝ)) / 4)]
    have hsub := (homothety_image_subset_lens_of_dilate (K := K) (u := u) (v := v)
      (hKc.starConvex hu) hlam0 hlam1 hcond).trans (le_refl _)
    have himg := Measure.addHaar_image_homothety
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) u lam
      ((1 / 2 : ℝ) • Am + (1 / 2 : ℝ) • Bp)
    rw [finrank_euclideanSpace_fin, abs_of_nonneg hlamn0] at himg
    have hfinal : ENNReal.ofReal (lam ^ n) * volume ((1 / 2 : ℝ) • Am + (1 / 2 : ℝ) • Bp)
        ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
      rw [← himg]
      exact measure_mono ((Set.image_mono hS).trans (homothety_image_subset_lens_of_dilate
        (hKc.starConvex hu) hlam0 hlam1 hcond))
    refine le_trans (mul_le_mul_right ?_ _) hfinal
    refine min_volume_le_volume_midpoint_sum hn0 ?_ ?_
    · exact ((convex_ball u δ).inter hKc).inter (convex_inner_sub_le_zero u (v - u))
    · exact ((convex_ball v δ).inter hKc).inter (convex_inner_sub_le_zero v (u - v))
  -- splitting each ball-slice along its half-space
  have hAvol : volume (Metric.ball u δ ∩ K)
      ≤ volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}) + volume Am := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro x hx
    rcases le_total 0 (⟪x - u, v - u⟫_ℝ) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hBvol : volume (Metric.ball v δ ∩ K)
      ≤ volume (Metric.ball v δ ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}) + volume Bp := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro x hx
    rcases le_total 0 (⟪x - v, u - v⟫_ℝ) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  -- assembly
  set c : ℝ≥0∞ := ENNReal.ofReal (lam ^ n) with hcdef
  set m : ℝ≥0∞ := min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) with hmdef
  set L : ℝ≥0∞ := volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) with hLdef
  have hA' : c * m ≤ L + c * volume Am := by
    calc c * m ≤ c * volume (Metric.ball u δ ∩ K) := mul_le_mul_right (min_le_left _ _) _
      _ ≤ c * (volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}) + volume Am) :=
          mul_le_mul_right hAvol _
      _ = c * volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ}) + c * volume Am :=
          mul_add _ _ _
      _ ≤ L + c * volume Am := add_le_add hAp le_rfl
  have hB' : c * m ≤ L + c * volume Bp := by
    calc c * m ≤ c * volume (Metric.ball v δ ∩ K) := mul_le_mul_right (min_le_right _ _) _
      _ ≤ c * (volume (Metric.ball v δ ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}) + volume Bp) :=
          mul_le_mul_right hBvol _
      _ = c * volume (Metric.ball v δ ∩ K ∩ {x | 0 ≤ ⟪x - v, u - v⟫_ℝ}) + c * volume Bp :=
          mul_add _ _ _
      _ ≤ L + c * volume Bp := add_le_add hBm le_rfl
  have hmin : c * m ≤ L + c * min (volume Am) (volume Bp) := by
    rcases le_total (volume Am) (volume Bp) with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have htwo : c * m ≤ 2 * L := by
    have : L + c * min (volume Am) (volume Bp) ≤ L + L := add_le_add le_rfl hmid
    calc c * m ≤ L + c * min (volume Am) (volume Bp) := hmin
      _ ≤ L + L := this
      _ = 2 * L := by rw [two_mul]
  have hcge : ENNReal.ofReal (1 / 20) ≤ c := by
    rw [hcdef]; exact ENNReal.ofReal_le_ofReal hc20
  have hstep : 2 * (ENNReal.ofReal (1 / 40) * m) ≤ 2 * L := by
    have he : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 40) = ENNReal.ofReal (1 / 20) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc 2 * (ENNReal.ofReal (1 / 40) * m) = ENNReal.ofReal (1 / 20) * m := by
          rw [← mul_assoc, he]
      _ ≤ c * m := mul_le_mul_left hcge _
      _ ≤ 2 * L := htwo
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hstep

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`**, in the paper's own shape: the lens carries a
constant fraction of `min{ℓ(u), ℓ(v)}·vol(δBₙ)`.  The constant here is `1/40`, not the paper's
`1/(e+1)`. -/
theorem kls_lemma35_at_sep_sqrt_dim (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 40) * min (ell K δ u) (ell K δ v)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have hkey : min (ell K δ u) (ell K δ v)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      = min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) := by
    rcases le_total (ell K δ u) (ell K δ v) with h | h
    · rw [min_eq_left h, ell_mul_volume_ball K hδ u]
      symm
      refine min_eq_left ?_
      rw [← ell_mul_volume_ball K hδ u, ← ell_mul_volume_ball K hδ v]
      exact mul_le_mul_left h _
    · rw [min_eq_right h, ell_mul_volume_ball K hδ v]
      symm
      refine min_eq_right ?_
      rw [← ell_mul_volume_ball K hδ u, ← ell_mul_volume_ball K hδ v]
      exact mul_le_mul_left h _
  rw [mul_assoc, hkey]
  exact volume_lens_ge_min_ball_inter hn hKc hu hv hδ hsep

end LensMin

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.midpoint_mem_ball_inter
#print axioms Arlib.MarkovChains.homothety_image_subset_lens_of_dilate
#print axioms Arlib.MarkovChains.min_volume_le_volume_midpoint_sum
#print axioms Arlib.MarkovChains.convex_inner_sub_le_zero
#print axioms Arlib.MarkovChains.volume_lens_ge_min_ball_inter
#print axioms Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim
