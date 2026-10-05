/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.LensMin
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.LensHalfspace
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyOverlap

/-!
# Cousins–Vempala's `cor:overlap` at separation `δ/√n`, under `ℓ`-comparability — proved

For a measurable convex `K ⊆ ℝⁿ` (`n ≥ 2`) with `vol(B(x,δ) ∩ K) ≠ 0` on `K`, a measurable
`T`, and `u, v ∈ K` with `‖u − v‖ < δ/√n` whose local conductances are comparable
(`d_ℓ(u,v) < 1/3`, written division-free as `ℓ(u) ≤ (3/2)·ℓ(v)` and `ℓ(v) ≤ (3/2)·ℓ(u)`),
one step of the speedy walk satisfies

    1  ≤  12 · (P_u(Tᶜ) + P_v(T))

(`overlap_speedyWalk_sqrt_of_ell_comparable`).  This is `lem:overlap`/`cor:overlap` of
Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*
(`1409.6011/vol3_journal.tex:581` and `:612`), at the paper's own separation and with the
paper's own hypotheses.  Nothing is `sorry`ed; see the axiom audit at the bottom.

This is the last step between `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim`
(`LensMin.lean`) and a conductance bound `Ω(δ/(σ√n))`: `12 ≤ 20`, so the bound composes with
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap`, which is done in
`conductance_speedyGaussian_ge_of_ell_comparable`.

## The proof — Cousins–Vempala's, with `1/8` for their `1/(e+1)`

With `C = B(u,δ) ∩ B(v,δ)` and `M = max{vol(B(u,δ) ∩ K), vol(B(v,δ) ∩ K)}`:

* `P_u(Tᶜ) ≥ vol(Tᶜ ∩ C ∩ K)/vol(B(u,δ) ∩ K) ≥ vol(Tᶜ ∩ C ∩ K)/M`, and symmetrically for
  `P_v(T)` — the one-step law is uniform on the accepted part of the proposal ball, and its
  holding atom is discarded;
* `T` and `Tᶜ` partition, so the two numerators sum to `vol(C ∩ K)`.  **That is the only
  place the split between `T` and `Tᶜ` is used**, and the only place the two terms combine;
* Lemma 3.5 of [KLS95] at `δ/√n` gives `vol(C ∩ K) ≥ (1/8)·min` (`volume_lens_ge_min_ball_inter_sharp`);
* comparability gives `min ≥ (2/3)·M`;
* so the sum is at least `(1/8)·(2/3) = 1/12`.

The paper reaches `1/6` because it quotes `1/(e+1) ≈ 0.269` for the lens constant where the
`1/8 = 0.125` proved here is used.

## The constant, and how `60` became `12`

Feeding `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim`'s constant `1/40` through the chain
above gives `1/60`, i.e. `1 ≤ 60·(…)`, which does **not** compose with the `20` that
`conductance_speedyGaussian_ge` demands.  The `1/40` is not, however, geometric: `LensMin.lean`
bounds its contraction factor `(1 − 1/n)ⁿ` below by `1/20`
(`Arlib.MarkovChains.inv_twenty_le_one_sub_inv_pow`), whereas `(1 − 1/n)ⁿ` *increases* in `n`
from `1/4` at `n = 2` to `e⁻¹`.  `quarter_le_one_sub_inv_pow` gives the sharp uniform bound
`1/4`, which carries the lens constant from `1/40` to `1/8` and the overlap constant from
`60` to `12` — with the geometry of `LensMin.lean` reused verbatim, not reproved.

A different sharpening — taking `λ = √(1 − 1/n)` rather than `λ = 1 − 1/n`, which the
half-space step's side condition `λ²δ² + t² ≤ δ²` does permit — was considered and **not
taken here**: the *midpoint* step of `LensMin.lean` needs `λ·(ζ − t) ≤ δ − t` with
`ζ = δ(1 + 1/(4n))`, and at `n = 2`, `t = δ/√2` that reads `0.2956δ ≤ 0.2929δ`, which is
false.  It replaces rational arithmetic by square roots throughout, and the `1/8` route
above is two changed lines and already composes.

⚠ **That rejection is correct only for the crude midpoint radius `ζ = δ(1 + 1/(4n))`, and
`Arlib/MarkovChains/Continuous/LensSharp.lean` since carried the route through.**  The crude
`ζ` is itself a weakening of the *exact* midpoint radius `(δ + √(δ² + t²))/2` via
`√(δ² + t²) ≤ δ + t²/(2δ)`; at `n = 2`, `t = δ/√2` the exact radius is `1.11237δ` against the
crude `1.125δ`, and the side condition becomes `0.28657δ ≤ 0.29289δ` — true, with 2% to
spare.  The 1% difference in radius binds only at `n = 2`, which is exactly where the
constant is decided.  `LensSharp.volume_lens_ge_min_ball_inter_quarter` therefore reaches
`1/4` with the binders of `volume_lens_ge_min_ball_inter_sharp` unchanged, and
`LensSharp.lens_side_two` machine-checks the `n = 2` side condition.  `1/(e+1) ≈ 0.269` is
*not* reachable from this skeleton: at `n = 2` the half-space factor caps at `λ² = 1/2` and
the midpoint factor at `0.5223`, so the harmonic combination caps at `0.2555`.

## The `δ/√n` counterexample is excluded — the whole content of the hypothesis

`Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample`
(`LensHalfspace.lean:636`) proves that the conclusion of
`Arlib.MarkovChains.overlap_speedyWalk_convex` is **false** at separation `δ/√n`.  Nothing
here contradicts it, because its witness violates comparability, by a wide margin and
verifiably: `exists_ell_not_comparable_at_sqrt_dim_counterexample` re-derives that witness
(`n = 23409`, `δ = 1`, `K = apexConeBody u v`, `‖u − v‖ = 1/306 < 1/153 = δ/√n`) and proves

    20 · vol(B(v,1) ∩ K)  <  vol(B(u,1) ∩ K),   hence  ¬ (ℓ(u) ≤ (3/2)·ℓ(v)).

`v` is the cone's apex, so `ℓ(v)` is more than `20×` smaller than `ℓ(u)`: `d_ℓ(u,v) > 19/20
= 0.95`, against a hypothesis that permits `1/3`.  The whole content of this file is that
reinstating Cousins–Vempala's `d_ℓ(u,v) < 1/3` — which `overlap_speedyWalk_convex`
deliberately deletes — is exactly what the `√n` separation costs.

Note also that the counterexample takes `h ≡ 1`, which is *not* the speedy walk's stationary
density: that density is proportional to `ℓ` (`Arlib.MarkovChains.ellMeasure`), and the paper
applies `cor:overlap` with `h = f·ℓ`.  With `h ∝ ℓ` the counterexample's own
`densDist h u v` would be `> 0.95`, so the consumer's `d_h(u,v) < 1/4` binder would already
exclude it.  See "what is assumed" below.

## Comparability versus the local-conductance floor

`Arlib.MarkovChains.overlap_speedyWalk` (`SpeedyOverlap.lean:640`) also reaches `δ/√n`, but
under the local-conductance **floor** `11 ≤ 20·ℓ(x)` for all `x ∈ K`.  That floor fails at
every boundary point of every bounded convex body, where `ℓ → 1/2 < 11/20`, so that theorem
is empty for convex bodies; its own witness is `K = ℝ²`.  Comparability is a different kind
of hypothesis: it is satisfiable on a bounded convex body of positive volume
(`exists_overlap_speedyWalk_sqrt_comparable_witness`, at `K = B(0,1) ⊆ ℝ²` and `δ = 3`, where
`ℓ` is constant on `K`), and it is the paper's.  It is still a genuine restriction — it fails
at a sharp corner, as the counterexample shows.

## What is assumed, and what is not

Assumed: `hpos` (`vol(B(x,δ) ∩ K) ≠ 0` on `K`, automatic on a bounded convex body of positive
volume by `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`), convexity, measurability,
and comparability.  No floor on `ℓ`, no bound on the diameter of `K`, no `n`-dependence beyond
`n ≥ 2`.  `u ∈ T`, `v ∉ T` and `densDist h u v < 1/4` are carried only to match the consumer's
binder and are **not used**, so the result is stronger than `cor:overlap` in those respects.

**Not proved here: `lem:f-dist` (`vol3_journal.tex:548`).**  Cousins–Vempala do not assume
`d_ℓ(u,v) < 1/3` in `cor:overlap`; they *derive* it from that corollary's own hypothesis
`d_h(u,v) < 1/4` for the specific density `h = f·ℓ`, using `0.9 ≤ f(v)/f(u) ≤ 1.1` at
separation `δ/√n` with `δ ≤ σ/(8√n)` — a Gaussian-ratio estimate the paper states only "for
`n` large enough", and whose arithmetic is tight (`(3/4)/1.1 = 0.6818 > 2/3`).  Formalising
it would turn `hcomp` from a hypothesis into a consequence of the consumer's existing binder,
and is the natural next step.  `ell_le_of_densDist_ell_lt` supplies the second half of that
bridge — `d_ℓ < 1/3 ⟹ comparability` — already.

## No rate claim

`thm:iso` is a hypothesis of `conductance_speedyGaussian_ge`, and `hcomp` is a hypothesis
here.  Nothing below asserts, or may be quoted as asserting, a polynomial mixing time.

## Main results

* `quarter_le_one_sub_inv_pow` — `(1 − 1/n)ⁿ ≥ 1/4`, the sharp uniform bound.
* `volume_lens_ge_min_ball_inter_sharp`, `kls_lemma35_at_sep_sqrt_dim_sharp` — Lemma 3.5 of
  [KLS95] at `δ/√n` with `1/8` in place of `1/40`.
* `one_le_twelve_mul_speedyWalk_add_of_comparable` — the core, constant `12`.
* `overlap_speedyWalk_sqrt_of_ell_comparable` — `cor:overlap` at `δ/√n`, per-pair hypothesis.
* `overlap_speedyWalk_sqrt_of_ell_comparable_global`,
  `overlap_speedyWalk_sqrt_of_densDist_ell` — the same in `hoverlap`'s exact binder shape.
* `conductance_speedyGaussian_ge_of_ell_comparable` — `thm:speedyconductance` at `δ/√n`.
* `exists_overlap_speedyWalk_sqrt_comparable_witness` — non-vacuity, on a bounded convex body.
* `exists_ell_not_comparable_at_sqrt_dim_counterexample` — the `δ/√n` counterexample is out of
  scope.

## References

Cousins and Vempala, §4.1 (`1409.6011/vol3_journal.tex:509–700`).
Kannan, Lovász and Simonovits (1995), Lemma 3.5 — proved at `δ/√n` in
`Arlib/MarkovChains/Continuous/LensMin.lean`, sharpened here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal
open scoped InnerProductSpace
open scoped Pointwise

section OverlapSqrt

variable {n : ℕ}

/-! ## 1. The contraction constant, sharpened from `1/20` to `1/4` -/

/-- **`(1 − 1/n)ⁿ ≥ 1/4` for `n ≥ 2`.**  This is the sharp constant-order bound:
`(1 − 1/n)ⁿ` *increases* in `n` from `1/4` at `n = 2` to `e⁻¹`, so `1/4` is attained and
cannot be improved uniformly in `n`.

`Arlib.MarkovChains.inv_twenty_le_one_sub_inv_pow` gives only `1/20`, which is what
`Arlib/MarkovChains/Continuous/LensMin.lean` consumes and hence the source of that file's
`1/40`.  The factor `5` recovered here is exactly what carries the overlap constant of this
file from `60` down to `12`, i.e. past the `20` that
`Arlib.MarkovChains.conductance_speedyGaussian_ge` demands.

The proof avoids proving monotonicity: at `n = 2` it is the equality `(1/2)² = 1/4`, and for
`n ≥ 3` it is `Arlib.MarkovChains.inv_exp_add_one_le_one_sub_inv_pow` together with
`1/4 ≤ 1/(e+1) ⟺ e ≤ 3`. -/
theorem quarter_le_one_sub_inv_pow (hn : 2 ≤ n) : (1 : ℝ) / 4 ≤ (1 - 1 / (n : ℝ)) ^ n := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · rw [← h2]
    norm_num
  · have h3' : 3 ≤ n := h3
    refine le_trans ?_ (inv_exp_add_one_le_one_sub_inv_pow h3')
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith

/-! ## 2. Lemma 3.5 of [KLS95] at separation `δ/√n`, with the constant `1/8` -/

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`, in the `min` form, with the constant `1/8`.**

This is `Arlib.MarkovChains.volume_lens_ge_min_ball_inter` with `1/40` improved to `1/8`.
The geometry is unchanged and is *not* reproved: the three bounds are the very lemmas
`Arlib.MarkovChains.volume_lens_inter_ge_halfspace`,
`Arlib.MarkovChains.midpoint_mem_ball_inter`,
`Arlib.MarkovChains.homothety_image_subset_lens_of_dilate` and
`Arlib.MarkovChains.min_volume_le_volume_midpoint_sum` that `LensMin.lean` proves.  The only
change is that the contraction factor `(1 − 1/n)ⁿ` is bounded below by `1/4`
(`quarter_le_one_sub_inv_pow`) rather than by `1/20`, and `1/8 = (1/4)/2` where the `2` is the
final combination of the forward and backward halves.

`1/8` is within a factor `2` of the paper's `1/(e+1) ≈ 0.269`; the remaining factor is the
`2` of that combination, not the contraction constant. -/
theorem volume_lens_ge_min_ball_inter_sharp (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 8) *
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
  -- **the one changed line**: `1/4`, not `1/20`
  have hc4 : (1 : ℝ) / 4 ≤ lam ^ n := quarter_le_one_sub_inv_pow hn
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
  have hcge : ENNReal.ofReal (1 / 4) ≤ c := by
    rw [hcdef]; exact ENNReal.ofReal_le_ofReal hc4
  have hstep : 2 * (ENNReal.ofReal (1 / 8) * m) ≤ 2 * L := by
    have he : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 8) = ENNReal.ofReal (1 / 4) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc 2 * (ENNReal.ofReal (1 / 8) * m) = ENNReal.ofReal (1 / 4) * m := by
          rw [← mul_assoc, he]
      _ ≤ c * m := mul_le_mul_left hcge _
      _ ≤ 2 * L := htwo
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hstep

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`, in the paper's own `ℓ` shape, with the
constant `1/8`** — `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` with `1/40` improved to
`1/8`.  Not used below (the proof of the overlap bound works with the ball-slice volumes
directly); stated because it is the form the paper quotes. -/
theorem kls_lemma35_at_sep_sqrt_dim_sharp (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 8) * min (ell K δ u) (ell K δ v)
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
  exact volume_lens_ge_min_ball_inter_sharp hn hKc hu hv hδ hsep

/-! ## 3. Comparability, in the two shapes -/

/-- **A one-sided `ℓ`-comparison is a one-sided comparison of the ball-slice volumes.**
`ell K δ x · vol(δBₙ) = vol(B(x,δ) ∩ K)` (`Arlib.MarkovChains.ell_mul_volume_ball`), and the
factor `vol(δBₙ)` does not depend on the centre. -/
theorem volume_ball_inter_le_of_ell_le {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ} (hδ : 0 < δ)
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y) :
    volume (Metric.ball x δ ∩ K) ≤ ENNReal.ofReal (3 / 2) * volume (Metric.ball y δ ∩ K) := by
  have h : ell K δ x * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      ≤ ENNReal.ofReal (3 / 2) * ell K δ y
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by gcongr
  rwa [ell_mul_volume_ball K hδ x, mul_assoc, ell_mul_volume_ball K hδ y] at h

/-- **`ℓ`-comparability transfers to the ball-slice volumes.**  `ell K δ x` is
`vol(B(x,δ) ∩ K)` divided by the *centre-independent* constant `vol(δBₙ)`
(`Arlib.MarkovChains.ell_mul_volume_ball`), so a two-sided comparison of local conductances
is literally a two-sided comparison of the numerators.

The conclusion is written `max ≤ (3/2)·min`, which is the division-free form of Cousins–
Vempala's `d_ℓ(u,v) < 1/3` (`1409.6011/vol3_journal.tex:581`): `d_ℓ = |ℓu − ℓv|/max < 1/3`
says `max − min < max/3`, i.e. `max < (3/2)·min`. -/
theorem max_volume_ball_inter_le_of_ell_comparable {K : Set (EuclideanSpace ℝ (Fin n))}
    {δ : ℝ} (hδ : 0 < δ) {u v : EuclideanSpace ℝ (Fin n)}
    (huv : ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v)
    (hvu : ell K δ v ≤ ENNReal.ofReal (3 / 2) * ell K δ u) :
    max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ ENNReal.ofReal (3 / 2)
          * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) := by
  rcases le_total (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) with hle | hle
  · rw [max_eq_right hle, min_eq_left hle]
    exact volume_ball_inter_le_of_ell_le hδ hvu
  · rw [max_eq_left hle, min_eq_right hle]
    exact volume_ball_inter_le_of_ell_le hδ huv

/-! ## 4. `cor:overlap` at separation `δ/√n` -/

/-- **The core of `cor:overlap` at separation `δ/√n`**, with the constant `12`, no
membership hypotheses on `T`, and comparability stated on the ball-slice volumes.

This is Cousins–Vempala's `lem:overlap` (`1409.6011/vol3_journal.tex:581–600`) verbatim,
with their `1/(e+1)` replaced by the `1/8` of `volume_lens_ge_min_ball_inter_sharp`:

* both one-step laws dominate the uniform law on the lens `C = B(u,δ) ∩ B(v,δ)`, each
  normalised by *its own* `vol(B(·,δ) ∩ K)`, hence both by the larger of the two, `M`;
* `T` and `Tᶜ` partition, so the two numerators add up to `vol(C ∩ K)` — **this is the only
  place the split between `T` and `Tᶜ` is used**;
* `vol(C ∩ K) ≥ (1/8)·min` by the sharpened Lemma 3.5, and `min ≥ (2/3)·M` by comparability;
* so the sum is at least `(1/8)·(2/3) = 1/12`.

The holding atom of the speedy walk is discarded (it only helps), and no lower bound on `ℓ`
is used — only that `vol(B(u,δ) ∩ K) ≠ 0`, which is automatic on a bounded convex body of
positive volume (`Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`). -/
theorem one_le_twelve_mul_speedyWalk_add_of_comparable (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K)
    (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) (hu0 : volume (Metric.ball u δ ∩ K) ≠ 0)
    (hcomp : max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ ENNReal.ofReal (3 / 2)
          * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    1 ≤ 12 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  set a : ℝ≥0∞ := volume (Metric.ball u δ ∩ K) with hadef
  set b : ℝ≥0∞ := volume (Metric.ball v δ ∩ K) with hbdef
  set M : ℝ≥0∞ := max a b with hMdef
  set m : ℝ≥0∞ := min a b with hmdef
  have hM0 : M ≠ 0 := by
    intro hc
    refine hu0 ?_
    have hle : a ≤ 0 := hc ▸ le_max_left a b
    simpa using hle
  have hMtop : M ≠ ⊤ := by
    rw [hMdef, hadef, hbdef]
    refine ne_of_lt (max_lt ?_ ?_) <;>
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top
  -- both one-step laws dominate the uniform law on the lens, normalised by `M`
  have hdom : ∀ (x : EuclideanSpace ℝ (Fin n)) (A : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet A → volume (Metric.ball x δ ∩ K) ≤ M → C ⊆ Metric.ball x δ →
      M⁻¹ * volume (A ∩ (C ∩ K)) ≤ speedyWalk K δ x A := by
    intro x A hA hle hsub
    rw [speedyWalk_apply_set hK δ x hA]
    refine le_trans ?_ le_self_add
    have hsub2 : A ∩ (C ∩ K) ⊆ A ∩ (Metric.ball x δ ∩ K) :=
      fun y hy => ⟨hy.1, hsub hy.2.1, hy.2.2⟩
    exact mul_le_mul' (ENNReal.inv_le_inv.2 hle) (measure_mono hsub2)
  have h1 : M⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ speedyWalk K δ u Tᶜ :=
    hdom u Tᶜ hT.compl (le_max_left _ _) Set.inter_subset_left
  have h2 : M⁻¹ * volume (T ∩ (C ∩ K)) ≤ speedyWalk K δ v T :=
    hdom v T hT (le_max_right _ _) Set.inter_subset_right
  -- `T` and `Tᶜ` partition the lens: the two numerators add up
  have h3 : volume (Tᶜ ∩ (C ∩ K)) + volume (T ∩ (C ∩ K)) = volume (C ∩ K) := by
    have hmeas := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rw [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at hmeas
    rw [add_comm]
    exact hmeas
  -- Lemma 3.5 at `δ/√n`, sharpened
  have hlens : ENNReal.ofReal (1 / 8) * m ≤ volume (C ∩ K) :=
    volume_lens_ge_min_ball_inter_sharp hn hKc hu hv hδ hsep
  -- comparability, in the multiplied-out form `(2/3)·M ≤ m`
  have hMm : ENNReal.ofReal (2 / 3) * M ≤ m := by
    have hprod : ENNReal.ofReal (2 / 3) * ENNReal.ofReal (3 / 2) = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2 / 3)]
      norm_num
    calc ENNReal.ofReal (2 / 3) * M
        ≤ ENNReal.ofReal (2 / 3) * (ENNReal.ofReal (3 / 2) * m) := by gcongr
      _ = (ENNReal.ofReal (2 / 3) * ENNReal.ofReal (3 / 2)) * m := by ring
      _ = m := by rw [hprod, one_mul]
  have hconst : (1 : ℝ≥0∞) = 12 * (ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 8),
      show (12 : ℝ≥0∞) = ENNReal.ofReal 12 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 12)]
    norm_num
  calc (1 : ℝ≥0∞) = 12 * (ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3)) := hconst
    _ = 12 * (M⁻¹ * (ENNReal.ofReal (1 / 8) * (ENNReal.ofReal (2 / 3) * M))) := by
        rw [show M⁻¹ * (ENNReal.ofReal (1 / 8) * (ENNReal.ofReal (2 / 3) * M))
            = ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3) * (M⁻¹ * M) by ring,
          ENNReal.inv_mul_cancel hM0 hMtop, mul_one]
    _ ≤ 12 * (M⁻¹ * (ENNReal.ofReal (1 / 8) * m)) := by gcongr
    _ ≤ 12 * (M⁻¹ * volume (C ∩ K)) := by gcongr
    _ = 12 * (M⁻¹ * volume (Tᶜ ∩ (C ∩ K)) + M⁻¹ * volume (T ∩ (C ∩ K))) := by
        rw [← mul_add, h3]
    _ ≤ 12 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by gcongr

/-- **Cousins–Vempala's `cor:overlap` at separation `δ/√n`**
(`1409.6011/vol3_journal.tex:612`), with the local-conductance comparability hypothesis
`d_ℓ(u,v) < 1/3` that the paper carries and
`Arlib.MarkovChains.overlap_speedyWalk_convex` deletes, restored — in the binder shape of
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap`, extended by the two
comparability premises.

    1  ≤  12 · (P_u(Tᶜ) + P_v(T)).

The constant is `12`, better than the `20` the consumer needs (see
`overlap_speedyWalk_sqrt_of_ell_comparable_global`, which is the version that can actually
be `exact`ed into `hoverlap` — comparability there must be a *global* hypothesis, since
`hoverlap`'s binder admits no extra per-pair premise).

`u ∈ T`, `v ∉ T` and `densDist h u v < 1/4` are not used; they are carried only so the
statement lines up with the consumer.  What *is* used is `hKc`, `hpos`, and the two
comparability premises. -/
theorem overlap_speedyWalk_sqrt_of_ell_comparable (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v →
      ell K δ v ≤ ENNReal.ofReal (3 / 2) * ell K δ u →
      1 ≤ 12 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  intro T hT u v _ huK hvK _ hsep _ huv hvu
  exact one_le_twelve_mul_speedyWalk_add_of_comparable hn hK hKc hδ huK hvK hsep.le
    (hpos u huK) (max_volume_ball_inter_le_of_ell_comparable hδ huv hvu) hT

/-- **`cor:overlap` at separation `δ/√n`, in exactly the shape
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap` binder demands**, so that

    exact overlap_speedyWalk_sqrt_of_ell_comparable_global hn hK hKc hδ hpos hcomp h

discharges it for `P := speedyWalk K δ`.

Comparability is a **global** hypothesis on `K` — every pair of points of `K` closer than
`δ/√n` has comparable local conductance — because `hoverlap`'s binder has no room for a
per-pair premise.  It is one-sided in the statement and used in both directions, by
`norm_sub_rev`.

The proved constant is `12` (`one_le_twelve_mul_speedyWalk_add_of_comparable`); it is
weakened to the `20` of the consumer here. -/
theorem overlap_speedyWalk_sqrt_of_ell_comparable_global (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  intro T hT u v _ huK hvK _ hsep _
  have hsep' : ‖v - u‖ < δ / Real.sqrt n := by rwa [norm_sub_rev]
  have h12 := one_le_twelve_mul_speedyWalk_add_of_comparable hn hK hKc hδ huK hvK hsep.le
    (hpos u huK)
    (max_volume_ball_inter_le_of_ell_comparable hδ (hcomp u huK v hvK hsep)
      (hcomp v hvK u huK hsep')) hT
  refine le_trans h12 ?_
  gcongr
  norm_num

/-! ## 5. Comparability *is* the paper's `d_ℓ(u,v) < 1/3` -/

/-- `ell K δ x ≠ 0` exactly when the accepted part of the proposal ball is non-null — which
is the `hpos` hypothesis of the overlap theorems. -/
theorem ell_ne_zero_of_volume_ball_inter_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)} (hx : volume (Metric.ball x δ ∩ K) ≠ 0) :
    ell K δ x ≠ 0 := by
  intro hc
  exact hx (by rw [← ell_mul_volume_ball K hδ x, hc, zero_mul])

/-- **`d_ℓ(u,v) < 1/3` implies the comparability hypothesis**, in the repository's own
`Arlib.densDist` vocabulary applied to `x ↦ (ell K δ x).toReal`.

This is what makes the hypothesis of `overlap_speedyWalk_sqrt_of_ell_comparable` *literally*
Cousins–Vempala's `lem:overlap` hypothesis (`1409.6011/vol3_journal.tex:581`), rather than a
convenient reformulation: `d_ℓ = |ℓu − ℓv|/max < 1/3` says `max − min < max/3`, i.e.
`max < (3/2)·min`, i.e. both one-sided comparisons.

`hu` and `hv` (non-degeneracy of the two local conductances) are needed: `d_ℓ` is `0/0 = 0`
at a pair where both vanish, which would make the hypothesis vacuously satisfied while the
one-step laws are undefined.  They come from `hpos` via
`ell_ne_zero_of_volume_ball_inter_ne_zero`. -/
theorem ell_le_of_densDist_ell_lt {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ell K δ u ≠ 0) (hv : ell K δ v ≠ 0)
    (hd : densDist (fun x => (ell K δ x).toReal) u v < 1 / 3) :
    ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v := by
  set A : ℝ := (ell K δ u).toReal with hAdef
  set B : ℝ := (ell K δ v).toReal with hBdef
  have hutop : ell K δ u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ u)
  have hvtop : ell K δ v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ v)
  have hA : 0 < A := ENNReal.toReal_pos hu hutop
  have hB : 0 < B := ENNReal.toReal_pos hv hvtop
  -- the real inequality `A ≤ (3/2)·B`
  have hreal : A ≤ 3 / 2 * B := by
    rw [densDist] at hd
    rcases le_total A B with hle | hle
    · nlinarith
    · rw [max_eq_left hle, abs_of_nonneg (by linarith : (0:ℝ) ≤ A - B),
        div_lt_div_iff₀ hA (by norm_num)] at hd
      linarith
  -- lift to `ℝ≥0∞`
  calc ell K δ u = ENNReal.ofReal A := (ENNReal.ofReal_toReal hutop).symm
    _ ≤ ENNReal.ofReal (3 / 2 * B) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (3 / 2) * ENNReal.ofReal B :=
        ENNReal.ofReal_mul (by norm_num)
    _ = ENNReal.ofReal (3 / 2) * ell K δ v := by rw [ENNReal.ofReal_toReal hvtop]

/-- **`cor:overlap` at separation `δ/√n`, with the hypothesis in the paper's own spelling**
`d_ℓ(u,v) < 1/3` (`1409.6011/vol3_journal.tex:581`), and in the binder shape
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap` demands.

Read against the paper: `lem:overlap` assumes `d_ℓ(u,v) < 1/3` for the pair at hand, and
`cor:overlap` *derives* that assumption from its own `d_h(u,v) < 1/4` by `lem:f-dist`
(`:548`), for the specific density `h = f·ℓ`.  The derivation is not formalised here — see
the module docstring — so `hcomp` is carried as a hypothesis, globally over `K` because
`hoverlap`'s binder has no room for a per-pair premise. -/
theorem overlap_speedyWalk_sqrt_of_densDist_ell (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < δ / Real.sqrt n →
      densDist (fun z => (ell K δ z).toReal) x y < 1 / 3)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  refine overlap_speedyWalk_sqrt_of_ell_comparable_global hn hK hKc hδ hpos
    (fun x hx y hy hxy => ?_) h
  exact ell_le_of_densDist_ell_lt (ell_ne_zero_of_volume_ball_inter_ne_zero hδ (hpos x hx))
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ (hpos y hy)) (hcomp x hx y hy hxy)

/-! ## 6. `thm:speedyconductance` at `δ/√n`, with `hoverlap` discharged -/

/-- **`hoverlap` discharged at separation `δ/√n`, on a convex body with comparable local
conductance.**  This is `Arlib.MarkovChains.conductance_speedyGaussian_ge` with its overlap
hypothesis supplied by `overlap_speedyWalk_sqrt_of_ell_comparable_global` — literally

    exact overlap_speedyWalk_sqrt_of_ell_comparable_global hn hK hKc hδ hpos hcomp h

for the speedy walk `P = speedyWalk K δ`.  Only `hiso` (`thm:iso`, unproved in this
repository) and `hcomp` remain.

Contrast `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell`, which discharges the same
hypothesis from the local-conductance **floor** `11 ≤ 20·ℓ(x)`: that floor fails at every
boundary point of every bounded convex body (`ℓ → 1/2` there), so that theorem is empty for
convex bodies, whereas `hcomp` holds outright whenever `ℓ` is constant on `K`
(`exists_overlap_speedyWalk_sqrt_comparable_witness`) and is Cousins–Vempala's own
hypothesis.

**This is not a polynomial-time statement and may not be quoted as one**: `hiso` and `hcomp`
are hypotheses. -/
theorem conductance_speedyGaussian_ge_of_ell_comparable (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hmass : 0 < ∫ x, h x)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpi : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      pi A = ENNReal.ofReal (∫ x in A, h x) / ENNReal.ofReal (∫ x, h x))
    (hrev : IsReversible (speedyWalk K δ) pi) (hpiK : pi Kᶜ = 0)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n ≤ densDist h u v) →
      δ * Real.log 2 / Real.sqrt n / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ (∫ x, h x) * ∫ x in S₃, h x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyWalk K δ) pi :=
  conductance_speedyGaussian_ge hn hσ hδ hδσ hh0 hmass hK (speedyWalk K δ) pi hpi hrev hpiK
    (overlap_speedyWalk_sqrt_of_ell_comparable_global hn hK hKc hδ hpos hcomp h) hiso

/-! ## 7. Non-vacuity, on a bounded convex body -/

/-- **Non-vacuity witness (`CLAUDE.md` §11).**  Every hypothesis of
`overlap_speedyWalk_sqrt_of_ell_comparable` holds *simultaneously* at `n = 2`,
`K = B(0,1) ⊆ ℝ²`, `δ = 3`, `u = 0`, `v = (1/2, 0)`, `T = B(0,1/4)`, `h ≡ 1`, and the
conclusion `1 ≤ 12·(P_u(Tᶜ) + P_v(T))` holds there.

**Why this witness and not `K = ℝⁿ`.**  The point of the comparability hypothesis is that,
unlike the local-conductance floor `11 ≤ 20·ℓ(x)` of
`Arlib.MarkovChains.overlap_speedyWalk`, it is satisfiable on a **bounded convex body of
positive volume** — the floor is not, since `ℓ → 1/2` at the boundary of any such body.  So
the witness is a genuine convex body, and `Bornology.IsBounded K` and `volume K ≠ 0` are
part of the statement.  Here `δ = 3` exceeds the diameter of `K`, so `B(x,δ) ⊇ K` for every
`x ∈ K` and `ℓ` is *constant* on `K` — comparability holds with equality.

This does **not** claim that comparability holds on every bounded convex body: it does not
(see `exists_ell_not_comparable_at_sqrt_dim_counterexample`).  It is a hypothesis, and it is
Cousins–Vempala's own. -/
theorem exists_overlap_speedyWalk_sqrt_comparable_witness :
    ∃ (K T : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ)
      (u v : EuclideanSpace ℝ (Fin 2)) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧
      MeasurableSet T ∧ 0 < δ ∧
      (∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0) ∧
      (∀ x ∈ K, ∀ y ∈ K, ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y) ∧
      u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < δ / Real.sqrt ((2 : ℕ) : ℝ) ∧ densDist h u v < 1 / 4 ∧
      1 ≤ 12 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 1 with hKdef
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℝ) with hvdef
  have hvnorm : ‖v‖ = 1 / 2 := by
    rw [hvdef, PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  have hKvol : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  -- `δ = 3` exceeds the diameter of `K`, so the proposal ball always covers `K`
  have hcover : ∀ x ∈ K, Metric.ball x (3 : ℝ) ∩ K = K := by
    intro x hx
    refine Set.inter_eq_right.mpr fun y hy => ?_
    have hx1 : dist x 0 < 1 := Metric.mem_ball.1 hx
    have hy1 : dist y 0 < 1 := Metric.mem_ball.1 hy
    refine Metric.mem_ball.2 ?_
    calc dist y x ≤ dist y 0 + dist 0 x := dist_triangle _ _ _
      _ < 3 := by rw [dist_comm (0 : EuclideanSpace ℝ (Fin 2)) x]; linarith
  -- hence `ℓ` is constant on `K`
  have hell : ∀ x ∈ K, ell K (3 : ℝ) x
      = volume K / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3) := by
    intro x hx
    rw [ell_apply, hcover x hx, volume_ball_eq x 3]
  have hpos : ∀ x ∈ K, volume (Metric.ball x (3 : ℝ) ∩ K) ≠ 0 := by
    intro x hx
    rw [hcover x hx]
    exact hKvol
  have hcomp : ∀ x ∈ K, ∀ y ∈ K,
      ell K (3 : ℝ) x ≤ ENNReal.ofReal (3 / 2) * ell K (3 : ℝ) y := by
    intro x hx y hy
    rw [hell x hx, hell y hy]
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc volume K / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3)
        = 1 * (volume K / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3)) :=
          (one_mul _).symm
      _ ≤ _ := by gcongr
  -- the separation `1/2 < 3/√2`
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hs0 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by rw [hcast2]; norm_num)
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) < 2 := by
    have h1 : Real.sqrt ((2 : ℕ) : ℝ) ^ 2 = ((2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg ((2 : ℕ) : ℝ), h1, hcast2]
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 2)) - v‖ < (3 : ℝ) / Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvnorm, div_lt_div_iff₀ (by norm_num) hs0]
    nlinarith [hs2]
  have hvT : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]
    norm_num
  have hvK : v ∈ K := by
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]
    norm_num
  have huK : (0 : EuclideanSpace ℝ (Fin 2)) ∈ K := Metric.mem_ball_self one_pos
  have hdens : densDist (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) 0 v < 1 / 4 := by
    simp [densDist]
  refine ⟨K, Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), 3, 0, v, fun _ => 1,
    measurableSet_ball, convex_ball _ _, Metric.isBounded_ball, hKvol, measurableSet_ball,
    by norm_num, hpos, hcomp, Metric.mem_ball_self (by norm_num), huK, hvK, hvT, hsep,
    hdens, ?_⟩
  exact overlap_speedyWalk_sqrt_of_ell_comparable (n := 2) (by norm_num) measurableSet_ball
    (convex_ball _ _) (by norm_num) hpos (fun _ => 1)
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) measurableSet_ball 0 v
    (Metric.mem_ball_self (by norm_num)) huK hvK hvT hsep hdens
    (hcomp 0 huK v hvK) (hcomp v hvK 0 huK)

/-! ## 8. The `δ/√n` counterexample is excluded by comparability -/

/-- **A volume gap refutes comparability.**  Contrapositive of
`volume_ball_inter_le_of_ell_le`. -/
theorem not_ell_le_of_volume_ball_inter_gap {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    (hδ : 0 < δ) {u v : EuclideanSpace ℝ (Fin n)}
    (hgap : ENNReal.ofReal (3 / 2) * volume (Metric.ball v δ ∩ K)
      < volume (Metric.ball u δ ∩ K)) :
    ¬ (ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v) :=
  fun hc => absurd (volume_ball_inter_le_of_ell_le hδ hc) (not_le.2 hgap)

/-- **The `δ/√n` counterexample of
`Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample` violates the
comparability hypothesis of this file** — machine-checked, on that counterexample's own data.

At `n = 23409`, `δ = 1`, `K = apexConeBody u v` (a bounded convex body of positive volume),
`v` its apex and `‖u − v‖ = 1/306 < 1/153 = δ/√n`, the counterexample's Bernoulli estimate
`(1 + t/4)ⁿ ≥ 161/8 > 20` gives

    20 · ℓ(v)  <  ℓ(u),

i.e. `d_ℓ(u,v) > 19/20 = 0.95`, against the `< 1/3` that `ell_le_of_densDist_ell_lt`
requires — a factor `20` on a hypothesis that allows `3/2`.  So
`overlap_speedyWalk_sqrt_of_ell_comparable` does **not** contradict that counterexample:
the counterexample is not in its scope, and this is the precise sense in which reinstating
Cousins–Vempala's `d_ℓ(u,v) < 1/3` is what the `√n` separation costs.

Note that the counterexample's own `h ≡ 1` is *not* the speedy walk's stationary density,
which is proportional to `ℓ`; with `h ∝ ℓ` its `densDist h u v` would be `> 0.95`, not `0`,
and the consumer's own `d_h(u,v) < 1/4` binder would already exclude it.  See the module
docstring. -/
theorem exists_ell_not_comparable_at_sqrt_dim_counterexample :
    ∃ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n)),
      2 ≤ n ∧ MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, volume (Metric.ball x 1 ∩ K) ≠ 0) ∧
      u ∈ K ∧ v ∈ K ∧ ‖u - v‖ < 1 / Real.sqrt n ∧
      (20 : ℝ≥0∞) * volume (Metric.ball v 1 ∩ K) < volume (Metric.ball u 1 ∩ K) ∧
      ¬ (ell K 1 u ≤ ENNReal.ofReal (3 / 2) * ell K 1 v) := by
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
  -- Bernoulli: `(1 + t/4)ⁿ ≥ 1 + n·t/4 = 161/8 > 20`
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
  have hsq : Real.sqrt ((n : ℕ) : ℝ) = 153 := by
    rw [hndef, show (((23409 : ℕ) : ℝ)) = (153 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  -- `3/2 ≤ 20`, so the volume gap refutes comparability
  have hgap' : ENNReal.ofReal (3 / 2) * volume (Metric.ball v 1 ∩ K)
      < volume (Metric.ball u 1 ∩ K) := by
    refine lt_of_le_of_lt (?_ : ENNReal.ofReal (3 / 2) * volume (Metric.ball v 1 ∩ K)
      ≤ 20 * volume (Metric.ball v 1 ∩ K)) hgap
    have h32 : ENNReal.ofReal (3 / 2) ≤ (20 : ℝ≥0∞) := by
      rw [show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    gcongr
  refine ⟨n, K, u, v, by omega, hKm, hKc, hKb, hKvol,
    fun x hx => volume_ball_inter_ne_zero_of_convex hKc hKb hKvol hx one_pos,
    mem_apexConeBody_of_left (by linarith), apex_mem_apexConeBody u v, ?_, hgap,
    not_ell_le_of_volume_ball_inter_gap one_pos hgap'⟩
  rw [hnormuv, hsq, htdef]
  norm_num

end OverlapSqrt

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.quarter_le_one_sub_inv_pow
#print axioms Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp
#print axioms Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_sharp
#print axioms Arlib.MarkovChains.volume_ball_inter_le_of_ell_le
#print axioms Arlib.MarkovChains.max_volume_ball_inter_le_of_ell_comparable
#print axioms Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable
#print axioms Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable
#print axioms Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global
#print axioms Arlib.MarkovChains.ell_ne_zero_of_volume_ball_inter_ne_zero
#print axioms Arlib.MarkovChains.ell_le_of_densDist_ell_lt
#print axioms Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_densDist_ell
#print axioms Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable
#print axioms Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_comparable_witness
#print axioms Arlib.MarkovChains.not_ell_le_of_volume_ball_inter_gap
#print axioms Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample
