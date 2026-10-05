/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.OverlapSqrt
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductanceSharp

/-!
# Lemma 3.5 of [KLS95] at separation `δ/√n`, with the lens constant `1/4` — proved

For a convex `K ∋ u, v` in `ℝⁿ` (`n ≥ 2`) and `‖u − v‖ ≤ δ/√n`,

    vol(K ∩ B(u,δ) ∩ B(v,δ))  ≥  (1/4) · min{ℓ(u), ℓ(v)} · vol(δBₙ)

(`kls_lemma35_at_sep_sqrt_dim_quarter`, and `volume_lens_ge_min_ball_inter_quarter` in the
ball-slice form).  This is Lemma 3.5 of [KLS95] as cited by Cousins–Vempala at
`1409.6011/vol3_journal.tex:592`, at the constant `1/4` in place of `1/40`
(`Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim`, `LensMin.lean`) and `1/8`
(`Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_sharp`, `OverlapSqrt.lean`).  Nothing is
`sorry`ed and no hypothesis beyond those two files' is carried — the hypotheses are exactly
`2 ≤ n`, `Convex ℝ K`, `u ∈ K`, `v ∈ K`, `0 < δ`, `‖u−v‖ ≤ δ/√n`, and the separation is used
only through `n‖u−v‖² ≤ δ²`.  See the axiom audit at the bottom.

## Why `1/4`: what the constant buys the Metropolis route

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`
(`MetropolisConductanceSharp.lean:431`) is the conductance bound the TTC volume price
consumes, not the speedy-walk one that `OverlapSqrt.lean` closes at `1/8`.  The threshold
quoted for that route is a lens constant of `3e/40 ≈ 0.2039` — `3/40` from the overlap chain
`20·κ·(2/3) ≥ 1`, times a worst-case acceptance factor `e` — which `1/8 = 0.125` misses by a
factor `1.63`.  `three_exp_div_forty_le_quarter` checks `3e/40 ≤ 1/4` mechanically, so `1/4`
clears it with about `22%` to spare.

§6 states the price in the form the consumer actually pays it.  A Metropolis overlap lemma at
separation `δ/√n` built on a lens constant `κ` carries a local-conductance floor of the shape
`1 ≤ 20·a·κ·θ`, where `a = e^{-(2Rδ+δ²)/(2s)}` is the repository's real acceptance floor
(`Arlib.MarkovChains.metropolisAccept_ge`) and `θ` is the floor on `ℓ`.  That is exactly the
demand `a·θ ≥ 1/(20κ)`, and since `a ≤ 1` (`acceptance_le_one`) and `ℓ ≤ 1` always:

| lens constant `κ` | demand `a·θ ≥ …` | verdict |
| --- | --- | --- |
| `1/40` (`kls_lemma35_at_sep_sqrt_dim`) | `2` | **impossible**, `floor_unsatisfiable_at_fortieth` |
| `1/8` (`…_sharp`) | `2/5 = 0.4` | satisfiable, but `θ ≥ 0.4/a` |
| `1/4` (here) | `1/5 = 0.2` | `θ ≥ 0.2/a` |
| `(1−1/n)ⁿ` (the `δ/n` floor in force today) | `1/(20(1−1/n)ⁿ) ∈ (e/20, 1/5]` | `0.2` at `n = 2`, `→ 0.136` |

So `1/4` **halves** the `θ` the `1/8` constant would demand, and lands on exactly the demand
the existing `δ/n` floor already makes at `n = 2`, and at most a factor `4/e ≈ 1.47` more
demanding than it at any `n` (`floor_quarter_le_floor_dim`, `floor_dim_at_two`).  The `1/40` of
`LensMin.lean` is not merely weak here: it makes the floor **unsatisfiable**, because it asks
for `a·θ ≥ 2` while both factors are at most `1`.

## The two changes to `LensMin.lean`'s skeleton

The geometry is `LensMin.lean`'s and is reused, not reproved: the three bounds are
`Arlib.MarkovChains.volume_lens_inter_ge_halfspace` (`StarPolar.lean:845`),
`Arlib.MarkovChains.min_volume_le_volume_midpoint_sum` and
`Arlib.MarkovChains.homothety_image_subset_lens_of_dilate`.  Two things change.

1. **The contraction ratio becomes `λ = √(1 − 1/n)`** instead of `1 − 1/n`.  This is the
   largest ratio the half-space step's side condition `λ²δ² + t² ≤ δ²` permits at the extreme
   separation `t = δ/√n`, so that step becomes tight, and the contraction factor rises from
   `(1 − 1/n)ⁿ ≥ 1/4` to `(√(1 − 1/n))ⁿ = √((1 − 1/n)ⁿ) ≥ 1/2`
   (`half_le_sqrt_one_sub_inv_pow`, off `Arlib.MarkovChains.quarter_le_one_sub_inv_pow`).

2. **The midpoint radius becomes the exact `(δ + √(δ² + t²))/2`**
   (`midpoint_mem_ball_inter_sharp`) instead of `LensMin.lean`'s `δ + t²/(4δ)`.

Change 2 is *forced by* change 1, and this is the whole content of the file.
`OverlapSqrt.lean`'s docstring records that `λ = √(1 − 1/n)` was tried and **rejected**
because the midpoint step's side condition `λ(ζ − t) ≤ δ − t` with `ζ = δ(1 + 1/(4n))` fails
at `n = 2`, `t = δ/√2`, where it reads `0.29549δ ≤ 0.29289δ`.  **That analysis is confirmed
here** — the numbers are right and the crude radius really does make `√(1 − 1/n)` illegal.
What it missed is that `ζ = δ + t²/(4δ)` is itself a weakening, of `(δ + √(δ²+t²))/2`, by the
estimate `√(δ²+t²) ≤ δ + t²/(2δ)`.  At `n = 2` the exact radius is `1.11237δ` against the
crude `1.125δ`, and the side condition becomes `0.28657δ ≤ 0.29289δ`, which holds with `2%`
to spare.  The excess is quadratic in `t` either way, so the two radii are asymptotically
identical; the `1%` difference matters only at `n = 2`, and only because that is exactly
where the constant binds.

The side condition is discharged in two pieces: `lens_side_two` at `n = 2` (where `λ = √2/2`
and the second square root `√(δ²+t²)` survives, so the proof clears both by squaring, using
`(51−36√2)t² + (28√2−36)·t(δ−√2 t) + (8−4√2)(δ−√2 t)² ≥ 0`), and `lens_side_sqrt` for
`n ≥ 3` (where the crude radius is still good enough, and after squaring the claim is the
polynomial `lens_side_poly`: `(δ+t)(2δ−t)⁴ ≤ 16δ⁴(δ−t)` for `3t² ≤ δ²`).

## `1/4` is this skeleton's ceiling, and `1/(e+1)` is not reachable from it

The paper quotes `1/(e+1) ≈ 0.269`.  It is **not** attainable by tuning constants here, and
the obstruction is `n = 2`, verifiably:

* the half-space factor is `λⁿ` with `λ² ≤ 1 − 1/n`, so at `n = 2` it is at most `1/2`;
* the midpoint factor at `n = 2` is at most `((1−s)/(ρ̂−s))²` at `s = 1/√2`,
  `ρ̂ = (1+√(1+s²))/2`, i.e. `0.7227² = 0.5223`;
* the assembly bounds `m` by `Λ/c₁ + Λ/c₂` (this file runs it at `c₁ = c₂ = λⁿ`, which is
  where the final `/2` comes from), so the best constant it can yield even with the two
  ratios chosen separately is `c₁c₂/(c₁+c₂) ≤ 0.5·0.5223/1.0223 = 0.2555 < 0.269`.

For `n = 3` the same accounting gives `0.286` and it rises to `e^{-1/2}e^{-1/4}/(e^{-1/2} +
e^{-1/4}) = 0.341` as `n → ∞`, so the binding case really is `n = 2` alone.  Reaching
`1/(e+1)` uniformly needs a different argument at small `n`, not a sharper constant; this file
does not attempt one, and `1/4` is what the assembly actually supports with the single ratio
`√(1 − 1/n)`.

## Scope

Sections 1–5 prove a geometric inequality; §6 is arithmetic about floors of the shape
`1 ≤ 20·a·κ·θ`, and is a *hypothetical* — it says what such a floor demands, not that any
theorem carries it; §7 is a one-sided kernel comparison.  **Nothing in this file proves an
overlap bound, a conductance bound, or a mixing time.**  In particular the Metropolis overlap
lemma at separation `δ/√n` is not proved here;
`Arlib.MarkovChains.metropolisGaussian_overlap_of_convex` remains at separation `δ/n`, and
`conductance_metropolisGaussian_sharp_ge`'s own hypotheses (`hiso` above all, which is
unproved in this repository) are untouched.  Nothing here may be quoted as an `O*(n³)` claim.

## Main results

* `lens_side_poly`, `lens_side_two`, `lens_side_sqrt` — the midpoint side condition at
  `λ = √(1 − 1/n)`, root-free.
* `half_le_sqrt_one_sub_inv_pow` — `(√(1 − 1/n))ⁿ ≥ 1/2`, sharp at `n = 2`.
* `midpoint_mem_ball_inter_sharp` — the midpoint step at the exact radius.
* `volume_lens_ge_min_ball_inter_quarter`, `kls_lemma35_at_sep_sqrt_dim_quarter` — the
  headline, at `1/4`.
* `three_exp_div_forty_le_quarter` — `3e/40 ≤ 1/4`, the Metropolis threshold, machine-checked.
* `acceptance_le_one`, `floor_fortieth_iff`, `floor_eighth_iff`, `floor_quarter_iff`,
  `floor_dim_at_two`, `floor_quarter_le_floor_dim`, `floor_unsatisfiable_at_fortieth` — what a
  floor `1 ≤ 20·a·κ·θ` demands of `θ` at each available lens constant.
* `acceptance_mul_ell_mul_speedyWalk_le_metropolisGaussian` — the speedy ↔ Metropolis kernel
  comparison, `a·ℓ(x)·speedyWalk ≤ metropolisGaussian`, absent from the repository until now.

## References

Kannan, Lovász and Simonovits (1995), Lemma 3.5.
Cousins and Vempala, §4.1 (`1409.6011/vol3_journal.tex:509–700`).
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal
open scoped InnerProductSpace
open scoped Pointwise

section LensSharp

variable {n : ℕ}

/-! ## 1. The two side-condition inequalities -/

/-- The side condition of the midpoint homothety at `n ≥ 3`, cleared of every square root.

`(δ + t)(2δ − t)⁴ ≤ 16δ⁴(δ − t)` for `0 ≤ t ≤ δ/√3`; the difference factors as
`t²·(8δ³ − 16δ²t + 7δt² − t³)` and the cubic is `2δ(2δ−3t)² + t(8δ² − 11δt − t²)`, whose last
factor is nonnegative exactly because `33t ≤ 23δ` and `3t² ≤ δ²` combine to
`8 − 23/3 − 1/3 = 0`. -/
theorem lens_side_poly {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (h3 : 3 * t ^ 2 ≤ δ ^ 2) :
    (δ + t) * (2 * δ - t) ^ 4 ≤ 16 * δ ^ 4 * (δ - t) := by
  -- `33 t ≤ 23 δ`, since `(33t)² = 363·(3t²) ≤ 363 δ² ≤ 529 δ² = (23δ)²`
  have hlin : 33 * t ≤ 23 * δ := by nlinarith [h3, ht, hδ, sq_nonneg t]
  -- hence `8δ² − 11δt − t² ≥ 0`: `11δt ≤ (23/3)δ²` and `t² ≤ δ²/3` leave exactly `0`
  have hquad : 0 ≤ 8 * δ ^ 2 - 11 * δ * t - t ^ 2 := by
    have h5 : 0 ≤ δ * (23 * δ - 33 * t) := mul_nonneg hδ.le (by linarith)
    nlinarith [h5, h3]
  -- the cubic `8δ³ − 16δ²t + 7δt² − t³ = 2δ(2δ−3t)² + t(8δ² − 11δt − t²)`
  have hcubic : 0 ≤ 8 * δ ^ 3 - 16 * δ ^ 2 * t + 7 * δ * t ^ 2 - t ^ 3 := by
    have hkey : 8 * δ ^ 3 - 16 * δ ^ 2 * t + 7 * δ * t ^ 2 - t ^ 3
        = 2 * δ * (2 * δ - 3 * t) ^ 2 + t * (8 * δ ^ 2 - 11 * δ * t - t ^ 2) := by ring
    rw [hkey]
    have h1 : 0 ≤ 2 * δ * (2 * δ - 3 * t) ^ 2 := by positivity
    have h2 : 0 ≤ t * (8 * δ ^ 2 - 11 * δ * t - t ^ 2) := mul_nonneg ht hquad
    linarith
  have hfin : 16 * δ ^ 4 * (δ - t) - (δ + t) * (2 * δ - t) ^ 4
      = t ^ 2 * (8 * δ ^ 3 - 16 * δ ^ 2 * t + 7 * δ * t ^ 2 - t ^ 3) := by ring
  have hprod : 0 ≤ t ^ 2 * (8 * δ ^ 3 - 16 * δ ^ 2 * t + 7 * δ * t ^ 2 - t ^ 3) :=
    mul_nonneg (sq_nonneg t) hcubic
  linarith [hfin, hprod]

/-- `√2` is between `1.414` and `1.415`. -/
private lemma sqrt_two_bounds : (1.414 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.415 := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [hsq, h0]

/-- `√(1/2) = √2/2`. -/
private lemma sqrt_half_eq : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [show (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 by rw [div_pow, hsq]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **The side condition of the midpoint homothety at `n = 2`.**

At `n = 2` the contraction ratio is `λ = √(1 − 1/2) = √2/2 ≈ 0.7071`, and the *sharp* midpoint
radius `ρ = (δ + √(δ²+t²))/2` must satisfy `λ(ρ − t) ≤ δ − t` for every `t ≤ δ/√2`.  At the
extreme `t = δ/√2` this reads `0.28657δ ≤ 0.29289δ` — true with `2%` to spare, whereas the
cruder radius `δ + t²/(4δ)` of `Arlib.MarkovChains.midpoint_mem_ball_inter` gives
`0.29549δ ≤ 0.29289δ`, which is false.  Sharpening the radius is exactly what makes the single
ratio `√(1 − 1/n)` legal at every `n ≥ 2`.

After clearing `λ` the claim is `b ≤ (2r−1)δ − (2r−2)t` with `r = √2`, `b = √(δ²+t²)`, and
squaring turns that into `0 ≤ (8−4r)δ² − (20−12r)δt + (11−8r)t²`, which is the identity
`(51−36r)t² + (28r−36)·t·(δ−rt) + (8−4r)(δ−rt)²` with all three coefficients positive. -/
theorem lens_side_two {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (h2 : 2 * t ^ 2 ≤ δ ^ 2) :
    Real.sqrt (1 / 2) * ((δ + Real.sqrt (δ ^ 2 + t ^ 2)) / 2 - t) ≤ δ - t := by
  obtain ⟨hrlo, hrhi⟩ := sqrt_two_bounds
  set r : ℝ := Real.sqrt 2 with hrdef
  have hr0 : (0 : ℝ) ≤ r := Real.sqrt_nonneg 2
  have hrsq : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set b : ℝ := Real.sqrt (δ ^ 2 + t ^ 2) with hbdef
  have hb0 : (0 : ℝ) ≤ b := Real.sqrt_nonneg _
  have hbsq : b ^ 2 = δ ^ 2 + t ^ 2 := Real.sq_sqrt (by positivity)
  -- `r t ≤ δ`, i.e. `t ≤ δ/√2`
  have hrt : r * t ≤ δ := by nlinarith [hrsq, h2, mul_nonneg hr0 ht, hδ, ht]
  have htd : t ≤ δ := by nlinarith [hrt, mul_nonneg (by linarith : (0:ℝ) ≤ r - 1) ht]
  -- the three positive coefficients, all from `r² = 2`
  have c1 : (0 : ℝ) ≤ 51 - 36 * r := by linarith
  have c2 : (0 : ℝ) ≤ 28 * r - 36 := by linarith
  have c3 : (0 : ℝ) ≤ 8 - 4 * r := by linarith
  have hkey : (0 : ℝ) ≤ (51 - 36 * r) * t ^ 2 + (28 * r - 36) * (t * (δ - r * t))
      + (8 - 4 * r) * (δ - r * t) ^ 2 := by
    have t1 := mul_nonneg c1 (sq_nonneg t)
    have t2 := mul_nonneg c2 (mul_nonneg ht (sub_nonneg.mpr hrt))
    have t3 := mul_nonneg c3 (sq_nonneg (δ - r * t))
    linarith
  -- the squared form
  have hexp : ((2 * r - 1) * δ - (2 * r - 2) * t) ^ 2 - (δ ^ 2 + t ^ 2)
      = (51 - 36 * r) * t ^ 2 + (28 * r - 36) * (t * (δ - r * t))
        + (8 - 4 * r) * (δ - r * t) ^ 2 := by
    linear_combination (4 * δ ^ 2 - 16 * t * δ + (4 * r + 24) * t ^ 2) * hrsq
  have hsq : b ^ 2 ≤ ((2 * r - 1) * δ - (2 * r - 2) * t) ^ 2 := by
    rw [hbsq]; linarith [hexp, hkey]
  have hrhs : (0 : ℝ) ≤ (2 * r - 1) * δ - (2 * r - 2) * t := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * r - 2) (by linarith : (0:ℝ) ≤ δ - t)
    nlinarith [this, hδ]
  have hb : b ≤ (2 * r - 1) * δ - (2 * r - 2) * t := by nlinarith [hsq, hb0, hrhs]
  -- unwind: `δ + b − 2t ≤ 2r(δ−t)` and `r·2r = 4`
  have h1 : δ + b - 2 * t ≤ 2 * r * (δ - t) := by linarith
  have h2' : r * (δ + b - 2 * t) ≤ r * (2 * r * (δ - t)) :=
    mul_le_mul_of_nonneg_left h1 hr0
  have h3 : r * (2 * r * (δ - t)) = 4 * (δ - t) := by
    rw [show r * (2 * r * (δ - t)) = 2 * r ^ 2 * (δ - t) by ring, hrsq]; ring
  rw [sqrt_half_eq, ← hrdef]
  linarith [h2', h3]

/-! ## 2. The contraction factor `√(1 − 1/n)ⁿ ≥ 1/2` -/

/-- **`(√(1 − 1/n))ⁿ ≥ 1/2` for `n ≥ 2`.**  The square of the left side is `(1 − 1/n)ⁿ`, which
`Arlib.MarkovChains.quarter_le_one_sub_inv_pow` bounds below by `1/4`.  As there, `1/2` is
attained at `n = 2` and cannot be improved uniformly in `n`: the quantity increases to
`e^{-1/2} ≈ 0.6065`. -/
theorem half_le_sqrt_one_sub_inv_pow (hn : 2 ≤ n) :
    (1 : ℝ) / 2 ≤ Real.sqrt (1 - 1 / (n : ℝ)) ^ n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
    linarith
  have hy0 : (0 : ℝ) ≤ Real.sqrt (1 - 1 / (n : ℝ)) ^ n := by positivity
  have hy2 : (Real.sqrt (1 - 1 / (n : ℝ)) ^ n) ^ 2 = (1 - 1 / (n : ℝ)) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx0]
  have hq : (1 : ℝ) / 4 ≤ (1 - 1 / (n : ℝ)) ^ n := quarter_le_one_sub_inv_pow hn
  nlinarith [hy0, hy2, hq]

/-- **The side condition of the midpoint homothety at `n ≥ 3`**, with the ratio given only
through `λ²δ² ≤ δ² − t²` (which is `λ² ≤ 1 − 1/n` together with `n t² ≤ δ²`).

Two square roots are eliminated in turn: the sharp radius is bounded by the crude one,
`(δ + √(δ²+t²))/2 ≤ δ + t²/(4δ) = (2δ−t)²/(4δ)`, and `λδ ≤ √(δ²−t²)`, after which the claim
is `√(δ²−t²)·(2δ−t)² ≤ 4δ²(δ−t)`, i.e. `lens_side_poly` squared. -/
theorem lens_side_sqrt {δ t lam : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (h3 : 3 * t ^ 2 ≤ δ ^ 2)
    (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 * δ ^ 2 ≤ δ ^ 2 - t ^ 2) :
    lam * ((δ + Real.sqrt (δ ^ 2 + t ^ 2)) / 2 - t) ≤ δ - t := by
  have htd : t < δ := by nlinarith
  set a : ℝ := Real.sqrt (δ ^ 2 - t ^ 2) with hadef
  have ha0 : (0 : ℝ) ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = δ ^ 2 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hlamd : lam * δ ≤ a := by nlinarith [mul_nonneg hlam0 hδ.le, hasq, ha0]
  -- the sharp radius is below the crude one
  have hzeta : (δ + Real.sqrt (δ ^ 2 + t ^ 2)) / 2 - t ≤ (2 * δ - t) ^ 2 / (4 * δ) := by
    have hb : Real.sqrt (δ ^ 2 + t ^ 2) ≤ (2 * δ ^ 2 + t ^ 2) / (2 * δ) := by
      have h1 : δ ^ 2 + t ^ 2 ≤ ((2 * δ ^ 2 + t ^ 2) / (2 * δ)) ^ 2 := by
        rw [div_pow]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (t ^ 2), sq_nonneg t]
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h2
    have he : (2 * δ - t) ^ 2 / (4 * δ) - ((δ + (2 * δ ^ 2 + t ^ 2) / (2 * δ)) / 2 - t) = 0 := by
      field_simp; ring
    linarith [hb, he]
  -- the polynomial side condition, unsquared
  have hpoly : a * (2 * δ - t) ^ 2 ≤ 4 * δ ^ 2 * (δ - t) := by
    have hkey := lens_side_poly hδ ht h3
    have hsq : (a * (2 * δ - t) ^ 2) ^ 2 ≤ (4 * δ ^ 2 * (δ - t)) ^ 2 := by
      have hexp : (a * (2 * δ - t) ^ 2) ^ 2 = (δ ^ 2 - t ^ 2) * (2 * δ - t) ^ 4 := by
        rw [mul_pow, hasq]; ring
      rw [hexp]
      have hstep : (δ ^ 2 - t ^ 2) * (2 * δ - t) ^ 4
          = (δ - t) * ((δ + t) * (2 * δ - t) ^ 4) := by ring
      rw [hstep]
      nlinarith [mul_le_mul_of_nonneg_left hkey (by linarith : (0:ℝ) ≤ δ - t)]
    nlinarith [hsq, mul_nonneg ha0 (sq_nonneg (2 * δ - t)),
      mul_nonneg (by positivity : (0:ℝ) ≤ 4 * δ ^ 2) (by linarith : (0:ℝ) ≤ δ - t)]
  -- assemble
  have hstep1 : lam * ((δ + Real.sqrt (δ ^ 2 + t ^ 2)) / 2 - t)
      ≤ lam * ((2 * δ - t) ^ 2 / (4 * δ)) := mul_le_mul_of_nonneg_left hzeta hlam0
  refine hstep1.trans ?_
  have hre : lam * ((2 * δ - t) ^ 2 / (4 * δ)) = lam * (2 * δ - t) ^ 2 / (4 * δ) := by ring
  rw [hre, div_le_iff₀ (by positivity : (0:ℝ) < 4 * δ)]
  have e1 : lam * δ * (2 * δ - t) ^ 2 ≤ a * (2 * δ - t) ^ 2 :=
    mul_le_mul_of_nonneg_right hlamd (sq_nonneg _)
  nlinarith [e1, hpoly, hδ]

/-! ## 3. The sharp midpoint radius -/

/-- **The midpoint step with the sharp radius.**  This is
`Arlib.MarkovChains.midpoint_mem_ball_inter` with the excess left in its exact form: for `x`
in `B(u,δ) ∩ K` on the far side of `u` from `v` and `y` in `B(v,δ) ∩ K` on the far side of `v`
from `u`, the midpoint lies in `K` and within

    (δ + √(δ² + t²))/2      (t = ‖u − v‖)

of **both** centres.  `LensMin.lean` weakens this to `δ + t²/(4δ)` — the bound
`√(δ²+t²) ≤ δ + t²/(2δ)` — which loses nothing asymptotically but is the difference between
`0.11237δ` and `0.125δ` of excess at `n = 2`, and hence between the ratio `√(1−1/n)` being
legal at every `n ≥ 2` and being illegal at `n = 2`.  That is the whole reason this file
exists.

The `t`-linear terms still cancel by the two sign conditions (`‖(x−u)+(v−u)‖² ≤ δ² + t²`); the
only change is that the resulting `√(δ²+t²)` is not further estimated. -/
theorem midpoint_mem_ball_inter_sharp {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {u v x y : EuclideanSpace ℝ (Fin n)} {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Metric.ball u δ ∩ K) (hxh : ⟪x - u, v - u⟫_ℝ ≤ 0)
    (hy : y ∈ Metric.ball v δ ∩ K) (hyh : ⟪y - v, u - v⟫_ℝ ≤ 0) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈
      (Metric.ball u ((δ + Real.sqrt (δ ^ 2 + ‖u - v‖ ^ 2)) / 2)
        ∩ Metric.ball v ((δ + Real.sqrt (δ ^ 2 + ‖u - v‖ ^ 2)) / 2)) ∩ K := by
  set t : ℝ := ‖u - v‖ with ht
  set z : EuclideanSpace ℝ (Fin n) := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hz
  have hxu : ‖x - u‖ < δ := by
    have := hx.1; rwa [Metric.mem_ball, dist_eq_norm] at this
  have hyv : ‖y - v‖ < δ := by
    have := hy.1; rwa [Metric.mem_ball, dist_eq_norm] at this
  have hvu : ‖v - u‖ = t := by rw [ht, norm_sub_rev]
  -- the two "corrected" vectors have norm at most `√(δ² + t²)` — exactly
  have hbound : ∀ a w : EuclideanSpace ℝ (Fin n), ‖a‖ < δ → ‖w‖ = t →
      ⟪a, w⟫_ℝ ≤ 0 → ‖a + w‖ ≤ Real.sqrt (δ ^ 2 + t ^ 2) := by
    intro a w ha hw hip
    have hsq : ‖a + w‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, w⟫_ℝ + ‖w‖ ^ 2 := norm_add_sq_real a w
    have h1 : ‖a + w‖ ^ 2 ≤ δ ^ 2 + t ^ 2 := by
      rw [hsq, hw]; nlinarith [norm_nonneg a]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _)] at h2
  have hzu : z - u = (1 / 2 : ℝ) • ((x - u) + (v - u)) + (1 / 2 : ℝ) • (y - v) := by
    rw [hz]; module
  have hzv : z - v = (1 / 2 : ℝ) • ((y - v) + (u - v)) + (1 / 2 : ℝ) • (x - u) := by
    rw [hz]; module
  have hbx : ‖(x - u) + (v - u)‖ ≤ Real.sqrt (δ ^ 2 + t ^ 2) := hbound _ _ hxu hvu hxh
  have hby : ‖(y - v) + (u - v)‖ ≤ Real.sqrt (δ ^ 2 + t ^ 2) := hbound _ _ hyv ht hyh
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, hzu]
    have hle := norm_add_le ((1 / 2 : ℝ) • ((x - u) + (v - u))) ((1 / 2 : ℝ) • (y - v))
    rw [norm_smul, norm_smul, Real.norm_eq_abs] at hle
    simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at hle
    linarith
  · rw [Metric.mem_ball, dist_eq_norm, hzv]
    have hle := norm_add_le ((1 / 2 : ℝ) • ((y - v) + (u - v))) ((1 / 2 : ℝ) • (x - u))
    rw [norm_smul, norm_smul, Real.norm_eq_abs] at hle
    simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at hle
    linarith
  · exact hKc hx.2 hy.2 (by norm_num) (by norm_num) (by norm_num)

/-! ## 4. The Metropolis threshold is cleared -/

/-- **`3e/40 ≤ 1/4`.**  `3e/40 ≈ 0.2039` is the lens constant the Metropolis route of
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` needs; `1/4` is what this file
proves.  Machine-checked so that the claim is not prose. -/
theorem three_exp_div_forty_le_quarter : 3 * Real.exp 1 / 40 ≤ 1 / 4 := by
  have := Real.exp_one_lt_d9
  linarith

/-! ## 5. Lemma 3.5 of [KLS95] at separation `δ/√n`, with the constant `1/4` -/

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`, in the `min` form, with the constant `1/4`.**

This is `Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp` with `1/8` improved to `1/4`.
The skeleton is `LensMin.lean`'s and the three bounds are its lemmas
`Arlib.MarkovChains.volume_lens_inter_ge_halfspace`,
`Arlib.MarkovChains.min_volume_le_volume_midpoint_sum` and
`Arlib.MarkovChains.homothety_image_subset_lens_of_dilate`; only two things change.

* The contraction ratio is `λ = √(1 − 1/n)` rather than `1 − 1/n`.  This is the largest ratio
  the half-space step's side condition `λ²δ² + t² ≤ δ²` allows at `t = δ/√n`, so the
  half-space bounds become *tight*, and the contraction factor rises from `(1 − 1/n)ⁿ ≥ 1/4`
  to `(√(1 − 1/n))ⁿ = √((1 − 1/n)ⁿ) ≥ 1/2` (`half_le_sqrt_one_sub_inv_pow`).
* The midpoint radius is the exact `(δ + √(δ²+t²))/2` of `midpoint_mem_ball_inter_sharp`
  rather than `LensMin.lean`'s `δ + t²/(4δ)`.  This is *forced*: with the crude radius the
  midpoint side condition `λ(ζ − t) ≤ δ − t` fails at `n = 2`, `t = δ/√2`, where it reads
  `0.29549δ ≤ 0.29289δ`.  With the exact radius it reads `0.28657δ ≤ 0.29289δ` and holds
  (`lens_side_two`), and for `n ≥ 3` it reduces to the polynomial `lens_side_poly`.

The final `2` is `LensMin.lean`'s combination of the forward and backward halves, so the
constant is `(1/2)/2 = 1/4`.

**`1/4` is the ceiling of this skeleton**, and the paper's `1/(e+1) ≈ 0.269` is *not*
reachable from it: at `n = 2` the half-space factor cannot exceed `λ² = 1 − 1/2 = 1/2` and the
midpoint factor cannot exceed `0.5223`, so even optimising the two ratios separately and
combining them harmonically (`c₁c₂/(c₁+c₂)`, which is what the assembly actually proves) caps
the constant at `0.2555 < 0.269`.  Beating `1/(e+1)` at `n = 2` needs a different argument, not
a different constant. -/
theorem volume_lens_ge_min_ball_inter_quarter (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 4) *
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
  -- the contraction ratio
  have hx0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
    linarith
  set lam : ℝ := Real.sqrt (1 - 1 / (n : ℝ)) with hlamdef
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hx0
  have hlam1 : lam ≤ 1 := by
    have hone : 1 - 1 / (n : ℝ) ≤ (1 : ℝ) := by
      have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    have h := Real.sqrt_le_sqrt hone
    simp only [Real.sqrt_one] at h
    exact h
  have hlamsq : lam ^ 2 = 1 - 1 / (n : ℝ) := Real.sq_sqrt hx0.le
  have hlamn0 : (0 : ℝ) ≤ lam ^ n := pow_nonneg hlam0.le n
  have hchalf : (1 : ℝ) / 2 ≤ lam ^ n := half_le_sqrt_one_sub_inv_pow hn
  -- the half-space side condition, now tight
  have hhs : lam ^ 2 * δ ^ 2 + ‖u - v‖ ^ 2 ≤ δ ^ 2 := by
    rw [hlamsq]
    have he : (1 - 1 / (n : ℝ)) * δ ^ 2 = δ ^ 2 - δ ^ 2 / (n : ℝ) := by field_simp
    have hle : ‖u - v‖ ^ 2 ≤ δ ^ 2 / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]; linarith [ht2]
    rw [he]; linarith
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
  -- the midpoint side condition, by cases on `n = 2` versus `n ≥ 3`
  have hcond : lam * ((δ + Real.sqrt (δ ^ 2 + ‖u - v‖ ^ 2)) / 2 - ‖u - v‖)
      ≤ δ - ‖u - v‖ := by
    rcases eq_or_lt_of_le hn with h2 | h3
    · have hn2 : (n : ℝ) = 2 := by rw [← h2]; norm_num
      have hlameq : lam = Real.sqrt (1 / 2) := by rw [hlamdef, hn2]; norm_num
      have hsep2 : 2 * ‖u - v‖ ^ 2 ≤ δ ^ 2 := by rw [← hn2]; exact ht2
      rw [hlameq]
      exact lens_side_two hδ htnn hsep2
    · have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
      have hsep3 : 3 * ‖u - v‖ ^ 2 ≤ δ ^ 2 := by
        nlinarith [ht2, sq_nonneg ‖u - v‖]
      refine lens_side_sqrt hδ htnn hsep3 hlam0.le ?_
      rw [hlamsq]
      have he : (1 - 1 / (n : ℝ)) * δ ^ 2 = δ ^ 2 - δ ^ 2 / (n : ℝ) := by field_simp
      have hle : ‖u - v‖ ^ 2 ≤ δ ^ 2 / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]; linarith [ht2]
      rw [he]; linarith
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
    set ζ : ℝ := (δ + Real.sqrt (δ ^ 2 + ‖u - v‖ ^ 2)) / 2 with hζdef
    have hS : ((1 / 2 : ℝ) • Am + (1 / 2 : ℝ) • Bp)
        ⊆ (Metric.ball u ζ ∩ Metric.ball v ζ) ∩ K := by
      rintro z ⟨a, ⟨x, hxAm, rfl⟩, b, ⟨y, hyBp, rfl⟩, rfl⟩
      exact midpoint_mem_ball_inter_sharp hKc hδ hxAm.1 hxAm.2 hyBp.1 hyBp.2
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
    have hstep : L + c * min (volume Am) (volume Bp) ≤ L + L := add_le_add le_rfl hmid
    calc c * m ≤ L + c * min (volume Am) (volume Bp) := hmin
      _ ≤ L + L := hstep
      _ = 2 * L := by rw [two_mul]
  have hcge : ENNReal.ofReal (1 / 2) ≤ c := by
    rw [hcdef]; exact ENNReal.ofReal_le_ofReal hchalf
  have hfinal : 2 * (ENNReal.ofReal (1 / 4) * m) ≤ 2 * L := by
    have he : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = ENNReal.ofReal (1 / 2) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc 2 * (ENNReal.ofReal (1 / 4) * m) = ENNReal.ofReal (1 / 2) * m := by
          rw [← mul_assoc, he]
      _ ≤ c * m := mul_le_mul_left hcge _
      _ ≤ 2 * L := htwo
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hfinal

/-- **Lemma 3.5 of [KLS95] at separation `δ/√n`, in the paper's own `ℓ` shape, with the
constant `1/4`.**  The `min` is essential and the `max` form is false; see
`Arlib.MarkovChains.exists_halfspace_max_lt`. -/
theorem kls_lemma35_at_sep_sqrt_dim_quarter (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) :
    ENNReal.ofReal (1 / 4) * min (ell K δ u) (ell K δ v)
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
  exact volume_lens_ge_min_ball_inter_quarter hn hKc hu hv hδ hsep

/-! ## 6. What the constant buys: the local-conductance floor it can support

Pure arithmetic about inequalities of the shape `1 ≤ 20·a·κ·θ` — the shape of the `hfloor`
hypothesis of `Arlib.MarkovChains.metropolisGaussian_overlap_of_convex` and, through it, of
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`.  **Nothing here asserts that
any theorem carries such a floor at any particular `κ`**; these lemmas say what a floor
would cost, so that a lens constant can be compared against the alternatives without
arithmetic done in prose. -/

/-- The acceptance floor `a = e^{-(2Rδ+δ²)/(2s)}` of `Arlib.MarkovChains.metropolisAccept_ge`
is at most `1`, since its exponent is `≤ 0`.  Together with `ℓ ≤ 1` this is what makes
`floor_unsatisfiable_at_fortieth` bite. -/
theorem acceptance_le_one {R δ s : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hs : 0 < s) :
    Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) ≤ 1 := by
  rw [Real.exp_le_one_iff, div_nonpos_iff]
  right
  exact ⟨by nlinarith [sq_nonneg δ], by linarith⟩

/-- At the lens constant `1/40` of `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim`, the floor
`1 ≤ 20·a·κ·θ` says `a·θ ≥ 2`. -/
theorem floor_fortieth_iff (a θ : ℝ) : 1 ≤ 20 * a * (1 / 40) * θ ↔ 2 ≤ a * θ := by
  constructor <;> intro h <;> nlinarith

/-- At the lens constant `1/8` of
`Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_sharp`, the floor says `a·θ ≥ 2/5`. -/
theorem floor_eighth_iff (a θ : ℝ) : 1 ≤ 20 * a * (1 / 8) * θ ↔ 2 / 5 ≤ a * θ := by
  constructor <;> intro h <;> nlinarith

/-- At the lens constant `1/4` of `kls_lemma35_at_sep_sqrt_dim_quarter`, the floor says
`a·θ ≥ 1/5` — half the demand of `floor_eighth_iff`. -/
theorem floor_quarter_iff (a θ : ℝ) : 1 ≤ 20 * a * (1 / 4) * θ ↔ 1 / 5 ≤ a * θ := by
  constructor <;> intro h <;> nlinarith

/-- **The `δ/n` floor in force today makes exactly the same demand at `n = 2`.**  That floor is
`1 ≤ 20·a·(1−1/n)ⁿ·θ`, and at `n = 2` the factor is `(1/2)² = 1/4`. -/
theorem floor_dim_at_two (a θ : ℝ) :
    1 ≤ 20 * a * (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) * θ ↔ 1 / 5 ≤ a * θ := by
  norm_num
  constructor <;> intro h <;> nlinarith

/-- **The `1/4` floor is at worst the `δ/n` floor**, for every `n ≥ 2`: anything meeting
`1 ≤ 20·a·(1/4)·θ` meets `1 ≤ 20·a·(1−1/n)ⁿ·θ`.  The gap is a factor `4(1−1/n)ⁿ ∈ [1, 4/e]`,
i.e. at most `4/e ≈ 1.47`, so the `√n` in the separation would cost at most that much in the
`θ` demanded — and nothing at all at `n = 2`. -/
theorem floor_quarter_le_floor_dim {n : ℕ} (hn : 2 ≤ n) {a θ : ℝ}
    (h : 1 ≤ 20 * a * (1 / 4) * θ) : 1 ≤ 20 * a * (1 - 1 / (n : ℝ)) ^ n * θ := by
  have hq : (1 : ℝ) / 4 ≤ (1 - 1 / (n : ℝ)) ^ n := quarter_le_one_sub_inv_pow hn
  nlinarith

/-- **The `1/40` of `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` cannot support this floor
at all.**  It demands `a·θ ≥ 2` (`floor_fortieth_iff`), while the acceptance floor satisfies
`a ≤ 1` (`acceptance_le_one`) and any admissible `θ` satisfies `θ ≤ 1`, local conductance
being a probability (`Arlib.MarkovChains.ell_le_one`).  So a Metropolis overlap lemma on `1/40`
would be vacuous, and the sharpening to `1/8` — and here to `1/4` — is not a cosmetic
improvement of a constant but the difference between an empty hypothesis and a met one. -/
theorem floor_unsatisfiable_at_fortieth {a θ : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1)
    (hθ : θ ≤ 1) : ¬ (1 ≤ 20 * a * (1 / 40) * θ) := by
  rw [floor_fortieth_iff]
  nlinarith

/-! ## 7. The speedy ↔ Metropolis kernel comparison

As of this writing the repository has no comparison between `Arlib.MarkovChains.speedyWalk`
and `Arlib.MarkovChains.metropolisGaussian` anywhere; every Metropolis result is proved
against the Metropolis one-step law directly.  This section supplies the one-sided comparison
that does hold, and says plainly what it costs. -/

/-- **The Metropolis kernel dominates the speedy walk, at the price `a·ℓ(x)`.**

    a · ℓ(x) · speedyWalk K δ x A  ≤  metropolisGaussian K δ s x A

for every measurable `A`, every `x` with `‖x‖ ≤ R` at which the walk is not stuck
(`vol(B(x,δ) ∩ K) ≠ 0`), where `a = e^{-(2Rδ+δ²)/(2s)}` is the acceptance floor of
`Arlib.MarkovChains.metropolisAccept_ge` — the repository's real floor, **not** `1/e` and not
an idealisation.

**Why the two factors, and why neither is removable.**  Both kernels put the same
*unnormalised* mass on `A ∩ B(x,δ) ∩ K`; they differ in what they divide by and in what they
reject.

* `ℓ(x) = vol(B(x,δ) ∩ K)/vol(δBₙ)` is the change of normalisation.  The speedy walk divides
  by `vol(B(x,δ) ∩ K)` — it conditions on the proposal landing in `K` — whereas the Metropolis
  kernel divides by `vol(δBₙ)` and lets a rejected proposal become a holding atom.  So the
  Metropolis kernel is *uniformly smaller off the atom* by exactly `ℓ(x)`, and this factor is
  exact, not an estimate.
* `a` is the Metropolis filter: the speedy walk accepts every proposal inside `K`, the
  Metropolis chain accepts one only with probability `min(1, g(y)/g(x))`, which
  `Arlib.MarkovChains.metropolisAccept_ge` floors by `a`.  This factor *is* an estimate, and
  it is where the boundedness hypothesis `‖x‖ ≤ R` enters.

**The comparison is one-sided and cannot be reversed.**  `metropolisGaussian` carries a
holding atom at every `x` at which some proposal is rejected — which is every `x` unless
`B(x,δ) ⊆ K` and `g` is constant on it — so `metropolisGaussian x {x}` is typically positive
while `speedyWalk x {x}` is zero off `StuckPoints`.  No reverse inequality of this shape can
hold with a constant factor.

**What it does and does not buy.**  It transports any *lower* bound on the speedy walk (an
overlap bound, say) to `metropolisGaussian` at the cost of `a·ℓ`, which is why floors of the
shape `1 ≤ 20·a·κ·θ` reappear: a speedy overlap `1 ≤ 20·(P^sp_u(Tᶜ) + P^sp_v(T))` becomes
`1 ≤ 20·(P^met_u(Tᶜ) + P^met_v(T))` only after `a·θ ≥ 1` is paid, which §6 shows is strictly
harder than what the direct route asks.  It is therefore a structural bridge, not a shortcut,
and no result in this repository is re-derived through it. -/
theorem acceptance_mul_ell_mul_speedyWalk_le_metropolisGaussian {s : ℝ} (hs : 0 < s)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R)
    (hstuck : volume (Metric.ball x δ ∩ K) ≠ 0)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * ell K δ x
        * speedyWalk K δ x A
      ≤ metropolisGaussian K δ s x A := by
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  set V : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hVdef
  set W : ℝ≥0∞ := volume (Metric.ball x δ ∩ K) with hWdef
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hWtop : W ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  -- off `StuckPoints` the speedy walk is the plain conditional ratio
  have hnotstuck : x ∉ StuckPoints K δ := fun hc => hstuck (mem_stuckPoints_iff.1 hc)
  have hsp : speedyWalk K δ x A = W⁻¹ * volume (A ∩ (Metric.ball x δ ∩ K)) := by
    rw [speedyWalk_apply_set hK δ x hA, Set.indicator_of_notMem hnotstuck]
    simp [hWdef]
  -- the change of normalisation is exactly `ℓ`
  have hellW : ell K δ x * V = W := ell_mul_volume_ball K hδ x
  have hnorm : ell K δ x * W⁻¹ = V⁻¹ := by
    have hone : ell K δ x * W⁻¹ * V = 1 := by
      calc ell K δ x * W⁻¹ * V = ell K δ x * V * W⁻¹ := by ring
        _ = W * W⁻¹ := by rw [hellW]
        _ = 1 := ENNReal.mul_inv_cancel hstuck hWtop
    calc ell K δ x * W⁻¹ = ell K δ x * W⁻¹ * (V * V⁻¹) := by
          rw [ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
      _ = ell K δ x * W⁻¹ * V * V⁻¹ := by ring
      _ = V⁻¹ := by rw [hone, one_mul]
  -- the Metropolis domination, at `C = B(x,δ)`
  have hdom : a * V⁻¹ * volume (A ∩ (Metric.ball x δ ∩ K)) ≤ metropolisGaussian K δ s x A :=
    mul_volume_le_metropolisGaussian hs hR hδ hx hA
      (measurableSet_ball.inter hK) (subset_refl _)
  calc a * ell K δ x * speedyWalk K δ x A
      = a * (ell K δ x * W⁻¹) * volume (A ∩ (Metric.ball x δ ∩ K)) := by rw [hsp]; ring
    _ = a * V⁻¹ * volume (A ∩ (Metric.ball x δ ∩ K)) := by rw [hnorm]
    _ ≤ metropolisGaussian K δ s x A := hdom

end LensSharp

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.lens_side_poly
#print axioms Arlib.MarkovChains.lens_side_two
#print axioms Arlib.MarkovChains.lens_side_sqrt
#print axioms Arlib.MarkovChains.midpoint_mem_ball_inter_sharp
#print axioms Arlib.MarkovChains.half_le_sqrt_one_sub_inv_pow
#print axioms Arlib.MarkovChains.three_exp_div_forty_le_quarter
#print axioms Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter
#print axioms Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim_quarter
#print axioms Arlib.MarkovChains.acceptance_le_one
#print axioms Arlib.MarkovChains.floor_fortieth_iff
#print axioms Arlib.MarkovChains.floor_eighth_iff
#print axioms Arlib.MarkovChains.floor_quarter_iff
#print axioms Arlib.MarkovChains.floor_dim_at_two
#print axioms Arlib.MarkovChains.floor_quarter_le_floor_dim
#print axioms Arlib.MarkovChains.floor_unsatisfiable_at_fortieth
#print axioms Arlib.MarkovChains.acceptance_mul_ell_mul_speedyWalk_le_metropolisGaussian
