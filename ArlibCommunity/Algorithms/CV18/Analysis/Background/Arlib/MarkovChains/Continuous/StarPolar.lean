/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyOverlap
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRun

/-!
# Lemma 3.5 of [KLS95] by homothety, and `cor:overlap` with no local-conductance floor

Cousins–Vempala's `lem:overlap` (`1409.6011/vol3_journal.tex:581`) rests on Lemma 3.5 of
[KLS95] (cited at `:592`):

    vol(K ∩ B(u,δ) ∩ B(v,δ))  ≥  min{ℓ(u), ℓ(v)} · vol(δBₙ) / (e+1),

which is what lets the overlap bound dispense with any lower bound on the local conductance
`ℓ(x) = vol(K ∩ B(x,δ))/vol(B(x,δ))`.  `Arlib/MarkovChains/Continuous/SpeedyOverlap.lean` does
not have that lemma, and pays for it with the hypothesis `11 ≤ 20·ℓ(x)` — a floor that **no
bounded convex body satisfies**, since `ℓ → 1/2` at the boundary.  This file proves the lemma
and removes the floor.

## What is proved

* `homothety_image_subset_lens` / `volume_lens_inter_ge` — **the crux.**  If `K` is
  star-shaped about `u`, contracting `K ∩ B(u,δ)` towards `u` by the factor `λ = 1 − ‖u−v‖/δ`
  lands inside `K ∩ B(u,δ) ∩ B(v,δ)`, so

      (1 − ‖u−v‖/δ)ⁿ · vol(K ∩ B(u,δ))  ≤  vol(K ∩ B(u,δ) ∩ B(v,δ)).

* `volume_lens_inter_ge_max` — the same, run from both endpoints of a convex `K ∋ u,v`, at
  separation `‖u−v‖ ≤ δ/n`: the lens carries a `(1 − 1/n)ⁿ` fraction of the **larger** of the
  two ball-slices.  (The paper's `min` becomes a `max`.)
* `kls_lemma35_at_sep_div_dim` — **Lemma 3.5 of [KLS95] in the paper's own shape**, constant
  `1/(e+1)` and all, for `n ≥ 3` and `‖u−v‖ ≤ δ/n`.
* `overlap_speedyWalk_convex` — **the payoff.**  `cor:overlap`'s conclusion
  `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` on a convex `K`, at separation `δ/n`, **with the local
  conductance floor of `Arlib.MarkovChains.overlap_speedyWalk` deleted**, and with the paper's
  `d_ℓ(u,v) < 1/3` unnecessary.
* `conductance_speedyWalk_ge_of_convex` — `thm:speedyconductance` with `hoverlap` discharged
  on a bounded convex body: `Φ ≥ δ·ln 2/(640·σ·n)`.
* `exists_overlap_speedyWalk_convex_witness` — non-vacuity at a **bounded** convex body
  (`K = B(0,1/2) ⊆ ℝ²`), where `20·ℓ ≡ 5 < 11`, i.e. exactly where
  `Arlib.MarkovChains.overlap_speedyWalk` does not apply.
* `volume_eq_lintegral_polar` — the polar identity, for the record (see below).
* `volume_lens_inter_ge_halfspace` — the sharper, direction-dependent contraction: on the half
  of `B(u,δ)` facing `v` the admissible factor is `√(1 − t²/δ²)`, whose `n`-th power is still
  `≥ 1/2` at the paper's separation `t = δ/√n`.  Unconditional, and the natural starting point
  for a `δ/√n` proof — but not sufficient on its own; see below.

## Convexity, star-shapedness, and the polar decomposition

**Star-convexity about `u` is all the crux needs** (`homothety_image_subset_lens` takes
`StarConvex ℝ u K`); `K ∩ B(u,δ)` is in fact convex, and convexity of `K` is used only to run
the estimate from *both* `u` and `v` in `volume_lens_inter_ge_max`.

**And the polar decomposition is not needed at all** — nor is it missing.  The `SpeedyOverlap`
docstring says the polar decomposition of a star-shaped set about an interior point is
something "Mathlib does not support today"; that is **incorrect**, and the record is corrected
at `volume_eq_lintegral_polar`.  Mathlib has the measure-preserving polar homeomorphism
(`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, `Measure.toSphere`,
`Measure.volumeIoiPow`), and this repository has packaged it about an arbitrary centre since
`HitAndRun.lean:479` (`Arlib.MarkovChains.lintegral_polar_at`).  Only the radial-function form
`vol = ∫_{Sⁿ⁻¹} ρ(θ)ⁿ/n dθ` is absent — and the sole consequence of it that Lemma 3.5 uses is
the `n`-homogeneity `vol(λ·S) = λⁿ·vol(S)`, which Mathlib supplies for an *arbitrary* set as
`MeasureTheory.Measure.addHaar_image_homothety`.

## What is assumed

Nothing is `sorry`ed and no axiom is declared; every result below is
`[propext, Classical.choice, Quot.sound]`.  Two hypotheses are carried as explicit binders:

* **`hpos : ∀ x ∈ K, vol(K ∩ B(x,δ)) ≠ 0`** in `overlap_speedyWalk_convex` and
  `conductance_speedyWalk_ge_of_convex`.  This is **not** a floor on `ℓ` in disguise:
  `volume_ball_inter_ne_zero_of_convex` discharges it for *every* bounded convex set of
  positive volume, with no lower bound on `ℓ` whatever, and the witness discharges it at a
  body where `ℓ = 1/4`.  It cannot be dropped: for `K` a segment in `ℝ²` every point of `K` is
  a *stuck point* of the speedy walk, both one-step probabilities are `0`, and the conclusion
  `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` is false.  The deleted floor `11 ≤ 20·ℓ` was silently excluding
  this degenerate case.
* **`hiso`** in `conductance_speedyWalk_ge_of_convex` — `thm:iso`, unproved in this
  repository, inherited verbatim from `Arlib.MarkovChains.conductance_speedyGaussian_ge`.

## The separation: `δ/n`, not `δ/√n` — an honest gap

The contraction factor must satisfy `λδ + ‖u−v‖ ≤ δ`, so a constant `λⁿ` forces
`‖u−v‖ = O(δ/n)`.  At the paper's `‖u−v‖ ≤ δ/√n` this argument gives only
`(1 − 1/√n)ⁿ ≈ e^{−√n}`, and **the `δ/√n` form of Lemma 3.5 is not proved here.**

It is not merely a matter of sharpening the constant.  At `‖u−v‖ = δ/√n` the `min` in the
paper's statement is essential: take `K` a thin cone with apex at `u` opening *away* from `v`;
then `K ∩ B(u,δ)` is concentrated within `‖u−v‖` of the sphere `∂B(u,δ)` on the far side, so
`vol(K ∩ B(u,δ) ∩ B(v,δ))/vol(K ∩ B(u,δ))` is exponentially small, and the statement survives
only because `ℓ(v)` is exponentially small too.  Any proof at `δ/√n` must therefore compare the
two centres, which the homothety argument does not do.  The estimate proved here is
insensitive to this — it holds with `max`, uniformly — but only at `δ/n`.

`volume_lens_inter_ge_halfspace` isolates what is missing, and reduces the `δ/√n` form of
Lemma 3.5 to a single clean inequality.  Writing `H_u = {x : ⟪x−u, v−u⟫ ≥ 0}` and
`H_v = {x : ⟪x−v, u−v⟫ ≥ 0}` (two half-spaces whose union is all of `ℝⁿ`), that lemma gives at
`‖u−v‖ ≤ δ/√n`, `n ≥ 2` — modulo the arithmetic `(1 − 1/n)^{n/2} ≥ 1/2`, which is *not*
formalised here —

    vol(K ∩ B(u,δ) ∩ B(v,δ))  ≥  ½ · max{vol(K ∩ B(u,δ) ∩ H_u), vol(K ∩ B(v,δ) ∩ H_v)}.

So `cor:overlap` at `δ/√n` would follow from a bound of the form
`max{vol(K ∩ B(u,δ) ∩ H_u), vol(K ∩ B(v,δ) ∩ H_v)} ≥ c·max{vol(K ∩ B(u,δ)), vol(K ∩ B(v,δ))}`
for a convex `K ∋ u,v`.  That inequality is **not proved here and is not assumed anywhere in
this file** — no theorem below carries it as a binder.

⚠ **It is also FALSE, and this paragraph used to say otherwise** (corrected 2026-08-12).  It
claimed the inequality "survives both configurations that defeat the naive arguments … we have
no proof of it, and no counterexample."  The second half was wrong, and the counterexample is
the very configuration the first half names:
`Arlib/MarkovChains/Continuous/LensHalfspace.lean` refutes it with
`Arlib.MarkovChains.exists_halfspace_max_lt` — for **every** `c > 0` there is a dimension and a
configuration at `‖u−v‖ ≤ δ/√n` where it fails.  The witness `apexConeBody u v` is the solid
cone with apex at `v` opening towards `u`: both half-space slices are trapped in the apex
slice, while an *expanding* homothety about `v` gives `(1+t/4)ⁿ·vol(K∩B_v) ≤ vol(K∩B_u)`.  So
the best possible constant at separation `t` is `≤ (1+t/4)^{−n}`, and a constant `c` forces
`t = O(δ/n)`.

**Hence the `δ/n` hypothesis of `Arlib.MarkovChains.volume_lens_inter_ge_max` below is
OPTIMAL up to the constant**, not an artefact — `Arlib.MarkovChains.volume_lens_le_apexConeBody`
proves `(1+t/4)ⁿ·vol(lens) ≤ max{vol(K∩B_u), vol(K∩B_v)}`.  No `δ/n^α` with `α < 1` is
available for the `max` form, and
`Arlib.MarkovChains.exists_overlap_speedyWalk_sqrt_dim_counterexample` shows the *conclusion*
of `overlap_speedyWalk_convex` genuinely fails at `‖u−v‖ < δ/√n` with every other hypothesis
holding.

**The real gap is elsewhere, and this is the useful part.**  `volume_lens_inter_ge_max` is
tight; what blocks `δ/√n` is the **shape** of `hoverlap`.  The paper's route needs the **min**
form of KLS 3.5 *together with* an `ℓ`-comparability hypothesis — exactly the `d_ℓ(u,v) < 1/3`
of `lem:overlap` that `overlap_speedyWalk_convex` deletes.  The two one-step laws are
normalised by `vol(K∩B_u)` and `vol(K∩B_v)` **separately**, so
`P_u(Tᶜ) + P_v(T) ≥ vol(lens)/max{…}` and the `min` alone does not close it; the
counterexample is precisely a configuration with `20·ℓ(v) < ℓ(u)`.  Note the paper's `min`
form itself is **not** impugned — `Arlib.MarkovChains.volume_lens_eq_min_apexConeBody` shows
the lens *equals* that `min` on this body, at constant `1`.

The cost of the gap is exactly one factor of `√n` in the conductance:
`conductance_speedyWalk_ge_of_convex` gives `Ω(δ/(σn))` where the paper claims `Ω(δ/(σ√n))`.
The `√n`-sharp *lens* estimate for balls is already in
`Arlib.MarkovChains.volume_ball_le_volume_inter_ball_add_sqrt`; it is the passage from the ball
to the **body** that is stuck at `δ/n`.

We could not verify the exact hypothesis of Lemma 3.5 against [KLS95] itself — that paper is
not in this tree (the untracked `258533.258665.pdf` at the repository root is a *different*
Kannan–Vempala paper, *Sampling Lattice Points*, STOC '97) — so this file does **not** claim
that Cousins–Vempala miscite it; it claims only
that the argument reconstructed here — the one the `1/(e+1)` constant fingerprints, since
`(1 − 1/n)ⁿ ≥ 1/(e+1)` holds exactly for `n ≥ 3` — needs `δ/n`.

## No rate claim

`thm:iso` is unproved here, and so is Lemma 3.5 at separation `δ/√n`.  Nothing below asserts,
or may be quoted as asserting, a polynomial mixing time.

## References

Cousins and Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*,
§4.1 (`1409.6011/vol3_journal.tex:509–700`).
Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a localization
lemma* (1995), Lemma 3.5.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped InnerProductSpace

/-! ## 1. The homothety inclusion -/

/-- **The homothety inclusion — the geometric crux.**  If `K` is star-shaped about `u`
(convexity of `K` together with `u ∈ K` gives this, and it is all that is used), then
contracting `K ∩ B(u,δ)` towards `u` by a factor `λ` with `λδ + ‖u−v‖ ≤ δ` lands inside
the *lens* `B(u,δ) ∩ B(v,δ)`, and stays inside `K`:

    homothety u λ '' (B(u,δ) ∩ K)  ⊆  (B(u,δ) ∩ B(v,δ)) ∩ K.

Three one-line checks: the image is in `K` because `u + λ(x−u) = (1−λ)u + λx` is a convex
combination of `u ∈ K` and `x ∈ K`; it is in `B(u,λδ) ⊆ B(u,δ)`; and it is in `B(v,δ)` by the
triangle inequality `λ‖x−u‖ + ‖u−v‖ < λδ + ‖u−v‖ ≤ δ`.

`0 < λ` is genuinely needed: at `λ = 0` the image is `{u}`, which is not in `B(v,δ)` when
`‖u−v‖ = δ`. -/
theorem homothety_image_subset_lens {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hsep : lam * δ + ‖u - v‖ ≤ δ) :
    AffineMap.homothety u lam '' (Metric.ball u δ ∩ K)
      ⊆ (Metric.ball u δ ∩ Metric.ball v δ) ∩ K := by
  rintro _ ⟨x, ⟨hxb, hxK⟩, rfl⟩
  have hxu : ‖x - u‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hxb
  have hval : AffineMap.homothety u lam x = (1 - lam) • u + lam • x := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have hnorm : dist (AffineMap.homothety u lam x) u = lam * ‖x - u‖ := by
    rw [dist_eq_norm, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
  have hlt : lam * ‖x - u‖ < lam * δ := mul_lt_mul_of_pos_left hxu hlam0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, hnorm]
    have : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
    linarith
  · rw [Metric.mem_ball]
    calc dist (AffineMap.homothety u lam x) v
        ≤ dist (AffineMap.homothety u lam x) u + dist u v := dist_triangle _ _ _
      _ = lam * ‖x - u‖ + ‖u - v‖ := by rw [hnorm, dist_eq_norm]
      _ < lam * δ + ‖u - v‖ := by linarith
      _ ≤ δ := hsep
  · rw [hval]
    exact hKc hxK (by linarith) hlam0.le (by ring)

/-! ## 2. The volume estimate -/

/-- **The radial volume estimate.**  Lebesgue measure is `n`-homogeneous, so the homothety
of `homothety_image_subset_lens` costs exactly the factor `λⁿ`:

    λⁿ · vol(K ∩ B(u,δ))  ≤  vol(K ∩ B(u,δ) ∩ B(v,δ)).

This is the only consequence of the polar decomposition of the star-shaped set `K ∩ B(u,δ)`
that the KLS estimate needs — `vol = ∫_{Sⁿ⁻¹} ρ(θ)ⁿ/n dθ` is `n`-homogeneous in `ρ`, and
scaling `ρ ↦ λρ` is exactly the homothety.  `MeasureTheory.Measure.addHaar_image_homothety`
supplies the homogeneity directly, for an arbitrary set, with no measurability side goal. -/
theorem volume_lens_inter_ge_homothety {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hsep : lam * δ + ‖u - v‖ ≤ δ) :
    ENNReal.ofReal (lam ^ n) * volume (Metric.ball u δ ∩ K)
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have himg := Measure.addHaar_image_homothety
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) u lam (Metric.ball u δ ∩ K)
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ n)] at himg
  calc ENNReal.ofReal (lam ^ n) * volume (Metric.ball u δ ∩ K)
      = volume (AffineMap.homothety u lam '' (Metric.ball u δ ∩ K)) := himg.symm
    _ ≤ _ := measure_mono (homothety_image_subset_lens hKc hlam0 hlam1 hsep)

/-- **The star-shaped overlap estimate.**  For `K` star-shaped about `u` and `‖u−v‖ < δ`,

    (1 − ‖u−v‖/δ)ⁿ · vol(K ∩ B(u,δ))  ≤  vol(K ∩ B(u,δ) ∩ B(v,δ)).

This is `volume_lens_inter_ge_homothety` at the largest admissible contraction factor
`λ = 1 − ‖u−v‖/δ`. -/
theorem volume_lens_inter_ge {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ‖u - v‖ < δ) :
    ENNReal.ofReal ((1 - ‖u - v‖ / δ) ^ n) * volume (Metric.ball u δ ∩ K)
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have h0 : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hfrac : ‖u - v‖ / δ < 1 := (div_lt_one hδ).2 hsep
  refine volume_lens_inter_ge_homothety hKc (by linarith) (by
    have : (0 : ℝ) ≤ ‖u - v‖ / δ := by positivity
    linarith) ?_
  have : (1 - ‖u - v‖ / δ) * δ = δ - ‖u - v‖ := by field_simp
  rw [this]
  linarith

/-- **The two-sided form**, for a convex `K` containing both `u` and `v`: the lens carries at
least a `(1 − 1/n)ⁿ` fraction of the **larger** of the two ball-slices,

    (1 − 1/n)ⁿ · max{vol(K ∩ B(u,δ)), vol(K ∩ B(v,δ))}  ≤  vol(K ∩ B(u,δ) ∩ B(v,δ)),

whenever `‖u − v‖ ≤ δ/n`.  Convexity is used exactly here — to run
`volume_lens_inter_ge` from *both* endpoints; star-shapedness about `u` alone gives only the
`u`-side.  The `max` (rather than the paper's `min`) is what removes the need for the
`d_ℓ(u,v) < 1/3` hypothesis of `lem:overlap`. -/
theorem volume_lens_inter_ge_max {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / n) :
    ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n)
        * max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h0 : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hlt : ‖u - v‖ < δ := by
    have : δ / (n : ℝ) < δ := by
      rw [div_lt_iff₀ hnpos]; nlinarith
    linarith
  have hfrac : ‖u - v‖ / δ ≤ 1 / (n : ℝ) := by
    rw [div_le_div_iff₀ hδ hnpos]
    rw [le_div_iff₀ hnpos] at hsep
    linarith
  have hmono : ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n)
      ≤ ENNReal.ofReal ((1 - ‖u - v‖ / δ) ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by
      have : (1 : ℝ) / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
      linarith)
    linarith
  have hsymm : ‖v - u‖ = ‖u - v‖ := norm_sub_rev _ _
  rcases le_total (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) with h | h
  · rw [max_eq_right h]
    have := volume_lens_inter_ge (hKc.starConvex hv) (u := v) (v := u) hδ (by rw [hsymm]; exact hlt)
    rw [hsymm] at this
    rw [Set.inter_comm (Metric.ball u δ) (Metric.ball v δ)]
    exact le_trans (by gcongr) this
  · rw [max_eq_left h]
    exact le_trans (by gcongr) (volume_lens_inter_ge (hKc.starConvex hu) hδ hlt)

/-! ## 3. The constant `(1 − 1/n)ⁿ` -/

/-- `(1 − 1/(m+2))^(m+1) ≥ e⁻¹`, i.e. `(1 + 1/(m+1))^(m+1) ≤ e`, which is
`1 + x ≤ eˣ` raised to the power `m+1` at `x = 1/(m+1)`. -/
theorem exp_neg_one_le_one_sub_inv_pow_pred (m : ℕ) :
    Real.exp (-1) ≤ (((m : ℝ) + 1) / ((m : ℝ) + 2)) ^ (m + 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hstep : ((m : ℝ) + 2) / ((m : ℝ) + 1) ≤ Real.exp (1 / ((m : ℝ) + 1)) := by
    have h := Real.add_one_le_exp (1 / ((m : ℝ) + 1))
    have : ((m : ℝ) + 2) / ((m : ℝ) + 1) = 1 / ((m : ℝ) + 1) + 1 := by
      field_simp
      ring
    rw [this]
    exact h
  have hA : (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1) ≤ Real.exp 1 := by
    calc (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1)
        ≤ (Real.exp (1 / ((m : ℝ) + 1))) ^ (m + 1) :=
          pow_le_pow_left₀ (by positivity) hstep _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
  have hApos : (0 : ℝ) < (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1) := by positivity
  have hinv : (((m : ℝ) + 1) / ((m : ℝ) + 2)) ^ (m + 1)
      = ((((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ (m + 1))⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hinv, Real.exp_neg]
  exact inv_anti₀ hApos hA

/-- **`(1 − 1/n)ⁿ ≥ e⁻¹·(1 − 1/n)`**, for `n ≥ 2` — the quantitative content of the
constant in Lemma 3.5. -/
theorem exp_neg_one_mul_le_one_sub_inv_pow {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-1) * (1 - 1 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hq : (1 : ℝ) - 1 / (((m : ℕ) + 2 : ℕ) : ℝ) = ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
    push_cast
    field_simp
    ring
  have hq0 : (0 : ℝ) ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) := by positivity
  rw [hq, pow_succ]
  exact mul_le_mul_of_nonneg_right (exp_neg_one_le_one_sub_inv_pow_pred m) hq0

/-- **`(1 − 1/n)ⁿ ≥ 1/20` for `n ≥ 2`** — the form the overlap bound consumes.
`e⁻¹ ≥ 1/10` and `1 − 1/n ≥ 1/2`. -/
theorem inv_twenty_le_one_sub_inv_pow {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / 20 ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : (1 : ℝ) / 2 ≤ 1 - 1 / (n : ℝ) := by
    have h1 : (1 : ℝ) / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have he : (1 : ℝ) / 10 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9
    linarith
  calc (1 : ℝ) / 20 = (1 / 10) * (1 / 2) := by norm_num
    _ ≤ Real.exp (-1) * (1 - 1 / (n : ℝ)) := by
        apply mul_le_mul he hq (by norm_num) (Real.exp_nonneg _)
    _ ≤ (1 - 1 / (n : ℝ)) ^ n := exp_neg_one_mul_le_one_sub_inv_pow hn

/-- **`(1 − 1/n)ⁿ ≥ 1/(e+1)` for `n ≥ 3`** — the constant printed in Cousins–Vempala's
`eq:kls-overlap`, recovered exactly.  For `n ≥ 4` it is `e⁻¹(1 − 1/n) = (n−1)/(ne) ≥ 1/(e+1)`,
which is `n ≥ e + 1`; at `n = 3` it is the numeric `8/27 ≥ 1/(e+1) ⟺ e ≥ 19/8`.
It **fails at `n = 2`**: `(1/2)² = 1/4 < 0.2689… = 1/(e+1)`. -/
theorem inv_exp_add_one_le_one_sub_inv_pow {n : ℕ} (hn : 3 ≤ n) :
    1 / (Real.exp 1 + 1) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he9 := Real.exp_one_lt_d9
  have he9' := Real.exp_one_gt_d9
  rcases eq_or_lt_of_le hn with h3 | h4
  · -- `n = 3`
    have hn3 : (n : ℝ) = 3 := by rw [← h3]; norm_num
    rw [← h3]
    have : (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 2 / 3 := by norm_num
    rw [this]
    rw [div_le_iff₀ (by linarith)]
    norm_num
    nlinarith
  · -- `n ≥ 4`
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    refine le_trans ?_ (exp_neg_one_mul_le_one_sub_inv_pow (by omega))
    rw [Real.exp_neg, div_le_iff₀ (by linarith)]
    have hkey : (1 : ℝ) - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) := by field_simp
    rw [hkey]
    have h1 : (Real.exp 1)⁻¹ * (((n : ℝ) - 1) / (n : ℝ)) * (Real.exp 1 + 1)
        = ((n : ℝ) - 1) * (Real.exp 1 + 1) / ((n : ℝ) * Real.exp 1) := by
      field_simp
    rw [h1, le_div_iff₀ (by positivity)]
    nlinarith

/-! ## 4. Positivity of `vol(K ∩ B(x,δ))` on a bounded convex body -/

/-- The homothety of a bounded star-shaped set about its centre lands in a small ball. -/
theorem homothety_image_subset_ball_inter {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ x K) {R δ lam : ℝ}
    (hR : K ⊆ Metric.closedBall x R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hlt : lam * R < δ) :
    AffineMap.homothety x lam '' K ⊆ Metric.ball x δ ∩ K := by
  rintro _ ⟨y, hyK, rfl⟩
  have hyR : ‖y - x‖ ≤ R := by
    have := hR hyK
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hnorm : dist (AffineMap.homothety x lam y) x = lam * ‖y - x‖ := by
    rw [dist_eq_norm, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
  have hval : AffineMap.homothety x lam y = (1 - lam) • x + lam • y := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, hnorm]
    have : lam * ‖y - x‖ ≤ lam * R := mul_le_mul_of_nonneg_left hyR hlam0.le
    linarith
  · rw [hval]
    exact hKc hyK (by linarith) hlam0.le (by ring)

/-- **A bounded convex body of positive volume has `vol(K ∩ B(x,δ)) > 0` at every `x ∈ K`.**

Contract `K` towards `x` by a factor small enough that the image sits inside `B(x,δ)`: the
image is still in `K`, and has volume `λⁿ·vol(K) > 0`.  This is what discharges the
positivity hypothesis `hpos` of `overlap_speedyWalk_convex` for a genuine convex *body*, and
it is the reason that hypothesis is not a disguised local-conductance floor: it holds for
**every** bounded convex set of positive volume, with no lower bound on `ℓ` whatever. -/
theorem volume_ball_inter_ne_zero_of_convex {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hKvol : volume K ≠ 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    volume (Metric.ball x δ ∩ K) ≠ 0 := by
  obtain ⟨R, hR⟩ := hKb.subset_closedBall x
  have hR0 : 0 ≤ R := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_self] at this
    exact this
  set lam : ℝ := min (1 / 2) (δ / (2 * (R + 1))) with hlamdef
  have hlam0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam1 : lam ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hlt : lam * R < δ := by
    have h1 : lam ≤ δ / (2 * (R + 1)) := min_le_right _ _
    have h2 : lam * R ≤ δ / (2 * (R + 1)) * R := mul_le_mul_of_nonneg_right h1 hR0
    have h3 : δ / (2 * (R + 1)) * R < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hsub := homothety_image_subset_ball_inter (hKc.starConvex hx) hR hlam0 hlam1 hlt
  have himg := Measure.addHaar_image_homothety
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) x lam K
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ n)] at himg
  have hpos : ENNReal.ofReal (lam ^ n) * volume K ≠ 0 := by
    refine mul_ne_zero ?_ hKvol
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  refine fun hzero => hpos ?_
  rw [← himg]
  exact measure_mono_null hsub hzero

/-! ## 5. Lemma 3.5 of [KLS95], at separation `δ/n` -/

/-- `ell K δ x · vol(δBₙ) = vol(K ∩ B(x,δ))`. -/
theorem ell_mul_volume_ball {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ell K δ x * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      = volume (Metric.ball x δ ∩ K) := by
  rw [ell_apply, ← volume_ball_eq x δ]
  exact ENNReal.div_mul_cancel (Metric.measure_ball_pos volume x hδ).ne' measure_ball_lt_top.ne

/-- **Lemma 3.5 of [KLS95], in the shape Cousins–Vempala quote it** (`eq:kls-overlap`,
`vol3_journal.tex:592`) — but at separation `δ/n`, not the paper's `δ/√n`:

    vol(K ∩ B(u,δ) ∩ B(v,δ))  ≥  min{ℓ(u), ℓ(v)} · vol(δBₙ) / (e+1)

for a convex `K` with `u, v ∈ K`, `‖u − v‖ ≤ δ/n` and `n ≥ 3`.

**What the constant is.**  The route here — contract `K ∩ B(u,δ)` towards `u` by the factor
`1 − ‖u−v‖/δ` — gives the strictly stronger `(1 − ‖u−v‖/δ)ⁿ · max{…}` of
`volume_lens_inter_ge_max`; at `‖u−v‖ = δ/n` that is `(1 − 1/n)ⁿ`, which is `≥ 1/(e+1)`
exactly for `n ≥ 3` (`inv_exp_add_one_le_one_sub_inv_pow`) and increases to `1/e`.  So the
paper's constant is recovered exactly, and the `min` is weakened to a `max`.

**The separation is `δ/n`, and this is a real gap.**  The contraction factor must satisfy
`λδ + ‖u−v‖ ≤ δ`, so `λⁿ ≥ 1/(e+1)` forces `‖u−v‖ = O(δ/n)`; at the paper's `‖u−v‖ ≤ δ/√n`
the same argument gives only `(1 − 1/√n)ⁿ ≈ e^{−√n}`.  The `δ/√n` statement is *not* proved
here and is not a corollary of anything here.  It is also not false for the reason the naive
argument fails: at `‖u−v‖ = δ/√n` the `min` is essential (a thin cone with apex at `u`
pointing away from `v` makes `vol(K ∩ B(u,δ) ∩ B(v,δ))/vol(K ∩ B(u,δ))` exponentially small,
and is saved only because `ℓ(v)` is then exponentially small too), whereas the estimate below
holds with `max` and needs no such case analysis.  Closing the gap needs a genuinely
different argument; see the module docstring. -/
theorem kls_lemma35_at_sep_div_dim {n : ℕ} (hn : 3 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ‖u - v‖ ≤ δ / n) :
    ENNReal.ofReal (1 / (Real.exp 1 + 1)) * min (ell K δ u) (ell K δ v)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have hconst : ENNReal.ofReal (1 / (Real.exp 1 + 1))
      ≤ ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) :=
    ENNReal.ofReal_le_ofReal (inv_exp_add_one_le_one_sub_inv_pow hn)
  have hminle : min (ell K δ u) (ell K δ v)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      ≤ max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) := by
    calc min (ell K δ u) (ell K δ v)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
        ≤ ell K δ u * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
          gcongr
          exact min_le_left _ _
      _ = volume (Metric.ball u δ ∩ K) := ell_mul_volume_ball K hδ u
      _ ≤ _ := le_max_left _ _
  calc ENNReal.ofReal (1 / (Real.exp 1 + 1)) * min (ell K δ u) (ell K δ v)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      = ENNReal.ofReal (1 / (Real.exp 1 + 1))
          * (min (ell K δ u) (ell K δ v)
            * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)) := by ring
    _ ≤ ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n)
          * max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)) := by
        gcongr
    _ ≤ _ := volume_lens_inter_ge_max (by omega) hKc hu hv hδ hsep

/-! ## 6. The payoff: `cor:overlap` with no local-conductance floor -/

/-- **`cor:overlap` for the speedy walk on a convex body, with no floor on `ℓ`**, at
separation `δ/n`.  In exactly the binder shape
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap` demands (with its `δ` taken to
be `δ/√n`; see `conductance_speedyWalk_ge_of_convex`).  For `u ∈ T`, `v ∉ T` in a convex `K`
with `‖u − v‖ < δ/n`,

    1  ≤  20 · (P_u(Tᶜ) + P_v(T)).

**What is different from `Arlib.MarkovChains.overlap_speedyWalk`.**  That theorem carries the
local-conductance floor `11 ≤ 20·ℓ(x)`, which fails for *every* bounded convex body (`ℓ → 1/2`
at the boundary), so it applies only to bodies with no `δ`-thin boundary.  **The floor is
gone here**, and what replaces it is `hpos`: `vol(K ∩ B(x,δ)) ≠ 0`.  That is not a floor in
disguise — `volume_ball_inter_ne_zero_of_convex` discharges it for every bounded convex set of
positive volume, uniformly, with no lower bound on `ℓ` — but it cannot be dropped: for `K` a
segment in `ℝ²`, every point of `K` is a *stuck point* of the speedy walk, `P_u(Tᶜ) = 0` and
`P_v(T) = 0`, and the conclusion is false.  `exists_overlap_speedyWalk_convex_witness` exhibits
a bounded convex body where `20·ℓ = 5 < 11`, i.e. where `overlap_speedyWalk` does not apply and
this theorem does.

The price is the separation: `δ/n` rather than the paper's `δ/√n`; see
`kls_lemma35_at_sep_div_dim`.

`u ∈ T`, `v ∉ T` and `d_h(u,v) < 1/4` are not used — they are carried only so the statement
matches the consumer's binder.  The paper's `d_ℓ(u,v) < 1/3` of `lem:overlap` is not needed
either, because `volume_lens_inter_ge_max` bounds the lens below by the `max` of the two
ball-slices rather than the `min`. -/
theorem overlap_speedyWalk_convex {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / (n : ℝ) → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  intro T hT u v _ huK hvK _ hsep _
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  set a : ℝ≥0∞ := volume (Metric.ball u δ ∩ K) with hadef
  set b : ℝ≥0∞ := volume (Metric.ball v δ ∩ K) with hbdef
  set M : ℝ≥0∞ := max a b with hMdef
  have hM0 : M ≠ 0 := by
    intro hc
    refine hpos u huK ?_
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
  have h3 : volume (Tᶜ ∩ (C ∩ K)) + volume (T ∩ (C ∩ K)) = volume (C ∩ K) := by
    have hmeas := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rw [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at hmeas
    rw [add_comm]
    exact hmeas
  have hlens : ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * M ≤ volume (C ∩ K) :=
    volume_lens_inter_ge_max hn hKc huK hvK hδ hsep.le
  have hconst : (1 : ℝ≥0∞) ≤ 20 * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) := by
    rw [show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20),
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    have := inv_twenty_le_one_sub_inv_pow hn
    linarith
  calc (1 : ℝ≥0∞) ≤ 20 * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) := hconst
    _ = 20 * (M⁻¹ * (ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * M)) := by
        rw [show M⁻¹ * (ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * M)
            = ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * (M⁻¹ * M) by ring,
          ENNReal.inv_mul_cancel hM0 hMtop, mul_one]
    _ ≤ 20 * (M⁻¹ * volume (C ∩ K)) := by gcongr
    _ = 20 * (M⁻¹ * volume (Tᶜ ∩ (C ∩ K)) + M⁻¹ * volume (T ∩ (C ∩ K))) := by
        rw [← mul_add, h3]
    _ ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by gcongr

/-! ## 7. `thm:speedyconductance` on a bounded convex body -/

/-- **`thm:speedyconductance` with `hoverlap` discharged, on a convex body — no floor on `ℓ`.**

This is `Arlib.MarkovChains.conductance_speedyGaussian_ge` applied at its parameter
`δ := δ/√n`, with `P := speedyWalk K δ` (that theorem takes the kernel as a parameter, so the
walk's step size and the theorem's `δ` are independent).  Its overlap binder then asks for
pairs at separation `(δ/√n)/√n = δ/n`, which is exactly what `overlap_speedyWalk_convex`
supplies.  The conclusion becomes

    Φ(speedyWalk K δ, π)  ≥  δ·ln 2 / (640·σ·n).

**Compared with `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell`.**  That corollary
gives `Ω(δ/(σ√n))` but assumes the local-conductance floor `11 ≤ 20·ℓ(x)` on all of `K`, which
no bounded convex body satisfies.  This one applies to every bounded convex body of positive
volume (`hpos` via `volume_ball_inter_ne_zero_of_convex`) and pays a factor `√n`: `Ω(δ/(σn))`.
The `√n` is exactly the separation gap of `kls_lemma35_at_sep_div_dim`.

**This is not a polynomial-time statement and may not be quoted as one**: `hiso` (`thm:iso`)
is a hypothesis and is unproved in this repository. -/
theorem conductance_speedyWalk_ge_of_convex {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / 8)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hmass : 0 < ∫ x, h x)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0)
    (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpi : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      pi A = ENNReal.ofReal (∫ x in A, h x) / ENNReal.ofReal (∫ x, h x))
    (hrev : IsReversible (speedyWalk K δ) pi) (hpiK : pi Kᶜ = 0)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ / Real.sqrt n * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ / Real.sqrt n * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist h u v) →
      δ / Real.sqrt n * Real.log 2 / Real.sqrt n / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ (∫ x, h x) * ∫ x in S₃, h x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * (n : ℝ)))
      ≤ conductance (speedyWalk K δ) pi := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hov : ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
    intro T hT u v huT huK hvK hvT hsep hd
    refine overlap_speedyWalk_convex hn hK hKc hδ hpos h T hT u v huT huK hvK hvT ?_ hd
    rwa [div_div, hs] at hsep
  have h1 : δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n)
      = δ * Real.log 2 / (640 * σ * (Real.sqrt n * Real.sqrt n)) := by
    field_simp
  have hconst : δ * Real.log 2 / (640 * σ * (n : ℝ))
      = δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n) := by
    rw [h1, hs]
  rw [hconst]
  exact conductance_speedyGaussian_ge hn hσ (by positivity)
    (by rw [div_le_div_iff₀ hspos (by positivity)]; nlinarith [hδσ, hspos])
    hh0 hmass hK (speedyWalk K δ) pi hpi hrev hpiK hov hiso

/-! ## 8. Non-vacuity, at a bounded convex body -/

/-- **The witness: a bounded convex body on which `overlap_speedyWalk`'s floor fails and
`overlap_speedyWalk_convex` applies.**

At `n = 2`, `K = B(0,1/2) ⊆ ℝ²`, `δ = 1`, `u = 0`, `v = (1/4,0)`, `T = B(0,1/8)`, `h ≡ 1`:

* `K` is convex, bounded and of positive volume, so `hpos` holds by
  `volume_ball_inter_ne_zero_of_convex`;
* `ℓ ≡ (1/2)² = 1/4` on `K` — since `K ⊆ B(x,1)` for every `x ∈ K` — so
  `20·ℓ(x) = 5 < 11`: the floor hypothesis `11 ≤ 20·ℓ(x)` of
  `Arlib.MarkovChains.overlap_speedyWalk` is **false here**, and that theorem does not apply;
* `u ∈ T`, `v ∉ T`, `‖u−v‖ = 1/4 < 1/2 = δ/n`, `d_h(u,v) = 0 < 1/4`;
* and the conclusion `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` nevertheless holds.

The existing witness `Arlib.MarkovChains.exists_overlap_speedyWalk_witness` is at `K = ℝ²`,
where `ℓ ≡ 1`; the point of this one is that the body is **bounded**, which is the case the
floor excludes and the case the algorithm actually runs in. -/
theorem exists_overlap_speedyWalk_convex_witness :
    ∃ (K T : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ)
      (u v : EuclideanSpace ℝ (Fin 2)) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧ 0 < δ ∧
      (∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0) ∧
      (∀ x ∈ K, ¬ ((11 : ℝ≥0∞) ≤ 20 * ell K δ x)) ∧
      MeasurableSet T ∧ u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < δ / ((2 : ℕ) : ℝ) ∧ densDist h u v < 1 / 4 ∧
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 (1 / 2) with hKdef
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℝ) with hvdef
  have hvnorm : ‖v‖ = 1 / 4 := by
    rw [hvdef, PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  have hVpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hKvol : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKc : Convex ℝ K := convex_ball _ _
  have hKb : Bornology.IsBounded K := Metric.isBounded_ball
  have hpos : ∀ x ∈ K, volume (Metric.ball x (1 : ℝ) ∩ K) ≠ 0 := fun x hx =>
    volume_ball_inter_ne_zero_of_convex hKc hKb hKvol hx (by norm_num)
  -- `ℓ ≡ 1/4` on `K`, so the floor `11 ≤ 20·ℓ` fails everywhere on `K`
  have hell : ∀ x ∈ K, ell K (1 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
      exact hx
    have hsub : K ⊆ Metric.ball x 1 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hball : volume K
        = ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 1 / 2),
        finrank_euclideanSpace_fin]
      norm_num
    rw [ell_apply, Set.inter_eq_self_of_subset_right hsub, hball, volume_ball_eq x 1]
    exact ENNReal.mul_div_cancel_right hVpos hVtop
  have hfloor : ∀ x ∈ K, ¬ ((11 : ℝ≥0∞) ≤ 20 * ell K (1 : ℝ) x) := by
    intro x hx hcon
    rw [hell x hx, show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20),
      show (11 : ℝ≥0∞) = ENNReal.ofReal 11 by simp] at hcon
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hcon
    norm_num at this
  have huK : (0 : EuclideanSpace ℝ (Fin 2)) ∈ K := by
    rw [hKdef]; exact Metric.mem_ball_self (by norm_num)
  have hvK : v ∈ K := by
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]; norm_num
  have hvT : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]
    norm_num
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 2)) - v‖ < (1 : ℝ) / ((2 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvnorm]
    norm_num
  have hdens : densDist (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) 0 v < 1 / 4 := by
    simp [densDist]
  refine ⟨K, Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8), 1, 0, v, fun _ => 1,
    measurableSet_ball, hKc, hKb, hKvol, by norm_num, hpos, hfloor, measurableSet_ball,
    Metric.mem_ball_self (by norm_num), huK, hvK, hvT, hsep, hdens, ?_⟩
  exact overlap_speedyWalk_convex (n := 2) (by norm_num) measurableSet_ball hKc (by norm_num)
    hpos (fun _ => 1) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8)) measurableSet_ball
    0 v (Metric.mem_ball_self (by norm_num)) huK hvK hvT (by exact_mod_cast hsep) hdens

/-! ## 9. The polar identity, for the record -/

/-- **Polar decomposition of the volume of a set about an arbitrary centre `u`:**

    vol(S)  =  ∫_{Sⁿ⁻¹} ∫_0^∞ r^{n−1} · 1_S(u + rθ) dr dσ(θ).

This is `Arlib.MarkovChains.lintegral_polar_at` (`HitAndRun.lean:479`) at the indicator of `S`,
and `lintegral_polar_at` is in turn Mathlib's
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` plus Tonelli.

**Correction to the record.**  The module docstring of
`Arlib/MarkovChains/Continuous/SpeedyOverlap.lean` states that the polar decomposition of a
star-shaped set about an interior point is something "Mathlib does not support today".  That is
**wrong**: Mathlib has the measure-preserving polar homeomorphism, `Measure.toSphere` and
`Measure.volumeIoiPow`, and this repository already packages them as `lintegral_polar` and
`lintegral_polar_at`, centred at an arbitrary point, since `HitAndRun.lean`.  What is genuinely
absent is only the *radial-function* packaging `vol = ∫ ρ(θ)ⁿ/n dθ` — and the estimate this
file proves does not need it: the single consequence of polar coordinates that Lemma 3.5 uses
is the `n`-homogeneity `vol(λ·S) = λⁿ·vol(S)`, which is
`MeasureTheory.Measure.addHaar_image_homothety`, valid for an arbitrary set. -/
theorem volume_eq_lintegral_polar {n : ℕ} (hn : 1 ≤ n) (u : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    volume S = ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ (n - 1))
            * S.indicator (fun _ => (1 : ℝ≥0∞)) (u + r • (θ : EuclideanSpace ℝ (Fin n)))
        ∂(volume : Measure ℝ) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  haveI : NeZero n := ⟨by omega⟩
  have hmeas : Measurable (S.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS
  rw [← lintegral_polar_at u hmeas, lintegral_indicator hS]
  simp

/-! ## 10. The sharper contraction on the half-space towards `v` -/

/-- **On the half of `B(u,δ)` that faces `v`, the admissible contraction factor is
`√(1 − t²/δ²)`, not `1 − t/δ`.**  Moving from `u` towards `v` one stays inside `B(v,δ)` for
almost the full radius `δ`: for `x` with `⟪x−u, v−u⟫ ≥ 0`,

    ‖u + λ(x−u) − v‖²  =  λ²‖x−u‖² − 2λ⟪x−u, v−u⟫ + t²  ≤  λ²δ² + t²,

so `λ = √(1 − t²/δ²)` suffices — and `λⁿ = (1 − t²/δ²)^{n/2} ≥ (1 − 1/n)^{n/2} ≥ 1/2` already
at the paper's separation `t = δ/√n`, where the uniform factor `(1 − t/δ)ⁿ ≈ e^{−√n}` is
useless.

This is the direction-dependent (polar) refinement, and it is where a `δ/√n` proof would have
to start.  It is **not** enough on its own: it bounds the lens below by the mass of
`K ∩ B(u,δ)` in the half-space facing `v`, and a thin cone with apex at `u` opening away from
`v` puts none of that mass there.  Closing the gap needs, in addition, a lower bound on

    max{vol(K ∩ B(u,δ) ∩ H_u), vol(K ∩ B(v,δ) ∩ H_v)}

in terms of `max{vol(K ∩ B(u,δ)), vol(K ∩ B(v,δ))}`, where `H_u`, `H_v` are the half-spaces
through `u` towards `v` and through `v` towards `u` (whose union is everything).  No such
bound is proved here, and none is assumed anywhere in this file. -/
theorem homothety_image_subset_lens_halfspace {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hlam : lam ^ 2 * δ ^ 2 + ‖u - v‖ ^ 2 ≤ δ ^ 2) :
    AffineMap.homothety u lam '' (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})
      ⊆ (Metric.ball u δ ∩ Metric.ball v δ) ∩ K := by
  rintro _ ⟨x, ⟨⟨hxb, hxK⟩, hxh⟩, rfl⟩
  have hxu : ‖x - u‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hxb
  have hval : AffineMap.homothety u lam x = (1 - lam) • u + lam • x := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have hdiff : AffineMap.homothety u lam x - v = lam • (x - u) - (v - u) := by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    abel
  have hnorm : dist (AffineMap.homothety u lam x) u = lam * ‖x - u‖ := by
    rw [dist_eq_norm, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
  have hip : 0 ≤ ⟪lam • (x - u), v - u⟫_ℝ := by
    rw [real_inner_smul_left]
    exact mul_nonneg hlam0.le hxh
  have hvu : ‖v - u‖ = ‖u - v‖ := norm_sub_rev _ _
  have hsq : ‖AffineMap.homothety u lam x - v‖ ^ 2
      = lam ^ 2 * ‖x - u‖ ^ 2 - 2 * ⟪lam • (x - u), v - u⟫_ℝ + ‖u - v‖ ^ 2 := by
    rw [hdiff, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0, hvu]
    ring
  have hlt : lam ^ 2 * ‖x - u‖ ^ 2 < lam ^ 2 * δ ^ 2 := by
    have h1 : ‖x - u‖ ^ 2 < δ ^ 2 := by nlinarith [norm_nonneg (x - u)]
    exact mul_lt_mul_of_pos_left h1 (by positivity)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, hnorm]
    nlinarith [norm_nonneg (x - u)]
  · rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [hsq, hip, hlt, hlam, hδ, norm_nonneg (AffineMap.homothety u lam x - v)]
  · rw [hval]
    exact hKc hxK (by linarith) hlam0.le (by ring)

/-- The volume form of `homothety_image_subset_lens_halfspace`. -/
theorem volume_lens_inter_ge_halfspace {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} (hKc : StarConvex ℝ u K) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hlam : lam ^ 2 * δ ^ 2 + ‖u - v‖ ^ 2 ≤ δ ^ 2) :
    ENNReal.ofReal (lam ^ n)
        * volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})
      ≤ volume ((Metric.ball u δ ∩ Metric.ball v δ) ∩ K) := by
  have himg := Measure.addHaar_image_homothety
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) u lam
    (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ n)] at himg
  calc ENNReal.ofReal (lam ^ n)
        * volume (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})
      = volume (AffineMap.homothety u lam ''
          (Metric.ball u δ ∩ K ∩ {x | 0 ≤ ⟪x - u, v - u⟫_ℝ})) := himg.symm
    _ ≤ _ := measure_mono (homothety_image_subset_lens_halfspace hKc hδ hlam0 hlam1 hlam)

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.homothety_image_subset_lens
#print axioms Arlib.MarkovChains.volume_lens_inter_ge_homothety
#print axioms Arlib.MarkovChains.volume_lens_inter_ge
#print axioms Arlib.MarkovChains.volume_lens_inter_ge_max
#print axioms Arlib.MarkovChains.exp_neg_one_le_one_sub_inv_pow_pred
#print axioms Arlib.MarkovChains.exp_neg_one_mul_le_one_sub_inv_pow
#print axioms Arlib.MarkovChains.inv_twenty_le_one_sub_inv_pow
#print axioms Arlib.MarkovChains.inv_exp_add_one_le_one_sub_inv_pow
#print axioms Arlib.MarkovChains.homothety_image_subset_ball_inter
#print axioms Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex
#print axioms Arlib.MarkovChains.ell_mul_volume_ball
#print axioms Arlib.MarkovChains.kls_lemma35_at_sep_div_dim
#print axioms Arlib.MarkovChains.overlap_speedyWalk_convex
#print axioms Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex
#print axioms Arlib.MarkovChains.exists_overlap_speedyWalk_convex_witness
#print axioms Arlib.MarkovChains.volume_eq_lintegral_polar
#print axioms Arlib.MarkovChains.homothety_image_subset_lens_halfspace
#print axioms Arlib.MarkovChains.volume_lens_inter_ge_halfspace
