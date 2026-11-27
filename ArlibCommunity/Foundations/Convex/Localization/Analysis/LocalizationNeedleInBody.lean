/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationMeasurable
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.IsoConcaveWeight

section
/-!
# The Localization Lemma with the needle inside the body

`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer_of_localization`
(`ArlibCommunity/Foundations/Convex/CrossRatioIsoperimetry/Analysis/IsoConcaveWeight.lean`) carries a binder `hloc` — the Localization Lemma of
Kannan–Lovász–Simonovits in the one-equality-one-inequality form (KLS Corollary 2.4), with the
extra requirement that the needle it produces lies **inside** the body `K`.  This file discharges
that binder for a compact convex `K` in dimension `n ≥ 2`.

## The source statement

`ArlibCommunity.Foundations.Convex.hloc_needle_in_body` is **Corollary 2.4** of Kannan–Lovász–Simonovits, *Isoperimetric
problems for convex bodies and a localization lemma*, Discrete Comput. Geom. **13** (1995),
541–559, p. 545: for a bounded convex `T`, `g` bounded lower semicontinuous and `h` continuous on
`T` with `∫_T g > 0` and `∫_T h = 0`, there is a needle `N = (I, l)` **with `I ⊆ T`** such that
`∫_N g > 0` and `∫_N h = 0`.  The containment `I ⊆ T` is part of the corollary, and it is the
clause `hloc` needs.  Two differences from the paper, both in the direction of what the consumer
asks for: the integrands here are continuous (the paper's `g` may be lower semicontinuous — a
strictly weaker hypothesis that this file does not attempt), and the profile is asked to be
log-concave rather than an `(n−1)`-st power of an affine function, which is weaker.

The paper's own proof of Corollary 2.4 reduces it to Lemma 2.1 by a perturbation `g − δ + h/ε`,
`ε² − h` and a **subsequence limit** of the resulting needles.  The route taken here is different
and does not need that compactness argument: the containment is read off the chain that
`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact_ge` already builds *inside* `K`, whose limit body
carries both endpoints of the needle.

## What was missing, and what replaces it

`ArlibCommunity.Foundations.Convex.exists_needle_of_compact_convex` (`LocalizationMeasurable.lean`) is the recorded entry
point from a body to a needle, and it is *not* usable here, for two independent reasons:

* it drops the clause that the needle lies in `K`;
* it carries the nondegeneracy hypothesis `hsep : ∀ x, g₁ x = 0 → g₂ x < ε`, which an arbitrary
  pair of continuous integrands does not satisfy.

Both are addressed below, and the second is *removed* rather than assumed.  The observation that
does it is that the target `hloc` puts **no** nondegeneracy clause on the needle direction `e`:
`needleMap p 0` is the constant needle at `p`, which is a legitimate witness.  So the proof splits
on whether the limit body `⋂ k, C k` of the localisation chain contains two distinct points:

* **two points** — the chain's needle machinery applies, and the needle is inside `K` because its
  base `b` and its tip `b + v` are the points of `⋂ k, C k` at heights `0` and `1`, and `K` is
  convex;
* **a single point `p`** — then `g₁ p = 0` and `ε ≤ g₂ p` follow from the chain's invariants by
  continuity (`ArlibCommunity.Foundations.Convex.eq_zero_of_iInter_subsingleton`, `ArlibCommunity.Foundations.Convex.le_of_iInter_subsingleton`), and the
  constant needle at `p` is the witness.

`hsep` is exactly what the recorded route used to rule out the second case; here it is proved
instead of assumed.

## The route through the stack

The needle machinery is replayed, not re-proved: each step below is the corresponding theorem of
the localisation stack with the two membership clauses `b ∈ ⋂ k, C k` and `b + v ∈ ⋂ k, C k`
carried along.  The replay is three lemmas deep, over the *shrinking-slab* branch
(`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab`), which is the branch a
genuinely shrinking chain can satisfy — the fixed-slab
`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear` cannot be used, see the module
docstring of `ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationClosed`.

* `ArlibCommunity.Foundations.Convex.exists_axis_of_collinear_mem` — `ArlibCommunity.Foundations.Convex.exists_axis_of_collinear` with the base point and
  the tip of the produced axis exhibited as points of the limit body.
* `ArlibCommunity.Foundations.Convex.exists_needle_mem_of_collinear_shrinkingSlab`,
  `ArlibCommunity.Foundations.Convex.exists_needle_mem_of_compact_chain`, `ArlibCommunity.Foundations.Convex.exists_needle_mem_of_compact_chain_euclidean`
  — the same clauses carried through the shrinking-slab needle theorem, the chain form and the
  transport to `EuclideanSpace`.

## Main results

* `ArlibCommunity.Foundations.Convex.hloc_needle_in_body` — the `hloc` binder of
  `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer_of_localization`, proved, for a compact convex body
  in dimension `n ≥ 2`.
* `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer` — that theorem with `hloc` discharged, leaving
  `hLem41` and `htrans`.

## The dimension restriction

`n ≥ 2` is inherited from `ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact_ge`, whose bisection
scheme cuts with a pencil of hyperplanes through a codimension-two flat.  Nothing below is stated
for `n = 1`; the consumer's `1 ≤ n` becomes `2 ≤ n` in
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer`, and that is the only change to its statement.
-/

open MeasureTheory Set Filter
open scoped ENNReal _root_.Topology

open ArlibCommunity.Foundations.Convex

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

/-! ### Making a continuous integrand global -/

section Cutoff

variable {n : ℕ}

/-- **A continuous function is bounded, integrable and compactly supported after a cutoff, and
unchanged on a compact set.**

The needle theorems of the localisation stack ask for integrands that are continuous, integrable
and *globally* bounded; an arbitrary continuous integrand is none of the last two.  Multiplying by
the bump `max 0 (min 1 (R + 1 - ‖x‖))`, which is `1` on `closedBall 0 R ⊇ K` and `0` off
`closedBall 0 (R+1)`, repairs both and changes nothing on `K`. -/
theorem exists_bounded_integrable_eqOn_of_isCompact {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) :
    ∃ (g' : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ), Continuous g' ∧ Integrable g' ∧
      (∀ x, |g' x| ≤ M) ∧ ∀ x ∈ K, g' x = g x := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  set χ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => max 0 (min 1 (R + 1 - ‖x‖)) with hχdef
  have hχc : Continuous χ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hχone : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have := hR hx
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [hχdef]
    simp only
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hχoff : ∀ x, R + 1 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    rw [hχdef]
    simp only
    exact max_eq_left (min_le_of_right_le (by linarith))
  -- the compact set carrying the support
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (R + 1) with hBdef
  have hBcomp : IsCompact B := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hBcomp.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨fun x => g x * χ x, max C 0, hg.mul hχc, ?_, ?_, ?_⟩
  · refine (hg.mul hχc).integrable_of_hasCompactSupport (HasCompactSupport.intro hBcomp ?_)
    intro x hx
    have hxn : R + 1 ≤ ‖x‖ := by
      rw [hBdef, Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    show g x * χ x = 0
    rw [hχoff x hxn, mul_zero]
  · intro x
    by_cases hx : x ∈ B
    · have h1 : |g x| ≤ C := by simpa using hC x hx
      have h2 : |g x * χ x| ≤ |g x| := by
        rw [abs_mul, abs_of_nonneg (hχ0 x)]
        exact mul_le_of_le_one_right (abs_nonneg _) (hχ1 x)
      exact le_trans (le_trans h2 h1) (le_max_left _ _)
    · have hxn : R + 1 ≤ ‖x‖ := by
        rw [hBdef, Metric.mem_closedBall, dist_zero_right, not_le] at hx
        exact hx.le
      show |g x * χ x| ≤ max C 0
      rw [hχoff x hxn, mul_zero, abs_zero]
      exact le_max_right _ _
  · intro x hx
    show g x * χ x = g x
    rw [hχone x hx, mul_one]

end Cutoff

/-! ### The axis of a collinear limit body, with its endpoints exhibited -/

section Axis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`ArlibCommunity.Foundations.Convex.exists_axis_of_collinear` with the base point and the tip of the axis exhibited as
points of the limit body.**

The proof of that theorem reads the axis off the two points of `⋂ k, D k` at heights `0` and `1`,
so its base point `b` *is* a point of the limit body and its tip `b + v` is the other one; the
statement discards both facts.  They are exactly what makes the needle lie inside the body: if the
limit body is contained in a convex `K`, then so is the whole segment from `b` to `b + v`. -/
theorem exists_axis_of_collinear_mem {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) {a : E} {φ : E →ₗ[ℝ] ℝ}
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (hcol : Collinear ℝ (⋂ k, D k)) :
    ∃ b v : E, φ b = φ a ∧ φ v = 1 ∧ b ∈ ⋂ k, D k ∧ b + v ∈ ⋂ k, D k ∧
      ∀ y ∈ ⋂ k, D k, y = b + φ (y - b) • v := by
  obtain ⟨y₀, hy₀, h0⟩ :=
    exists_mem_iInter_height hDcomp hDmono hspan (left_mem_Icc.mpr zero_le_one)
  obtain ⟨y₁, hy₁, h1⟩ :=
    exists_mem_iInter_height hDcomp hDmono hspan (right_mem_Icc.mpr zero_le_one)
  rw [map_sub] at h0 h1
  obtain ⟨w, hw⟩ := (collinear_iff_of_mem hy₀).mp hcol
  obtain ⟨r₁, hr₁⟩ := hw y₁ hy₁
  have hy₁w : y₁ = r₁ • w + y₀ := by simpa only [vadd_eq_add] using hr₁
  have hkey : r₁ * φ w = 1 := by
    have h : φ y₁ = r₁ * φ w + φ y₀ := by rw [hy₁w, map_add, map_smul, smul_eq_mul]
    linarith
  refine ⟨y₀, r₁ • w, by linarith, by rw [map_smul, smul_eq_mul, hkey], hy₀, ?_,
    fun y hy => ?_⟩
  · rw [add_comm, ← hy₁w]; exact hy₁
  · obtain ⟨r, hr⟩ := hw y hy
    have hyw : y = r • w + y₀ := by simpa only [vadd_eq_add] using hr
    have hheight : φ (y - y₀) = r * φ w := by
      rw [hyw, add_sub_cancel_right, map_smul, smul_eq_mul]
    rw [hheight, smul_smul, hyw]
    have hcoef : r * φ w * r₁ = r := by
      have : r * (r₁ * φ w) = r := by rw [hkey, mul_one]
      linarith [this, mul_comm (φ w) r₁]
    rw [hcoef, add_comm]

end Axis

/-! ### The needle of a chain, with its two endpoints in the limit body -/

section NeedleMem

variable {m : ℕ}

/-- **`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` with the endpoints
of the needle exhibited in the limit body.**

The proof of that theorem is replayed verbatim with `ArlibCommunity.Foundations.Convex.exists_axis_of_collinear` replaced by
`ArlibCommunity.Foundations.Convex.exists_axis_of_collinear_mem`; nothing else changes, and the normalisation clause
`φ v = 1` — which is not needed downstream, `hloc` putting no nondegeneracy condition on the
needle direction — is dropped. -/
theorem exists_needle_mem_of_collinear_shrinkingSlab (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hCconv : ∀ k, Convex ℝ (C k))
    (hCcomp : ∀ k, IsCompact (C k)) (hCmono : ∀ k, C (k + 1) ⊆ C k)
    (hCpos : ∀ k, 0 < volume (C k))
    {l u : ℕ → ℝ} (hl0 : ∀ k, l k ≤ 0) (hu1 : ∀ k, 1 ≤ u k)
    (hslab : ∀ k, ∀ y ∈ C k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ C k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    (hcol : Collinear ℝ (⋂ k, C k))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in C k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ y in C k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), b ∈ ⋂ k, C k ∧ b + v ∈ ⋂ k, C k ∧
      (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hlu : ∀ k, l k < u k := fun k => lt_of_le_of_lt (hl0 k) (lt_of_lt_of_le one_pos (hu1 k))
  have hsub : ∀ k, Icc (0 : ℝ) 1 ⊆ Icc (l k) (u k) := fun k => Icc_subset_Icc (hl0 k) (hu1 k)
  have hspan01 : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ C k, φ (y - a) = t :=
    fun k t ht => hspan k t (hsub k ht)
  obtain ⟨b, v, hb, hφv, hbmem, hbvmem, haxis⟩ :=
    exists_axis_of_collinear_mem hCcomp hCmono hspan01 hcol
  have hshift : ∀ y : Fin (m + 1) → ℝ, φ (y - b) = φ (y - a) := by
    intro y; rw [map_sub, map_sub, hb]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab
    hm hφv hCconv hCcomp hCmono hCpos hlu
    (fun k y hy => by rw [hshift]; exact hslab k y hy)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      exact ⟨y, hy, by rw [hshift]; exact hyt⟩)
    hl hu haxis hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hbmem, hbvmem, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

/-- **`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_ne_zero` with the endpoints of
the needle exhibited in the limit body.**

The replay of that theorem — the height functional of
`ArlibCommunity.Foundations.Convex.exists_unitHeight_functional`, the shrinking slab of
`ArlibCommunity.Foundations.Convex.exists_slab_of_compact_chain`, then the previous lemma. -/
theorem exists_needle_mem_of_compact_chain (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hCcomp : ∀ k, IsCompact (C k))
    (hCconv : ∀ k, Convex ℝ (C k)) (hCmono : ∀ k, C (k + 1) ⊆ C k)
    (hCpos : ∀ k, 0 < volume (C k)) (hcol : Collinear ℝ (⋂ k, C k))
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ ⋂ k, C k) (hq : q ∈ ⋂ k, C k) (hpq : p ≠ q)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in C k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ y in C k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), b ∈ ⋂ k, C k ∧ b + v ∈ ⋂ k, C k ∧
      (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hIcomp : IsCompact (⋂ k, C k) :=
    (hCcomp 0).of_isClosed_subset (isClosed_iInter fun k => (hCcomp k).isClosed)
      (Set.iInter_subset _ 0)
  obtain ⟨a, φ, haS, hone, hIle⟩ := exists_unitHeight_functional hIcomp hp hq hpq
  obtain ⟨l, u, hl0, hu1, hslab, hspan, hl, hu⟩ :=
    exists_slab_of_compact_chain hCcomp hCconv hCmono haS hone hIle
  exact exists_needle_mem_of_collinear_shrinkingSlab hm hCconv hCcomp hCmono hCpos hl0 hu1
    hslab hspan hl hu hcol hg₁ hg₂ hM₁ hM₂ hzero hεpos hge

/-- **The needle of a chain in `EuclideanSpace`, with its two endpoints in the limit body.**

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_ne_zero` replayed over the
previous lemma.  The transport is the one of `ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationTransport`; the two
membership clauses cross it because the transported chain is literally the preimage of the
original one, so `⋂ k, F k = WithLp.toLp 2 ⁻¹' ⋂ k, C k`. -/
theorem exists_needle_mem_of_compact_chain_euclidean (hm : m ≠ 0)
    {C : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1)))} (hCcomp : ∀ k, IsCompact (C k))
    (hCconv : ∀ k, Convex ℝ (C k)) (hCmono : ∀ k, C (k + 1) ⊆ C k)
    (hCpos : ∀ k, 0 < volume (C k)) (hcol : Collinear ℝ (⋂ k, C k))
    {p q : EuclideanSpace ℝ (Fin (m + 1))} (hp : p ∈ ⋂ k, C k) (hq : q ∈ ⋂ k, C k) (hpq : p ≠ q)
    {g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in C k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ y in C k, g₂ y) :
    ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), b ∈ ⋂ k, C k ∧ b + v ∈ ⋂ k, C k ∧
      (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  classical
  set F : ℕ → Set (Fin (m + 1) → ℝ) :=
    fun k => (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' C k with hF
  have hvol : ∀ k, volume (F k) = volume (C k) := fun k =>
    volume_preimage_toLp ((hCcomp k).isClosed.measurableSet).nullMeasurableSet
  have hFcomp : ∀ k, IsCompact (F k) := fun k => isCompact_preimage_toLp_iff.mpr (hCcomp k)
  have hFconv : ∀ k, Convex ℝ (F k) := fun k => convex_preimage_toLp_iff.mpr (hCconv k)
  have hFmono : ∀ k, F (k + 1) ⊆ F k := fun k => Set.preimage_mono (hCmono k)
  have hFpos : ∀ k, 0 < volume (F k) := fun k => by rw [hvol k]; exact hCpos k
  have hiInter : (⋂ k, F k)
      = (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' ⋂ k, C k := by
    rw [Set.preimage_iInter]
  have hFcol : Collinear ℝ (⋂ k, F k) := by
    rw [hiInter]; exact collinear_preimage_toLp_iff.mpr hcol
  have hmemF : ∀ (x : EuclideanSpace ℝ (Fin (m + 1))), x ∈ (⋂ k, C k) →
      WithLp.ofLp x ∈ ⋂ k, F k := by
    intro x hx
    rw [hiInter]
    simpa using hx
  have hpq' : (WithLp.ofLp p : Fin (m + 1) → ℝ) ≠ WithLp.ofLp q :=
    fun h => hpq (WithLp.ofLp_injective 2 h)
  have hcont₁ : Continuous fun y : Fin (m + 1) → ℝ => g₁ (WithLp.toLp 2 y) :=
    hg₁.comp (PiLp.continuous_toLp 2 fun _ : Fin (m + 1) => ℝ)
  have hcont₂ : Continuous fun y : Fin (m + 1) → ℝ => g₂ (WithLp.toLp 2 y) :=
    hg₂.comp (PiLp.continuous_toLp 2 fun _ : Fin (m + 1) => ℝ)
  have hzeroF : ∀ k, (∫ y in F k, g₁ (WithLp.toLp 2 y)) = 0 := by
    intro k
    rw [hF, setIntegral_preimage_toLp g₁ (C k)]
    exact hzero k
  have hgeF : ∀ k, ε * (volume (F k)).toReal ≤ ∫ y in F k, g₂ (WithLp.toLp 2 y) := by
    intro k
    rw [hvol k, hF, setIntegral_preimage_toLp g₂ (C k)]
    exact hge k
  obtain ⟨b, v, W, hbmem, hbvmem, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needle_mem_of_compact_chain hm hFcomp hFconv hFmono hFpos
      hFcol (hmemF p hp) (hmemF q hq) hpq' hcont₁ hcont₂ (fun x => hM₁ _) (fun x => hM₂ _)
      hzeroF hεpos hgeF
  rw [hiInter] at hbmem hbvmem
  refine ⟨WithLp.toLp 2 b, WithLp.toLp 2 v, W, hbmem, ?_, hW0, hWsupp, hWint, hWc, ?_, ?_⟩
  · have : (WithLp.toLp 2 (b + v) : EuclideanSpace ℝ (Fin (m + 1)))
        = WithLp.toLp 2 b + WithLp.toLp 2 v := rfl
    rw [← this]
    exact hbvmem
  · rw [← hW₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2
  · refine lt_of_lt_of_le hW₂ (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2

end NeedleMem

/-! ### The degenerate case: a chain that collapses to a point -/

section Degenerate

variable {n : ℕ}

/-- **A chain collapsing to a point localises the integral of a continuous function at that
point.**

If the compact decreasing bodies `C k` have intersection contained in `{p}` then, for every
`η > 0`, some `C k` is contained in the set where `g` differs from `g p` by less than `η`, and
there the set integral of `g` is trapped between the two constants `g p ∓ η` times the volume.
This is Cantor's intersection theorem in the form "a neighbourhood of the intersection contains
some member of the chain" (`exists_subset_nhds_of_isCompact`). -/
theorem exists_setIntegral_between_of_iInter_subsingleton
    {C : ℕ → Set (EuclideanSpace ℝ (Fin n))} (hCcomp : ∀ k, IsCompact (C k))
    (hCmono : ∀ k, C (k + 1) ⊆ C k) {p : EuclideanSpace ℝ (Fin n)}
    (hsub : (⋂ k, C k) ⊆ {p}) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {η : ℝ} (hη : 0 < η) :
    ∃ k, (volume (C k)).toReal * (g p - η) ≤ (∫ y in C k, g y) ∧
      (∫ y in C k, g y) ≤ (volume (C k)).toReal * (g p + η) := by
  have hanti : Antitone C := antitone_nat_of_succ_le hCmono
  have hdir : Directed (· ⊇ ·) C := fun i j =>
    ⟨max i j, hanti (le_max_left i j), hanti (le_max_right i j)⟩
  have hUopen : IsOpen (g ⁻¹' Ioo (g p - η) (g p + η)) := isOpen_Ioo.preimage hg
  have hmem : ∀ x ∈ ⋂ k, C k, g ⁻¹' Ioo (g p - η) (g p + η) ∈ 𝓝 x := by
    intro x hx
    refine hUopen.mem_nhds ?_
    have hxp : x = p := hsub hx
    rw [hxp]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hCcomp
    (mem_nhdsSet_iff_forall.mpr hmem)
  have hms : MeasurableSet (C k) := (hCcomp k).measurableSet
  have hfin : volume (C k) ≠ ⊤ := (hCcomp k).measure_lt_top.ne
  have hint : IntegrableOn g (C k) volume := hg.continuousOn.integrableOn_compact (hCcomp k)
  refine ⟨k, ?_, ?_⟩
  · have hlow : (∫ _y in C k, (g p - η)) ≤ ∫ y in C k, g y :=
      setIntegral_mono_on (integrableOn_const hfin) hint hms fun x hx => (hk hx).1.le
    rwa [setIntegral_const, smul_eq_mul, Measure.real] at hlow
  · have hhigh : (∫ y in C k, g y) ≤ ∫ _y in C k, (g p + η) :=
      setIntegral_mono_on hint (integrableOn_const hfin) hms fun x hx => (hk hx).2.le
    rwa [setIntegral_const, smul_eq_mul, Measure.real] at hhigh

/-- **A chain collapsing to `p` with vanishing `g`-mass forces `g p = 0`.** -/
theorem eq_zero_of_iInter_subsingleton
    {C : ℕ → Set (EuclideanSpace ℝ (Fin n))} (hCcomp : ∀ k, IsCompact (C k))
    (hCmono : ∀ k, C (k + 1) ⊆ C k) (hCpos : ∀ k, 0 < volume (C k))
    {p : EuclideanSpace ℝ (Fin n)} (hsub : (⋂ k, C k) ⊆ {p})
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hzero : ∀ k, (∫ y in C k, g y) = 0) : g p = 0 := by
  have key : ∀ η : ℝ, 0 < η → |g p| ≤ η := by
    intro η hη
    obtain ⟨k, hlow, hhigh⟩ :=
      exists_setIntegral_between_of_iInter_subsingleton hCcomp hCmono hsub hg hη
    have hvol : 0 < (volume (C k)).toReal :=
      ENNReal.toReal_pos (hCpos k).ne' (hCcomp k).measure_lt_top.ne
    rw [hzero k] at hlow hhigh
    have h1 : (volume (C k)).toReal * (g p - η) ≤ (volume (C k)).toReal * 0 := by
      rw [mul_zero]; exact hlow
    have h2 : (volume (C k)).toReal * 0 ≤ (volume (C k)).toReal * (g p + η) := by
      rw [mul_zero]; exact hhigh
    have h1' := le_of_mul_le_mul_left h1 hvol
    have h2' := le_of_mul_le_mul_left h2 hvol
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  by_contra hne
  have hpos : 0 < |g p| := abs_pos.mpr hne
  have := key (|g p| / 2) (by linarith)
  linarith

/-- **A chain collapsing to `p` with `g`-mass at least `ε` times the volume forces `ε ≤ g p`.** -/
theorem le_of_iInter_subsingleton
    {C : ℕ → Set (EuclideanSpace ℝ (Fin n))} (hCcomp : ∀ k, IsCompact (C k))
    (hCmono : ∀ k, C (k + 1) ⊆ C k) (hCpos : ∀ k, 0 < volume (C k))
    {p : EuclideanSpace ℝ (Fin n)} (hsub : (⋂ k, C k) ⊆ {p})
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) {ε : ℝ}
    (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ y in C k, g y) : ε ≤ g p := by
  have key : ∀ η : ℝ, 0 < η → ε ≤ g p + η := by
    intro η hη
    obtain ⟨k, _, hhigh⟩ :=
      exists_setIntegral_between_of_iInter_subsingleton hCcomp hCmono hsub hg hη
    have hvol : 0 < (volume (C k)).toReal :=
      ENNReal.toReal_pos (hCpos k).ne' (hCcomp k).measure_lt_top.ne
    have h : (volume (C k)).toReal * ε ≤ (volume (C k)).toReal * (g p + η) := by
      have := hge k
      nlinarith [this, hhigh]
    exact le_of_mul_le_mul_left h hvol
  by_contra hcon
  have hlt : g p < ε := lt_of_not_ge hcon
  have := key ((ε - g p) / 2) (by linarith)
  linarith

end Degenerate

/-! ### From the stack's raw needle to the shape `hloc` asks for -/

section Shape

variable {n : ℕ}

/-- **The shape bridge.**

The localisation stack delivers a needle `(b, v)` with a profile `W` that is nonnegative,
supported in `[0,1]`, integrable, and concave *after* an `(n−1)`-st root and only on the **open**
interval; and it delivers the two needle masses as **full-line** integrals.  `hloc` asks for a
**log-concave** profile on the **closed** interval `Icc α β` and for **set** integrals over it,
plus the containment of the needle in `K`.

Both are supplied here.  The profile is `ArlibCommunity.Foundations.Convex.exists_concave_profile_of_localization` at `c = 1`
— the endpoint-extended `(n−1)`-st root `L`, concave on `Icc 0 1` — raised back to the power
`n − 1`; it is log-concave because a nonnegative concave function is
(`ArlibCommunity.Foundations.Convex.logConcaveOn_of_concaveOn`) and a nonnegative power of a log-concave function is
(`ArlibCommunity.Foundations.Convex.LogConcaveOn.rpow`).  It agrees with `W` off the two endpoints, which is a null set, so
every integral is unchanged.  The containment is convexity of `K` applied to
`b + r • v = (1 − r) • b + r • (b + v)`. -/
theorem exists_hloc_shape_of_needle (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) {b v : EuclideanSpace ℝ (Fin n)} (hb : b ∈ K) (hbv : b + v ∈ K)
    {W : ℝ → ℝ} (hW0 : ∀ t, 0 ≤ W t) (hWsupp : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0)
    (hWint : Integrable W)
    (hWc : ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))))
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (h₁ : (∫ t : ℝ, W t * g₁ (b + t • v)) = 0)
    (h₂ : 0 < ∫ t : ℝ, W t * g₂ (b + t • v)) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
      (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
      (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
      IntervalIntegrable D volume α β ∧
      (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
      0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t := by
  obtain ⟨L, hLnn, hLconc, hLpow, hLoff⟩ :=
    exists_concave_profile_of_localization hn one_pos hW0 hWc
  -- the profile `hloc` asks for
  set P : ℝ → ℝ := fun t => L t ^ (n - 1) with hPdef
  have hPnn : ∀ t, 0 ≤ P t := fun t => pow_nonneg (hLnn t) _
  have hPW : ∀ t : ℝ, t ≠ 0 → t ≠ 1 → P t = W t := by
    intro t ht0 ht1
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      have := hLpow t htIoo
      rwa [inv_one, one_mul] at this
    · rw [hPdef]
      simp only
      rw [hLoff t ht, hWsupp t ht]
  have hPaeW : P =ᵐ[volume] W := ae_eq_of_forall_ne_pair (x := 0) (y := 1) hPW
  -- the needle lies in `K`
  have hseg : ∀ r ∈ Set.Icc (0 : ℝ) 1, needleMap b v r ∈ K := by
    intro r hr
    have hmem := hKc hb hbv (by linarith [hr.2] : (0 : ℝ) ≤ 1 - r) hr.1 (by ring)
    have heq : (1 - r) • b + r • (b + v) = needleMap b v r := by
      simp only [needleMap, smul_add, sub_smul, one_smul]
      abel
    rwa [heq] at hmem
  -- log-concavity of the profile
  have hLC : LogConcaveOn (Set.Icc (0 : ℝ) 1) P := by
    have hbase : LogConcaveOn (Set.Icc (0 : ℝ) 1) L :=
      logConcaveOn_of_concaveOn hLconc fun x _ => hLnn x
    have hr := hbase.rpow (fun x _ => hLnn x) (Nat.cast_nonneg (n - 1))
    have heq : (fun t => L t ^ (((n - 1 : ℕ) : ℝ))) = fun t => L t ^ (n - 1) := by
      funext t
      exact Real.rpow_natCast (L t) (n - 1)
    rwa [heq] at hr
  -- integrability of the profile
  have hPint : Integrable P := hWint.congr hPaeW.symm
  -- the two needle masses, as set integrals over `Icc 0 1`
  have hmass : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      (∫ t in Set.Icc (0 : ℝ) 1, g (needleMap b v t) * P t) = ∫ t : ℝ, W t * g (b + t • v) := by
    intro g
    have hcongr : (∫ t in Set.Icc (0 : ℝ) 1, g (needleMap b v t) * P t)
        = ∫ t in Set.Icc (0 : ℝ) 1, W t * g (b + t • v) := by
      refine integral_congr_ae (ae_restrict_of_ae (ae_eq_of_forall_ne_pair (x := 0) (y := 1) ?_))
      intro t ht0 ht1
      rw [hPW t ht0 ht1]
      exact mul_comm _ _
    rw [hcongr]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro t ht
    rw [hWsupp t ht, zero_mul]
  exact ⟨b, v, 0, 1, P, zero_le_one, hseg, fun t _ => hPnn t, hLC,
    hPint.intervalIntegrable, by rw [hmass g₁]; exact h₁, by rw [hmass g₂]; exact h₂⟩

end Shape

/-! ### The Localization Lemma with the needle inside the body -/

section Hloc

variable {n : ℕ}

/-- **The Localization Lemma of Kannan–Lovász–Simonovits, one equality and one inequality, with
the needle inside the body.**

This is the `hloc` binder of `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer_of_localization`, copied
clause for clause, for a compact convex body of dimension `n ≥ 2`: for continuous `g₁, g₂` with
`∫_K g₁ = 0` and `0 < ∫_K g₂` there are a point `p`, a direction `e`, an interval `[α, β]` whose
needle `needleMap p e '' [α,β]` lies **in `K`**, and a nonnegative log-concave profile `D` on
`[α, β]`, integrable there, with `∫ g₁ ∘ needle · D = 0` and `0 < ∫ g₂ ∘ needle · D`.

The proof is the localisation chain of `ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact_ge` run at
`ε = (∫_K g₂)/(2 vol K)`, followed by a split on the limit body `⋂ k, C k`:

* if it has two distinct points, `ArlibCommunity.Foundations.Convex.exists_needle_mem_of_compact_chain_euclidean` returns a
  needle whose base and tip are points of it, hence of `K`, and `K` convex closes the segment
  into `K`;
* if it is a single point `p`, the chain's own invariants force `g₁ p = 0` and `ε ≤ g₂ p`
  (`ArlibCommunity.Foundations.Convex.eq_zero_of_iInter_subsingleton`, `ArlibCommunity.Foundations.Convex.le_of_iInter_subsingleton`), and the constant
  needle `needleMap p 0` on `[0,1]` with the constant profile `1` is the witness — `hloc` puts no
  nondegeneracy condition on `e`.

The integrands are first replaced by globally bounded, integrable ones agreeing with them on `K`
(`ArlibCommunity.Foundations.Convex.exists_bounded_integrable_eqOn_of_isCompact`); since the needle lies in `K`, that changes
neither hypothesis nor conclusion. -/
theorem hloc_needle_in_body (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K) :
    ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hKm : MeasurableSet K := hKcomp.measurableSet
  intro g₁ g₂ hg₁ hg₂ hzero hpos
  -- make the integrands globally bounded and integrable, without changing them on `K`
  obtain ⟨f₁, M₁, hf₁c, hf₁i, hf₁b, hf₁eq⟩ :=
    exists_bounded_integrable_eqOn_of_isCompact hKcomp hg₁
  obtain ⟨f₂, M₂, hf₂c, hf₂i, hf₂b, hf₂eq⟩ :=
    exists_bounded_integrable_eqOn_of_isCompact hKcomp hg₂
  have hM₁ : ∀ x, |f₁ x| ≤ max M₁ M₂ := fun x => le_trans (hf₁b x) (le_max_left _ _)
  have hM₂ : ∀ x, |f₂ x| ≤ max M₁ M₂ := fun x => le_trans (hf₂b x) (le_max_right _ _)
  have hzero' : (∫ x in K, f₁ x) = 0 := by
    rw [setIntegral_congr_fun hKm fun x hx => hf₁eq x hx]; exact hzero
  have hpos' : 0 < ∫ x in K, f₂ x := by
    rw [setIntegral_congr_fun hKm fun x hx => hf₂eq x hx]; exact hpos
  -- the chain, run at half the average of `f₂`
  have hvolpos : 0 < volume K := measure_pos_of_setIntegral_pos volume hpos'
  have hvolR : 0 < (volume K).toReal :=
    ENNReal.toReal_pos hvolpos.ne' hKcomp.measure_lt_top.ne
  set ε : ℝ := (∫ x in K, f₂ x) / (2 * (volume K).toReal) with hεdef
  have hεpos : 0 < ε := div_pos hpos' (by linarith)
  have hεeq : ε * (volume K).toReal = (∫ x in K, f₂ x) / 2 := by
    rw [hεdef]; field_simp
  have hεlt : ε * (volume K).toReal < ∫ x in K, f₂ x := by rw [hεeq]; linarith
  obtain ⟨C, hC0, hCmono, hCinv, hCcol⟩ :=
    exists_flat_cut_chain_collinear_compact_ge hn hf₁i hf₂i hKcomp hKc hzero' hεlt
  have hCcomp : ∀ k, IsCompact (C k) := fun k => (hCinv k).1
  have hCconv : ∀ k, Convex ℝ (C k) := fun k => (hCinv k).2.1
  have hCsub : ∀ k, C k ⊆ K := fun k => (hCinv k).2.2.1
  have hCpos : ∀ k, 0 < volume (C k) := fun k => (hCinv k).2.2.2.1
  have hCzero : ∀ k, (∫ y in C k, f₁ y) = 0 := fun k => (hCinv k).2.2.2.2.1
  have hCge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ y in C k, f₂ y := fun k => (hCinv k).2.2.2.2.2
  -- it suffices to produce the needle for the globalised integrands
  suffices hkey : ∃ (p e : EuclideanSpace ℝ (Fin (m + 1))) (α β : ℝ) (P : ℝ → ℝ), α ≤ β ∧
      (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
      (∀ t ∈ Set.Icc α β, 0 ≤ P t) ∧ LogConcaveOn (Set.Icc α β) P ∧
      IntervalIntegrable P volume α β ∧
      (∫ t in Set.Icc α β, f₁ (needleMap p e t) * P t) = 0 ∧
      0 < ∫ t in Set.Icc α β, f₂ (needleMap p e t) * P t by
    obtain ⟨p, e, α, β, P, hαβ, hseg, hP0, hlc, hint, hI₁, hI₂⟩ := hkey
    refine ⟨p, e, α, β, P, hαβ, hseg, hP0, hlc, hint, ?_, ?_⟩
    · have h : (∫ t in Set.Icc α β, g₁ (needleMap p e t) * P t)
          = ∫ t in Set.Icc α β, f₁ (needleMap p e t) * P t := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [hf₁eq _ (hseg t ht)]
      rw [h]; exact hI₁
    · have h : (∫ t in Set.Icc α β, g₂ (needleMap p e t) * P t)
          = ∫ t in Set.Icc α β, f₂ (needleMap p e t) * P t := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [hf₂eq _ (hseg t ht)]
      rw [h]; exact hI₂
  by_cases hdeg : ∃ p ∈ ⋂ k, C k, ∃ q ∈ ⋂ k, C k, p ≠ q
  · -- the limit body is a genuine segment: the stack's needle, with its endpoints in `K`
    obtain ⟨p, hp, q, hq, hpq⟩ := hdeg
    obtain ⟨b, v, W, hbmem, hbvmem, hW0, hWsupp, hWint, hWc, hI₁, hI₂⟩ :=
      exists_needle_mem_of_compact_chain_euclidean hm hCcomp hCconv hCmono hCpos hCcol hp hq hpq
        hf₁c hf₂c hM₁ hM₂ hCzero hεpos hCge
    have hbK : b ∈ K := hCsub 0 (Set.mem_iInter.mp hbmem 0)
    have hbvK : b + v ∈ K := hCsub 0 (Set.mem_iInter.mp hbvmem 0)
    have hexp : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by push_cast; ring
    refine exists_hloc_shape_of_needle hn hKc hbK hbvK hW0 hWsupp hWint ?_ hI₁ hI₂
    rw [hexp]
    exact hWc
  · -- the limit body is a single point: the constant needle there
    push Not at hdeg
    have hCne : ∀ k, (C k).Nonempty := by
      intro k
      rcases Set.eq_empty_or_nonempty (C k) with h | h
      · have hk := hCpos k
        rw [h, measure_empty] at hk
        exact absurd hk (lt_irrefl 0)
      · exact h
    obtain ⟨p, hp⟩ : (⋂ k, C k).Nonempty := by
      obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        C hCmono hCne (hCcomp 0) fun k => (hCcomp k).isClosed
      exact ⟨p, hp⟩
    have hsubs : (⋂ k, C k) ⊆ {p} := fun y hy => hdeg y hy p hp
    have hf₁p : f₁ p = 0 :=
      eq_zero_of_iInter_subsingleton hCcomp hCmono hCpos hsubs hf₁c hCzero
    have hf₂p : ε ≤ f₂ p := le_of_iInter_subsingleton hCcomp hCmono hCpos hsubs hf₂c hCge
    have hpK : p ∈ K := hCsub 0 (Set.mem_iInter.mp hp 0)
    have hneedle : ∀ t : ℝ, needleMap p (0 : EuclideanSpace ℝ (Fin (m + 1))) t = p := by
      intro t; simp [needleMap]
    have hvolIcc : (volume (Set.Icc (0 : ℝ) 1)).toReal = 1 := by
      rw [Real.volume_Icc]; norm_num
    have hconst : ∀ g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        (∫ t in Set.Icc (0 : ℝ) 1,
          g (needleMap p (0 : EuclideanSpace ℝ (Fin (m + 1))) t) * (1 : ℝ)) = g p := by
      intro g
      have heq : (∫ t in Set.Icc (0 : ℝ) 1,
            g (needleMap p (0 : EuclideanSpace ℝ (Fin (m + 1))) t) * (1 : ℝ))
          = ∫ _t in Set.Icc (0 : ℝ) 1, g p := by
        refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
        rw [mul_one, hneedle t]
      rw [heq, setIntegral_const, smul_eq_mul, Measure.real, hvolIcc, one_mul]
    refine ⟨p, 0, 0, 1, fun _ => 1, zero_le_one, ?_, fun t _ => zero_le_one,
      logConcaveOn_const (convex_Icc 0 1) zero_le_one, intervalIntegrable_const, ?_, ?_⟩
    · intro r _
      rw [hneedle r]
      exact hpK
    · rw [hconst f₁]; exact hf₁p
    · rw [hconst f₂]; linarith

end Hloc

/-! ### The conductance theorem with `hloc` discharged -/

section Conductance

variable {n : ℕ}


end Conductance

/-! ### Axiom audit -/

section AxiomCheck

#print axioms ArlibCommunity.Foundations.Convex.exists_bounded_integrable_eqOn_of_isCompact
#print axioms ArlibCommunity.Foundations.Convex.exists_axis_of_collinear_mem
#print axioms ArlibCommunity.Foundations.Convex.exists_needle_mem_of_collinear_shrinkingSlab
#print axioms ArlibCommunity.Foundations.Convex.exists_needle_mem_of_compact_chain
#print axioms ArlibCommunity.Foundations.Convex.exists_needle_mem_of_compact_chain_euclidean
#print axioms ArlibCommunity.Foundations.Convex.exists_setIntegral_between_of_iInter_subsingleton
#print axioms ArlibCommunity.Foundations.Convex.eq_zero_of_iInter_subsingleton
#print axioms ArlibCommunity.Foundations.Convex.le_of_iInter_subsingleton
#print axioms ArlibCommunity.Foundations.Convex.exists_hloc_shape_of_needle
#print axioms ArlibCommunity.Foundations.Convex.hloc_needle_in_body

end AxiomCheck

end ArlibCommunity.Foundations.Convex

end

section
/-!
# Product inequalities from one-equality localization

This file packages the elementary reduction from the one-equality/one-inequality localization
lemma to a strict four-function product inequality.  It is the bounded-body, continuous-integrand
step needed before the one-dimensional analysis in the Gaussian cooling argument.

The output profile is the arbitrary nonnegative log-concave profile supplied by
`ArlibCommunity.Foundations.Convex.hloc_needle_in_body`; no claim that it is exponential is made here.
-/

open MeasureTheory Set

open ArlibCommunity.Foundations.Convex

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

variable {n : ℕ}

/-- Two strictly positive integrals over a compact convex body remain strictly positive on one
common localization needle.  The equality fed to `hloc_needle_in_body` is
`B * q₁ - A * q₂`, where `A` and `B` are the two ambient integrals. -/
theorem exists_logConcave_profile_two_pos (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K)
    {q₁ q₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hq₁c : Continuous q₁)
    (hq₂c : Continuous q₂) (hq₁pos : 0 < ∫ x in K, q₁ x)
    (hq₂pos : 0 < ∫ x in K, q₂ x) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ), a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      0 < ∫ t in Icc a b, q₁ (needleMap p e t) * D t ∧
      0 < ∫ t in Icc a b, q₂ (needleMap p e t) * D t := by
  let A : ℝ := ∫ x in K, q₁ x
  let B : ℝ := ∫ x in K, q₂ x
  have hA : 0 < A := by simpa [A] using hq₁pos
  have hB : 0 < B := by simpa [B] using hq₂pos
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hq₁int : IntegrableOn q₁ K := hq₁c.continuousOn.integrableOn_compact hKcomp
  have hq₂int : IntegrableOn q₂ K := hq₂c.continuousOn.integrableOn_compact hKcomp
  have hzero : (∫ x in K, (B * q₁ x - A * q₂ x)) = 0 := by
    rw [integral_sub (hq₁int.const_mul B) (hq₂int.const_mul A),
      integral_const_mul, integral_const_mul]
    simp only [A, B]
    ring
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hzeroD, hq₁Dpos⟩ :=
    hloc_needle_in_body hn hKc hKcl hKb
      (fun x ↦ B * q₁ x - A * q₂ x) q₁
      ((continuous_const.mul hq₁c).sub (continuous_const.mul hq₂c)) hq₁c hzero hA
  have hDon : IntegrableOn D (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hDint
  have hneedle : Continuous (needleMap p e) := continuous_needleMap p e
  have hq₁Don : IntegrableOn (fun t ↦ q₁ (needleMap p e t) * D t) (Icc a b) :=
    hDon.continuousOn_mul (hq₁c.comp hneedle).continuousOn isCompact_Icc
  have hq₂Don : IntegrableOn (fun t ↦ q₂ (needleMap p e t) * D t) (Icc a b) :=
    hDon.continuousOn_mul (hq₂c.comp hneedle).continuousOn isCompact_Icc
  have hzeroD' :
      (∫ t in Icc a b,
        B * (q₁ (needleMap p e t) * D t) - A * (q₂ (needleMap p e t) * D t)) = 0 := by
    rw [← hzeroD]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _
    ring
  have hlinear :
      B * (∫ t in Icc a b, q₁ (needleMap p e t) * D t) -
          A * (∫ t in Icc a b, q₂ (needleMap p e t) * D t) = 0 := by
    rw [integral_sub (hq₁Don.const_mul B) (hq₂Don.const_mul A),
      integral_const_mul, integral_const_mul] at hzeroD'
    exact hzeroD'
  have hq₂Dpos : 0 < ∫ t in Icc a b, q₂ (needleMap p e t) * D t := by
    by_contra hnot
    have hnonpos : (∫ t in Icc a b, q₂ (needleMap p e t) * D t) ≤ 0 :=
      le_of_not_gt hnot
    have hleft : 0 < B * (∫ t in Icc a b, q₁ (needleMap p e t) * D t) :=
      mul_pos hB hq₁Dpos
    have hright : A * (∫ t in Icc a b, q₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA.le hnonpos
    linarith
  exact ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hq₁Dpos, hq₂Dpos⟩

/-- A strict failure of a four-function product inequality over a compact convex body localizes
to a strict failure against one common nonnegative log-concave one-dimensional profile.

The positivity assumptions on the second and third ambient integrals are exactly those needed to
choose a positive separator `r` with `A₄ / A₂ < r < A₁ / A₃`.  In the Gaussian cooling
application all four functions are positive Gaussian densities (one may take `f₃ = c * g₀`
and `f₄ = g₀`), so these assumptions are automatic once the body has positive volume. -/
theorem exists_logConcave_profile_product_lt (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K)
    {f₁ f₂ f₃ f₄ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₁c : Continuous f₁) (hf₂c : Continuous f₂) (hf₃c : Continuous f₃)
    (hf₄c : Continuous f₄) (hf₂0 : ∀ x, 0 ≤ f₂ x)
    (hf₃0 : ∀ x, 0 ≤ f₃ x) (hf₄0 : ∀ x, 0 ≤ f₄ x)
    (hf₂pos : 0 < ∫ x in K, f₂ x) (hf₃pos : 0 < ∫ x in K, f₃ x)
    (hfail : (∫ x in K, f₃ x) * (∫ x in K, f₄ x) <
      (∫ x in K, f₁ x) * (∫ x in K, f₂ x)) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ), a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₄ (needleMap p e t) * D t) <
        (∫ t in Icc a b, f₁ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by
  let A₁ : ℝ := ∫ x in K, f₁ x
  let A₂ : ℝ := ∫ x in K, f₂ x
  let A₃ : ℝ := ∫ x in K, f₃ x
  let A₄ : ℝ := ∫ x in K, f₄ x
  have hA₂0 : 0 < A₂ := by simpa [A₂] using hf₂pos
  have hA₃0 : 0 < A₃ := by simpa [A₃] using hf₃pos
  have hA₄0 : 0 ≤ A₄ := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x ↦ hf₄0 x)
  have hfail' : A₃ * A₄ < A₁ * A₂ := by simpa [A₁, A₂, A₃, A₄] using hfail
  have hA₁0 : 0 < A₁ := by
    by_contra hnot
    have hA₁nonpos : A₁ ≤ 0 := le_of_not_gt hnot
    have hright : A₁ * A₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA₁nonpos hA₂0.le
    have hleft : 0 ≤ A₃ * A₄ := mul_nonneg hA₃0.le hA₄0
    linarith
  let r : ℝ := (A₁ * A₂ + A₃ * A₄) / (2 * A₂ * A₃)
  have hr₁ : 0 < A₁ - r * A₃ := by
    dsimp only [r]
    field_simp [ne_of_gt hA₂0, ne_of_gt hA₃0]
    nlinarith
  have hr₂ : 0 < r * A₂ - A₄ := by
    dsimp only [r]
    field_simp [ne_of_gt hA₂0, ne_of_gt hA₃0]
    nlinarith
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hf₁int : IntegrableOn f₁ K := hf₁c.continuousOn.integrableOn_compact hKcomp
  have hf₂int : IntegrableOn f₂ K := hf₂c.continuousOn.integrableOn_compact hKcomp
  have hf₃int : IntegrableOn f₃ K := hf₃c.continuousOn.integrableOn_compact hKcomp
  have hf₄int : IntegrableOn f₄ K := hf₄c.continuousOn.integrableOn_compact hKcomp
  have hq₁pos : 0 < ∫ x in K, (f₁ x - r * f₃ x) := by
    rw [integral_sub hf₁int (hf₃int.const_mul r), integral_const_mul]
    simpa [A₁, A₃] using hr₁
  have hq₂pos : 0 < ∫ x in K, (r * f₂ x - f₄ x) := by
    rw [integral_sub (hf₂int.const_mul r) hf₄int, integral_const_mul]
    simpa [A₂, A₄] using hr₂
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hq₁Dpos, hq₂Dpos⟩ :=
    exists_logConcave_profile_two_pos (q₁ := fun x ↦ f₁ x - r * f₃ x)
      (q₂ := fun x ↦ r * f₂ x - f₄ x) hn hKc hKcl hKb
      (hf₁c.sub (continuous_const.mul hf₃c))
      ((continuous_const.mul hf₂c).sub hf₄c) hq₁pos hq₂pos
  have hDon : IntegrableOn D (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hDint
  have hneedle : Continuous (needleMap p e) := continuous_needleMap p e
  have hfDon : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f →
      IntegrableOn (fun t ↦ f (needleMap p e t) * D t) (Icc a b) := by
    intro f hfc
    exact hDon.continuousOn_mul (hfc.comp hneedle).continuousOn isCompact_Icc
  have hf₁Don := hfDon f₁ hf₁c
  have hf₂Don := hfDon f₂ hf₂c
  have hf₃Don := hfDon f₃ hf₃c
  have hf₄Don := hfDon f₄ hf₄c
  have hlocal₁ : 0 < (∫ t in Icc a b, f₁ (needleMap p e t) * D t) -
      r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) := by
    rw [show (fun t ↦ (f₁ (needleMap p e t) - r * f₃ (needleMap p e t)) * D t) =
        (fun t ↦ f₁ (needleMap p e t) * D t -
          r * (f₃ (needleMap p e t) * D t)) by funext t; ring,
      integral_sub hf₁Don (hf₃Don.const_mul r), integral_const_mul] at hq₁Dpos
    exact hq₁Dpos
  have hlocal₂ : 0 < r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) -
      (∫ t in Icc a b, f₄ (needleMap p e t) * D t) := by
    rw [show (fun t ↦ (r * f₂ (needleMap p e t) - f₄ (needleMap p e t)) * D t) =
        (fun t ↦ r * (f₂ (needleMap p e t) * D t) -
          f₄ (needleMap p e t) * D t) by funext t; ring,
      integral_sub (hf₂Don.const_mul r) hf₄Don, integral_const_mul] at hq₂Dpos
    exact hq₂Dpos
  have hI₂0 : 0 ≤ ∫ t in Icc a b, f₂ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₂0 _) (hD0 t ht)
  have hI₃0 : 0 ≤ ∫ t in Icc a b, f₃ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₃0 _) (hD0 t ht)
  have hI₄0 : 0 ≤ ∫ t in Icc a b, f₄ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₄0 _) (hD0 t ht)
  have hrpos : 0 < r := by
    by_contra hnot
    have hrnonpos : r ≤ 0 := le_of_not_gt hnot
    have : r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrnonpos hI₂0
    linarith
  have hI₂pos : 0 < ∫ t in Icc a b, f₂ (needleMap p e t) * D t := by
    by_contra hnot
    have hI₂nonpos : (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      le_of_not_gt hnot
    have : r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hrpos.le hI₂nonpos
    linarith
  refine ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, ?_⟩
  have hfirst :
      r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) <
        (∫ t in Icc a b, f₁ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by
    apply mul_lt_mul_of_pos_right _ hI₂pos
    linarith
  have hsecond :
      (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₄ (needleMap p e t) * D t) ≤
        (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t)) := by
    apply mul_le_mul_of_nonneg_left _ hI₃0
    linarith
  calc
    _ ≤ (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
        (r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t)) := hsecond
    _ = r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
        (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by ring
    _ < _ := hfirst

#print axioms exists_logConcave_profile_two_pos
#print axioms exists_logConcave_profile_product_lt

end ArlibCommunity.Foundations.Convex

end
