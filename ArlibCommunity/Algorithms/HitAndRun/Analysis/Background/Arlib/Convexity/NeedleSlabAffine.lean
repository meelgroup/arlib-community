/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationClosed
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleSlab

/-!
# The localisation needle in general position, from a chain whose slab shrinks

`Arlib.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab`
(`Arlib.Convexity.NeedleSlab`) is stated in the frame in which the needle is the first coordinate
axis.  This file carries it to general position and hands it the geometry that
`Arlib.exists_flat_cut_chain_collinear_compact` actually produces, closing item **(E)** of
`Arlib.Convexity.LocalizationAssembly`.

The rigidity that item (E) records is that
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` asks all bodies to lie in *and* span one
fixed slab, which forces the height range to be constant along the chain.  Here the `k`-th body
lies in and spans its **own** slab `[l k, u k]`, with `l k ≤ 0`, `1 ≤ u k`, `l k → 0`, `u k → 1`:
the slabs *shrink*, from outside, onto the slab of the limit needle.  For a decreasing chain of
compact convex bodies `l k` and `u k` are simply the minimum and maximum of the height functional
on `D k`, so both hypotheses are automatic once the limit segment has been normalised to unit
height.

## Main results

* `Arlib.exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab` — (G2c) for a shrinking
  slab: an arbitrary needle `t ↦ a + t • v` and an arbitrary height functional `φ` with `φ v = 1`.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab` — the transverse-thinness
  hypothesis discharged from compactness, via `Arlib.exists_tendsto_transverse_modulus_pair`.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` — the `haxis`
  hypothesis replaced by `Collinear ℝ (⋂ k, D k)`, which is exactly what the localisation chain
  delivers.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_shrinking_box` — **the acid test**: the genuinely
  shrinking boxes `D k = [-1/(k+1), 1 + 1/(k+1)] × [-1/(k+1), 1/(k+1)]^m`, which shrink in
  *every* direction including along the needle, satisfy every hypothesis at once.  The fixed-slab
  form cannot accept them: their height range is `[-1/(k+1), 1 + 1/(k+1)]`, which is not constant
  in `k`, so no normalisation makes `hslab` and `hspan` hold simultaneously for a fixed slab.

## What is still missing

The chain of `Arlib.exists_flat_cut_chain_collinear_compact` lives in `EuclideanSpace ℝ (Fin n)`
whereas the needle theorems live in `Fin (m+1) → ℝ`; a measure-preserving transport between the
two is **not** supplied here, so the end-to-end composition is stated in `Fin (m+1) → ℝ`.  That
is a purely technical mismatch, unchanged by this file.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### (G2c) for a shrinking slab -/

section GeneralPosition

variable {m : ℕ}

/-- **The localisation needle in general position, from a chain whose slab shrinks.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_affine` with the fixed slab `{y | φ (y - a) ∈ [0,1]}`
replaced by the moving slabs `{y | φ (y - a) ∈ [l k, u k]}`, subject only to `l k → 0` and
`u k → 1`.  The transport is the frame of `Arlib.exists_linearEquiv_frame` together with
`Arlib.setIntegral_comp_affine` and `Arlib.addHaar_preimage_affine`, exactly as in the fixed-slab
form: the Jacobian is a single positive constant and cancels out of both conclusions.

The integrands are asked to be *continuous*, not merely measurable: the point of the needle axis
at rescaled height `s` moves with `k`, and continuity is what makes the integrand follow it. -/
theorem exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDm : ∀ k, MeasurableSet (D k)) (hDfin : ∀ k, volume (D k) ≠ ⊤)
    (hDpos : ∀ k, 0 < volume (D k)) (hDbdd : ∀ k, ∃ R : ℝ, ∀ y ∈ D k, ‖y‖ ≤ R)
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    {δ : ℕ → ℝ}
    (hδ₁ : ∀ k, ∀ y ∈ D k, |g₁ y - g₁ (a + φ (y - a) • v)| ≤ δ k)
    (hδ₂ : ∀ k, ∀ y ∈ D k, |g₂ y - g₂ (a + φ (y - a) • v)| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (a + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (a + t • v) := by
  obtain ⟨L, hLφ, hLcons⟩ := exists_linearEquiv_frame (m := m) (v := v) (φ := φ) hφv
  have hAm : Measurable fun x : Fin (m + 1) → ℝ => a + L x := measurable_affineSelfMap a L
  have hAc : Continuous fun x : Fin (m + 1) → ℝ => a + L x :=
    continuous_const.add
      (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)).continuous_of_finiteDimensional
  have hheight : ∀ x : Fin (m + 1) → ℝ, φ (a + L x - a) = x 0 := by
    intro x; rw [add_sub_cancel_left]; exact hLφ x
  have hAcons : ∀ t : ℝ, a + L (Fin.cons t (0 : Fin m → ℝ)) = a + t • v := by
    intro t; rw [hLcons t]
  have haxis : ∀ x : Fin (m + 1) → ℝ,
      a + L (Fin.cons (x 0) (0 : Fin m → ℝ)) = a + φ (a + L x - a) • v := by
    intro x; rw [hAcons, hheight]
  have hdet : LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' L).ne_zero
  have hdpos : 0 < |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹| :=
    abs_pos.mpr (inv_ne_zero hdet)
  have hvol : ∀ k, volume ((fun x => a + L x) ⁻¹' D k)
      = ENNReal.ofReal |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹|
        * volume (D k) := fun k => addHaar_preimage_affine volume a L (hDm k)
  have hvolR : ∀ k, (volume ((fun x => a + L x) ⁻¹' D k)).toReal
      = |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹|
        * (volume (D k)).toReal := by
    intro k; rw [hvol k, ENNReal.toReal_mul, ENNReal.toReal_ofReal hdpos.le]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_shrinkingSlab hm
    (C := fun k => (fun x => a + L x) ⁻¹' D k)
    (g₁ := fun x => g₁ (a + L x)) (g₂ := fun x => g₂ (a + L x))
    (fun k => convex_preimage_affine a L (hDconv k)) (fun k => hAm (hDm k))
    (fun k => by rw [hvol k]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDfin k))
    (fun k => by
      rw [hvol k]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hdpos).ne' (hDpos k).ne')
    (fun k t => by
      obtain ⟨R, hR⟩ := hDbdd k
      obtain ⟨R', hR'⟩ := exists_forall_abs_le_preimage_affine a L hR
      exact volume_slice_ne_top_of_forall_abs_le hR' t)
    hlu
    (fun k x hx => by rw [← hheight x]; exact hslab k _ hx)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      have hAx : a + L (L.symm (y - a)) = y := by
        rw [LinearEquiv.apply_symm_apply]; abel
      have hx0 : (L.symm (y - a) : Fin (m + 1) → ℝ) 0 = t := by
        rw [← hheight (L.symm (y - a)), hAx, hyt]
      refine ⟨Fin.tail (L.symm (y - a) : Fin (m + 1) → ℝ), ?_⟩
      show a + L (Fin.cons t (Fin.tail (L.symm (y - a) : Fin (m + 1) → ℝ))) ∈ D k
      rw [← hx0, Fin.cons_self_tail, hAx]
      exact hy)
    hl hu (hg₁.comp hAc) (hg₂.comp hAc) (fun x => hM₁ _) (fun x => hM₂ _)
    (fun k x hx => by rw [haxis x]; exact hδ₁ k _ hx)
    (fun k x hx => by rw [haxis x]; exact hδ₂ k _ hx) hδ0
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₁.measurable, hzero k, smul_zero])
    hεpos
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₂.measurable, smul_eq_mul, hvolR k]
      nlinarith [mul_le_mul_of_nonneg_left (hge k) hdpos.le])
  exact ⟨W, hW0, hWsupp, hWint, hWc, by simpa only [hAcons] using hW₁,
    by simpa only [hAcons] using hW₂⟩

end GeneralPosition

/-! ### The thinness bridge, for a shrinking slab -/

section Compact

variable {m : ℕ}

/-- **The localisation needle from a *compact* chain whose slab shrinks to the needle's.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` with the fixed slab replaced by the
moving one.  The transverse-thinness moduli are still supplied by
`Arlib.exists_tendsto_transverse_modulus_pair`, which uses only compactness and the
finite-intersection property — no metric decay, and nothing about the slab. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    (haxis : ∀ y ∈ ⋂ k, D k, y = a + φ (y - a) • v)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (a + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (a + t • v) := by
  obtain ⟨δ, hδ0, hδ₁, hδ₂⟩ :=
    exists_tendsto_transverse_modulus_pair hDcomp hDmono haxis hg₁ hg₂ hM₁ hM₂
  refine exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab hm hφv hDconv
    (fun k => (hDcomp k).isClosed.measurableSet) (fun k => (hDcomp k).measure_lt_top.ne)
    hDpos (fun k => ?_) hlu hslab hspan hl hu hg₁ hg₂ hM₁ hM₂ hδ₁ hδ₂ hδ0 hzero hεpos hge
  exact isBounded_iff_forall_norm_le.mp (hDcomp k).isBounded

/-- **The localisation needle from a compact chain with a *collinear* limit body and a shrinking
slab.**

The `haxis` hypothesis of the previous theorem — "every point of `⋂ k, D k` lies on the
prescribed needle axis" — replaced by the purely geometric `Collinear ℝ (⋂ k, D k)`, which is what
`Arlib.exists_flat_cut_chain_collinear_compact` produces.  The axis is *produced*, not assumed:
`Arlib.exists_axis_of_collinear` reads its base point and direction off the points of the
intersection at heights `0` and `1`, whose existence is Cantor's intersection theorem
(`Arlib.exists_mem_iInter_height`) applied to the slab `[0,1]`, which is contained in every
`[l k, u k]` by `hl0` and `hu1`.

This is the shape a *shrinking* chain can satisfy: the bodies are only asked to lie in and span
the slab they actually occupy, and the sole normalisation is that the limit segment has unit
height. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    {l u : ℕ → ℝ} (hl0 : ∀ k, l k ≤ 0) (hu1 : ∀ k, 1 ≤ u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    (hcol : Collinear ℝ (⋂ k, D k))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), φ v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hlu : ∀ k, l k < u k := fun k => lt_of_le_of_lt (hl0 k) (lt_of_lt_of_le one_pos (hu1 k))
  have hsub : ∀ k, Icc (0 : ℝ) 1 ⊆ Icc (l k) (u k) := fun k =>
    Icc_subset_Icc (hl0 k) (hu1 k)
  have hspan01 : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t :=
    fun k t ht => hspan k t (hsub k ht)
  obtain ⟨b, v, hb, hφv, haxis⟩ := exists_axis_of_collinear hDcomp hDmono hspan01 hcol
  have hshift : ∀ y : Fin (m + 1) → ℝ, φ (y - b) = φ (y - a) := by
    intro y; rw [map_sub, map_sub, hb]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab
    hm hφv hDconv hDcomp hDmono hDpos hlu
    (fun k y hy => by rw [hshift]; exact hslab k y hy)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      exact ⟨y, hy, by rw [hshift]; exact hyt⟩)
    hl hu haxis hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

end Compact

/-! ### The acid test: a chain that shrinks in *every* direction -/

section ShrinkingBox

variable {m : ℕ}

/-- **Non-vacuity, with a genuinely shrinking chain.**

Every hypothesis of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` is
met simultaneously by the boxes

`D k = [-1/(k+1), 1 + 1/(k+1)] × [-1/(k+1), 1/(k+1)]^m`,

which shrink in **every** direction — including along the needle — and whose intersection is the
unit segment `[0,1] × {0}^m`, hence collinear.  They are convex, compact, decreasing and of
positive volume; the `k`-th one lies in and spans its own slab `[l k, u k]` with
`l k = -1/(k+1) ≤ 0`, `u k = 1 + 1/(k+1) ≥ 1`, `l k → 0`, `u k → 1`.

This is what the fixed-slab form `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`
cannot accept: for these boxes the height range `[-1/(k+1), 1 + 1/(k+1)]` genuinely varies with
`k`, so no affine normalisation of the height makes `hslab` and `hspan` hold for one fixed slab
at every stage — which is exactly the obstruction recorded as item (E).  The witness of
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_box` has to keep the extent along the
needle constant at `[0,1]` for precisely this reason.

The profile that comes out is nonzero, since its integral is positive. -/
theorem exists_needleIntegral_eq_zero_and_pos_shrinking_box (hm : m ≠ 0) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ),
      (LinearMap.proj (0 : Fin (m + 1)) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      0 < ∫ t : ℝ, W t * (1 : ℝ) := by
  classical
  set ρ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hρ
  have hρpos : ∀ k, 0 < ρ k := fun k => by rw [hρ]; positivity
  have hρanti : ∀ k, ρ (k + 1) ≤ ρ k := by
    intro k
    rw [hρ]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact one_div_le_one_div_of_le h1 h2
  set l : ℕ → ℝ := fun k => -ρ k with hldef
  set u : ℕ → ℝ := fun k => 1 + ρ k with hudef
  set D : ℕ → Set (Fin (m + 1) → ℝ) := fun k =>
    univ.pi fun i => if i = 0 then Icc (l k) (u k) else Icc (-ρ k) (ρ k) with hD
  have hDcomp : ∀ k, IsCompact (D k) := by
    intro k
    refine isCompact_univ_pi fun i => ?_
    by_cases hi : i = 0
    · rw [if_pos hi]; exact isCompact_Icc
    · rw [if_neg hi]; exact isCompact_Icc
  have hDconv : ∀ k, Convex ℝ (D k) := by
    intro k
    refine convex_pi fun i _ => ?_
    by_cases hi : i = 0
    · rw [if_pos hi]; exact convex_Icc _ _
    · rw [if_neg hi]; exact convex_Icc _ _
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    have hr := hρanti k
    by_cases hi : i = 0
    · rw [if_pos hi] at hyi ⊢
      exact Set.Icc_subset_Icc (by rw [hldef]; simp only; linarith)
        (by rw [hudef]; simp only; linarith) hyi
    · rw [if_neg hi] at hyi ⊢
      exact Set.Icc_subset_Icc (by linarith) (by linarith) hyi
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    have hr := hρpos k
    rw [hD]
    simp only
    rw [volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    by_cases hi : i = 0
    · rw [if_pos hi, Real.volume_Icc]
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      rw [hldef, hudef]; simp only; linarith
    · rw [if_neg hi, Real.volume_Icc]
      exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  set φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0 with hφ
  have hslab : ∀ k, ∀ y ∈ D k, φ (y - 0) ∈ Icc (l k) (u k) := by
    intro k y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [if_pos rfl] at h0
    simpa [hφ] using h0
  have hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - 0) = t := by
    intro k t ht
    refine ⟨fun i => if i = 0 then t else 0, Set.mem_univ_pi.mpr fun i => ?_, by simp [hφ]⟩
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi]; exact ht
    · rw [if_neg hi, if_neg hi]
      exact ⟨by linarith [hρpos k], (hρpos k).le⟩
  have hρ0 : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto l atTop (𝓝 0) := by simpa [hldef] using hρ0.neg
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [hudef] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add hρ0
  have hl0 : ∀ k, l k ≤ 0 := fun k => by rw [hldef]; simp only; linarith [hρpos k]
  have hu1 : ∀ k, 1 ≤ u k := fun k => by rw [hudef]; simp only; linarith [hρpos k]
  -- the intersection is the unit segment, hence collinear
  have hzeroCoord : ∀ y ∈ ⋂ k, D k, ∀ i : Fin (m + 1), i ≠ 0 → y i = 0 := by
    intro y hy i hi
    have hy' : ∀ k, y ∈ D k := fun k => Set.mem_iInter.mp hy k
    by_contra hne
    have habs : 0 < |y i| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs
    have hmem := Set.mem_univ_pi.mp (hy' n) i
    rw [if_neg hi] at hmem
    have : |y i| ≤ ρ n := abs_le.mpr ⟨hmem.1, hmem.2⟩
    rw [hρ] at this
    simp only at this
    linarith
  have hcol : Collinear ℝ (⋂ k, D k) := by
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨0, Pi.single 0 1, fun y hy => ⟨y 0, ?_⟩⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi, hzeroCoord y hy i hi]
  obtain ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, -, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab hm (a := 0) (φ := φ)
      hDconv hDcomp hDmono hDpos hl0 hu1 hslab hspan hl hu hcol
      (g₁ := fun _ => (0 : ℝ)) (g₂ := fun _ => (1 : ℝ)) continuous_const continuous_const
      (M := 1) (fun _ => by norm_num) (fun _ => by norm_num)
      (fun k => integral_zero _ _) (ε := 1) one_pos
      (fun k => by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, one_mul])
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₂⟩

end ShrinkingBox

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_shrinking_box
