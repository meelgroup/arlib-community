/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAssembly
import ArlibCommunity.Foundations.Convex.Localization.Analysis.ConcaveSelection

section
/-!
# (G2c): the affine change of coordinates for the localisation needle

`ArlibCommunity.Foundations.Convex.needleIntegral_eq_zero_and_ge` (in `ArlibCommunity.Foundations.Convexity.LocalizationAssembly`) delivers the
two conclusions of the equality-refined Localization Lemma, but **in a fixed frame**: the needle
is the first coordinate axis of `ℝ^(m+1)`, the bodies sit in the slab `{x | x 0 ∈ [0,1]}`, and
the height of a point is literally its first coordinate.  The localisation chain of that same
file, on the other hand, produces bodies shrinking to an *arbitrary* segment.

This file removes that mismatch.  It is gap **(G2c)** of `ArlibCommunity.Foundations.Convexity.NeedleProfile`.

## Main results

* `ArlibCommunity.Foundations.Convex.exists_linearEquiv_frame` — a linear automorphism of `ℝ^(m+1)` carrying the first
  coordinate axis onto a prescribed line `ℝ ∙ v` and reading the first coordinate back off as a
  prescribed functional `φ` with `φ v = 1`.  Built from a basis of `ker φ`.
* `ArlibCommunity.Foundations.Convex.map_affine_addHaar`, `ArlibCommunity.Foundations.Convex.addHaar_preimage_affine`, `ArlibCommunity.Foundations.Convex.setIntegral_comp_affine` —
  the Haar-measure transport under `x ↦ a + L x`: a single constant Jacobian `|det L|⁻¹`.
* `ArlibCommunity.Foundations.Convex.concaveOn_limit_normalised_slice_profile` — the limit of the *normalised* slice profiles
  has a concave `1/m`-th power, so the `W` produced below is an honest needle profile.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos` — `ArlibCommunity.Foundations.Convex.needleIntegral_eq_zero_and_ge` with the
  profile hypotheses (G2a), (G2b) discharged from `ArlibCommunity.Foundations.Convexity.ConcaveSelection` and `W`
  quantified existentially.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine` — **(G2c)**: the same two conclusions for
  an arbitrary needle `t ↦ a + t • v` and arbitrary height functional `φ`.

The Jacobian never has to be split into a first-coordinate scaling times a transverse
determinant, contrary to what the (G2c) paragraph of `ArlibCommunity.Foundations.Convexity.NeedleProfile`
anticipated: the profile hypotheses are discharged *in the frame*, before the transport, so the
only thing the transport moves is a set integral and a volume, and the single constant cancels.
-/

open MeasureTheory Set Filter Module

open scoped ENNReal _root_.Topology


open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

/-! ### The frame: a linear equivalence carrying the first axis onto a prescribed direction -/

section Frame

variable {m : ℕ}

/-- **The needle frame.**

Given a direction `v` and a linear functional `φ` normalised by `φ v = 1`, there is a linear
automorphism `L` of `ℝ^(m+1)` which

* carries the first coordinate axis onto the line `ℝ ∙ v`, at unit speed in the parameter
  (`L (t, 0, …, 0) = t • v`), and
* reads the first coordinate back off as `φ` (`φ (L x) = x 0`).

Consequently `x ↦ a + L x` carries the slab `{x | x 0 ∈ [0,1]}` onto the slab
`{y | φ (y - a) ∈ [0,1]}` and the segment parameter `t` onto `a + t • v`.  The transverse part of
`L` is an arbitrary isomorphism of `{x | x 0 = 0}` onto `ker φ`, obtained from a basis of the
latter. -/
theorem exists_linearEquiv_frame {v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    (hφv : φ v = 1) :
    ∃ L : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ),
      (∀ x, φ (L x) = x 0) ∧ ∀ t : ℝ, L (Fin.cons t (0 : Fin m → ℝ)) = t • v := by
  classical
  -- `φ` is onto, so its kernel has dimension `m`.
  have hsurj : Function.Surjective φ := fun c => ⟨c • v, by rw [map_smul, hφv, smul_eq_mul, mul_one]⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrk : finrank ℝ (LinearMap.ker φ) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := Fin (m + 1) → ℝ) (V₂ := ℝ) φ
    rw [hrange] at h
    simp only [finrank_top, finrank_self, Module.finrank_pi, Fintype.card_fin] at h
    omega
  set Bk := Module.finBasisOfFinrankEq ℝ (LinearMap.ker φ) hrk with hBk
  set w : Fin m → (Fin (m + 1) → ℝ) := fun j => (Bk j : Fin (m + 1) → ℝ) with hw
  have hw0 : ∀ j, φ (w j) = 0 := fun j => (Bk j).2
  have hwli : LinearIndependent ℝ w :=
    Bk.linearIndependent.map' (LinearMap.ker φ).subtype (Submodule.ker_subtype _)
  -- the frame map sends the standard basis to `v, w 0, …, w (m-1)`
  set vw : Fin (m + 1) → (Fin (m + 1) → ℝ) := Fin.cons v w with hvw
  set T : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    ∑ i : Fin (m + 1), (LinearMap.proj i).smulRight (vw i) with hT
  have hTapp : ∀ x : Fin (m + 1) → ℝ, T x = ∑ i : Fin (m + 1), x i • (vw i) := by
    intro x
    rw [hT]
    simp [LinearMap.sum_apply]
  have hTphi : ∀ x, φ (T x) = x 0 := by
    intro x
    rw [hTapp x, map_sum, Fin.sum_univ_succ]
    simp only [hvw, Fin.cons_zero, Fin.cons_succ, map_smul, hφv, hw0, smul_eq_mul, mul_zero,
      mul_one]
    simp
  have hTcons : ∀ t : ℝ, T (Fin.cons t (0 : Fin m → ℝ)) = t • v := by
    intro t
    rw [hTapp, Fin.sum_univ_succ]
    simp [hvw]
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : x 0 = 0 := by rw [← hTphi x, hx, map_zero]
    have hsum : ∑ j : Fin m, x j.succ • w j = 0 := by
      have := hTapp x
      rw [hx] at this
      rw [Fin.sum_univ_succ] at this
      simp only [hvw, Fin.cons_zero, Fin.cons_succ, hx0, zero_smul, zero_add] at this
      exact this.symm
    have hcoef : ∀ j : Fin m, x j.succ = 0 :=
      fun j => by
        have := Fintype.linearIndependent_iff.mp hwli (fun j => x j.succ) hsum
        exact this j
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hx0
    · intro j; exact hcoef j
  exact ⟨LinearEquiv.ofInjectiveEndo T hTinj, hTphi, hTcons⟩

end Frame

/-! ### Transporting volume and integrals through an invertible affine self-map -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- An invertible affine self-map of a finite-dimensional real normed space is measurable. -/
theorem measurable_affineSelfMap (a : E) (L : E ≃ₗ[ℝ] E) : Measurable fun x => a + L x :=
  (measurable_const_add a).comp (L : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The preimage of a convex set under an invertible affine self-map is convex. -/
theorem convex_preimage_affine (a : E) (L : E ≃ₗ[ℝ] E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ ((fun x => a + L x) ⁻¹' s) := by
  intro x hx y hy p q hp hq hpq
  have hq' : q = 1 - p := by linarith
  subst hq'
  have hcomb : a + L (p • x + (1 - p) • y) = p • (a + L x) + (1 - p) • (a + L y) := by
    simp only [map_add, map_smul]
    module
  simpa only [Set.mem_preimage, hcomb] using hs hx hy hp hq (by ring)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The pushforward of a Haar measure under an invertible affine self-map** is the same measure
rescaled by the absolute value of the inverse determinant of the linear part.  The translation
contributes nothing, by translation invariance. -/
theorem map_affine_addHaar (a : E) (L : E ≃ₗ[ℝ] E) :
    Measure.map (fun x => a + L x) μ
      = ENNReal.ofReal |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • μ := by
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
  have hLm : Measurable ((L : E →ₗ[ℝ] E) : E → E) :=
    (L : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable
  have h1 : (fun x => a + L x) = (fun y : E => a + y) ∘ ((L : E →ₗ[ℝ] E) : E → E) := rfl
  rw [h1, ← Measure.map_map (measurable_const_add a) hLm,
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, Measure.map_smul (hf := by fun_prop),
    map_add_left_eq_self]

/-- The volume of the preimage of a set under an invertible affine self-map. -/
theorem addHaar_preimage_affine (a : E) (L : E ≃ₗ[ℝ] E) {s : Set E} (hs : MeasurableSet s) :
    μ ((fun x => a + L x) ⁻¹' s)
      = ENNReal.ofReal |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| * μ s := by
  rw [← Measure.map_apply (measurable_affineSelfMap a L) hs, map_affine_addHaar μ a L,
    Measure.smul_apply, smul_eq_mul]

/-- **Change of variables for a set integral under an invertible affine self-map.**  Both the
domain and the integrand are transported, so the only trace left is the constant Jacobian. -/
theorem setIntegral_comp_affine (a : E) (L : E ≃ₗ[ℝ] E) {s : Set E} (hs : MeasurableSet s)
    {f : E → ℝ} (hf : Measurable f) :
    ∫ x in (fun x => a + L x) ⁻¹' s, f (a + L x) ∂μ
      = |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • ∫ y in s, f y ∂μ := by
  have hA : Measurable fun x : E => a + L x := measurable_affineSelfMap a L
  have hind : Measurable (s.indicator f) := hf.indicator hs
  calc ∫ x in (fun x => a + L x) ⁻¹' s, f (a + L x) ∂μ
      = ∫ x, ((fun x => a + L x) ⁻¹' s).indicator (fun x => f (a + L x)) x ∂μ :=
        (integral_indicator (hA hs)).symm
    _ = ∫ x, s.indicator f (a + L x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact Set.indicator_comp_right (f := fun x : E => a + L x) (g := f) (s := s) (x := x)
    _ = ∫ y, s.indicator f y ∂Measure.map (fun x => a + L x) μ :=
        (integral_map hA.aemeasurable hind.stronglyMeasurable.aestronglyMeasurable).symm
    _ = |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • ∫ y, s.indicator f y ∂μ := by
        rw [map_affine_addHaar μ a L, integral_smul_measure,
          ENNReal.toReal_ofReal (abs_nonneg _)]
    _ = |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| • ∫ y in s, f y ∂μ := by rw [integral_indicator hs]

end Transport

/-! ### Coordinatewise bounds survive the frame change -/

section Bounds

variable {m : ℕ}

/-- If a set is norm-bounded then so is its preimage under an invertible affine self-map, in the
explicit coordinatewise shape that `ArlibCommunity.Foundations.Convex.volume_slice_ne_top_of_forall_abs_le` consumes. -/
theorem exists_forall_abs_le_preimage_affine (a : Fin (m + 1) → ℝ)
    (L : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ)) {S : Set (Fin (m + 1) → ℝ)} {R : ℝ}
    (hS : ∀ y ∈ S, ‖y‖ ≤ R) :
    ∃ R' : ℝ, ∀ x ∈ (fun x => a + L x) ⁻¹' S, ∀ i, |x i| ≤ R' := by
  set Lc : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (L.symm : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) with hLc
  refine ⟨‖Lc‖ * (R + ‖a‖), fun x hx i => ?_⟩
  have hy : ‖a + L x‖ ≤ R := hS _ hx
  have hxeq : Lc (a + L x - a) = x := by
    simp only [hLc, LinearMap.coe_toContinuousLinearMap', add_sub_cancel_left,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hnorm : ‖a + L x - a‖ ≤ R + ‖a‖ := by
    have : a + L x - a = (a + L x) + (-a) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by simpa using add_le_add hy (le_refl ‖a‖))
  calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x‖ := norm_le_pi_norm x i
    _ = ‖Lc (a + L x - a)‖ := by rw [hxeq]
    _ ≤ ‖Lc‖ * ‖a + L x - a‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * (R + ‖a‖) := by
        exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

end Bounds

/-! ### The two conclusions, with the profile hypotheses discharged -/

section InFrame

variable {m : ℕ}

/-- **The limit of the normalised slice profiles has a concave `1/m`-th power.**

`ArlibCommunity.Foundations.Convex.concaveOn_limit_slice_profile` applied with the renormalisation
`c k = (vol (C (ψ k)))^(-1/m)`, which turns the *sharp* profiles `vol (slice ·)^{1/m}` into the
`1/m`-th powers of the *normalised* profiles.  This is what makes the `W` produced below an
honest needle profile rather than an arbitrary function. -/
theorem concaveOn_limit_normalised_slice_profile (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, (slice (C k) t).Nonempty)
    {ψ : ℕ → ℕ} (_hψ : StrictMono ψ) {W : ℝ → ℝ}
    (hW : ∀ t : ℝ, Tendsto
      (fun k => (volume (slice (C (ψ k)) t)).toReal / (volume (C (ψ k))).toReal) atTop (𝓝 (W t))) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) := by
  have hVpos : ∀ k, (0 : ℝ) < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  refine (concaveOn_limit_slice_profile hm (K := fun k => C (ψ k))
    (fun k => hconv (ψ k)) (fun k => hCm (ψ k)) (convex_Ioo 0 1)
    (fun k t ht => hspan (ψ k) t (Ioo_subset_Icc_self ht)) (fun k t _ => hsfin (ψ k) t)
    (c := fun k => ((volume (C (ψ k))).toReal ^ (1 / (m : ℝ)))⁻¹)
    (fun k => inv_nonneg.mpr (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (G := fun t => W t ^ (1 / (m : ℝ))) (fun t _ => ?_)).1
  have heq : ∀ k : ℕ, ((volume (C (ψ k))).toReal ^ (1 / (m : ℝ)))⁻¹
      * (volume (slice (C (ψ k)) t)).toReal ^ (1 / (m : ℝ))
      = ((volume (slice (C (ψ k)) t)).toReal / (volume (C (ψ k))).toReal) ^ (1 / (m : ℝ)) := by
    intro k
    rw [Real.div_rpow ENNReal.toReal_nonneg (hVpos (ψ k)).le]
    ring
  simp only [heq]
  exact (hW t).rpow_const (Or.inr hmpos.le)

/-- **`ArlibCommunity.Foundations.Convex.needleIntegral_eq_zero_and_ge` with (G2a) and (G2b) discharged.**

The uniform bound `hB` and the pointwise profile convergence `hlim` of
`ArlibCommunity.Foundations.Convex.needleIntegral_eq_zero_and_ge` are supplied by `ArlibCommunity.Foundations.Convex.normalised_volume_slice_le` and
`ArlibCommunity.Foundations.Convex.exists_subseq_tendsto_normalised_slice_profile'` once the bodies are convex, slice-finite
and span the slab; the profile `W` becomes existentially quantified, which is exactly the shape
the Localization Lemma asserts.

Two further properties of the constructed profile are stated, because every downstream consumer
needs them and the existential would otherwise discard them:

* **support** — `W t = 0` off `[0,1]`, because each normalised slice profile vanishes there
  (the bodies lie in the slab) and `W` is their pointwise limit;
* **integrability** — `W` is measurable (a pointwise limit of the measurable profiles
  `ArlibCommunity.Foundations.Convex.measurable_volume_slice_toReal`), nonnegative, bounded by `2^(m+1)`
  (`ArlibCommunity.Foundations.Convex.normalised_volume_slice_le`) and supported in `[0,1]`, so
  `ArlibCommunity.Foundations.Convex.integrable_of_forall_notMem_Icc` applies.  This is not decorative: a Bochner integral
  of a non-integrable nonnegative function is `0`, not `+∞`. -/
theorem exists_needleIntegral_eq_zero_and_pos (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, (slice (C k) t).Nonempty)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    {δ : ℕ → ℝ}
    (hδ₁ : ∀ k, ∀ x ∈ C k, |g₁ x - g₁ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ₂ : ∀ k, ∀ x ∈ C k, |g₂ x - g₂ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hzero : ∀ k, (∫ x in C k, g₁ x) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ x in C k, g₂ x) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (Fin.cons t (0 : Fin m → ℝ))) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (Fin.cons t (0 : Fin m → ℝ)) := by
  obtain ⟨ψ, hψ, W, hW⟩ := exists_subseq_tendsto_normalised_slice_profile' hm hconv hCm hCfin
    hCpos hsfin hslab hspan
  have hVpos : ∀ k, (0 : ℝ) < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  have hW0 : ∀ t, 0 ≤ W t := fun t => ge_of_tendsto' (hW t)
    (fun k => div_nonneg ENNReal.toReal_nonneg (hVpos (ψ k)).le)
  -- the profiles vanish off the slab, hence so does their pointwise limit
  have hWsupp : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0 := by
    intro t ht
    have hconst : (fun k => (volume (slice (C (ψ k)) t)).toReal / (volume (C (ψ k))).toReal)
        = fun _ : ℕ => (0 : ℝ) := by
      funext k
      have hempty : slice (C (ψ k)) t = ∅ :=
        Set.eq_empty_of_forall_notMem fun y hy => ht (by simpa using hslab (ψ k) _ hy)
      rw [hempty, measure_empty, ENNReal.toReal_zero, zero_div]
    have h := hW t
    rw [hconst] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- `W` is measurable as a pointwise limit of measurable profiles
  have hWm : Measurable W := by
    refine measurable_of_tendsto_metrizable' atTop
      (f := fun k t => (volume (slice (C (ψ k)) t)).toReal / (volume (C (ψ k))).toReal)
      (fun k => (measurable_volume_slice_toReal (hCm (ψ k))).div_const _) ?_
    exact tendsto_pi_nhds.mpr hW
  have hWB : ∀ t, W t ≤ (2 : ℝ) ^ (m + 1) := fun t =>
    le_of_tendsto (hW t) (Filter.Eventually.of_forall fun k =>
      normalised_volume_slice_le hm (hconv (ψ k)) (hCm (ψ k)) (hCfin (ψ k)) (hCpos (ψ k))
        (hsfin (ψ k)) (hslab (ψ k)) (hspan (ψ k)) t)
  refine ⟨W, hW0, hWsupp, integrable_of_forall_notMem_Icc hWm hW0 hWB hWsupp,
    concaveOn_limit_normalised_slice_profile hm hconv hCm hCfin hCpos hsfin hspan hψ hW,
    needleIntegral_eq_zero_and_ge (C := fun k => C (ψ k)) (fun k => hCm (ψ k))
    (fun k => hCfin (ψ k)) (fun k => hCpos (ψ k)) (fun k => hslab (ψ k)) hg₁m hg₂m hM₁ hM₂
    (δ := fun k => δ (ψ k)) (fun k => hδ₁ (ψ k)) (fun k => hδ₂ (ψ k))
    (hδ0.comp hψ.tendsto_atTop) (B := 2 ^ (m + 1)) ?_ hW (fun k => hzero (ψ k)) hεpos
    (fun k => hge (ψ k))⟩
  exact fun k t => normalised_volume_slice_le hm (hconv (ψ k)) (hCm (ψ k)) (hCfin (ψ k))
    (hCpos (ψ k)) (hsfin (ψ k)) (hslab (ψ k)) (hspan (ψ k)) t

end InFrame

/-! ### (G2c): the needle in general position -/

section GeneralPosition

variable {m : ℕ}

/-- **(G2c), closed: the localisation needle in general position.**

`ArlibCommunity.Foundations.Convex.needleIntegral_eq_zero_and_ge` is stated in the frame in which the needle is the first
coordinate axis and the height of a point is its first coordinate.  Here the needle is the
arbitrary segment `t ↦ a + t • v`, the height of a point `y` is `φ (y - a)` for an arbitrary
linear functional `φ` normalised by `φ v = 1`, and the bodies `D k` are arbitrary convex bounded
bodies of the corresponding slab.  The two conclusions are the same.

The transport is by the frame of `ArlibCommunity.Foundations.Convex.exists_linearEquiv_frame` together with the change of
variables `ArlibCommunity.Foundations.Convex.setIntegral_comp_affine` and `ArlibCommunity.Foundations.Convex.addHaar_preimage_affine`: the Jacobian `d`
of the frame is a single positive constant, and it cancels out of both conclusions — out of the
first because the `g₁`-masses are `0`, out of the second because it multiplies the volume and the
`g₂`-mass by the same factor.  The transverse determinant never has to be separated from the
first-coordinate scaling, because the profile hypotheses have already been discharged in the
frame by `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos`. -/
theorem exists_needleIntegral_eq_zero_and_pos_affine (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDm : ∀ k, MeasurableSet (D k)) (hDfin : ∀ k, volume (D k) ≠ ⊤)
    (hDpos : ∀ k, 0 < volume (D k)) (hDbdd : ∀ k, ∃ R : ℝ, ∀ y ∈ D k, ‖y‖ ≤ R)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
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
  have hheight : ∀ x : Fin (m + 1) → ℝ, φ (a + L x - a) = x 0 := by
    intro x; rw [add_sub_cancel_left]; exact hLφ x
  have hAcons : ∀ t : ℝ, a + L (Fin.cons t (0 : Fin m → ℝ)) = a + t • v := by
    intro t; rw [hLcons t]
  have haxis : ∀ x : Fin (m + 1) → ℝ,
      a + L (Fin.cons (x 0) (0 : Fin m → ℝ)) = a + φ (a + L x - a) • v := by
    intro x; rw [hAcons, hheight]
  -- the Jacobian of the frame
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
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ := exists_needleIntegral_eq_zero_and_pos hm
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
    (hg₁m.comp hAm) (hg₂m.comp hAm) (fun x => hM₁ _) (fun x => hM₂ _)
    (fun k x hx => by rw [haxis x]; exact hδ₁ k _ hx)
    (fun k x hx => by rw [haxis x]; exact hδ₂ k _ hx) hδ0
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₁m, hzero k, smul_zero])
    hεpos
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₂m, smul_eq_mul, hvolR k]
      nlinarith [mul_le_mul_of_nonneg_left (hge k) hdpos.le])
  exact ⟨W, hW0, hWsupp, hWint, hWc, by simpa only [hAcons] using hW₁,
    by simpa only [hAcons] using hW₂⟩

end GeneralPosition

end ArlibCommunity.Foundations.Convex

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.exists_linearEquiv_frame
#print axioms ArlibCommunity.Foundations.Convex.measurable_affineSelfMap
#print axioms ArlibCommunity.Foundations.Convex.map_affine_addHaar
#print axioms ArlibCommunity.Foundations.Convex.addHaar_preimage_affine
#print axioms ArlibCommunity.Foundations.Convex.setIntegral_comp_affine
#print axioms ArlibCommunity.Foundations.Convex.convex_preimage_affine
#print axioms ArlibCommunity.Foundations.Convex.exists_forall_abs_le_preimage_affine
#print axioms ArlibCommunity.Foundations.Convex.concaveOn_limit_normalised_slice_profile
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine

end

section
/-!
# The transverse-thinness bridge for the localisation needle

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine` consumes a *transverse-thinness modulus*:
a sequence `δ k → 0` with

`∀ y ∈ D k, |g y - g (a + φ (y - a) • v)| ≤ δ k`,

i.e. the integrand varies by `o(1)` between a point of the `k`-th body of the localisation chain
and the point of the needle axis at the same height.  The localisation chain of
`ArlibCommunity.Foundations.Convexity.LocalizationAssembly` delivers instead the *geometric* statement that the
intersection `⋂ k, C k` is collinear (`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear`).

This file bridges the two, and does so with **no metric decay hypothesis at all**: the only extra
input is that the bodies are compact.  The mechanism is the finite-intersection property, not a
diameter estimate — `ArlibCommunity.Foundations.Convex.le_diam_of_sign_separated` shows no diameter decay is available, and
none is used.

## Main results

* `ArlibCommunity.Foundations.Convex.eventually_subset_of_antitone_isCompact` — a decreasing sequence of compact sets is
  eventually contained in **any** open neighbourhood of its intersection.
* `ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus` — hence, if every point of `⋂ k, C k` lies on the
  needle axis and `g` is bounded continuous, the explicit moduli
  `δ k = sSup {|g y - g (axis y)| : y ∈ C k}` tend to `0`.
* `ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus_pair` — the same modulus can be taken to work for two
  integrands at once, which is what the equality form of the Localization Lemma needs.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact` — **(G2c) and the thinness bridge
  combined**: the needle conclusions in general position, with the thinness hypothesis replaced
  by compactness of the bodies together with `⋂ k, D k ⊆ axis`.  The profile `W` it delivers is
  nonnegative with a **concave** `1/m`-th power, i.e. `W = ℓ^m` for a concave `ℓ` — the concave
  form of the Localization Lemma, which `ArlibCommunity.Foundations.Convex.logConcaveOn_concaveNeedleDensity` shows is what
  every downstream consumer of a needle in this repository actually asks for.

## What is *not* proved here

Nothing shows that the bodies produced by `ArlibCommunity.Foundations.Convex.exists_flat_cut_chain` are closed — they are
built by cutting with half-spaces, one of whose two sides is open.  Replacing that construction
by one with closed sides (or intersecting each body with its closure and checking the invariants
survive) is the remaining step, and it is a statement about the *chain*, not about the limit
passage.
-/

open MeasureTheory Set Filter _root_.Topology


open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

/-! ### A decreasing sequence of compacts is eventually inside any neighbourhood of its limit -/

section Compact

/-- **A decreasing sequence of compact sets is eventually contained in any open set containing
its intersection.**

This is the finite-intersection property: the closed sets `C k \ U` decrease to `∅` inside the
compact `C 0`, so finitely many of them already have empty intersection, and the largest index
occurring works.  No metric, and in particular no decay of diameters, is involved. -/
theorem eventually_subset_of_antitone_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : ℕ → Set X} (hC : ∀ k, IsCompact (C k)) (hmono : ∀ k, C (k + 1) ⊆ C k)
    {U : Set X} (hU : IsOpen U) (hsub : (⋂ k, C k) ⊆ U) :
    ∃ N : ℕ, ∀ k, N ≤ k → C k ⊆ U := by
  classical
  have hanti : Antitone C := antitone_nat_of_succ_le hmono
  have hclosed : ∀ k, IsClosed (C k ∩ Uᶜ) := fun k =>
    (hC k).isClosed.inter hU.isClosed_compl
  have hempty : C 0 ∩ ⋂ k, (C k ∩ Uᶜ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hxI : x ∈ ⋂ k, C k := Set.mem_iInter.mpr fun k =>
      (Set.mem_iInter.mp hx.2 k).1
    exact (Set.mem_iInter.mp hx.2 0).2 (hsub hxI)
  obtain ⟨u, hu⟩ := (hC 0).elim_finite_subfamily_closed (fun k => C k ∩ Uᶜ) hclosed (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  refine ⟨u.sup id, fun k hk => ?_⟩
  intro x hx
  by_contra hxU
  refine Set.eq_empty_iff_forall_notMem.mp (Set.disjoint_iff_inter_eq_empty.mp hu) x ⟨hanti (Nat.zero_le k) hx, ?_⟩
  refine Set.mem_iInter₂.mpr fun i hi => ?_
  have hik : i ≤ k := le_trans (Finset.le_sup (f := id) hi) hk
  exact ⟨hanti hik hx, hxU⟩

end Compact

/-! ### The thinness modulus -/

section Modulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The point of the needle axis `t ↦ a + t • v` at the same height as `y`, the height being
measured by `φ`.  This is a plain formula, written out here only to keep statements short. -/
private theorem continuous_axisPoint (a v : E) (φ : E →ₗ[ℝ] ℝ) :
    Continuous fun y : E => a + φ (y - a) • v :=
  continuous_const.add
    (((φ.continuous_of_finiteDimensional).comp
      (continuous_id.sub continuous_const)).smul continuous_const)

/-- **The transverse-thinness bridge.**

If the bodies `C k` are compact and decreasing, every point of their intersection lies on the
needle axis, and `g` is bounded and continuous, then the exact moduli

`δ k = sSup {|g y - g (a + φ (y - a) • v)| : y ∈ C k}`

dominate the transverse oscillation of `g` on `C k` and tend to `0`. -/
theorem exists_tendsto_transverse_modulus {C : ℕ → Set E} (hC : ∀ k, IsCompact (C k))
    (hmono : ∀ k, C (k + 1) ⊆ C k) {a v : E} {φ : E →ₗ[ℝ] ℝ}
    (haxis : ∀ y ∈ ⋂ k, C k, y = a + φ (y - a) • v)
    {g : E → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ k, ∀ y ∈ C k, |g y - g (a + φ (y - a) • v)| ≤ δ k := by
  classical
  set h : E → ℝ := fun y => |g y - g (a + φ (y - a) • v)| with hhdef
  have hhc : Continuous h := (hg.sub (hg.comp (continuous_axisPoint a v φ))).abs
  have hh0 : ∀ y, 0 ≤ h y := fun _ => abs_nonneg _
  have habs : ∀ p q : ℝ, |p - q| ≤ |p| + |q| := fun p q => by
    simpa [sub_eq_add_neg] using abs_add_le p (-q)
  have hbdd : ∀ k, BddAbove (h '' C k) := by
    intro k
    refine ⟨2 * M, ?_⟩
    rintro z ⟨y, _, rfl⟩
    exact le_trans (habs _ _) (by linarith [hM y, hM (a + φ (y - a) • v)])
  set δ : ℕ → ℝ := fun k => sSup (h '' C k) with hδdef
  have hle : ∀ k, ∀ y ∈ C k, h y ≤ δ k := fun k y hy =>
    le_csSup (hbdd k) ⟨y, hy, rfl⟩
  have hδ0 : ∀ k, 0 ≤ δ k := by
    intro k
    rcases (C k).eq_empty_or_nonempty with he | ⟨y, hy⟩
    · rw [hδdef]; simp [he]
    · exact le_trans (hh0 y) (hle k y hy)
  refine ⟨δ, ?_, hle⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsub : (⋂ k, C k) ⊆ h ⁻¹' Iio (ε / 2) := by
    intro y hy
    have hy' : y = a + φ (y - a) • v := haxis y hy
    have hgy : g (a + φ (y - a) • v) = g y := by rw [← hy']
    have hz : h y = 0 := by
      show |g y - g (a + φ (y - a) • v)| = 0
      rw [hgy, sub_self, abs_zero]
    simp only [Set.mem_preimage, hz, Set.mem_Iio]
    linarith
  obtain ⟨N, hN⟩ := eventually_subset_of_antitone_isCompact hC hmono
    (isOpen_Iio.preimage hhc) hsub
  refine ⟨N, fun k hk => ?_⟩
  have hub : δ k ≤ ε / 2 := by
    rcases (C k).eq_empty_or_nonempty with he | ⟨y0, hy0⟩
    · rw [hδdef]; simp only [he, Set.image_empty, Real.sSup_empty]; linarith
    · refine csSup_le ⟨h y0, ⟨y0, hy0, rfl⟩⟩ ?_
      rintro z ⟨y, hy, rfl⟩
      exact le_of_lt (hN k hk hy)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδ0 k)]
  linarith

/-- **A single thinness modulus for two integrands**, as the equality form of the Localization
Lemma needs: take the pointwise maximum of the two moduli. -/
theorem exists_tendsto_transverse_modulus_pair {C : ℕ → Set E} (hC : ∀ k, IsCompact (C k))
    (hmono : ∀ k, C (k + 1) ⊆ C k) {a v : E} {φ : E →ₗ[ℝ] ℝ}
    (haxis : ∀ y ∈ ⋂ k, C k, y = a + φ (y - a) • v)
    {g₁ g₂ : E → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {M : ℝ}
    (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      (∀ k, ∀ y ∈ C k, |g₁ y - g₁ (a + φ (y - a) • v)| ≤ δ k) ∧
      ∀ k, ∀ y ∈ C k, |g₂ y - g₂ (a + φ (y - a) • v)| ≤ δ k := by
  obtain ⟨δ₁, hδ₁lim, hδ₁⟩ := exists_tendsto_transverse_modulus hC hmono haxis hg₁ hM₁
  obtain ⟨δ₂, hδ₂lim, hδ₂⟩ := exists_tendsto_transverse_modulus hC hmono haxis hg₂ hM₂
  refine ⟨fun k => max (δ₁ k) (δ₂ k), ?_, fun k y hy => le_max_of_le_left (hδ₁ k y hy),
    fun k y hy => le_max_of_le_right (hδ₂ k y hy)⟩
  simpa using hδ₁lim.max hδ₂lim

end Modulus

/-! ### (G2c) and the thinness bridge, combined -/

section Combined

variable {m : ℕ}

/-- **The localisation needle from a compact chain shrinking to the axis.**

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine` with its transverse-thinness hypothesis
discharged by `ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus_pair`.  What is left to ask of the chain
is purely geometric: the bodies are convex, compact, decreasing, of positive volume, sit in and
span the slab `{y | φ (y - a) ∈ [0,1]}`, and **every point of their intersection lies on the
needle axis** — which is exactly what a collinear limit body positioned along `t ↦ a + t • v`
provides.  No diameter decay and no modulus of continuity are required. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
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
  refine exists_needleIntegral_eq_zero_and_pos_affine hm hφv hDconv
    (fun k => (hDcomp k).isClosed.measurableSet) (fun k => (hDcomp k).measure_lt_top.ne)
    hDpos (fun k => ?_) hslab hspan hg₁.measurable hg₂.measurable hM₁ hM₂ hδ₁ hδ₂ hδ0
    hzero hεpos hge
  exact isBounded_iff_forall_norm_le.mp (hDcomp k).isBounded

/-- **Non-vacuity of `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact`.**

Every hypothesis of that theorem is met simultaneously by the shrinking boxes
`D k = [0,1] × [0, 1/(k+1)]^m`, the axis `t ↦ t • e₀`, the height functional `φ = proj 0`, and
`g₁ = 0`, `g₂ = 1`, `ε = 1`.  The boxes are convex, compact, decreasing, of *positive* volume,
they sit in and span the slab, and their intersection is exactly the segment `[0, e₀]` — so the
`haxis` hypothesis, which is the whole content of the thinness bridge, is genuinely satisfiable
with nondegenerate bodies.  The limit profile that comes out is nonzero, since its integral is
positive. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_box (hm : m ≠ 0) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      0 < ∫ t : ℝ, W t * (1 : ℝ) := by
  classical
  set r : ℕ → Fin (m + 1) → ℝ := fun k i => if i = 0 then 1 else 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k i, 0 < r k i := by
    intro k i
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      positivity
  set D : ℕ → Set (Fin (m + 1) → ℝ) := fun k => univ.pi fun i => Icc (0 : ℝ) (r k i) with hD
  have hDcomp : ∀ k, IsCompact (D k) := fun k => isCompact_univ_pi fun _ => isCompact_Icc
  have hDconv : ∀ k, Convex ℝ (D k) := fun k => convex_pi fun _ _ => convex_Icc _ _
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    refine Set.Icc_subset_Icc_right ?_ hyi
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      exact one_div_le_one_div_of_le h1 h2
  have hvol : ∀ k, volume (D k) = ∏ i : Fin (m + 1), ENNReal.ofReal (r k i) := by
    intro k
    rw [hD]
    simp only [volume_pi_pi, Real.volume_Icc, sub_zero]
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    rw [hvol k, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (ENNReal.ofReal_pos.mpr (hrpos k i)).ne'
  set φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0 with hφ
  set v : Fin (m + 1) → ℝ := Pi.single 0 1 with hv
  have hφv : φ v = 1 := by rw [hφ, hv]; simp
  have hslab : ∀ k, ∀ y ∈ D k, φ (y - 0) ∈ Icc (0 : ℝ) 1 := by
    intro k y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [hr] at h0
    simpa [hφ] using h0
  have hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - 0) = t := by
    intro k t ht
    refine ⟨fun i => if i = 0 then t else 0, Set.mem_univ_pi.mpr fun i => ?_, by simp [hφ]⟩
    by_cases hi : i = 0
    · simp only [hi, if_true, hr]
      simpa using ht
    · simp only [hi, if_false]
      exact ⟨le_rfl, (hrpos k i).le⟩
  have haxis : ∀ y ∈ ⋂ k, D k, y = 0 + φ (y - 0) • v := by
    intro y hy
    have hy' : ∀ k, y ∈ D k := fun k => Set.mem_iInter.mp hy k
    have hzero : ∀ i : Fin (m + 1), i ≠ 0 → y i = 0 := by
      intro i hi
      refine le_antisymm ?_ ((Set.mem_univ_pi.mp (hy' 0) i).1)
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hcon
      have := (Set.mem_univ_pi.mp (hy' n) i).2
      rw [hr] at this
      simp only [hi, if_false] at this
      linarith
    funext i
    by_cases hi : i = 0
    · simp [hi, hφ, hv]
    · simp [hi, hv, hzero i hi, hφ]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact hm hφv hDconv
    hDcomp hDmono hDpos hslab hspan haxis (g₁ := fun _ => (0 : ℝ)) (g₂ := fun _ => (1 : ℝ))
    continuous_const continuous_const (M := 1) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun k => integral_zero _ _) (ε := 1) one_pos
    (fun k => by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, one_mul])
  exact ⟨W, hW0, hWsupp, hWint, hWc, hW₂⟩

end Combined

end ArlibCommunity.Foundations.Convex

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.eventually_subset_of_antitone_isCompact
#print axioms ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus
#print axioms ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus_pair
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_box

end
