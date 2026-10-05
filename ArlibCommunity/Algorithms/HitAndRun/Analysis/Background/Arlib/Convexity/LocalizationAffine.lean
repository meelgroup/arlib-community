/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationAssembly
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.ConcaveSelection

/-!
# (G2c): the affine change of coordinates for the localisation needle

`Arlib.needleIntegral_eq_zero_and_ge` (in `Arlib.Convexity.LocalizationAssembly`) delivers the
two conclusions of the equality-refined Localization Lemma, but **in a fixed frame**: the needle
is the first coordinate axis of `ℝ^(m+1)`, the bodies sit in the slab `{x | x 0 ∈ [0,1]}`, and
the height of a point is literally its first coordinate.  The localisation chain of that same
file, on the other hand, produces bodies shrinking to an *arbitrary* segment.

This file removes that mismatch.  It is gap **(G2c)** of `Arlib.Convexity.NeedleProfile`.

## Main results

* `Arlib.exists_linearEquiv_frame` — a linear automorphism of `ℝ^(m+1)` carrying the first
  coordinate axis onto a prescribed line `ℝ ∙ v` and reading the first coordinate back off as a
  prescribed functional `φ` with `φ v = 1`.  Built from a basis of `ker φ`.
* `Arlib.map_affine_addHaar`, `Arlib.addHaar_preimage_affine`, `Arlib.setIntegral_comp_affine` —
  the Haar-measure transport under `x ↦ a + L x`: a single constant Jacobian `|det L|⁻¹`.
* `Arlib.concaveOn_limit_normalised_slice_profile` — the limit of the *normalised* slice profiles
  has a concave `1/m`-th power, so the `W` produced below is an honest needle profile.
* `Arlib.exists_needleIntegral_eq_zero_and_pos` — `Arlib.needleIntegral_eq_zero_and_ge` with the
  profile hypotheses (G2a), (G2b) discharged from `Arlib.Convexity.ConcaveSelection` and `W`
  quantified existentially.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_affine` — **(G2c)**: the same two conclusions for
  an arbitrary needle `t ↦ a + t • v` and arbitrary height functional `φ`.

The Jacobian never has to be split into a first-coordinate scaling times a transverse
determinant, contrary to what the (G2c) paragraph of `Arlib.Convexity.NeedleProfile`
anticipated: the profile hypotheses are discharged *in the frame*, before the transport, so the
only thing the transport moves is a set integral and a volume, and the single constant cancels.
-/

open MeasureTheory Set Filter Module

open scoped ENNReal Topology

namespace Arlib

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
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, Measure.map_smul,
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
explicit coordinatewise shape that `Arlib.volume_slice_ne_top_of_forall_abs_le` consumes. -/
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

`Arlib.concaveOn_limit_slice_profile` applied with the renormalisation
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

/-- **`Arlib.needleIntegral_eq_zero_and_ge` with (G2a) and (G2b) discharged.**

The uniform bound `hB` and the pointwise profile convergence `hlim` of
`Arlib.needleIntegral_eq_zero_and_ge` are supplied by `Arlib.normalised_volume_slice_le` and
`Arlib.exists_subseq_tendsto_normalised_slice_profile'` once the bodies are convex, slice-finite
and span the slab; the profile `W` becomes existentially quantified, which is exactly the shape
the Localization Lemma asserts.

Two further properties of the constructed profile are stated, because every downstream consumer
needs them and the existential would otherwise discard them:

* **support** — `W t = 0` off `[0,1]`, because each normalised slice profile vanishes there
  (the bodies lie in the slab) and `W` is their pointwise limit;
* **integrability** — `W` is measurable (a pointwise limit of the measurable profiles
  `Arlib.measurable_volume_slice_toReal`), nonnegative, bounded by `2^(m+1)`
  (`Arlib.normalised_volume_slice_le`) and supported in `[0,1]`, so
  `Arlib.integrable_of_forall_notMem_Icc` applies.  This is not decorative: a Bochner integral
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

`Arlib.needleIntegral_eq_zero_and_ge` is stated in the frame in which the needle is the first
coordinate axis and the height of a point is its first coordinate.  Here the needle is the
arbitrary segment `t ↦ a + t • v`, the height of a point `y` is `φ (y - a)` for an arbitrary
linear functional `φ` normalised by `φ v = 1`, and the bodies `D k` are arbitrary convex bounded
bodies of the corresponding slab.  The two conclusions are the same.

The transport is by the frame of `Arlib.exists_linearEquiv_frame` together with the change of
variables `Arlib.setIntegral_comp_affine` and `Arlib.addHaar_preimage_affine`: the Jacobian `d`
of the frame is a single positive constant, and it cancels out of both conclusions — out of the
first because the `g₁`-masses are `0`, out of the second because it multiplies the volume and the
`g₂`-mass by the same factor.  The transverse determinant never has to be separated from the
first-coordinate scaling, because the profile hypotheses have already been discharged in the
frame by `Arlib.exists_needleIntegral_eq_zero_and_pos`. -/
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

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.exists_linearEquiv_frame
#print axioms Arlib.measurable_affineSelfMap
#print axioms Arlib.map_affine_addHaar
#print axioms Arlib.addHaar_preimage_affine
#print axioms Arlib.setIntegral_comp_affine
#print axioms Arlib.convex_preimage_affine
#print axioms Arlib.exists_forall_abs_le_preimage_affine
#print axioms Arlib.concaveOn_limit_normalised_slice_profile
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_affine
