/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRun
import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# The sphere measure under isometries, and the law of one coordinate

Two things are built here, both about `MeasureTheory.Measure.toSphere` — Mathlib's
unnormalised surface measure on the unit sphere — and both recorded as *missing Mathlib API*
elsewhere in this repository.

## 1. Invariance

* `Arlib.MarkovChains.toSphere_map_sphereMap` — **`toSphere` is invariant under every linear
  isometry equivalence.**  This is the rotation invariance of the surface measure.  The proof
  is short once one uses the *right* Mathlib characterisation:
  `MeasureTheory.Measure.toSphere_apply' : μ.toSphere s = n * μ (Ioo 0 1 • ↑'' s)` describes
  `toSphere s` as the volume of the open cone on `s`, and cones commute with linear maps, so
  the statement reduces to `LinearIsometryEquiv.measurePreserving`.
* `Arlib.MarkovChains.toSphere_map_neg` — **`(volume.toSphere).map Neg.neg = volume.toSphere`**,
  the antipodal case, obtained from the previous one with `LinearIsometryEquiv.neg`.  This is
  the single piece of API that `Arlib/Convexity/HitAndRunStep.lean` records as absent from
  Mathlib v4.32 and works around by reflecting the *body* instead of the sphere.
  `toSphere_preimage_neg` and `lintegral_toSphere_neg` are the set and integral forms;
  `unifSphere_preimage_neg` is the normalised version.

## 2. The law of `⟪θ, w⟫`

* `Arlib.MarkovChains.map_inner_toSphere_congr` — **the law of a single coordinate is
  well-defined**: the pushforward of `toSphere` under `θ ↦ ⟪θ, w⟫` is the *same* measure on
  `ℝ` for every unit vector `w`.  This is what makes "the distribution of one coordinate of a
  uniform point of `Sⁿ⁻¹`" a meaningful object.  `toSphere_setOf_inner_congr` and
  `lintegral_inner_toSphere_congr` are the set and integral forms.
* `Arlib.MarkovChains.toSphere_abs_inner_gt` — **the symmetric cap is exactly twice the
  one-sided cap**: `σ{|⟪θ,w⟫| > c} = 2·σ{⟪θ,w⟫ > c}` for `c ≥ 0`, from the antipodal
  invariance.
* `Arlib.MarkovChains.finrank_mul_lintegral_inner_sq` — **the second moment**:
  `n · ∫ ⟪θ,w⟫² dσ = σ(Sⁿ⁻¹)`.  So `n^{-1/2}` is *exactly* the root-mean-square value of
  `⟪θ, w⟫`.
* `Arlib.MarkovChains.toSphere_univ_le_finrank_mul_cap` and
  `Arlib.MarkovChains.finrank_mul_toSphere_cap_lt_le` — **the two pigeonhole bounds**.  Since
  the `n` coordinates of a unit vector have squares summing to `1`, at least one of them is
  `≥ 1/n` and at most `n − 1` of them are `> 1/n`.  With the rotation invariance above this
  gives, for the cap of the paper,

      1/n  ≤  σ{θ : √n·|⟪θ,w⟫| ≥ |w|}    and    σ{θ : √n·|⟪θ,w⟫| > |w|}  ≤  1 − 1/n.

## 3. The cap hypothesis of Lemma 4.1

`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean` threads an unproved hypothesis `hcap`,
a bound on `hitAndRun K u {x : ‖x−u‖·‖u−v‖ < √n·|⟪x−u, u−v⟫|}`.  Two theorems here address it:

* `Arlib.MarkovChains.hitAndRun_le_unifSphere_of_cone` — **a cone event of one step is bounded
  by the uniform measure of its directions.**  The set above is a double cone about `u` that
  misses `u`, so the walk contributes nothing along a good direction and at most the chord's
  own mass along a bad one.  This turns `hcap` from a statement about the walk into a
  statement about the sphere, with no convexity and no hypothesis on `K`.
* `Arlib.MarkovChains.hitAndRun_almostOrthogonal_le` — that reduction, specialised.
* `Arlib.MarkovChains.hitAndRun_almostOrthogonal_le_one_sub_inv` — **`hcap` discharged with
  `q₂ = 1 − 1/n`**, unconditionally.  At `n = 2` this is exactly the `1/2` that
  `Arlib.MarkovChains.tvLe_hitAndRun_lemma41` needs.  (The `_of_half` corollary that once
  recorded this figure was **deleted** in `868a1c9`'s follow-up: correcting the paper's false
  `hchord` raised the budget to `1/8 + q₂ + 1/2`, which is vacuous at `q₂ = 1/2`.)

## What is *not* here, and why

The sharp cap constant is **not** proved, and nothing here claims it.  The true value of
`σ{θ : √n·|⟪θ,w⟫| ≥ |w|}` is `1/2` at `n = 2` and decreases to `2(1 − Φ(1)) = 0.31731…`; the
constant `1 − 1/500` of Lovász–Vempala's Lemma 4.1 needs `q₂ ≤ 0.3233` (see the arithmetic in
the module docstring of `HitAndRunOverlap.lean`), i.e. a bound within about `2%` of sharp,
uniformly in `n`.

`finrank_mul_lintegral_inner_sq` is the obstruction in one line: the threshold is the
root-mean-square value, so the event is a *central* one.  Chebyshev, Chernoff and every
moment bound are trivial at the mean, and the two pigeonhole bounds `1/n` and `1 − 1/n` are
the best that the constraint `∑ᵢ ⟪θ, eᵢ⟫² = 1` alone can give (both are attained by vectors
satisfying only that constraint).  Getting the true constant requires the actual density
`(1 − t²)^{(n−3)/2}` of `⟪θ, w⟫` together with an explicit, uniform-in-`n` estimate of its
tail at `t = n^{-1/2}` — a quantitative central limit theorem for the Beta distribution.
Mathlib v4.32 has neither the density nor the estimate, and neither is a small addition.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Module Set
open scoped ENNReal Pointwise RealInnerProductSpace

section Invariance

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F]

/-- A linear isometry equivalence, restricted to the unit spheres. -/
def sphereMap (f : E ≃ₗᵢ[ℝ] F) (θ : sphere (0 : E) 1) : sphere (0 : F) 1 :=
  ⟨f θ, by
    rw [mem_sphere_zero_iff_norm, f.norm_map]
    exact mem_sphere_zero_iff_norm.1 θ.2⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
@[simp] theorem coe_sphereMap (f : E ≃ₗᵢ[ℝ] F) (θ : sphere (0 : E) 1) :
    ((sphereMap f θ : sphere (0 : F) 1) : F) = f (θ : E) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem measurable_sphereMap (f : E ≃ₗᵢ[ℝ] F) : Measurable (sphereMap f) :=
  (Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _).measurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The underlying set of the preimage of `s` under `sphereMap f` is the preimage of the
underlying set of `s` under `f`. -/
theorem image_coe_preimage_sphereMap (f : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    ((↑) '' (sphereMap f ⁻¹' s) : Set E) = f ⁻¹' ((↑) '' s) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨sphereMap f θ, hθ, rfl⟩
  · rintro ⟨η, hη, hx⟩
    have hxs : x ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, ← f.norm_map x, ← hx]
      exact mem_sphere_zero_iff_norm.1 η.2
    refine ⟨⟨x, hxs⟩, ?_, rfl⟩
    have : sphereMap f ⟨x, hxs⟩ = η := Subtype.ext hx.symm
    show sphereMap f ⟨x, hxs⟩ ∈ s
    rwa [this]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- A linear equivalence commutes with dilation by a set of scalars. -/
theorem smul_set_preimage_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] F) (S : Set ℝ) (A : Set F) :
    S • (f ⁻¹' A) = f ⁻¹' (S • A) := by
  ext x
  simp only [Set.mem_smul, Set.mem_preimage]
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, hr, f y, hy, by rw [← f.map_smul]⟩
  · rintro ⟨r, hr, a, ha, hx⟩
    refine ⟨r, hr, f.symm a, by simpa using ha, ?_⟩
    apply f.injective
    rw [f.map_smul, f.apply_symm_apply, hx]

/-- **`Measure.toSphere` is invariant under every linear isometry equivalence.**

This is the rotation invariance of the (unnormalised) surface measure on the unit sphere.
Mathlib v4.32 does not have it; it follows from `MeasureTheory.Measure.toSphere_apply'`,
which describes `toSphere` as the volume of the open cone `Ioo 0 1 • s`, together with
`LinearIsometryEquiv.measurePreserving`. -/
theorem toSphere_map_sphereMap (f : E ≃ₗᵢ[ℝ] F) :
    (volume : Measure E).toSphere.map (sphereMap f) = (volume : Measure F).toSphere := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_sphereMap f) hs,
    Measure.toSphere_apply' _ (hs.preimage (measurable_sphereMap f)),
    Measure.toSphere_apply' _ hs, image_coe_preimage_sphereMap,
    smul_set_preimage_linearIsometryEquiv]
  have hdim : finrank ℝ E = finrank ℝ F := f.toLinearEquiv.finrank_eq
  have hvol : (volume : Measure E) (f ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)))
      = (volume : Measure F) (Ioo (0 : ℝ) 1 • ((↑) '' s)) :=
    f.measurePreserving.measure_preimage_emb f.toMeasurableEquiv.measurableEmbedding _
  rw [hdim, hvol]

/-- **`Measure.toSphere` is invariant under the antipodal map `θ ↦ -θ`.**

This is the single piece of Mathlib API that `Arlib/Convexity/HitAndRunStep.lean` records as
missing. -/
theorem toSphere_map_neg :
    (volume : Measure E).toSphere.map (Neg.neg : sphere (0 : E) 1 → sphere (0 : E) 1)
      = (volume : Measure E).toSphere := by
  have h : (sphereMap (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E))
      = (Neg.neg : sphere (0 : E) 1 → sphere (0 : E) 1) := by
    funext θ
    exact Subtype.ext rfl
  rw [← h]
  exact toSphere_map_sphereMap _

omit [FiniteDimensional ℝ E] in
theorem measurableSet_sphere_setOf_inner {w : E} {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B} :=
  hB.preimage ((continuous_inner.comp
    (continuous_subtype_val.prodMk continuous_const)).measurable)

/-- `toSphere` is invariant under the antipodal map, set version. -/
theorem toSphere_preimage_neg {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    (volume : Measure E).toSphere (Neg.neg ⁻¹' s) = (volume : Measure E).toSphere s := by
  conv_rhs => rw [← toSphere_map_neg (E := E)]
  rw [Measure.map_apply (by fun_prop) hs]

/-- `toSphere` is invariant under the antipodal map, `lintegral` version. -/
theorem lintegral_toSphere_neg {g : sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ θ, g (-θ) ∂((volume : Measure E).toSphere)
      = ∫⁻ θ, g θ ∂((volume : Measure E).toSphere) := by
  conv_rhs => rw [← toSphere_map_neg (E := E)]
  rw [lintegral_map hg (by fun_prop)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The incoming half-ray directions are the antipodes of the outgoing ones.

Together with `toSphere_preimage_neg` this replaces the body-reflection workaround of
`Arlib.toSphere_badDir_neg_le`. -/
theorem setOf_sub_smul_notMem_eq_preimage_neg (x : E) (c : ℝ) (K : Set E) :
    {θ : sphere (0 : E) 1 | x - c • (θ : E) ∉ K}
      = Neg.neg ⁻¹' {θ : sphere (0 : E) 1 | x + c • (θ : E) ∉ K} := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_preimage, coe_neg_sphere, smul_neg, ← sub_eq_add_neg]

end Invariance

/-! ## The law of a single coordinate -/

section CoordLaw

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Any unit vector can be carried to any other by a linear isometry of the space. -/
theorem exists_linearIsometryEquiv_apply_eq {w w' : E} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) :
    ∃ f : E ≃ₗᵢ[ℝ] E, f w = w' := by
  have hwne : w ≠ 0 := fun h => by simp [h] at hw
  haveI : Nontrivial E := ⟨⟨w, 0, hwne⟩⟩
  have hpos : 0 < finrank ℝ E := Module.finrank_pos
  have hcard : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) := by simp
  set i₀ : Fin (finrank ℝ E) := ⟨0, hpos⟩ with hi₀
  have key : ∀ v : E, ‖v‖ = 1 →
      ∃ b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E, b i₀ = v := by
    intro v hv
    have horth : Orthonormal ℝ
        (({i₀} : Set (Fin (finrank ℝ E))).domRestrict (fun _ => v)) := by
      refine ⟨fun _ => ?_, ?_⟩
      · change ‖v‖ = 1
        exact hv
      intro i j hij
      exact absurd (Subtype.ext (i.2.trans j.2.symm)) hij
    obtain ⟨b, hbv⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    exact ⟨b, hbv i₀ rfl⟩
  obtain ⟨b, hb⟩ := key w hw
  obtain ⟨b', hb'⟩ := key w' hw'
  refine ⟨b.repr.trans b'.repr.symm, ?_⟩
  classical
  rw [← hb, ← hb']
  simp [OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]

/-- **The law of `⟪θ, w⟫` for `θ` uniform on the unit sphere does not depend on the unit
vector `w`.**

This is the statement that "the distribution of a single coordinate of a uniform point of
`Sⁿ⁻¹`" is a well-defined object: the pushforward of the surface measure under
`θ ↦ ⟪θ, w⟫` is the same measure on `ℝ` for every unit `w`. -/
theorem map_inner_toSphere_congr {w w' : E} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) :
    (volume : Measure E).toSphere.map (fun θ : sphere (0 : E) 1 => ⟪(θ : E), w⟫)
      = (volume : Measure E).toSphere.map (fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫) := by
  obtain ⟨f, hf⟩ := exists_linearIsometryEquiv_apply_eq hw hw'
  have hmeas : Measurable fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫ :=
    (continuous_inner.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  symm
  calc (volume : Measure E).toSphere.map (fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫)
      = (((volume : Measure E).toSphere.map (sphereMap f)).map
          fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫) := by
        rw [toSphere_map_sphereMap]
    _ = (volume : Measure E).toSphere.map
          ((fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫) ∘ sphereMap f) :=
        Measure.map_map hmeas (measurable_sphereMap f)
    _ = (volume : Measure E).toSphere.map (fun θ : sphere (0 : E) 1 => ⟪(θ : E), w⟫) := by
        congr 1
        funext θ
        simp only [Function.comp_apply, coe_sphereMap, ← hf, f.inner_map_map]

/-- The measure of a "coordinate event" on the sphere does not depend on the unit vector. -/
theorem toSphere_setOf_inner_congr {w w' : E} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) {B : Set ℝ}
    (hB : MeasurableSet B) :
    (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B}
      = (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | ⟪(θ : E), w'⟫ ∈ B} := by
  have hmw : Measurable fun θ : sphere (0 : E) 1 => ⟪(θ : E), w⟫ :=
    (continuous_inner.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  have hmw' : Measurable fun θ : sphere (0 : E) 1 => ⟪(θ : E), w'⟫ :=
    (continuous_inner.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  have h := congrArg (fun μ : Measure ℝ => μ B) (map_inner_toSphere_congr hw hw')
  simp only [Measure.map_apply hmw hB, Measure.map_apply hmw' hB] at h
  exact h

/-- **The symmetric cap is exactly twice the one-sided cap.**

For every unit `w` and every threshold `c ≥ 0`,
`σ{θ : |⟪θ, w⟫| > c} = 2 · σ{θ : ⟪θ, w⟫ > c}`.  This is the factor of two between "the
surface of the cap `C`" and "the surface of the cap relative to the half-sphere". -/
theorem toSphere_abs_inner_gt (w : E) {c : ℝ} (hc : 0 ≤ c) :
    (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | c < |⟪(θ : E), w⟫|}
      = 2 * (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | c < ⟪(θ : E), w⟫} := by
  set P : Set (sphere (0 : E) 1) := {θ | c < ⟪(θ : E), w⟫} with hP
  set N : Set (sphere (0 : E) 1) := {θ | ⟪(θ : E), w⟫ < -c} with hN
  have hPm : MeasurableSet P :=
    measurableSet_sphere_setOf_inner (w := w) (B := Set.Ioi c) measurableSet_Ioi
  have hNm : MeasurableSet N :=
    measurableSet_sphere_setOf_inner (w := w) (B := Set.Iio (-c)) measurableSet_Iio
  have hNP : N = Neg.neg ⁻¹' P := by
    ext θ
    simp only [hN, hP, Set.mem_setOf_eq, Set.mem_preimage, coe_neg_sphere, inner_neg_left]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hunion : {θ : sphere (0 : E) 1 | c < |⟪(θ : E), w⟫|} = P ∪ N := by
    ext θ
    simp only [hP, hN, Set.mem_setOf_eq, Set.mem_union, lt_abs, lt_neg]
  have hdisj : Disjoint P N := by
    rw [Set.disjoint_left]
    intro θ hθP hθN
    simp only [hP, Set.mem_setOf_eq] at hθP
    simp only [hN, Set.mem_setOf_eq] at hθN
    linarith
  rw [hunion, measure_union hdisj hNm, hNP, toSphere_preimage_neg hPm, two_mul]

/-! ### What one orthonormal basis gives -/

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Parseval on the unit sphere: the squares of the coordinates sum to one. -/
theorem sum_inner_sq_eq_one (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E)
    (θ : sphere (0 : E) 1) : ∑ i, ⟪(θ : E), b i⟫ ^ 2 = 1 := by
  have h := b.sum_inner_mul_inner (θ : E) (θ : E)
  have h2 : ∀ i : Fin (finrank ℝ E),
      ⟪(θ : E), b i⟫ * ⟪b i, (θ : E)⟫ = ⟪(θ : E), b i⟫ ^ 2 := by
    intro i
    rw [real_inner_comm (b i) (θ : E)]
    ring
  simp only [h2] at h
  rw [h, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 θ.2, one_pow]

omit [FiniteDimensional ℝ E] in
theorem measurable_inner_sphere (w : E) :
    Measurable fun θ : sphere (0 : E) 1 => ⟪(θ : E), w⟫ :=
  (continuous_inner.comp (continuous_subtype_val.prodMk continuous_const)).measurable

/-- The `lintegral` of a function of one coordinate does not depend on the unit vector. -/
theorem lintegral_inner_toSphere_congr {w w' : E} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ θ, g ⟪(θ : E), w⟫ ∂((volume : Measure E).toSphere)
      = ∫⁻ θ, g ⟪(θ : E), w'⟫ ∂((volume : Measure E).toSphere) := by
  rw [← lintegral_map hg (measurable_inner_sphere w),
    ← lintegral_map hg (measurable_inner_sphere w'), map_inner_toSphere_congr hw hw']

/-- **The second moment of one coordinate on the sphere is exactly `1/n`.**

`n · ∫ ⟪θ, w⟫² dσ(θ) = σ(Sⁿ⁻¹)` for every unit `w`.  In other words the threshold `n^{-1/2}`
appearing in Lovász's set `A₂` is *exactly* the root-mean-square value of `⟪θ, w⟫`.  That is
why no concentration or moment inequality can bound the measure of `A₂` away from `1`: the
event is a central one, not a tail. -/
theorem finrank_mul_lintegral_inner_sq {w : E} (hw : ‖w‖ = 1) :
    (finrank ℝ E : ℝ≥0∞) *
        ∫⁻ θ, ENNReal.ofReal (⟪(θ : E), w⟫ ^ 2) ∂((volume : Measure E).toSphere)
      = (volume : Measure E).toSphere Set.univ := by
  classical
  have hwne : w ≠ 0 := fun h => by simp [h] at hw
  haveI : Nontrivial E := ⟨⟨w, 0, hwne⟩⟩
  set b := stdOrthonormalBasis ℝ E with hb
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (t ^ 2) :=
    (measurable_id.pow_const 2).ennreal_ofReal
  have heach : ∀ i, ∫⁻ θ, ENNReal.ofReal (⟪(θ : E), b i⟫ ^ 2)
        ∂((volume : Measure E).toSphere)
      = ∫⁻ θ, ENNReal.ofReal (⟪(θ : E), w⟫ ^ 2) ∂((volume : Measure E).toSphere) :=
    fun i => lintegral_inner_toSphere_congr (b.orthonormal.1 i) hw hg
  calc (finrank ℝ E : ℝ≥0∞) *
        ∫⁻ θ, ENNReal.ofReal (⟪(θ : E), w⟫ ^ 2) ∂((volume : Measure E).toSphere)
      = ∑ i, ∫⁻ θ, ENNReal.ofReal (⟪(θ : E), b i⟫ ^ 2)
          ∂((volume : Measure E).toSphere) := by
        rw [Finset.sum_congr rfl (fun i _ => heach i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ = ∫⁻ θ, ∑ i, ENNReal.ofReal (⟪(θ : E), b i⟫ ^ 2)
          ∂((volume : Measure E).toSphere) :=
        (lintegral_finsetSum _ (fun i _ => hg.comp (measurable_inner_sphere (b i)))).symm
    _ = ∫⁻ _, (1 : ℝ≥0∞) ∂((volume : Measure E).toSphere) := by
        refine lintegral_congr fun θ => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), sum_inner_sq_eq_one b θ,
          ENNReal.ofReal_one]
    _ = (volume : Measure E).toSphere Set.univ := lintegral_one

/-- **The pigeonhole lower bound on the spherical cap.**

Some coordinate of a unit vector always has square at least `1/n`, so the closed cap
`{θ : n⟪θ, w⟫² ≥ 1}` — the paper's set `C`, doubled — has measure at least `1/n` of the
sphere. -/
theorem toSphere_univ_le_finrank_mul_cap {w : E} (hw : ‖w‖ = 1) :
    (volume : Measure E).toSphere Set.univ
      ≤ (finrank ℝ E : ℝ≥0∞) * (volume : Measure E).toSphere
          {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ {t : ℝ | 1 ≤ (finrank ℝ E : ℝ) * t ^ 2}} := by
  classical
  have hwne : w ≠ 0 := fun h => by simp [h] at hw
  haveI : Nontrivial E := ⟨⟨w, 0, hwne⟩⟩
  have hpos : 0 < finrank ℝ E := Module.finrank_pos
  haveI : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hpos⟩⟩
  set b := stdOrthonormalBasis ℝ E with hb
  set B : Set ℝ := {t : ℝ | 1 ≤ (finrank ℝ E : ℝ) * t ^ 2} with hB
  have hBm : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  set S : Fin (finrank ℝ E) → Set (sphere (0 : E) 1) :=
    fun i => {θ | ⟪(θ : E), b i⟫ ∈ B} with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i => measurableSet_sphere_setOf_inner hBm
  have hSeq : ∀ i, (volume : Measure E).toSphere (S i)
      = (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B} :=
    fun i => toSphere_setOf_inner_congr (b.orthonormal.1 i) hw hBm
  have hcover : ∀ θ : sphere (0 : E) 1,
      (1 : ℝ≥0∞) ≤ ∑ i, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ := by
    intro θ
    have hsum : ∑ i : Fin (finrank ℝ E), (finrank ℝ E : ℝ)⁻¹
        ≤ ∑ i : Fin (finrank ℝ E), ⟪(θ : E), b i⟫ ^ 2 := by
      rw [sum_inner_sq_eq_one b θ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [mul_inv_cancel₀ (by positivity)]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
      (Finset.univ_nonempty (α := Fin (finrank ℝ E))) hsum
    have hmem : θ ∈ S i := by
      have hn : (0 : ℝ) < (finrank ℝ E : ℝ) := by positivity
      rw [hS]
      show (1 : ℝ) ≤ (finrank ℝ E : ℝ) * ⟪(θ : E), b i⟫ ^ 2
      rw [inv_le_iff_one_le_mul₀ hn] at hi
      linarith [hi]
    calc (1 : ℝ≥0∞) = (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ := by
          rw [Set.indicator_of_mem hmem, Pi.one_apply]
      _ ≤ ∑ j, (S j).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ :=
          Finset.single_le_sum
            (f := fun j => (S j).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ)
            (fun j _ => bot_le) (Finset.mem_univ i)
  calc (volume : Measure E).toSphere Set.univ
      = ∫⁻ _, 1 ∂((volume : Measure E).toSphere) := by
        rw [lintegral_one]
    _ ≤ ∫⁻ θ, ∑ i, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ
          ∂((volume : Measure E).toSphere) := lintegral_mono hcover
    _ = ∑ i, (volume : Measure E).toSphere (S i) := by
        rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hSm i))]
        exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one (hSm i)
    _ = (finrank ℝ E : ℝ≥0∞) * (volume : Measure E).toSphere
          {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B} := by
        simp only [hSeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The pigeonhole upper bound on the spherical cap.**

At most `n − 1` of the `n` coordinates of a unit vector can have square strictly larger than
`1/n`, so the open cap `{θ : n⟪θ, w⟫² > 1}` has measure at most `(n−1)/n` of the sphere. -/
theorem finrank_mul_toSphere_cap_lt_le {w : E} (hw : ‖w‖ = 1) :
    (finrank ℝ E : ℝ≥0∞) * (volume : Measure E).toSphere
        {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ {t : ℝ | 1 < (finrank ℝ E : ℝ) * t ^ 2}}
      ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) * (volume : Measure E).toSphere Set.univ := by
  classical
  have hwne : w ≠ 0 := fun h => by simp [h] at hw
  haveI : Nontrivial E := ⟨⟨w, 0, hwne⟩⟩
  have hpos : 0 < finrank ℝ E := Module.finrank_pos
  haveI : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hpos⟩⟩
  set b := stdOrthonormalBasis ℝ E with hb
  set B : Set ℝ := {t : ℝ | 1 < (finrank ℝ E : ℝ) * t ^ 2} with hB
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (by fun_prop)
  set S : Fin (finrank ℝ E) → Set (sphere (0 : E) 1) :=
    fun i => {θ | ⟪(θ : E), b i⟫ ∈ B} with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i => measurableSet_sphere_setOf_inner hBm
  have hSeq : ∀ i, (volume : Measure E).toSphere (S i)
      = (volume : Measure E).toSphere {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B} :=
    fun i => toSphere_setOf_inner_congr (b.orthonormal.1 i) hw hBm
  have hmiss : ∀ θ : sphere (0 : E) 1, ∃ i, θ ∉ S i := by
    intro θ
    by_contra hcon
    have hcon' : ∀ i, θ ∈ S i := fun i => by
      by_contra h
      exact hcon ⟨i, h⟩
    have hn : (0 : ℝ) < (finrank ℝ E : ℝ) := by positivity
    have hlt : ∑ i : Fin (finrank ℝ E), (finrank ℝ E : ℝ)⁻¹
        < ∑ i : Fin (finrank ℝ E), ⟪(θ : E), b i⟫ ^ 2 := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun i _ => ?_
      have := hcon' i
      rw [hS] at this
      have hi : (1 : ℝ) < (finrank ℝ E : ℝ) * ⟪(θ : E), b i⟫ ^ 2 := this
      rw [inv_lt_iff_one_lt_mul₀ hn]
      linarith
    rw [sum_inner_sq_eq_one b θ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_inv_cancel₀ (by positivity)] at hlt
    exact lt_irrefl _ hlt
  have hcount : ∀ θ : sphere (0 : E) 1,
      ∑ i, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ
        ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
    intro θ
    obtain ⟨i₀, hi₀⟩ := hmiss θ
    calc ∑ i, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ
        = ∑ i ∈ Finset.univ.erase i₀, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ :=
          (Finset.sum_erase (f := fun i => (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ)
            Finset.univ (by rw [Set.indicator_of_notMem hi₀])).symm
      _ ≤ (Finset.univ.erase i₀).card • (1 : ℝ≥0∞) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
          by_cases hj : θ ∈ S j
          · rw [Set.indicator_of_mem hj, Pi.one_apply]
          · rw [Set.indicator_of_notMem hj]
            exact bot_le
      _ = ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
          simp
  calc (finrank ℝ E : ℝ≥0∞) * (volume : Measure E).toSphere
        {θ : sphere (0 : E) 1 | ⟪(θ : E), w⟫ ∈ B}
      = ∑ i, (volume : Measure E).toSphere (S i) := by
        simp only [hSeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∫⁻ θ, ∑ i, (S i).indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) θ
          ∂((volume : Measure E).toSphere) := by
        rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hSm i))]
        exact (Finset.sum_congr rfl fun i _ => lintegral_indicator_one (hSm i)).symm
    _ ≤ ∫⁻ _, ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) ∂((volume : Measure E).toSphere) :=
        lintegral_mono hcount
    _ = ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) * (volume : Measure E).toSphere Set.univ := by
        rw [lintegral_const]

end CoordLaw

/-! ## Cone events of the hit-and-run step -/

section Cone

variable {n : ℕ}

/-- `unifSphere` is invariant under the antipodal map. -/
theorem unifSphere_preimage_neg {s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : MeasurableSet s) : unifSphere n (Neg.neg ⁻¹' s) = unifSphere n s := by
  rw [unifSphere, Measure.smul_apply, Measure.smul_apply, toSphere_preimage_neg hs]

/-- **A cone event of one hit-and-run step is bounded by the uniform measure of its set of
directions.**

If `A` avoids the centre `u` and every point of `A` on the ray `u + ℝθ` forces the direction
`θ` to lie in `D`, then `P_u(A) ≤ σ(D)`, where `σ` is the *normalised* surface measure.  No
convexity, and no hypothesis on `K` beyond measurability, is needed: on a bad direction the
whole ray contributes nothing, and on a good one the chord contributes at most its own mass.

This is what turns the "spherical cap" hypothesis of Lovász's Lemma 8 from a statement about
the walk into a statement about the sphere. -/
theorem hitAndRun_le_unifSphere_of_cone {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (huA : u ∉ A)
    {D : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)} (hD : MeasurableSet D)
    (hcone : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (t : ℝ), t ≠ 0 →
      u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A → θ ∈ D) :
    hitAndRun K u A ≤ unifSphere n D := by
  rw [hitAndRun_apply_set hK u hA, Set.indicator_of_notMem huA, mul_zero, add_zero,
    hitAndRunProposal_apply' K u hA,
    lintegral_prod _ (measurable_polarIntegrand hK hA u).aemeasurable]
  have hbound : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∫⁻ t, A.indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) * chordDensity K u (θ, t)
          ∂(volume : Measure ℝ)
        ≤ D.indicator 1 θ := by
    intro θ
    by_cases hθ : θ ∈ D
    · rw [Set.indicator_of_mem hθ, Pi.one_apply]
      calc ∫⁻ t, A.indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) *
              chordDensity K u (θ, t) ∂(volume : Measure ℝ)
          ≤ ∫⁻ t, chordDensity K u (θ, t) ∂(volume : Measure ℝ) := by
            refine lintegral_mono fun t => ?_
            by_cases h : u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A
            · rw [Set.indicator_of_mem h, Pi.one_apply, one_mul]
            · rw [Set.indicator_of_notMem h, zero_mul]
              exact bot_le
        _ ≤ 1 := by
            simp only [chordDensity]
            simp_rw [indicator_eq_chordSet_indicator K u (θ : EuclideanSpace ℝ (Fin n))]
            rw [lintegral_const_mul _
                (measurable_one.indicator (measurableSet_chordSet hK u _)),
              lintegral_indicator_one (measurableSet_chordSet hK u _)]
            exact ENNReal.inv_mul_le_one _
    · rw [Set.indicator_of_notMem hθ, nonpos_iff_eq_zero]
      have hzero : ∀ t : ℝ,
          A.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
              (u + t • (θ : EuclideanSpace ℝ (Fin n))) * chordDensity K u (θ, t) = 0 := by
        intro t
        rcases eq_or_ne t 0 with rfl | ht
        · rw [zero_smul, add_zero, Set.indicator_of_notMem huA, zero_mul]
        · rw [Set.indicator_of_notMem (fun h => hθ (hcone θ t ht h)), zero_mul]
      simp only [hzero, lintegral_zero]
  calc ∫⁻ θ, ∫⁻ t, A.indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) *
          chordDensity K u (θ, t) ∂(volume : Measure ℝ) ∂(unifSphere n)
      ≤ ∫⁻ θ, D.indicator 1 θ ∂(unifSphere n) := lintegral_mono hbound
    _ = unifSphere n D := lintegral_indicator_one hD

/-- The set `A₂` of Lovász's Lemma 8 is measurable. -/
theorem measurableSet_almostOrthogonal (u v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin n) |
      ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|} := by
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin n) => ‖x - u‖ * ‖u - v‖ := by fun_prop
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt n * |⟪x - u, u - v⟫| :=
    continuous_const.mul ((continuous_id.sub continuous_const).inner continuous_const).abs
  exact measurableSet_lt h1.measurable h2.measurable

/-- The set of "bad" directions of Lovász's Lemma 8 is measurable. -/
theorem measurableSet_almostOrthogonalDir (u v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      ‖u - v‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), u - v⟫|} := by
  have h2 : Continuous fun θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), u - v⟫| :=
    continuous_const.mul ((continuous_subtype_val.inner continuous_const)).abs
  exact measurableSet_lt measurable_const h2.measurable

/-- **The cap hypothesis `hcap` of `tvLe_hitAndRun_lemma41`, reduced to the unit sphere.**

`P_u{x : |⟨x − u, u − v⟩| > n^{-1/2}|x − u||u − v|} ≤ σ{θ : |⟨θ, u − v⟩| > n^{-1/2}|u − v|}`,
where `σ = unifSphere n` is the normalised surface measure.  The event is a double cone about
`u`, so the walk contributes at most the measure of the directions it opens on. -/
theorem hitAndRun_almostOrthogonal_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u v : EuclideanSpace ℝ (Fin n)) :
    hitAndRun K u {x : EuclideanSpace ℝ (Fin n) |
        ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ unifSphere n {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          ‖u - v‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), u - v⟫|} := by
  refine hitAndRun_le_unifSphere_of_cone hK u (measurableSet_almostOrthogonal u v) ?_
    (measurableSet_almostOrthogonalDir u v) ?_
  · simp
  · intro θ t ht hmem
    simp only [Set.mem_setOf_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.1 θ.2, mul_one, real_inner_smul_left, abs_mul] at hmem
    simp only [Set.mem_setOf_eq]
    have habs : 0 < |t| := abs_pos.2 ht
    nlinarith [hmem, habs]

/-! ### The dimension-dependent cap bound `q₂ = 1 - 1/n` -/

theorem one_lt_sqrt_mul_abs_iff (n : ℕ) (s : ℝ) :
    1 < Real.sqrt n * |s| ↔ 1 < (n : ℝ) * s ^ 2 := by
  have hx : 0 ≤ Real.sqrt n * |s| := by positivity
  have hsq : (Real.sqrt n * |s|) ^ 2 = (n : ℝ) * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)), sq_abs]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The set of bad directions, rewritten against a *unit* vector and without square roots. -/
theorem almostOrthogonalDir_eq {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖w‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|}
      = {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ ∈ {t : ℝ | 1 < (n : ℝ) * t ^ 2}} := by
  have hn0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hnpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  ext θ
  have hsplit : ⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫
      = ‖w‖ * ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ := by
    rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  simp only [Set.mem_setOf_eq, hsplit, abs_mul, abs_of_pos hnpos]
  rw [← one_lt_sqrt_mul_abs_iff n]
  constructor
  · intro h
    nlinarith [h, hnpos]
  · intro h
    nlinarith [h, hnpos]

/-- **The spherical-cap bound `σ(A₂) ≤ 1 - 1/n`**, proved unconditionally.

At most `n - 1` of the `n` coordinates of a unit vector can exceed the root-mean-square value
`n^{-1/2}` strictly, so the set of directions `θ` with `√n·|⟨θ, w⟩| > |w|` has normalised
surface measure at most `(n-1)/n`.  At `n = 2` this is exactly the value `1/2` that
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41` needs.  (The `_of_half` corollary that once
  recorded this figure was **deleted** in `868a1c9`'s follow-up: correcting the paper's false
  `hchord` raised the budget to `1/8 + q₂ + 1/2`, which is vacuous at `q₂ = 1/2`.) -/
theorem unifSphere_almostOrthogonalDir_le (hn : n ≠ 0) (w : EuclideanSpace ℝ (Fin n)) :
    unifSphere n {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖w‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|}
      ≤ ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
  haveI : NeZero n := ⟨hn⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnR]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  rcases eq_or_ne w 0 with rfl | hw
  · have : {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖(0 : EuclideanSpace ℝ (Fin n))‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)),
          (0 : EuclideanSpace ℝ (Fin n))⟫|} = ∅ := by
      ext θ; simp
    rw [this, measure_empty]
    exact bot_le
  -- the unit vector
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hw
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set S : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {θ | ‖w‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|} with hSdef
  have hSeq : S = {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ ∈
        {t : ℝ | 1 < (finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) * t ^ 2}} := by
    rw [hSdef, almostOrthogonalDir_eq hw, hfr]
  have hkey := finrank_mul_toSphere_cap_lt_le (E := EuclideanSpace ℝ (Fin n)) hunit
  rw [← hSeq, hfr] at hkey
  -- normalise
  have hA0 : sphereArea n ≠ 0 := sphereArea_ne_zero
  have hAtop : sphereArea n ≠ ⊤ := sphereArea_ne_top n
  have hAeq : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ
      = sphereArea n := rfl
  rw [hAeq] at hkey
  have hstep : (n : ℝ≥0∞) * unifSphere n S ≤ ((n - 1 : ℕ) : ℝ≥0∞) := by
    rw [unifSphere, Measure.smul_apply, smul_eq_mul]
    calc (n : ℝ≥0∞) * ((sphereArea n)⁻¹ *
            (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere S)
        = (sphereArea n)⁻¹ *
            ((n : ℝ≥0∞) * (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere S) := by ring
      _ ≤ (sphereArea n)⁻¹ * (((n - 1 : ℕ) : ℝ≥0∞) * sphereArea n) := by
          gcongr
      _ = ((n - 1 : ℕ) : ℝ≥0∞) := by
          rw [mul_comm ((n - 1 : ℕ) : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAtop,
            one_mul]
  have hn0' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hdiv : unifSphere n S ≤ ((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hn0') (Or.inl hntop), mul_comm]
    exact hstep
  refine hdiv.trans (le_of_eq ?_)
  have hcast : ((n - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn), Nat.cast_one]
  rw [hcast, ← ENNReal.ofReal_natCast (n := n),
    ← ENNReal.ofReal_div_of_pos hnR]
  congr 1
  field_simp

theorem one_le_sqrt_mul_abs_iff (n : ℕ) (s : ℝ) :
    1 ≤ Real.sqrt n * |s| ↔ 1 ≤ (n : ℝ) * s ^ 2 := by
  have hx : 0 ≤ Real.sqrt n * |s| := by positivity
  have hsq : (Real.sqrt n * |s|) ^ 2 = (n : ℝ) * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)), sq_abs]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The *closed* cap of the paper, rewritten against a unit vector and without square roots. -/
theorem almostOrthogonalDirClosed_eq {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖w‖ ≤ Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|}
      = {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ ∈ {t : ℝ | 1 ≤ (n : ℝ) * t ^ 2}} := by
  have hn0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hnpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  ext θ
  have hsplit : ⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫
      = ‖w‖ * ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ := by
    rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  simp only [Set.mem_setOf_eq, hsplit, abs_mul, abs_of_pos hnpos]
  rw [← one_le_sqrt_mul_abs_iff n]
  constructor
  · intro h
    nlinarith [h, hnpos]
  · intro h
    nlinarith [h, hnpos]

/-- **The spherical cap is never smaller than `1/n` of the sphere.**

This is the pigeonhole bound in the other direction: some coordinate of a unit vector always
has square at least `1/n`, so the closed cap `{θ : √n·|⟨θ, w⟩| ≥ |w|}` — exactly the set
whose measure Lovász's proof calls a "standard computation" and prints as `1/6` — has
normalised surface measure at least `1/n`.  For `n ≤ 5` this already exceeds `1/6`. -/
theorem inv_le_unifSphere_almostOrthogonalDirClosed (hn : n ≠ 0)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    ((n : ℝ≥0∞))⁻¹ ≤ unifSphere n {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖w‖ ≤ Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|} := by
  haveI : NeZero n := ⟨hn⟩
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hw
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set S : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {θ | ‖w‖ ≤ Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|} with hSdef
  have hSeq : S = {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      ⟪(θ : EuclideanSpace ℝ (Fin n)), ‖w‖⁻¹ • w⟫ ∈
        {t : ℝ | 1 ≤ (finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) * t ^ 2}} := by
    rw [hSdef, almostOrthogonalDirClosed_eq hw, hfr]
  have hkey := toSphere_univ_le_finrank_mul_cap (E := EuclideanSpace ℝ (Fin n)) hunit
  rw [← hSeq, hfr] at hkey
  have hA0 : sphereArea n ≠ 0 := sphereArea_ne_zero
  have hAtop : sphereArea n ≠ ⊤ := sphereArea_ne_top n
  have hAeq : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ
      = sphereArea n := rfl
  rw [hAeq] at hkey
  have hn0' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hstep : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) * unifSphere n S := by
    rw [unifSphere, Measure.smul_apply, smul_eq_mul]
    calc (1 : ℝ≥0∞) = (sphereArea n)⁻¹ * sphereArea n :=
          (ENNReal.inv_mul_cancel hA0 hAtop).symm
      _ ≤ (sphereArea n)⁻¹ *
            ((n : ℝ≥0∞) * (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere S) := by
          gcongr
      _ = (n : ℝ≥0∞) * ((sphereArea n)⁻¹ *
            (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere S) := by ring
  calc ((n : ℝ≥0∞))⁻¹ = (n : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * unifSphere n S) := by gcongr
    _ = unifSphere n S := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hn0' hntop, one_mul]

/-- **The cap hypothesis `hcap` of `tvLe_hitAndRun_lemma41`, discharged with
`q₂ = 1 - 1/n`.** -/
theorem hitAndRun_almostOrthogonal_le_one_sub_inv (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u v : EuclideanSpace ℝ (Fin n)) :
    hitAndRun K u {x : EuclideanSpace ℝ (Fin n) |
        ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal (1 - 1 / (n : ℝ)) :=
  (hitAndRun_almostOrthogonal_le hK u v).trans
    (unifSphere_almostOrthogonalDir_le hn (u - v))

end Cone

/-! ### Axiom profile -/

section AxiomCheck

#print axioms toSphere_map_sphereMap
#print axioms toSphere_map_neg
#print axioms toSphere_preimage_neg
#print axioms lintegral_toSphere_neg
#print axioms setOf_sub_smul_notMem_eq_preimage_neg
#print axioms unifSphere_preimage_neg
#print axioms exists_linearIsometryEquiv_apply_eq
#print axioms map_inner_toSphere_congr
#print axioms toSphere_setOf_inner_congr
#print axioms lintegral_inner_toSphere_congr
#print axioms toSphere_abs_inner_gt
#print axioms sum_inner_sq_eq_one
#print axioms finrank_mul_lintegral_inner_sq
#print axioms toSphere_univ_le_finrank_mul_cap
#print axioms finrank_mul_toSphere_cap_lt_le
#print axioms hitAndRun_le_unifSphere_of_cone
#print axioms hitAndRun_almostOrthogonal_le
#print axioms unifSphere_almostOrthogonalDir_le
#print axioms inv_le_unifSphere_almostOrthogonalDirClosed
#print axioms hitAndRun_almostOrthogonal_le_one_sub_inv

end AxiomCheck

end Arlib.MarkovChains
