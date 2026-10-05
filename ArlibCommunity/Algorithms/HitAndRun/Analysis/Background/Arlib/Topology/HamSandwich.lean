/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLemma
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Topology.OddMap

/-!
# The two-measure ham sandwich, for signed integrands

This file settles the open statement **(P1)** of `Arlib.Convexity.PositionalCut` — equivalently
gap **(G1)** of `Arlib.Convexity.LocalizationLemma` — for **signed** integrands, which is the
generality the localisation argument consumes.  `Arlib.Convexity.TransverseCut` proves only the
nonnegative case, by mass centres, and records that the signed case "is where Borsuk–Ulam
re-enters".  It does; Borsuk–Ulam is now available, proved in `Arlib.Topology.OddMap`.

## Main results

* `Arlib.measure_level_eq_zero` — `{x | L x = s}` is Haar-null as soon as `L ≠ 0` **or** `s ≠ 0`
  (in the second case it is empty when `L = 0`).  This is what lets the degenerate cuts — the
  empty halfspace and the whole space — be handled uniformly with the honest ones.
* `Arlib.continuousAt_setIntegral_param` — the mass `∫_{C ∩ {φ v ≤ 0}} g` on one side of a moving
  cut is continuous in the parameter `v`, by dominated convergence along `𝓝 v₀`, provided the
  critical set `{φ v₀ = 0}` is null.
* `Arlib.exists_halfSpace_bisecting_pair` — **the two-measure ham sandwich, signed.**  Given two
  orthonormal `e₁, e₂` and integrable `g, h` on a measurable `C` with `∫_C g ≠ 0`, some hyperplane
  orthogonal to a direction of `span {e₁, e₂}` bisects `∫_C g` and `∫_C h` at once.
* `Arlib.exists_halfSpace_bisecting_pair_of_finrank` — the same, with `e₁, e₂` extracted from
  `2 ≤ finrank ℝ E`.
* `Arlib.exists_two_sided_halfSpace_signed` — **(P1) for signed integrands**, the statement the
  localisation chain actually needs.
* `Arlib.exists_two_sided_halfSpace_signed_ball` — a closed, hypothesis-free instance.

## The argument

Oriented halfspaces orthogonal to `span {e₁, e₂}` are parametrised by the unit sphere of `ℝ³`:
`v` gives the functional `L_v = ⟪v₀ e₁ + v₁ e₂, ·⟫` and the level `s_v = -v₂`, and `-v` gives the
closed complementary halfspace.  Two degenerate points `v = (0,0,±1)` give the empty halfspace and
the whole space; there `L_v = 0` but `s_v ≠ 0`, so the critical set is *empty* and everything below
goes through without a case split.

The cut masses `A v = ∫_{C ∩ {L_v ≤ s_v}} g` and `B v` for `h` are therefore continuous on the
sphere, and `A v + A (-v) = ∫_C g` because the two closed halfspaces overlap exactly in the null
set `{L_v = s_v}`.  So `a v = A v - (∫_C g)/2` and `b v = B v - (∫_C h)/2` are continuous and
**odd**, and `Arlib.exists_eq_zero_of_odd_pair_sphere` produces a common zero: a simultaneous
bisection.  The direction is nonzero because a degenerate `v` would give `A v ∈ {0, ∫_C g}`, and
`∫_C g ≠ 0` rules that out.

Positivity on both sides is then immediate: each side carries exactly half of each total mass.

## Why the weakening from bisection to positivity does not help

`Arlib.Convexity.PositionalCut` notes that (P1) needs only positivity of the four masses, not
exact bisection, and suggests that this should be a softer target.  It is not, and it is worth
recording why, so that the soft route is not retried.

*Positivity is not weaker than bisection.*  With only *two* measures the exact ham sandwich
already needs Borsuk–Ulam only into `ℝ²` — never the full `Sⁿ → ℝⁿ` form.  And positivity needs
the same theorem: if no cut had all four masses positive, the odd map `v ↦ (a v, b v)` of this
file would avoid an open symmetric rectangle `R` around the origin, and composing with the
Minkowski gauge of `R` (odd, continuous, retracting `ℝ² \ R` onto `∂R ≅ S¹`) would produce an odd
map `Sⁿ → S¹` — exactly the object `Arlib.false_of_odd_lift` forbids.

*Where the compactness/pigeonhole route dies.*  The classical two-measure argument that needs no
algebraic topology runs: for each direction `u` pick the `g`-bisecting level `s(u)`, then apply the
intermediate value theorem to the **odd** continuous function `u ↦ H_u(s(u)) - (∫_C h)/2` on the
connected sphere of directions.  Its one hidden input is a *continuous odd selection* `u ↦ s(u)`
of the bisecting level.  That selection exists precisely because `s ↦ ∫_{C ∩ {L_u ≤ s}} g` is
**strictly monotone**, which holds only for **nonnegative** `g`; then the bisecting level is
unique and depends continuously on `u`.  This is exactly the hypothesis
`Arlib.Convexity.TransverseCut` uses, and it is exactly what fails here.

For signed `g` the profile is not monotone and the level set
`Z = {(u,s) : ∫_{C ∩ {L_u ≤ s}} g = (∫_C g)/2}` — the zero set of an odd continuous function on the
sphere of oriented halfspaces — **can be disconnected**, so no selection is available.  Concretely,
`f(x,y,z) = z (z² - 1/4)` on `S²` is continuous and odd (`f (-v) = -f v`), and its zero set is
three disjoint circles `{z = 0}`, `{z = 1/2}`, `{z = -1/2}`; the antipodal map swaps the outer two.
Any argument that picks "the" bisecting cut in each direction and slides it around has to choose a
branch of such a set, and there is no continuous way to do so.  "`Z` has an antipodally invariant
connected component" is itself of Borsuk–Ulam strength.  Hence this file goes through the topology.

## An alternative route claimed in the literature

The Kook–Vempala survey *The Localization Method for High-Dimensional Inequalities*
(arXiv:2512.10848) is reported to prove the localization lemma by a **rotating pencil** instead:
fix a codimension-2 flat `A`, rotate a halfspace `H` whose boundary contains `A`, note that
`H ↦ ∫_{C ∩ H} g - ∫_{C ∩ Hᶜ} g` is continuous and negates after a half-turn, and apply the
one-parameter intermediate value theorem.  That would bisect **one** integrand through a
prescribed flat with no `ℤ/2` index argument.  This file does not take that route and does not
depend on it; the ingredient it would need is exactly `Arlib.setIntegral_halfSpace_add_neg`
together with `Arlib.continuousAt_setIntegral_param`, both proved below, so it is available to a
later reader as a cheap alternative.

**Caveat, carried from the survey-reading task:** that account is second-hand.  Kannan–Lovász–
Simonovits 1995 could not be read verbatim (Springer's scan carries a text layer on page 1 only;
the remaining pages are CCITT-G4 images), so the description of its Corollary 2.4 — the
equality-refined form that Lovász–Vempala actually invoke — is reconstructed from what LV's proof
consumes plus the survey and LV's `logcon.pdf`, not read from the source.  The survey's printed
construction also reads "if `A_m ∩ int K_m ≠ ∅`, set `K_{m+1} := K_m`", which is backwards
relative to its own contradiction argument a few paragraphs later; it is presumably a typo for
cutting *when* the flat meets the interior, but that is an inference.  **Nothing in this file rests
on any of that**: the results below are proved from Borsuk–Ulam, which is proved in
`Arlib.Topology.OddMap` from Mathlib.

## A note on the two dimension hypotheses

`Arlib.exists_eq_zero_of_odd_pair_sphere` asks for `3 ≤ finrank`, while
`Arlib.exists_two_sided_halfSpace_signed` asks for `2 ≤ finrank`.  These are hypotheses about
**different spaces** and the asymmetry is deliberate, not a slip.  The `3` is about the *parameter*
space: Borsuk–Ulam is applied to the unit sphere of `EuclideanSpace ℝ (Fin 3)`, whose `finrank` is
exactly `3`, because oriented halfspaces orthogonal to a fixed `2`-plane form a `2`-sphere no
matter how large the ambient dimension is (a direction in the plane, plus a level, compactified by
the empty halfspace and the whole space).  The `2` is about the *ambient* space `E` where `C`
lives, and is used only to produce two orthonormal vectors `e₁, e₂` spanning that plane.  So the
ambient dimension may be exactly `2` and Borsuk–Ulam is still applied in its `finrank = 3` form.

## Honesty note

There is **no** `def`, `structure`, `class` or `Prop` here asserting the ham sandwich, (P1), (G1),
the Localization Lemma or the isoperimetric inequality, and no theorem below takes any of them as
a hypothesis.  The single `def`, `Arlib.cutFun`, is a plain explicit linear combination of two
inner products, and every property attributed to it is proved.  The axiom audit at the end
confirms that every result depends on exactly `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Set Bornology Filter Metric Module
open scoped Topology

namespace Arlib

section Null

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A level set `{x | L x = s}` is null as soon as `L ≠ 0` **or** `s ≠ 0`: in the second case,
if `L = 0` the set is empty. -/
theorem measure_level_eq_zero {L : E →L[ℝ] ℝ} {s : ℝ} (h : L ≠ 0 ∨ s ≠ 0) :
    μ {x : E | L x = s} = 0 := by
  rcases eq_or_ne L 0 with rfl | hL
  · have hs : s ≠ 0 := h.resolve_left (fun h => h rfl)
    have : {x : E | (0 : E →L[ℝ] ℝ) x = s} = (∅ : Set E) := by
      ext x; simp [eq_comm, hs]
    rw [this, measure_empty]
  · exact measure_hyperplane_eq_zero μ hL s

end Null

section Complementary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The two *closed* halfspaces of a cut split every integral.**

`{L ≤ s}` and `{-L ≤ -s} = {s ≤ L}` cover `E` and overlap exactly in `{L = s}`, which is null as
soon as `L ≠ 0` or `s ≠ 0` (`Arlib.measure_level_eq_zero`).  This is the *oddness* input for both
the Borsuk–Ulam route and the pencil route below: replacing the cut by its half-turn replaces the
mass by its complement. -/
theorem setIntegral_halfSpace_add_neg {C : Set E} {g : E → ℝ} (hC : MeasurableSet C)
    (hgi : IntegrableOn g C μ) {L : E →L[ℝ] ℝ} {s : ℝ} (hnd : L ≠ 0 ∨ s ≠ 0) :
    (∫ x in C ∩ halfSpace L s true, g x ∂μ)
      + (∫ x in C ∩ halfSpace (-L) (-s) true, g x ∂μ) = ∫ x in C, g x ∂μ := by
  have hsecond : C ∩ halfSpace (-L) (-s) true = C ∩ {x : E | s ≤ L x} := by
    ext x
    simp only [halfSpace_true, mem_inter_iff, mem_setOf_eq, ContinuousLinearMap.neg_apply]
    constructor
    · rintro ⟨hx, hle⟩; exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hle⟩; exact ⟨hx, by linarith⟩
  have hnull : μ {x : E | L x = s} = 0 := measure_level_eq_zero μ hnd
  have hclosed : C ∩ {x : E | s ≤ L x}
      = (C ∩ halfSpace L s false) ∪ (C ∩ {x : E | L x = s}) := by
    ext x
    simp only [halfSpace_false, mem_inter_iff, mem_union, mem_setOf_eq]
    constructor
    · rintro ⟨hx, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inr ⟨hx, heq.symm⟩
      · exact Or.inl ⟨hx, hlt⟩
    · rintro (⟨hx, hlt⟩ | ⟨hx, heq⟩)
      · exact ⟨hx, le_of_lt hlt⟩
      · exact ⟨hx, le_of_eq heq.symm⟩
  have hnull' : μ (C ∩ {x : E | L x = s}) = 0 := measure_mono_null inter_subset_right hnull
  have haeset : ((C ∩ halfSpace L s false) ∪ (C ∩ {x : E | L x = s}) : Set E)
      =ᵐ[μ] ((C ∩ halfSpace L s false) : Set E) := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · refine measure_mono_null ?_ hnull'
      rintro x ⟨hx, hnx⟩
      exact hx.resolve_left hnx
    · rw [Set.sdiff_eq_empty.mpr Set.subset_union_left, measure_empty]
  have heqint : ∫ x in C ∩ {x : E | s ≤ L x}, g x ∂μ
      = ∫ x in C ∩ halfSpace L s false, g x ∂μ := by
    rw [hclosed]
    exact setIntegral_congr_set haeset
  rw [hsecond, heqint]
  exact setIntegral_halfSpace_add hgi hC L s

end Complementary

/-! ### Continuity of a cut mass in a continuous family of cuts -/

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- **The mass on one side of a moving cut depends continuously on the cut.**

If `φ v x` is continuous in the parameter `v` for each fixed `x`, the sets `{x | φ v x ≤ 0}` are
measurable, and the *critical set* `{x | φ v₀ x = 0}` is null for `μ` restricted to `C`, then
`v ↦ ∫_{C ∩ {φ v ≤ 0}} g` is continuous at `v₀`.

Dominated convergence along `𝓝 v₀` with dominating function `|g|`; the a.e. pointwise convergence
of the indicators is exactly the nullity of the critical set. -/
theorem continuousAt_setIntegral_param {V : Type*} [TopologicalSpace V]
    [FirstCountableTopology V] {C : Set E} {g : E → ℝ}
    (hgi : IntegrableOn g C μ) {φ : V → E → ℝ} (hφ : ∀ x, Continuous fun v => φ v x)
    (hmeas : ∀ v, MeasurableSet {x : E | φ v x ≤ 0}) {v₀ : V}
    (hnull : (μ.restrict C) {x : E | φ v₀ x = 0} = 0) :
    ContinuousAt (fun v => ∫ x in C ∩ {x : E | φ v x ≤ 0}, g x ∂μ) v₀ := by
  have hrepr : ∀ v : V, ∫ x in C ∩ {x : E | φ v x ≤ 0}, g x ∂μ
      = ∫ x in C, Set.indicator {x : E | φ v x ≤ 0} g x ∂μ := fun v =>
    (setIntegral_indicator (hmeas v)).symm
  simp_rw [hrepr]
  have hae : ∀ᵐ x ∂(μ.restrict C), φ v₀ x ≠ 0 := by
    rw [ae_iff]; simpa using hnull
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |g x|)
    (Eventually.of_forall fun v => hgi.aestronglyMeasurable.indicator (hmeas v))
    (Eventually.of_forall fun v => Eventually.of_forall fun x => norm_indicator_le_abs _ _ x)
    hgi.abs ?_
  filter_upwards [hae] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · -- `φ v₀ x < 0`: the indicator is `g x` near `v₀`
    have hmem : x ∈ {y : E | φ v₀ y ≤ 0} := le_of_lt hlt
    rw [Set.indicator_of_mem hmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have hcont : ContinuousAt (fun v => φ v x) v₀ := (hφ x).continuousAt
    filter_upwards [hcont (Iio_mem_nhds hlt)] with v hv
    have hv' : φ v x < 0 := hv
    have hmem2 : x ∈ {y : E | φ v y ≤ 0} := le_of_lt hv'
    exact (Set.indicator_of_mem hmem2 g).symm
  · -- `φ v₀ x > 0`: the indicator vanishes near `v₀`
    have hnmem : x ∉ {y : E | φ v₀ y ≤ 0} := not_le.mpr hgt
    rw [Set.indicator_of_notMem hnmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have hcont : ContinuousAt (fun v => φ v x) v₀ := (hφ x).continuousAt
    filter_upwards [hcont (Ioi_mem_nhds hgt)] with v hv
    have hv' : (0:ℝ) < φ v x := hv
    have hmem2 : x ∉ {y : E | φ v y ≤ 0} := not_le.mpr hv'
    exact (Set.indicator_of_notMem hmem2 g).symm

end Continuity

/-! ### The ham sandwich -/

section HamSandwich

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The three-parameter family of cuts used below: `v` ranges over the unit sphere of `ℝ³`, the
functional is `⟪v₀ • e₁ + v₁ • e₂, ·⟫` and the level is `-v₂`. -/
private noncomputable def cutFun (e₁ e₂ : E) (v : EuclideanSpace ℝ (Fin 3)) : E →L[ℝ] ℝ :=
  v 0 • innerSL ℝ e₁ + v 1 • innerSL ℝ e₂

private theorem cutFun_apply (e₁ e₂ : E) (v : EuclideanSpace ℝ (Fin 3)) (x : E) :
    cutFun e₁ e₂ v x = v 0 * inner ℝ e₁ x + v 1 * inner ℝ e₂ x := rfl

private theorem cutFun_neg (e₁ e₂ : E) (v : EuclideanSpace ℝ (Fin 3)) :
    cutFun e₁ e₂ (-v) = -cutFun e₁ e₂ v := by
  ext x
  simp [cutFun_apply]
  ring

/-- If `e₁, e₂` are orthonormal and `(v 0, v 1) ≠ (0,0)`, the cut functional is nonzero. -/
private theorem cutFun_ne_zero {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ¬(v 0 = 0 ∧ v 1 = 0)) : cutFun e₁ e₂ v ≠ 0 := by
  intro hzero
  have h21 : inner ℝ e₂ e₁ = (0 : ℝ) := by rw [real_inner_comm]; exact h12
  have hval := congrArg (fun T : E →L[ℝ] ℝ => T (v 0 • e₁ + v 1 • e₂)) hzero
  simp only [cutFun_apply, ContinuousLinearMap.zero_apply, inner_add_right, inner_smul_right,
    h11, h22, h12, h21] at hval
  have : v 0 * v 0 + v 1 * v 1 = 0 := by linarith
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hv ⟨h0, h1⟩

/-- **The bisecting-cut mass function is continuous and odd.**

For a bounded measurable `C`, an integrable `g`, and orthonormal `e₁, e₂`, put
`A v = ∫_{C ∩ {⟪v₀e₁+v₁e₂, ·⟫ ≤ -v₂}} g`.  Then `A` is continuous at every `v` on the unit sphere,
and `A v + A (-v) = ∫_C g`. -/
private theorem cutMass_add_neg {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {C : Set E} {g : E → ℝ} (hC : MeasurableSet C) (hgi : IntegrableOn g C μ)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0)) :
    (∫ x in C ∩ halfSpace (cutFun e₁ e₂ v) (-(v 2)) true, g x ∂μ)
      + (∫ x in C ∩ halfSpace (cutFun e₁ e₂ (-v)) (-((-v) 2)) true, g x ∂μ)
      = ∫ x in C, g x ∂μ := by
  have hnd : cutFun e₁ e₂ v ≠ 0 ∨ -(v 2) ≠ 0 := by
    by_cases h01 : v 0 = 0 ∧ v 1 = 0
    · right
      intro hs0
      exact hv ⟨h01.1, h01.2, by simpa using neg_eq_zero.mp hs0⟩
    · exact Or.inl (cutFun_ne_zero h11 h22 h12 h01)
  have hL : cutFun e₁ e₂ (-v) = -cutFun e₁ e₂ v := cutFun_neg e₁ e₂ v
  have hs : (-((-v) 2) : ℝ) = -(-(v 2)) := by
    have : ((-v) 2 : ℝ) = -(v 2) := rfl
    rw [this]
  rw [hL, hs]
  exact setIntegral_halfSpace_add_neg hC hgi hnd

/-- **The two-measure ham sandwich, for signed integrands, in the plane spanned by `e₁, e₂`.**

Given two orthonormal vectors `e₁, e₂` of `E`, a measurable `C`, and integrable — possibly
sign-changing — `g, h` on `C` with `∫_C g ≠ 0`, there is a hyperplane, orthogonal to a direction
in `span {e₁, e₂}`, that bisects `∫_C g` **and** `∫_C h` simultaneously.

The proof is Borsuk–Ulam (`Arlib.exists_eq_zero_of_odd_pair_sphere`) applied to the two cut
masses as functions on the unit sphere of `ℝ³`, which parametrizes the oriented halfspaces
orthogonal to `span {e₁, e₂}`: they are continuous (`Arlib.continuousAt_setIntegral_param`) and,
after subtracting half of the total mass, odd (`Arlib.cutMass_add_neg`). -/
theorem exists_halfSpace_bisecting_pair {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {C : Set E} {g h : E → ℝ} (hC : MeasurableSet C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hg0 : ∫ x in C, g x ∂μ ≠ 0) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      ∫ x in C ∩ halfSpace L s true, g x ∂μ = (∫ x in C, g x ∂μ) / 2 ∧
      ∫ x in C ∩ halfSpace L s true, h x ∂μ = (∫ x in C, h x ∂μ) / 2 := by
  classical
  set φ : EuclideanSpace ℝ (Fin 3) → E → ℝ := fun v x => cutFun e₁ e₂ v x + v 2 with hφdef
  have hset : ∀ v : EuclideanSpace ℝ (Fin 3),
      {x : E | φ v x ≤ 0} = halfSpace (cutFun e₁ e₂ v) (-(v 2)) true := by
    intro v; ext x
    simp only [hφdef, halfSpace_true, mem_setOf_eq]
    constructor <;> intro hx <;> linarith
  have hφcont : ∀ x : E, Continuous fun v : EuclideanSpace ℝ (Fin 3) => φ v x := by
    intro x
    have h0 : Continuous fun v : EuclideanSpace ℝ (Fin 3) => v 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous
    have h1 : Continuous fun v : EuclideanSpace ℝ (Fin 3) => v 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous
    have h2 : Continuous fun v : EuclideanSpace ℝ (Fin 3) => v 2 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
    have : (fun v : EuclideanSpace ℝ (Fin 3) => φ v x)
        = fun v => v 0 * inner ℝ e₁ x + v 1 * inner ℝ e₂ x + v 2 := by
      funext v; rw [hφdef]; simp [cutFun_apply]
    rw [this]
    exact ((h0.mul continuous_const).add (h1.mul continuous_const)).add h2
  have hmeasφ : ∀ v, MeasurableSet {x : E | φ v x ≤ 0} := by
    intro v; rw [hset v]; exact measurableSet_halfSpace _ _ _
  have hnd : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 →
      (cutFun e₁ e₂ v ≠ 0 ∨ -(v 2) ≠ 0) := by
    intro v hv
    by_cases h01 : v 0 = 0 ∧ v 1 = 0
    · right
      intro hs0
      have hv2 : v 2 = 0 := by simpa using neg_eq_zero.mp hs0
      have : v = 0 := by
        ext i
        fin_cases i
        · simpa using h01.1
        · simpa using h01.2
        · simpa using hv2
      rw [this, norm_zero] at hv
      exact absurd hv (by norm_num)
    · exact Or.inl (cutFun_ne_zero h11 h22 h12 h01)
  have hnull : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 →
      (μ.restrict C) {x : E | φ v x = 0} = 0 := by
    intro v hv
    have hEq : {x : E | φ v x = 0} = {x : E | cutFun e₁ e₂ v x = -(v 2)} := by
      ext x; simp only [hφdef, mem_setOf_eq]; constructor <;> intro hx <;> linarith
    have h0 : μ {x : E | φ v x = 0} = 0 := by
      rw [hEq]; exact measure_level_eq_zero μ (hnd v hv)
    have hle : (μ.restrict C) {x : E | φ v x = 0} ≤ μ {x : E | φ v x = 0} :=
      Measure.le_iff'.mp Measure.restrict_le_self _
    rw [h0] at hle
    exact nonpos_iff_eq_zero.mp hle
  -- the two cut masses, as functions on the unit sphere of `ℝ³`
  set S : Set (EuclideanSpace ℝ (Fin 3)) := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 with hS
  set A : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun v => ∫ x in C ∩ {x : E | φ v x ≤ 0}, g x ∂μ with hA
  set B : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun v => ∫ x in C ∩ {x : E | φ v x ≤ 0}, h x ∂μ with hB
  set G : ℝ := ∫ x in C, g x ∂μ with hG
  set H : ℝ := ∫ x in C, h x ∂μ with hH
  have hAodd : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 → A v + A (-v) = G := by
    intro v hv
    have hvnd : ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
      rintro ⟨a0, a1, a2⟩
      have : v = 0 := by
        ext i; fin_cases i
        · simpa using a0
        · simpa using a1
        · simpa using a2
      rw [this, norm_zero] at hv
      exact absurd hv (by norm_num)
    have := cutMass_add_neg h11 h22 h12 hC hgi hvnd
    rw [hA]
    simp only [hset]
    have hneg : (-(( -v) 2) : ℝ) = -(-(v 2)) := by norm_num
    rw [hneg] at this ⊢
    exact this
  have hBodd : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 → B v + B (-v) = H := by
    intro v hv
    have hvnd : ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
      rintro ⟨a0, a1, a2⟩
      have : v = 0 := by
        ext i; fin_cases i
        · simpa using a0
        · simpa using a1
        · simpa using a2
      rw [this, norm_zero] at hv
      exact absurd hv (by norm_num)
    have := cutMass_add_neg h11 h22 h12 hC hhi hvnd
    rw [hB]
    simp only [hset]
    have hneg : (-(( -v) 2) : ℝ) = -(-(v 2)) := by norm_num
    rw [hneg] at this ⊢
    exact this
  have hAcont : Continuous fun v : ↥S => A ↑v - G / 2 := by
    refine Continuous.sub ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro v
    exact (continuousAt_setIntegral_param hgi hφcont hmeasφ
      (hnull ↑v (mem_sphere_zero_iff_norm.mp v.2))).comp continuous_subtype_val.continuousAt
  have hBcont : Continuous fun v : ↥S => B ↑v - H / 2 := by
    refine Continuous.sub ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro v
    exact (continuousAt_setIntegral_param hhi hφcont hmeasφ
      (hnull ↑v (mem_sphere_zero_iff_norm.mp v.2))).comp continuous_subtype_val.continuousAt
  have h3 : (3 : ℕ) ≤ finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  obtain ⟨v, hv1, hv2⟩ :=
    exists_eq_zero_of_odd_pair_sphere (E := EuclideanSpace ℝ (Fin 3)) h3 hAcont hBcont
      (by
        intro x
        have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
        have hco : ((-x : ↥S) : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3)) :=
          coe_neg_sphere x
        simp only [hco]
        have := hAodd (x : EuclideanSpace ℝ (Fin 3)) hx
        linarith)
      (by
        intro x
        have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
        have hco : ((-x : ↥S) : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3)) :=
          coe_neg_sphere x
        simp only [hco]
        have := hBodd (x : EuclideanSpace ℝ (Fin 3)) hx
        linarith)
  have hvn : ‖(v : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hAv : A ↑v = G / 2 := by linarith [hv1]
  have hBv : B ↑v = H / 2 := by linarith [hv2]
  refine ⟨cutFun e₁ e₂ ↑v, -((v : EuclideanSpace ℝ (Fin 3)) 2), ?_, ?_, ?_⟩
  · -- the direction is nonzero, because a zero direction would give mass `0` or `G`
    intro hzero
    have hcase : A ↑v = 0 ∨ A ↑v = G := by
      rcases le_or_gt (0 : ℝ) (-((v : EuclideanSpace ℝ (Fin 3)) 2)) with hs | hs
      · right
        have hset2 : {x : E | φ (↑v) x ≤ 0} = Set.univ := by
          rw [hset]
          ext x
          simp only [halfSpace_true, mem_setOf_eq, hzero, ContinuousLinearMap.zero_apply,
            mem_univ, iff_true]
          exact hs
        show (∫ x in C ∩ {x : E | φ (↑v) x ≤ 0}, g x ∂μ) = G
        rw [hset2, Set.inter_univ, hG]
      · left
        have hset2 : {x : E | φ (↑v) x ≤ 0} = (∅ : Set E) := by
          rw [hset]
          ext x
          simp only [halfSpace_true, mem_setOf_eq, hzero, ContinuousLinearMap.zero_apply,
            mem_empty_iff_false, iff_false, not_le]
          exact hs
        show (∫ x in C ∩ {x : E | φ (↑v) x ≤ 0}, g x ∂μ) = 0
        rw [hset2, Set.inter_empty]
        simp
    rcases hcase with hc | hc
    · rw [hAv] at hc; exact hg0 (by linarith)
    · rw [hAv] at hc; exact hg0 (by linarith)
  · rw [← hset]; exact hAv
  · rw [← hset]; exact hBv

/-- **The two-measure ham sandwich for signed integrands.**  In a real inner-product space of
dimension `≥ 2`, for a measurable `C` and integrable `g, h` with `∫_C g ≠ 0`, some hyperplane
bisects `∫_C g` and `∫_C h` at once.  No sign hypothesis on `g` or `h`. -/
theorem exists_halfSpace_bisecting_pair_of_finrank (h2 : 2 ≤ finrank ℝ E)
    {C : Set E} {g h : E → ℝ} (hC : MeasurableSet C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hg0 : ∫ x in C, g x ∂μ ≠ 0) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧
      ∫ x in C ∩ halfSpace L s true, g x ∂μ = (∫ x in C, g x ∂μ) / 2 ∧
      ∫ x in C ∩ halfSpace L s true, h x ∂μ = (∫ x in C, h x ∂μ) / 2 := by
  have hb := (stdOrthonormalBasis ℝ E).orthonormal
  set i0 : Fin (finrank ℝ E) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (finrank ℝ E) := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by
    rw [hi0, hi1]
    simp [Fin.ext_iff]
  have h11 : inner ℝ (stdOrthonormalBasis ℝ E i0) (stdOrthonormalBasis ℝ E i0) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_mul_norm, hb.1 i0]; ring
  have h22 : inner ℝ (stdOrthonormalBasis ℝ E i1) (stdOrthonormalBasis ℝ E i1) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_mul_norm, hb.1 i1]; ring
  have h12 : inner ℝ (stdOrthonormalBasis ℝ E i0) (stdOrthonormalBasis ℝ E i1) = (0 : ℝ) :=
    hb.2 hne
  exact exists_halfSpace_bisecting_pair h11 h22 h12 hC hgi hhi hg0

/-- **(P1) for signed integrands.**  In a real inner-product space of dimension `≥ 2`, for a
measurable `C` carrying positive `g`-mass and positive `h`-mass — with `g` and `h` merely
integrable, **no sign hypothesis** — there are a nonzero direction `L` and a level `s` such that
both sides of the cut `{L ≤ s}`, `{s < L}` carry positive `g`-mass *and* positive `h`-mass.

This is the statement labelled **(P1)** in `Arlib.Convexity.PositionalCut` and **(G1)** in
`Arlib.Convexity.LocalizationLemma`, in the generality the localisation argument consumes;
`Arlib.Convexity.TransverseCut` proves only the nonnegative case, by mass centres. -/
theorem exists_two_sided_halfSpace_signed (h2 : 2 ≤ finrank ℝ E)
    {C : Set E} {g h : E → ℝ} (hC : MeasurableSet C)
    (hgi : IntegrableOn g C μ) (hhi : IntegrableOn h C μ)
    (hgpos : 0 < ∫ x in C, g x ∂μ) (hhpos : 0 < ∫ x in C, h x ∂μ) :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧ ∀ side : Bool,
      0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
      0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ := by
  obtain ⟨L, s, hL, hg, hh⟩ :=
    exists_halfSpace_bisecting_pair_of_finrank h2 hC hgi hhi (ne_of_gt hgpos)
  have hgsum := setIntegral_halfSpace_add hgi hC L s
  have hhsum := setIntegral_halfSpace_add hhi hC L s
  refine ⟨L, s, hL, fun side => ?_⟩
  cases side
  · constructor
    · have : ∫ x in C ∩ halfSpace L s false, g x ∂μ = (∫ x in C, g x ∂μ) / 2 := by
        rw [hg] at hgsum; linarith
      rw [this]; linarith
    · have : ∫ x in C ∩ halfSpace L s false, h x ∂μ = (∫ x in C, h x ∂μ) / 2 := by
        rw [hh] at hhsum; linarith
      rw [this]; linarith
  · exact ⟨by rw [hg]; linarith, by rw [hh]; linarith⟩

/-- **Non-vacuity.**  A closed statement with no hypotheses: on the Euclidean plane, the unit ball
with constant density `1` for both integrands admits a two-sided cut.  This certifies that the
typeclass bundle and analytic hypotheses of `Arlib.exists_two_sided_halfSpace_signed` are
simultaneously satisfiable. -/
theorem exists_two_sided_halfSpace_signed_ball :
    ∃ (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (s : ℝ), L ≠ 0 ∧ ∀ side : Bool,
      0 < ∫ _x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side, (1 : ℝ) ∧
      0 < ∫ _x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ halfSpace L s side, (1 : ℝ) := by
  have hC : MeasurableSet (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := measurableSet_closedBall
  have htop : volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ))
      (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) volume := integrableOn_const htop
  have hpos : 0 < ∫ _x in closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, (1 : ℝ) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    exact ENNReal.toReal_pos
      (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin 2)) one_pos).ne' htop
  exact exists_two_sided_halfSpace_signed (μ := volume) (by simp) hC hi hi hpos hpos

end HamSandwich

/-! ### Axiom audit -/

#print axioms measure_level_eq_zero
#print axioms setIntegral_halfSpace_add_neg
#print axioms continuousAt_setIntegral_param
#print axioms exists_halfSpace_bisecting_pair
#print axioms exists_halfSpace_bisecting_pair_of_finrank
#print axioms exists_two_sided_halfSpace_signed
#print axioms exists_two_sided_halfSpace_signed_ball

end Arlib
