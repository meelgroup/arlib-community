/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sets.VietorisTopology
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.BrunnSharp
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLemma

/-!
# The limit passage of the Localization Lemma: Blaschke selection, and what the profile is

This file attacks gap **(G2)** listed in the module docstring of
`Arlib.Convexity.LocalizationLemma`: the limit passage in the Lovász–Simonovits localisation
argument.  That gap was described there as needing three things:

1. the **Blaschke selection theorem** (Hausdorff-compactness of the convex bodies inside a fixed
   ball);
2. the **sharp** (`1/m`-concave) Brunn–Minkowski inequality for cross-sections;
3. a **convergence theorem** identifying `lim (1/vol Cₖ) ∫_{Cₖ} g` with a needle integral
   `∫₀¹ ℓ(t)^{n-1} g(a + t(b-a)) dt`, with `ℓ` **affine**.

Item 2 has since landed in `Arlib.Convexity.BrunnSharp` (`Arlib.brunn_slice_sharp`,
`Arlib.brunn_slice_concaveOn`).  **This file closes item 1 and settles the shape of item 3's
answer — negatively.**  Concretely:

## What is proved here

**Blaschke selection, for convex bodies** (`Arlib.exists_subseq_tendsto_hausdorffDist_convex`).
A sequence of nonempty compact **convex** subsets of a fixed compact set has a subsequence
converging in Hausdorff distance to a nonempty compact **convex** set.  The compactness input is
Mathlib's `TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact` (which
`Mathlib.Analysis.Convex.Body` does *not* expose for `ConvexBody`); the new content is
`Arlib.convex_of_tendsto_hausdorffDist` — **convexity survives Hausdorff limits** — proved by an
explicit `2 · hausdorffDist` estimate on `Metric.infDist` of the midpoint.

**Stability of concavity under pointwise limits** (`Arlib.concaveOn_of_tendsto`,
`Arlib.nonneg_of_tendsto`), and their combination with sharp Brunn
(`Arlib.concaveOn_limit_slice_profile`): *if the (arbitrarily renormalised) sharp cross-section
profiles `t ↦ cⱼ · vol(slice Kⱼ t)^{1/m}` of a sequence of convex measurable bodies converge
pointwise on a convex set `S` of heights, the limit profile is nonnegative and **concave** on `S`.*
That is exactly what sharp Brunn buys for the limit passage.

**A converse to Brunn's theorem** (§ *generalised cones*).  For a convex base `A ⊆ ℝ^m` with
`0 ∈ A` and **any** nonnegative concave `g` on `[0,1]`, the *generalised cone*
`Arlib.profileBody A g = {x | x 0 ∈ [0,1] ∧ tail x ∈ g (x 0) • A}` is a convex subset of
`ℝ^(m+1)` (`Arlib.convex_profileBody`) whose slice at height `t` is exactly `g t • A`
(`Arlib.slice_profileBody`), so that its sharp profile is exactly
`g t · vol(A)^{1/m}` (`Arlib.profile_profileBody`).  Two consequences:

* `Arlib.exists_convex_slice_volume_needleWeight` — the **needle weight** `ℓ(t)^m` of
  `Arlib.needleWeight` *is* realised, exactly, as the slice-volume function of a convex body.
  So the target profile of the Localization Lemma is not vacuous.
* `Arlib.exists_convex_slice_profile_not_affine` — there is a convex body in `ℝ^(m+1)` whose
  sharp slice profile is `t ↦ min t (1 - t)`, which is concave (`Arlib.concaveOn_tent`) but
  **not** convex (`Arlib.not_convexOn_tent`), hence not affine.

## What is therefore still missing from (G2), precisely

The docstring of `Arlib.Convexity.LocalizationLemma` records the sharp form of Brunn–Minkowski
as what is needed "to pin the limit profile to a power of an affine function".  Sharp Brunn is
indeed **necessary** — the log-concave form gives no profile at all — but it is **not
sufficient**, and `Arlib.exists_convex_slice_profile_not_affine` is the proof.  Read together,
`Arlib.brunn_slice_concaveOn` and `Arlib.convex_profileBody` say that the sharp cross-section
profiles of convex bodies in `ℝ^(m+1)` are **exactly** the nonnegative concave functions on the
support interval; the affine ones are a *proper* subclass of these.  Concretely, the bipyramid
`profileBody A (fun t => min t (1 - t))` is convex and has profile `min t (1 - t)`, which is
concave but not affine.  Thinness does not rescue the situation: `profileBody (ε • A) g` has
profile `ε · g` by `Arlib.profile_profileBody`, so shrinking the base to make the body hug its
axis leaves the *normalised* profile unchanged.  (`Arlib.exists_convex_slice_profile_not_affine`
claims only convexity of the body, not measurability; it does not need it, because
`Arlib.slice_profileBody` computes every slice exactly, and each slice is a scaled box.)

So (G2) has **two** residual pieces, neither proved nor assumed here.

*(i) The weak-convergence statement.*  `lim (1/vol Cₖ) ∫_{Cₖ} f = ∫₀¹ G(t)^m f(a + t(b-a)) dt`
for lower semicontinuous integrable `f`, where `G` is the concave limit profile supplied by
`Arlib.concaveOn_limit_slice_profile`.

*(ii) The concave-to-affine reduction.*  Stated exactly:

> given `G : [0,1] → ℝ≥0` concave, `m ≠ 0`, and lower semicontinuous integrable `g, h` on a
> segment `[a,b] ⊆ ℝⁿ` with `∫₀¹ G(t)^m g(a + t(b-a)) dt > 0` and
> `∫₀¹ G(t)^m h(a + t(b-a)) dt > 0`, produce `a', b' ∈ ℝⁿ` and `p, q ≥ 0` with
> `∫₀¹ ((1-t)p + tq)^m g(a' + t(b'-a')) dt > 0` and likewise for `h`.

> **⚠ CORRECTION (see `Arlib.Convexity.NeedleProfile`).**  This section used to continue: "In
> the literature the affine form of the Localization Lemma is reached by a further reduction of
> this kind on top of the limit body; formalising it is exactly what remains."  That overstated
> the case: **piece (ii) is not load-bearing for anything in this repository, and dropping it
> costs nothing downstream.**
>
> Every one-dimensional consumer of a needle here takes as its input the *log-concavity* of the
> needle density — that is the stated contract of `Arlib.logConcaveOn_needleDensity` and of
> `Arlib.IsLogConcave.comp_needleMap` — and affineness of `ℓ` is used only as a route to that
> log-concavity, through `Arlib.logConcaveOn_needleWeight`.  But a nonnegative concave function
> is log-concave (`Arlib.logConcaveOn_of_concaveOn`), hence so is any nonnegative power of one.
> `Arlib.logConcaveOn_concaveNeedleDensity` proves that `t ↦ G t ^ k · f(a + t·v)` is
> log-concave on `[0,1]` for **any** nonnegative concave `G`, and
> `Arlib.logConcaveOn_needleDensity_of_concaveNeedle` recovers the affine case from it.  So the
> *concave* form of the Localization Lemma feeds every consumer exactly as the affine form does.
>
> `Arlib.exists_convex_slice_profile_not_affine` below is **still true and still worth having**:
> it correctly refutes the claim that sharp Brunn–Minkowski identifies the limit profile as a
> power of an affine function.  It simply refutes a step that this development does not need.
>
> Piece (i), the weak-convergence statement, **is now proved** — see
> `Arlib.abs_setIntegral_sub_slice_profile_le` and
> `Arlib.tendsto_average_setIntegral_of_profile` in `Arlib.Convexity.NeedleProfile`, together
> with the Fubini and measurability infrastructure there.  It is proved in coordinates in which
> the needle is the first coordinate axis, and it consumes a *modulus-of-continuity* hypothesis
> on `f` rather than lower semicontinuity, so two hypotheses of it remain undischarged (a Helly
> selection for the profiles, and a uniform bound on them) plus an affine change of coordinates.
> Those three items, listed exactly in that file's module docstring, are the whole of what is
> left of (G2).

In particular **(G2) is not closed** — but it is materially smaller than the list above
suggests — and **(G1) (the Borsuk–Ulam / two-measure ham-sandwich hyperplane) is untouched**, so
the Localization Lemma remains unproved and unassumed.

## Honesty note

As in `Arlib.Convexity.LocalizationLemma`, this file contains **no** `def`/`structure`/`class`
whose name or content asserts the Localization Lemma, the isoperimetric inequality, or Blaschke
selection.  `Arlib.profileBody` is a plain explicit set; every other name below is a theorem
proved outright.  Blaschke selection is *proved* (from Mathlib's compactness of
`NonemptyCompacts`), not posited.
-/

open Set Filter Topology Metric MeasureTheory TopologicalSpace Pointwise
open scoped ENNReal

namespace Arlib

/-! ### Blaschke selection

Mathlib's `Mathlib/Analysis/Convex/Body.lean` gives `ConvexBody V` the Hausdorff metric but
proves no compactness or selection theorem for it.  What Mathlib *does* have is
`TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact`: the nonempty compact subsets
of a compact set form a compact space in the Hausdorff metric.  The missing step for convex
bodies is that convexity is a *closed* condition, which is `convex_of_tendsto_hausdorffDist`. -/

section Blaschke

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Convexity survives Hausdorff limits.**  If each `C n` is a nonempty compact convex set and
`hausdorffDist (C n) L → 0` for a nonempty bounded closed `L`, then `L` is convex.

The estimate: given `x, y ∈ L` and weights `a + b = 1`, pick nearest points `u, v ∈ C n`; then
`dist x u, dist y v ≤ hausdorffDist (C n) L`, the combination `a • u + b • v` lies in `C n` by
convexity and is within `hausdorffDist (C n) L` of `a • x + b • y`, whence
`infDist (a • x + b • y) L ≤ 2 · hausdorffDist (C n) L → 0`. -/
theorem convex_of_tendsto_hausdorffDist {C : ℕ → Set E} {L : Set E}
    (hconv : ∀ n, Convex ℝ (C n)) (hne : ∀ n, (C n).Nonempty) (hcpt : ∀ n, IsCompact (C n))
    (hLcl : IsClosed L) (hLne : L.Nonempty) (hLbdd : Bornology.IsBounded L)
    (hlim : Tendsto (fun n => hausdorffDist (C n) L) atTop (𝓝 0)) :
    Convex ℝ L := by
  intro x hx y hy a b ha hb hab
  set z : E := a • x + b • y with hz
  rw [hLcl.mem_iff_infDist_zero hLne]
  refine le_antisymm ?_ infDist_nonneg
  have key : ∀ n, infDist z L ≤ 2 * hausdorffDist (C n) L := by
    intro n
    have hEne : hausdorffEDist L (C n) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded hLne (hne n) hLbdd (hcpt n).isBounded
    have hEne' : hausdorffEDist (C n) L ≠ ⊤ := by rwa [hausdorffEDist_comm] at hEne
    obtain ⟨u, hu, hux⟩ := (hcpt n).exists_infDist_eq_dist (hne n) x
    obtain ⟨v, hv, hvy⟩ := (hcpt n).exists_infDist_eq_dist (hne n) y
    have hxu : dist x u ≤ hausdorffDist (C n) L := by
      rw [← hux, hausdorffDist_comm]
      exact infDist_le_hausdorffDist_of_mem hx hEne
    have hyv : dist y v ≤ hausdorffDist (C n) L := by
      rw [← hvy, hausdorffDist_comm]
      exact infDist_le_hausdorffDist_of_mem hy hEne
    have hmem : a • u + b • v ∈ C n := hconv n hu hv ha hb hab
    have hdist : dist z (a • u + b • v) ≤ hausdorffDist (C n) L := by
      have hsub : z - (a • u + b • v) = a • (x - u) + b • (y - v) := by
        simp only [hz, smul_sub]; abel
      have hstep : dist z (a • u + b • v) ≤ a * dist x u + b * dist y v := by
        rw [dist_eq_norm, hsub]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb, ← dist_eq_norm, ← dist_eq_norm]
      refine hstep.trans ?_
      calc a * dist x u + b * dist y v
          ≤ a * hausdorffDist (C n) L + b * hausdorffDist (C n) L := by gcongr
        _ = hausdorffDist (C n) L := by rw [← add_mul, hab, one_mul]
    calc infDist z L ≤ infDist (a • u + b • v) L + dist z (a • u + b • v) :=
          infDist_le_infDist_add_dist
      _ ≤ hausdorffDist (C n) L + hausdorffDist (C n) L :=
          add_le_add (infDist_le_hausdorffDist_of_mem hmem hEne') hdist
      _ = 2 * hausdorffDist (C n) L := by ring
  have hlim2 : Tendsto (fun n => 2 * hausdorffDist (C n) L) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 : ℝ)
  exact ge_of_tendsto hlim2 (Eventually.of_forall key)

omit [NormedSpace ℝ E] in
/-- **Blaschke selection theorem**, compact-set form.  Mathlib supplies the compactness of
`{L : NonemptyCompacts E | ↑L ⊆ K}`; this repackages it as a subsequence statement about plain
sets. -/
theorem exists_subseq_tendsto_hausdorffDist {K : Set E} (hK : IsCompact K) {C : ℕ → Set E}
    (hne : ∀ n, (C n).Nonempty) (hcpt : ∀ n, IsCompact (C n)) (hsub : ∀ n, C n ⊆ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Set E,
      L.Nonempty ∧ IsCompact L ∧ L ⊆ K ∧
      Tendsto (fun n => hausdorffDist (C (φ n)) L) atTop (𝓝 0) := by
  set B : ℕ → NonemptyCompacts E := fun n => ⟨⟨C n, hcpt n⟩, hne n⟩ with hB
  have hcoe : ∀ n, ((B n : NonemptyCompacts E) : Set E) = C n := fun _ => rfl
  have hmem : ∀ n, B n ∈ {L : NonemptyCompacts E | (L : Set E) ⊆ K} := fun n => hsub n
  obtain ⟨a, ha, φ, hφ, htend⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact hK).tendsto_subseq hmem
  refine ⟨φ, hφ, (a : Set E), a.nonempty, a.isCompact, ha, ?_⟩
  have h := tendsto_iff_dist_tendsto_zero.mp htend
  simpa only [Function.comp_apply, NonemptyCompacts.dist_eq, hcoe] using h

/-- **Blaschke selection theorem for convex bodies.**  A sequence of nonempty compact convex
subsets of a fixed compact set has a subsequence converging in Hausdorff distance to a nonempty
compact **convex** subset of it.

This is the piece of gap (G2) of `Arlib.Convexity.LocalizationLemma` that concerns compactness.
It is *proved*, not assumed. -/
theorem exists_subseq_tendsto_hausdorffDist_convex {K : Set E} (hK : IsCompact K) {C : ℕ → Set E}
    (hne : ∀ n, (C n).Nonempty) (hcpt : ∀ n, IsCompact (C n)) (hconv : ∀ n, Convex ℝ (C n))
    (hsub : ∀ n, C n ⊆ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Set E,
      L.Nonempty ∧ IsCompact L ∧ Convex ℝ L ∧ L ⊆ K ∧
      Tendsto (fun n => hausdorffDist (C (φ n)) L) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, L, hLne, hLcpt, hLK, hlim⟩ := exists_subseq_tendsto_hausdorffDist hK hne hcpt hsub
  exact ⟨φ, hφ, L, hLne, hLcpt,
    convex_of_tendsto_hausdorffDist (fun n => hconv (φ n)) (fun n => hne (φ n))
      (fun n => hcpt (φ n)) hLcpt.isClosed hLne hLcpt.isBounded hlim, hLK, hlim⟩

end Blaschke

/-! ### Pointwise limits of concave functions -/

section ConcaveLimit

variable {F : Type*} [AddCommMonoid F] [Module ℝ F]

/-- A pointwise limit of concave functions is concave. -/
theorem concaveOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {S : Set F}
    (hS : Convex ℝ S) {f : ι → F → ℝ} {g : F → ℝ} (hf : ∀ i, ConcaveOn ℝ S (f i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    ConcaveOn ℝ S g := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ S := hS hx hy ha hb hab
  have h1 : Tendsto (fun i => a • f i x + b • f i y) l (𝓝 (a • g x + b • g y)) :=
    ((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)
  exact le_of_tendsto_of_tendsto' h1 (hlim _ hxy) fun i => (hf i).2 hx hy ha hb hab

omit [AddCommMonoid F] [Module ℝ F] in
/-- A pointwise limit of functions nonnegative on `S` is nonnegative on `S`. -/
theorem nonneg_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {S : Set F}
    {f : ι → F → ℝ} {g : F → ℝ} (hf : ∀ i, ∀ x ∈ S, 0 ≤ f i x)
    (hlim : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    ∀ x ∈ S, 0 ≤ g x :=
  fun x hx => ge_of_tendsto (hlim x hx) (Eventually.of_forall fun i => hf i x hx)

end ConcaveLimit

/-! ### What sharp Brunn buys for the limit passage

The limit of renormalised sharp cross-section profiles of convex bodies is a nonnegative
**concave** function.  This is the exact contribution of `Arlib.brunn_slice_concaveOn` to gap
(G2); the section after this one shows that it is also the *whole* contribution — the limit
need not be affine. -/

/-- **The limit of renormalised sharp cross-section profiles is nonnegative and concave.**

`c j` is an arbitrary nonnegative renormalisation (in the localisation argument, `c j` is
`(vol K j)^{-1/m}` or similar); concavity is preserved by nonnegative scaling, so the statement
is insensitive to which normalisation is chosen. -/
theorem concaveOn_limit_slice_profile {m : ℕ} (hm : m ≠ 0) {K : ℕ → Set (Fin (m + 1) → ℝ)}
    (hconv : ∀ j, Convex ℝ (K j)) (hmeas : ∀ j, MeasurableSet (K j)) {S : Set ℝ}
    (hS : Convex ℝ S) (hne : ∀ j, ∀ t ∈ S, (slice (K j) t).Nonempty)
    (hfin : ∀ j, ∀ t ∈ S, volume (slice (K j) t) ≠ ⊤) {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j)
    {G : ℝ → ℝ}
    (hlim : ∀ t ∈ S, Tendsto (fun j => c j * (volume (slice (K j) t)).toReal ^ (1 / (m : ℝ)))
      atTop (𝓝 (G t))) :
    ConcaveOn ℝ S G ∧ ∀ t ∈ S, 0 ≤ G t := by
  refine ⟨concaveOn_of_tendsto hS
      (f := fun j t => c j * (volume (slice (K j) t)).toReal ^ (1 / (m : ℝ))) ?_ hlim,
    nonneg_of_tendsto ?_ hlim⟩
  · intro j
    have h := (brunn_slice_concaveOn hm (hconv j) (hmeas j) hS (hne j) (hfin j)).smul (hc j)
    simpa only [smul_eq_mul] using h
  · exact fun j t _ => mul_nonneg (hc j) (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-! ### Generalised cones: a converse to Brunn's theorem

Every nonnegative concave profile on `[0,1]` is the sharp cross-section profile of an honest
convex body.  Hence sharp Brunn characterises the class of profiles *exactly*, and cannot
distinguish affine profiles inside it. -/

section ProfileBody

/-- For a convex set containing the origin, `s • A ⊆ r • A` whenever `0 ≤ s ≤ r`. -/
theorem smul_set_subset_smul_set_of_le {F : Type*} [AddCommGroup F] [Module ℝ F] {A : Set F}
    (hA : Convex ℝ A) (hA0 : (0 : F) ∈ A) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    s • A ⊆ r • A := by
  rcases eq_or_lt_of_le (hs.trans hsr) with hr | hr
  · have hs0 : s = 0 := le_antisymm (hsr.trans hr.ge) hs
    have hr0 : r = 0 := hr.symm
    rw [hs0, hr0]
  · have hrne : r ≠ 0 := ne_of_gt hr
    rintro _ ⟨w, hw, rfl⟩
    refine Set.mem_smul_set.mpr ⟨(s / r) • w,
      hA.smul_mem_of_zero_mem hA0 hw ⟨div_nonneg hs hr.le, (div_le_one hr).2 hsr⟩, ?_⟩
    have hrs : r * (s / r) = s := by field_simp
    rw [smul_smul, hrs]

variable {m : ℕ}

/-- The **generalised cone** over the base `A ⊆ ℝ^m` with profile `g : ℝ → ℝ`:
`{x ∈ ℝ^(m+1) | x 0 ∈ [0,1] and (x 1, …, x m) ∈ g (x 0) • A}`.

A plain explicit set; it asserts nothing.  For `g` affine this is a frustum (a truncated cone);
for `g = min t (1-t)` it is a bipyramid over `A`. -/
def profileBody (A : Set (Fin m → ℝ)) (g : ℝ → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | x 0 ∈ Icc (0 : ℝ) 1 ∧ Fin.tail x ∈ g (x 0) • A}

@[simp] theorem mem_profileBody {A : Set (Fin m → ℝ)} {g : ℝ → ℝ} {x : Fin (m + 1) → ℝ} :
    x ∈ profileBody A g ↔ x 0 ∈ Icc (0 : ℝ) 1 ∧ Fin.tail x ∈ g (x 0) • A := Iff.rfl

/-- The slice of a generalised cone at a height in `[0,1]` is the scaled base. -/
theorem slice_profileBody (A : Set (Fin m → ℝ)) (g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    slice (profileBody A g) t = g t • A := by
  ext y
  simp only [mem_slice, mem_profileBody, Fin.cons_zero, Fin.tail_cons]
  exact and_iff_right ht

/-- **A generalised cone with a nonnegative concave profile over a convex base containing the
origin is convex.**  This is the converse direction of Brunn's theorem. -/
theorem convex_profileBody {A : Set (Fin m → ℝ)} (hA : Convex ℝ A) (hA0 : (0 : Fin m → ℝ) ∈ A)
    {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc (0 : ℝ) 1) g) (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) :
    Convex ℝ (profileBody A g) := by
  rintro x ⟨hx0, hxt⟩ y ⟨hy0, hyt⟩ a b ha hb hab
  have hz0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
  have hIcc : a * x 0 + b * y 0 ∈ Icc (0 : ℝ) 1 := by
    simpa using convex_Icc (0 : ℝ) 1 hx0 hy0 ha hb hab
  refine ⟨by rw [hz0]; exact hIcc, ?_⟩
  have htail : Fin.tail (a • x + b • y) = a • Fin.tail x + b • Fin.tail y := by
    funext i; simp [Fin.tail]
  rw [htail, hz0]
  obtain ⟨u, hu, hxu⟩ := Set.mem_smul_set.mp hxt
  obtain ⟨v, hv, hyv⟩ := Set.mem_smul_set.mp hyt
  rw [← hxu, ← hyv]
  have hgx : 0 ≤ g (x 0) := hg0 _ hx0
  have hgy : 0 ≤ g (y 0) := hg0 _ hy0
  have hA1 : 0 ≤ a * g (x 0) := mul_nonneg ha hgx
  have hB1 : 0 ≤ b * g (y 0) := mul_nonneg hb hgy
  have hs0 : 0 ≤ a * g (x 0) + b * g (y 0) := add_nonneg hA1 hB1
  have hsle : a * g (x 0) + b * g (y 0) ≤ g (a * x 0 + b * y 0) := by
    simpa [smul_eq_mul] using hg.2 hx0 hy0 ha hb hab
  have hmem : a • (g (x 0) • u) + b • (g (y 0) • v) ∈ (a * g (x 0) + b * g (y 0)) • A := by
    rcases eq_or_lt_of_le hs0 with hsz | hspos
    · have h1 : a * g (x 0) = 0 := by linarith
      have h2 : b * g (y 0) = 0 := by linarith
      have hzero : a • (g (x 0) • u) + b • (g (y 0) • v) = (0 : Fin m → ℝ) := by
        rw [smul_smul, smul_smul, h1, h2, zero_smul, zero_smul, add_zero]
      have hsz' : a * g (x 0) + b * g (y 0) = 0 := hsz.symm
      rw [hzero, hsz']
      exact Set.mem_smul_set.mpr ⟨0, hA0, by simp⟩
    · have hsne : a * g (x 0) + b * g (y 0) ≠ 0 := ne_of_gt hspos
      have e1 : (a * g (x 0) + b * g (y 0))
          * (a * g (x 0) / (a * g (x 0) + b * g (y 0))) = a * g (x 0) := by
        field_simp
      have e2 : (a * g (x 0) + b * g (y 0))
          * (b * g (y 0) / (a * g (x 0) + b * g (y 0))) = b * g (y 0) := by
        field_simp
      refine Set.mem_smul_set.mpr ⟨(a * g (x 0) / (a * g (x 0) + b * g (y 0))) • u
        + (b * g (y 0) / (a * g (x 0) + b * g (y 0))) • v,
        hA hu hv (div_nonneg hA1 hs0) (div_nonneg hB1 hs0) (by field_simp), ?_⟩
      simp only [smul_add, smul_smul]
      rw [e1, e2]
  exact smul_set_subset_smul_set_of_le hA hA0 hs0 hsle hmem

/-- The slice volume of a generalised cone: `vol (slice (profileBody A g) t) = g t ^ m · vol A`. -/
theorem volume_slice_profileBody {A : Set (Fin m → ℝ)} {g : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hgt : 0 ≤ g t) :
    volume (slice (profileBody A g) t) = ENNReal.ofReal (g t ^ m) * volume A := by
  rw [slice_profileBody A g ht, volume_smul_set_of_nonneg hgt]

/-- **The sharp profile of a generalised cone is `g` itself**, up to the constant
`vol(A)^{1/m}`.  So every nonnegative concave `g` on `[0,1]` occurs as a sharp cross-section
profile. -/
theorem profile_profileBody (hm : m ≠ 0) {A : Set (Fin m → ℝ)} {g : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hgt : 0 ≤ g t) :
    (volume (slice (profileBody A g) t)).toReal ^ (1 / (m : ℝ))
      = g t * (volume A).toReal ^ (1 / (m : ℝ)) := by
  rw [volume_slice_profileBody ht hgt, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hgt m),
    Real.mul_rpow (pow_nonneg hgt m) ENNReal.toReal_nonneg]
  congr 1
  rw [one_div, ← Real.rpow_natCast (g t) m, ← Real.rpow_mul hgt,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm), Real.rpow_one]

/-! #### The unit cube as a base -/

/-- The unit cube of `ℝ^m`. -/
private def cube (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi fun _ : Fin m => Set.Icc (0 : ℝ) 1

private theorem convex_cube : Convex ℝ (cube m) := convex_pi fun _ _ => convex_Icc 0 1

private theorem zero_mem_cube : (0 : Fin m → ℝ) ∈ cube m := fun i _ => by norm_num

private theorem volume_cube : volume (cube m) = 1 := by
  rw [cube, volume_pi_pi]
  simp [Real.volume_Icc]

/-! #### The needle weight is realised exactly -/

/-- **The needle weight `ℓ(t)^m = ((1-t)p + tq)^m` of `Arlib.needleWeight` is realised, exactly,
as the slice-volume function of a convex body in `ℝ^(m+1)`.**

So the profile that the Localization Lemma asks for is not vacuous: it is the profile of the
frustum `profileBody (unit cube) ℓ`. -/
theorem exists_convex_slice_volume_needleWeight {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ K : Set (Fin (m + 1) → ℝ), Convex ℝ K ∧
      ∀ t ∈ Icc (0 : ℝ) 1, volume (slice K t) = ENNReal.ofReal (needleWeight p q m t) := by
  refine ⟨profileBody (cube m) (fun s => (1 - s) * p + s * q),
    convex_profileBody convex_cube zero_mem_cube (concaveOn_affine_interp p q)
      (fun t ht => affine_interp_nonneg hp hq ht), fun t ht => ?_⟩
  rw [volume_slice_profileBody ht (affine_interp_nonneg hp hq ht), volume_cube, mul_one]
  rfl

/-! #### …but so is a non-affine profile: the bipyramid -/

/-- The "tent" function `t ↦ min t (1 - t)` is concave on `[0,1]`. -/
theorem concaveOn_tent : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => min t (1 - t)) := by
  refine ⟨convex_Icc 0 1, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have e : a * (1 - x) + b * (1 - y) = (a + b) - (a * x + b * y) := by ring
  rcases le_total (a * x + b * y) (1 - (a * x + b * y)) with h | h
  · rw [min_eq_left h]
    have k1 : a * min x (1 - x) ≤ a * x := mul_le_mul_of_nonneg_left (min_le_left _ _) ha
    have k2 : b * min y (1 - y) ≤ b * y := mul_le_mul_of_nonneg_left (min_le_left _ _) hb
    linarith
  · rw [min_eq_right h]
    have k1 : a * min x (1 - x) ≤ a * (1 - x) := mul_le_mul_of_nonneg_left (min_le_right _ _) ha
    have k2 : b * min y (1 - y) ≤ b * (1 - y) := mul_le_mul_of_nonneg_left (min_le_right _ _) hb
    linarith

/-- The "tent" function is **not** convex on `[0,1]`; since it is concave, it is not affine. -/
theorem not_convexOn_tent : ¬ ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => min t (1 - t)) := by
  intro h
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hkey := h.2 h01 h11 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  norm_num at hkey

/-- **Sharp Brunn pins the slice profile down to a power of a *concave* function, and no
further.**  There is a convex body in `ℝ^(m+1)` — a bipyramid over the unit cube — whose sharp
cross-section profile is the tent function `t ↦ min t (1 - t)`, which is concave but not convex,
hence not affine.

This is the precise obstruction to the claim that the sharp Brunn–Minkowski inequality
identifies the limit profile of the localisation argument as a power of an *affine* function:
it does not.  The residual gap in (G2) is the concave-to-affine reduction, spelled out in this
file's module docstring. -/
theorem exists_convex_slice_profile_not_affine (hm : m ≠ 0) :
    ∃ K : Set (Fin (m + 1) → ℝ), Convex ℝ K ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (volume (slice K t)).toReal ^ (1 / (m : ℝ)) = min t (1 - t)) ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => min t (1 - t)) ∧
      ¬ ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => min t (1 - t)) := by
  have htent : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ min t (1 - t) := by
    rintro t ⟨h0, h1⟩; exact le_min h0 (by linarith)
  refine ⟨profileBody (cube m) (fun t => min t (1 - t)),
    convex_profileBody convex_cube zero_mem_cube concaveOn_tent htent, fun t ht => ?_,
    concaveOn_tent, not_convexOn_tent⟩
  rw [profile_profileBody hm ht (htent t ht), volume_cube]
  simp

end ProfileBody

end Arlib

/-! ### Axiom check -/

#print axioms Arlib.convex_of_tendsto_hausdorffDist
#print axioms Arlib.exists_subseq_tendsto_hausdorffDist
#print axioms Arlib.exists_subseq_tendsto_hausdorffDist_convex
#print axioms Arlib.concaveOn_of_tendsto
#print axioms Arlib.nonneg_of_tendsto
#print axioms Arlib.concaveOn_limit_slice_profile
#print axioms Arlib.smul_set_subset_smul_set_of_le
#print axioms Arlib.slice_profileBody
#print axioms Arlib.convex_profileBody
#print axioms Arlib.volume_slice_profileBody
#print axioms Arlib.profile_profileBody
#print axioms Arlib.exists_convex_slice_volume_needleWeight
#print axioms Arlib.concaveOn_tent
#print axioms Arlib.not_convexOn_tent
#print axioms Arlib.exists_convex_slice_profile_not_affine
