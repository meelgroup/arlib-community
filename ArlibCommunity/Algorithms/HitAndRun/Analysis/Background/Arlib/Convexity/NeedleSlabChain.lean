/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleSlabAffine

/-!
# Every nondegenerate compact convex chain satisfies the shrinking-slab hypotheses

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` asks the `k`-th body to
lie in and span its own slab `[l k, u k]`, with `l k ≤ 0 ≤ 1 ≤ u k` and `l k → 0`, `u k → 1`.
This file shows those hypotheses are **not** a restriction on the chain: they hold for *every*
decreasing chain of compact convex bodies whose intersection contains two distinct points, once
the height functional has been normalised so that the intersection has height range exactly
`[0,1]`.

That is the difference from the fixed slab of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact`,
which asks the height range of **every** `D k` to be `[0,1]` and hence forces it to be constant
along the chain (`Arlib.exists_mem_iInter_height`) — item **(E)** of
`Arlib.Convexity.LocalizationAssembly`.

## Main results

* `Arlib.exists_slab_of_compact_chain` — the slabs.  `l k` and `u k` are the minimum and maximum
  of the height functional on `D k`; `hslab` and `hspan` are then automatic (compactness for the
  extrema, the intermediate value theorem along a chord for the spanning), and `l k → 0`,
  `u k → 1` follow from the finite-intersection property
  (`Arlib.eventually_subset_of_antitone_isCompact`) — no metric decay and no rate.
* `Arlib.exists_unitHeight_functional` — the normalisation.  For a compact convex set with two
  distinct points there is a base point in it and a linear functional for which its height range
  is exactly `[0,1]`.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` — **the composition**: from a
  decreasing chain of compact convex bodies of positive volume, with collinear intersection
  containing two distinct points, and the two localisation invariants `∫_{D k} g₁ = 0` and
  `ε · vol (D k) ≤ ∫_{D k} g₂`, the two conclusions of the equality-refined Localization Lemma,
  with a nonnegative profile whose `1/m`-th power is concave.

## What the composition still needs from the caller

Two things, both stated as explicit hypotheses rather than hidden:

* **Nondegeneracy.**  The intersection must contain two distinct points.  A chain whose
  intersection is a single point produces a degenerate needle, for which the conclusion as stated
  (a profile on `(0,1)`) is not the right shape.  `Arlib.le_diam_of_sign_separated` shows the
  intersection is forced to be nondegenerate when the positive parts of `g₁` and `g₂` are
  separated by a slab, but that is a hypothesis on the data, not a consequence of the chain.
* **The ambient type.**  `Arlib.exists_flat_cut_chain_collinear_compact` produces its chain in
  `EuclideanSpace ℝ (Fin n)` while the needle theorems live in `Fin (m+1) → ℝ`.  A
  measure-preserving transport between the two is **not** supplied here.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### The height range of a chain of compact convex bodies -/

section HeightRange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The slabs of a compact convex chain, and their shrinking.**

Let `D` be a decreasing sequence of compact convex bodies, `a` a point of their intersection, and
`φ` a linear functional for which the intersection has height range exactly `[0,1]` (heights
measured by `φ (· - a)`).  Then, taking `l k` and `u k` to be the minimum and maximum of the
height on `D k`:

* every `D k` lies in the slab `[l k, u k]` and *spans* it — the first by definition of the
  extrema, the second by the intermediate value theorem along the chord joining the two extremal
  points, which lies in `D k` by convexity;
* `l k ≤ 0 ≤ 1 ≤ u k`, because `a` and the point of height `1` belong to every `D k`;
* `l k → 0` and `u k → 1`.

The last item is where the chain's shrinking is used, and it uses only the finite-intersection
property: `{y | φ (y - a) ∈ (-ε, 1 + ε)}` is an open set containing `⋂ k, D k`, so
`Arlib.eventually_subset_of_antitone_isCompact` puts every late `D k` inside it.  No metric
decay, no Hausdorff convergence and no rate. -/
theorem exists_slab_of_compact_chain {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    {a : E} {φ : E →ₗ[ℝ] ℝ} (ha : a ∈ ⋂ k, D k)
    (hone : ∃ q ∈ ⋂ k, D k, φ (q - a) = 1)
    (hIle : ∀ y ∈ ⋂ k, D k, φ (y - a) ∈ Icc (0 : ℝ) 1) :
    ∃ l u : ℕ → ℝ, (∀ k, l k ≤ 0) ∧ (∀ k, 1 ≤ u k) ∧
      (∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k)) ∧
      (∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto u atTop (𝓝 1) := by
  classical
  set h : E → ℝ := fun y => φ (y - a) with hhdef
  have hcont : Continuous h :=
    (φ.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
  obtain ⟨q, hqI, hq1⟩ := hone
  have haD : ∀ k, a ∈ D k := fun k => Set.mem_iInter.mp ha k
  have hqD : ∀ k, q ∈ D k := fun k => Set.mem_iInter.mp hqI k
  have himg : ∀ k, IsCompact (h '' D k) := fun k => (hDcomp k).image hcont
  have himgne : ∀ k, (h '' D k).Nonempty := fun k => ⟨h a, ⟨a, haD k, rfl⟩⟩
  refine ⟨fun k => sInf (h '' D k), fun k => sSup (h '' D k), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    [skip; skip; skip; skip; skip; skip]
  all_goals {
    have hlmem : ∀ k, sInf (h '' D k) ∈ h '' D k := fun k => (himg k).sInf_mem (himgne k)
    have humem : ∀ k, sSup (h '' D k) ∈ h '' D k := fun k => (himg k).sSup_mem (himgne k)
    have hbddB : ∀ k, BddBelow (h '' D k) := fun k => (himg k).bddBelow
    have hbddA : ∀ k, BddAbove (h '' D k) := fun k => (himg k).bddAbove
    have hslab : ∀ k, ∀ y ∈ D k, h y ∈ Icc (sInf (h '' D k)) (sSup (h '' D k)) := fun k y hy =>
      ⟨csInf_le (hbddB k) ⟨y, hy, rfl⟩, le_csSup (hbddA k) ⟨y, hy, rfl⟩⟩
    have hha : h a = 0 := by simp [hhdef]
    have hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k →
        -ε < sInf (h '' D k) ∧ sSup (h '' D k) < 1 + ε := by
      intro ε hε
      have hopen : IsOpen (h ⁻¹' Ioo (-ε) (1 + ε)) := isOpen_Ioo.preimage hcont
      have hsub : (⋂ k, D k) ⊆ h ⁻¹' Ioo (-ε) (1 + ε) := by
        intro y hy
        obtain ⟨h1, h2⟩ := hIle y hy
        exact ⟨by linarith, by linarith⟩
      obtain ⟨N, hN⟩ := eventually_subset_of_antitone_isCompact hDcomp hDmono hopen hsub
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨p, hp, hpl⟩ := hlmem k
      obtain ⟨r, hr, hru⟩ := humem k
      exact ⟨by rw [← hpl]; exact (hN k hk hp).1, by rw [← hru]; exact (hN k hk hr).2⟩
    first
      | -- `l k ≤ 0`
        exact fun k => hha ▸ (hslab k a (haD k)).1
      | -- `1 ≤ u k`
        exact fun k => hq1 ▸ (hslab k q (hqD k)).2
      | -- `hslab`
        exact hslab
      | -- `hspan`
        (intro k t ht
         obtain ⟨p, hp, hpl⟩ := hlmem k
         obtain ⟨r, hr, hru⟩ := humem k
         have hfmem : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (r - p) ∈ D k := by
           intro s hs
           have heq : p + s • (r - p) = (1 - s) • p + s • r := by module
           rw [heq]
           exact hDconv k hp hr (by linarith [hs.2]) hs.1 (by ring)
         have hfc : ContinuousOn (fun s : ℝ => h (p + s • (r - p))) (Icc 0 1) :=
           (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
         have h0 : h (p + (0 : ℝ) • (r - p)) = sInf (h '' D k) := by simpa using hpl
         have h1 : h (p + (1 : ℝ) • (r - p)) = sSup (h '' D k) := by
           simpa [add_sub_cancel] using hru
         have hiv := intermediate_value_Icc (zero_le_one (α := ℝ)) hfc
         rw [h0, h1] at hiv
         obtain ⟨s, hs, hsv⟩ := hiv ht
         exact ⟨p + s • (r - p), hfmem s hs, hsv⟩)
      | -- `l k → 0`
        (rw [Metric.tendsto_atTop]
         intro ε hε
         obtain ⟨N, hN⟩ := hbound ε hε
         refine ⟨N, fun k hk => ?_⟩
         have h1 := (hN k hk).1
         have h2 : sInf (h '' D k) ≤ 0 := hha ▸ (hslab k a (haD k)).1
         rw [Real.dist_eq, sub_zero, abs_of_nonpos h2]
         linarith)
      | -- `u k → 1`
        (rw [Metric.tendsto_atTop]
         intro ε hε
         obtain ⟨N, hN⟩ := hbound ε hε
         refine ⟨N, fun k hk => ?_⟩
         have h1 := (hN k hk).2
         have h2 : (1 : ℝ) ≤ sSup (h '' D k) := hq1 ▸ (hslab k q (hqD k)).2
         rw [Real.dist_eq, abs_of_nonneg (by linarith)]
         linarith) }

end HeightRange

/-! ### Normalising the limit body to unit height -/

section Normalisation

variable {m : ℕ}

/-- **A compact convex set with two distinct points has unit height in a suitable frame.**

There is a base point `a` of `S` and a linear functional `φ` for which the height range
`φ '' (S - a)` is exactly `[0,1]`: take any coordinate `j` in which `q - p` does not vanish,
scale the `j`-th projection so that it sends `q - p` to `1`, then translate the base point to the
minimiser and rescale by the total height, which is at least `1` and hence nonzero.

This is the only normalisation the shrinking-slab needle theorem needs, and it is available for
*any* nondegenerate compact convex limit body — no collinearity is used here. -/
theorem exists_unitHeight_functional {S : Set (Fin (m + 1) → ℝ)} (hScomp : IsCompact S)
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ∃ (a : Fin (m + 1) → ℝ) (φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ), a ∈ S ∧
      (∃ z ∈ S, φ (z - a) = 1) ∧ ∀ y ∈ S, φ (y - a) ∈ Icc (0 : ℝ) 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), q j - p j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hpq (funext fun j => by have := hcon j; linarith)
  set ψ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := (q j - p j)⁻¹ • LinearMap.proj j with hψdef
  have hψapp : ∀ y : Fin (m + 1) → ℝ, ψ y = (q j - p j)⁻¹ * y j := fun y => rfl
  have hψw : ψ (q - p) = 1 := by
    rw [hψapp]
    simp only [Pi.sub_apply]
    exact inv_mul_cancel₀ hj
  have hcontψ : Continuous fun y : Fin (m + 1) → ℝ => ψ y :=
    ψ.continuous_of_finiteDimensional
  have himg : IsCompact ((fun y => ψ y) '' S) := hScomp.image hcontψ
  have himgne : ((fun y => ψ y) '' S).Nonempty := ⟨ψ p, ⟨p, hp, rfl⟩⟩
  obtain ⟨a, haS, hamin⟩ := himg.sInf_mem himgne
  obtain ⟨z, hzS, hzmax⟩ := himg.sSup_mem himgne
  have hamin' : ψ a = sInf ((fun y => ψ y) '' S) := hamin
  have hzmax' : ψ z = sSup ((fun y => ψ y) '' S) := hzmax
  have hle : ∀ y ∈ S, ψ a ≤ ψ y ∧ ψ y ≤ ψ z := by
    intro y hy
    constructor
    · rw [hamin']; exact csInf_le himg.bddBelow ⟨y, hy, rfl⟩
    · rw [hzmax']; exact le_csSup himg.bddAbove ⟨y, hy, rfl⟩
  have hgap : (1 : ℝ) ≤ ψ z - ψ a := by
    have h1 := (hle p hp).1
    have h2 := (hle q hq).2
    have h3 : ψ q - ψ p = 1 := by rw [← hψw, map_sub]
    linarith
  have hgap0 : (0 : ℝ) < ψ z - ψ a := by linarith
  refine ⟨a, (ψ z - ψ a)⁻¹ • ψ, haS, ⟨z, hzS, ?_⟩, fun y hy => ?_⟩
  · show (ψ z - ψ a)⁻¹ * ψ (z - a) = 1
    rw [map_sub]
    exact inv_mul_cancel₀ hgap0.ne'
  · obtain ⟨h1, h2⟩ := hle y hy
    show (ψ z - ψ a)⁻¹ * ψ (y - a) ∈ Icc (0 : ℝ) 1
    rw [map_sub]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hgap0.le) (by linarith)
    · rw [inv_mul_le_iff₀ hgap0]
      linarith

end Normalisation

/-! ### The composition -/

section Composition

variable {m : ℕ}

/-- **The localisation needle from an arbitrary nondegenerate compact convex chain.**

Every hypothesis of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab`
about the *slab* is discharged here: the height functional is produced by
`Arlib.exists_unitHeight_functional` and the slabs by `Arlib.exists_slab_of_compact_chain`.  What
is left to ask of the chain is exactly what a localisation chain provides —

* decreasing compact convex bodies of positive volume (`Arlib.exists_flat_cut_chain_collinear_compact`),
* a collinear intersection (same),
* the two mass invariants `∫_{D k} g₁ = 0` and `ε · vol (D k) ≤ ∫_{D k} g₂`
  (`Arlib.exists_flat_cut_chain_collinear_compact_ge`),

— together with **nondegeneracy** of the limit body, which is a hypothesis on the data and not a
consequence of the chain (see the module docstring).

No hypothesis relates the height range of `D k` to that of `D 0`: the chain may shrink in every
direction, including along the needle.

The profile is delivered **supported in `[0,1]` and integrable**, not merely nonnegative and
concave-to-the-`1/m`: both come from the origin
`Arlib.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab` and are threaded through unchanged,
since every step of the transport reuses the *same* `W`.  Consumers need both — a Bochner integral
of a non-integrable nonnegative function is `0`, not `+∞`, so a monotone comparison of needle
masses is false without integrability, and `∫ t : ℝ` is not `∫ t in [α,β]` without the support. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain (hm : m ≠ 0)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ ⋂ k, D k) (hq : q ∈ ⋂ k, D k) (hpq : p ≠ q)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hIcomp : IsCompact (⋂ k, D k) :=
    (hDcomp 0).of_isClosed_subset (isClosed_iInter fun k => (hDcomp k).isClosed)
      (Set.iInter_subset _ 0)
  obtain ⟨a, φ, haS, hone, hIle⟩ := exists_unitHeight_functional hIcomp hp hq hpq
  obtain ⟨l, u, hl0, hu1, hslab, hspan, hl, hu⟩ :=
    exists_slab_of_compact_chain hDcomp hDconv hDmono haS hone hIle
  obtain ⟨b, v, W, -, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab hm hDconv hDcomp hDmono
      hDpos hl0 hu1 hslab hspan hl hu hcol hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

end Composition

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.exists_slab_of_compact_chain
#print axioms Arlib.exists_unitHeight_functional
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain
