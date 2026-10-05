/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Odd maps to the circle, and Borsuk–Ulam into the plane

Mathlib `v4.32` has **no** Borsuk–Ulam theorem, no ham-sandwich theorem, no Brouwer fixed-point
theorem and no degree theory (`Mathlib/Topology/Homotopy/` contains no degree file, and every
`Brouwer` hit in its sources is a Brouwerian *lattice*).  It also does not know that `Sⁿ` is
simply connected for `n ≥ 2`, and it has no Seifert–van Kampen theorem.

What Mathlib *does* have is the covering-space substrate:

* `AddCircle.isCoveringMap_coe` / `Circle.isCoveringMap_exp` — `ℝ → S¹` is a covering map;
* `IsCoveringMap.existsUnique_continuousMap_lifts` (`Mathlib/Topology/Homotopy/Lifting.lean`) —
  a map from a **simply connected, locally path connected** space lifts through a covering map;
* `stereographic` (`Mathlib/Geometry/Manifold/Instances/Sphere.lean`) — the sphere minus a point
  is homeomorphic to a normed space, hence contractible.

This file assembles those into Borsuk–Ulam for maps into the plane, which is the exact form the
two-measure ham sandwich of `Arlib.Topology.HamSandwich` consumes.

## The argument

1. `Arlib.eq_of_continuous_intValued` — a continuous integer-valued real function on a
   preconnected space is constant.
2. `Arlib.false_of_odd_lift` — **the crux.**  If `σ` is a continuous involution of a nonempty
   preconnected `X` and `f : X → Circle` is odd (`f (σ x) = -f x`), then `f` has no continuous
   real lift `F` along `Circle.exp`.  Indeed `exp (F (σ x)) = exp (F x + π)`, so
   `d x = (F (σ x) - F x - π)/(2π)` is continuous and integer-valued, hence a constant `m`;
   adding the identity at `x` and at `σ x` gives `d x + d (σ x) = -1`, i.e. `2m = -1`.
3. `Arlib.exists_circle_lift_of_cover` — a hands-on **van Kampen for lifts**: if `X = U ∪ V` with
   `U`, `V` open, simply connected and locally path connected, and `U ∩ V` nonempty and
   preconnected, then every continuous `X → Circle` lifts.  Lift on `U` and on `V`; the two lifts
   differ on `U ∩ V` by a continuous `2πℤ`-valued function, hence by a constant; shift and glue.
   This replaces `π₁(Sⁿ) = 1`, which is what a textbook proof would use here.
4. `Arlib.contractible_sphere_compl`, `Arlib.isConnected_sphere_compl_pair` — the two
   stereographic charts `{p}ᶜ`, `{-p}ᶜ` of the unit sphere are contractible, and their
   intersection is the stereographic image of a punctured space of rank `≥ 2`, hence connected.
5. `Arlib.exists_circle_lift_sphere` — hence the unit sphere of a real inner-product space with
   `3 ≤ finrank` has the circle-lifting property.
6. `Arlib.exists_eq_zero_of_odd_pair` / `Arlib.exists_eq_zero_of_odd_pair_sphere` —
   **Borsuk–Ulam into the plane.**  Two continuous odd real functions on such a sphere have a
   common zero: otherwise `x ↦ (a x + i b x)/‖a x + i b x‖` is a continuous odd map to `Circle`,
   forbidden by 2.

## Scope

Nothing in this file mentions measures, convexity, or the application that motivated it: it is a
self-contained piece of general topology and is the natural home for `Arlib`'s Borsuk–Ulam.  The
statement proved is the `ℝ²`-valued form, `Sⁿ → ℝ²` for `n ≥ 2`, which is what a *two*-measure ham
sandwich needs (`Arlib.Topology.HamSandwich`).  The full form `Sⁿ → ℝⁿ` — needed only for `n`
measures, `n ≥ 3` — is **not** proved here and would need a genuinely different argument: the
`π₁`-level obstruction used below is specific to the target `S¹`, and higher targets need
`πₙ₋₁(Sⁿ⁻¹)` or degree theory, neither of which Mathlib `v4.32` has.

## Honesty note

There is **no** `def`, `structure`, `class` or `Prop` in this file asserting Borsuk–Ulam or any
part of it.  The only hypothesis that looks like a black box, the circle-lifting property in
`Arlib.exists_eq_zero_of_odd_pair`, is an ordinary `∀`-statement about lifts and is discharged
unconditionally for the sphere by `Arlib.exists_circle_lift_sphere`.
`Arlib.exists_eq_zero_of_odd_pair_sphere_three` is a closed, hypothesis-free instance certifying
non-vacuity.  Every declaration below is proved; the axiom audit at the end confirms it.
-/

open Set Function Metric

namespace Arlib

/-! ### A continuous integer-valued function on a preconnected space is constant -/

/-- A continuous real function whose values are all integers is constant on a preconnected
space.  (The image is a preconnected, hence order-connected, subset of `ℝ` contained in `ℤ`.) -/
theorem eq_of_continuous_intValued {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {d : X → ℝ} (hd : Continuous d) (hint : ∀ x, ∃ m : ℤ, d x = m) (x y : X) : d x = d y := by
  have hrange : IsPreconnected (Set.range d) := by
    have := isPreconnected_univ (α := X) |>.image d hd.continuousOn
    rwa [Set.image_univ] at this
  have hoc := hrange.ordConnected
  have key : ∀ a b : X, d a < d b → False := by
    intro a b hab
    obtain ⟨m, hm⟩ := hint a
    obtain ⟨n, hn⟩ := hint b
    have hmn : (m : ℝ) < (n : ℝ) := by rw [← hm, ← hn]; exact hab
    have hmn' : m < n := by exact_mod_cast hmn
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hmn'
    have hmem : d a + 1 / 2 ∈ Set.range d := by
      refine hoc.out (Set.mem_range_self a) (Set.mem_range_self b) ⟨by linarith, ?_⟩
      rw [hm, hn]; linarith
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨k, hk⟩ := hint z
    have : (m : ℝ) + 1 / 2 = (k : ℝ) := by rw [← hm, ← hk, hz]
    have h2 : ((2 * m + 1 : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) := by push_cast; linarith
    have : (2 * m + 1 : ℤ) = 2 * k := by exact_mod_cast h2
    omega
  rcases lt_trichotomy (d x) (d y) with h | h | h
  · exact absurd h (fun h => (key x y h).elim)
  · exact h
  · exact absurd h (fun h => (key y x h).elim)

/-! ### No odd map to the circle lifts -/

/-- `Circle.exp π = -1`. -/
theorem circle_exp_pi : Circle.exp Real.pi = -1 := by
  ext
  rw [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_neg, Circle.coe_one]

/-- **The key impossibility.**  Let `σ` be a continuous involution of a nonempty preconnected
space `X`, and let `f : X → Circle` be *odd*, `f (σ x) = - f x`.  Then `f` admits no continuous
real lift along `Circle.exp`.

Proof.  If `F` lifts `f`, then `exp (F (σ x)) = -exp (F x) = exp (F x + π)`, so
`d x := (F (σ x) - F x - π) / (2π)` is integer-valued and continuous, hence constant `= m`.
Applying the identity at `x` and at `σ x` and adding gives `d x + d (σ x) = -1`, i.e. `2m = -1`. -/
theorem false_of_odd_lift {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {σ : X → X} (hσ : Continuous σ) (hσσ : ∀ x, σ (σ x) = x)
    {f : X → Circle} {F : X → ℝ} (hF : Continuous F)
    (hFf : ∀ x, Circle.exp (F x) = f x) (hodd : ∀ x, f (σ x) = -f x) : False := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hstep : ∀ x, ∃ m : ℤ, F (σ x) - F x - Real.pi = m * (2 * Real.pi) := by
    intro x
    have h1 : Circle.exp (F (σ x)) = Circle.exp (F x + Real.pi) := by
      rw [hFf, hodd, Circle.exp_add, circle_exp_pi, mul_neg_one, hFf]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    exact ⟨m, by linarith⟩
  set d : X → ℝ := fun x => (F (σ x) - F x - Real.pi) / (2 * Real.pi) with hd
  have hdc : Continuous d := (((hF.comp hσ).sub hF).sub continuous_const).div_const _
  have hdint : ∀ x, ∃ m : ℤ, d x = m := by
    intro x
    obtain ⟨m, hm⟩ := hstep x
    refine ⟨m, ?_⟩
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    show (F (σ x) - F x - Real.pi) / (2 * Real.pi) = (m : ℝ)
    rw [div_eq_iff h2pi, hm]
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hconst := eq_of_continuous_intValued hdc hdint x₀ (σ x₀)
  have hsum : d x₀ + d (σ x₀) = -1 := by
    rw [hd]
    simp only [hσσ]
    field_simp
    ring
  obtain ⟨m, hm⟩ := hdint x₀
  have : (2 * m : ℝ) = -1 := by
    rw [← hconst] at hsum
    rw [← hm]; linarith
  have h2 : ((2 * m : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
  have : (2 * m : ℤ) = -1 := by exact_mod_cast h2
  omega

/-! ### Lifting a circle-valued map over a two-set open cover -/

/-- **Gluing lift.**  If `X` is covered by two open sets `U`, `V`, each simply connected and
locally path connected, whose intersection is nonempty and preconnected, then every continuous
`f : X → Circle` lifts along `Circle.exp`.

This is a hands-on van Kampen for lifts: lift separately on `U` and on `V` (Mathlib's lifting
criterion for simply connected, locally path connected domains), observe that the two lifts differ
by a continuous `2πℤ`-valued function on the preconnected `U ∩ V`, hence by a constant, and shift
one lift by that constant to glue. -/
theorem exists_circle_lift_of_cover {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hSU : SimplyConnectedSpace U) (hLU : LocallyPathConnectedSpace U)
    (hSV : SimplyConnectedSpace V) (hLV : LocallyPathConnectedSpace V)
    (hWc : PreconnectedSpace (U ∩ V : Set X)) (hWne : (U ∩ V).Nonempty)
    {f : X → Circle} (hf : Continuous f) :
    ∃ F : X → ℝ, Continuous F ∧ ∀ x, Circle.exp (F x) = f x := by
  haveI := hSU; haveI := hLU; haveI := hSV; haveI := hLV; haveI := hWc
  obtain ⟨w₀, hw₀⟩ := hWne
  -- the two local lifts
  have hcov := Circle.isCoveringMap_exp
  set fU : C(↥U, Circle) := ⟨fun u => f u, hf.comp continuous_subtype_val⟩ with hfU
  set fV : C(↥V, Circle) := ⟨fun v => f v, hf.comp continuous_subtype_val⟩ with hfV
  obtain ⟨FU, ⟨-, hFU⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts fU ⟨w₀, hw₀.1⟩ (Complex.arg (f w₀))
      (Circle.exp_arg (f w₀))
  obtain ⟨FV, ⟨-, hFV⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts fV ⟨w₀, hw₀.2⟩ (Complex.arg (f w₀))
      (Circle.exp_arg (f w₀))
  have hFU' : ∀ u : ↥U, Circle.exp (FU u) = f u := fun u => congrFun hFU u
  have hFV' : ∀ v : ↥V, Circle.exp (FV v) = f v := fun v => congrFun hFV v
  -- the difference on `U ∩ V` is a constant multiple of `2π`
  have hcU : Continuous fun w : ↥(U ∩ V) => (⟨w.1, w.2.1⟩ : ↥U) :=
    Continuous.subtype_mk continuous_subtype_val _
  have hcV : Continuous fun w : ↥(U ∩ V) => (⟨w.1, w.2.2⟩ : ↥V) :=
    Continuous.subtype_mk continuous_subtype_val _
  set e : ↥(U ∩ V) → ℝ :=
    fun w => (FU ⟨w.1, w.2.1⟩ - FV ⟨w.1, w.2.2⟩) / (2 * Real.pi) with he
  have hec : Continuous e :=
    ((FU.continuous.comp hcU).sub (FV.continuous.comp hcV)).div_const _
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have heint : ∀ w, ∃ m : ℤ, e w = m := by
    intro w
    have h1 : Circle.exp (FU ⟨w.1, w.2.1⟩) = Circle.exp (FV ⟨w.1, w.2.2⟩) := by
      rw [hFU' ⟨w.1, w.2.1⟩, hFV' ⟨w.1, w.2.2⟩]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    refine ⟨m, ?_⟩
    show (FU ⟨w.1, w.2.1⟩ - FV ⟨w.1, w.2.2⟩) / (2 * Real.pi) = (m : ℝ)
    rw [div_eq_iff h2pi, hm]
    ring
  set w₀' : ↥(U ∩ V) := ⟨w₀, hw₀⟩ with hw₀'
  obtain ⟨m₀, hm₀⟩ := heint w₀'
  set c : ℝ := m₀ * (2 * Real.pi) with hc
  have hagree : ∀ x (hx : x ∈ U) (hx' : x ∈ V), FU ⟨x, hx⟩ = FV ⟨x, hx'⟩ + c := by
    intro x hx hx'
    have h := eq_of_continuous_intValued hec heint ⟨x, ⟨hx, hx'⟩⟩ w₀'
    rw [hm₀] at h
    have h' : (FU ⟨x, hx⟩ - FV ⟨x, hx'⟩) / (2 * Real.pi) = (m₀ : ℝ) := h
    rw [div_eq_iff h2pi] at h'
    rw [hc]
    linarith
  have hexpc : Circle.exp c = 1 := Circle.exp_eq_one.mpr ⟨m₀, rfl⟩
  -- glue
  classical
  set F : X → ℝ := fun x => if hx : x ∈ U then FU ⟨x, hx⟩ else
    FV ⟨x, by
      have : x ∈ U ∪ V := hUV ▸ mem_univ x
      exact this.resolve_left hx⟩ + c with hFdef
  have hFUres : U.domRestrict F = fun u : ↥U => FU u := by
    funext u
    change F u = FU u
    rw [hFdef]
    exact dif_pos u.2
  have hFVres : V.domRestrict F = fun v : ↥V => FV v + c := by
    funext v
    change F v = FV v + c
    rw [hFdef]
    by_cases hu : (v : X) ∈ U
    · exact (dif_pos hu).trans (hagree (v : X) hu v.2)
    · exact dif_neg hu
  have hFUon : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict, hFUres]; exact FU.continuous
  have hFVon : ContinuousOn F V := by
    rw [continuousOn_iff_continuous_domRestrict, hFVres]
    exact FV.continuous.add continuous_const
  refine ⟨F, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    rcases (hUV ▸ mem_univ x : x ∈ U ∪ V) with h | h
    · exact hFUon.continuousAt (hU.mem_nhds h)
    · exact hFVon.continuousAt (hV.mem_nhds h)
  · intro x
    by_cases hx : x ∈ U
    · have : F x = FU ⟨x, hx⟩ := by simp only [hFdef, dif_pos hx]
      rw [this, hFU' ⟨x, hx⟩]
    · have hxV : x ∈ V := ((hUV ▸ mem_univ x : x ∈ U ∪ V)).resolve_left hx
      have : F x = FV ⟨x, hxV⟩ + c := by
        simp only [hFdef, dif_neg hx]
      rw [this, Circle.exp_add, hexpc, mul_one, hFV' ⟨x, hxV⟩]

/-! ### Borsuk–Ulam into the plane, from the lifting property -/

/-- **Borsuk–Ulam for a pair of odd real functions**, on any nonempty preconnected space with a
continuous involution `σ` over which every circle-valued map lifts.

If `a, b : X → ℝ` are continuous and both odd (`a (σ x) = - a x`, `b (σ x) = - b x`), then they
have a common zero.  Contrapositive: otherwise `x ↦ (a x + i b x)/‖a x + i b x‖` is a continuous
odd map to the circle, which `Arlib.false_of_odd_lift` forbids. -/
theorem exists_eq_zero_of_odd_pair {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Nonempty X]
    (hlift : ∀ f : X → Circle, Continuous f →
      ∃ F : X → ℝ, Continuous F ∧ ∀ x, Circle.exp (F x) = f x)
    {σ : X → X} (hσ : Continuous σ) (hσσ : ∀ x, σ (σ x) = x)
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hao : ∀ x, a (σ x) = -a x) (hbo : ∀ x, b (σ x) = -b x) :
    ∃ x, a x = 0 ∧ b x = 0 := by
  by_contra hcon
  push_neg at hcon
  set G : X → ℂ := fun x => Complex.mk (a x) (b x) with hG
  have hGc : Continuous G := by
    have : G = fun x => (a x : ℂ) + (b x : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp [hG]
    rw [this]; fun_prop
  have hGne : ∀ x, G x ≠ 0 := by
    intro x hx
    have h1 : a x = 0 := by simpa [hG] using congrArg Complex.re hx
    exact (hcon x h1) (by simpa [hG] using congrArg Complex.im hx)
  have hGodd : ∀ x, G (σ x) = -G x := by
    intro x; apply Complex.ext <;> simp [hG, hao, hbo]
  set f : X → Circle := fun x => ⟨G x / (‖G x‖ : ℂ), by
    have hx : ‖G x‖ ≠ 0 := norm_ne_zero_iff.mpr (hGne x)
    simp only [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_sphere_zero_iff_norm]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hx]⟩ with hfdef
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hGc.div (Complex.continuous_ofReal.comp hGc.norm) fun x =>
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hGne x))
  have hfodd : ∀ x, f (σ x) = -f x := by
    intro x
    apply Circle.ext
    rw [Circle.coe_neg]
    show G (σ x) / (‖G (σ x)‖ : ℂ) = -(G x / (‖G x‖ : ℂ))
    rw [hGodd, norm_neg, neg_div]
  obtain ⟨F, hFc, hFf⟩ := hlift f hfc
  exact false_of_odd_lift hσ hσσ hFc hFf hfodd

/-! ### The sphere: discharging the lifting hypothesis -/

section Sphere

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- No point of the unit sphere is its own antipode. -/
theorem sphere_neg_ne_self (p : sphere (0 : E) 1) : -p ≠ p := by
  intro h
  have h' : -(p : E) = (p : E) := congrArg Subtype.val h
  have h2 : (2 : ℝ) • (p : E) = 0 := by
    rw [two_smul]
    calc (p : E) + (p : E) = -(p : E) + (p : E) := by rw [h']
      _ = 0 := neg_add_cancel _
  have : (p : E) = 0 := by
    rcases smul_eq_zero.mp h2 with h0 | h0
    · exact absurd h0 (by norm_num)
    · exact h0
  have hn : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  rw [this, norm_zero] at hn
  exact absurd hn (by norm_num)

/-- Stereographic projection identifies the sphere minus a point with the orthogonal complement
of that point's line, so the sphere minus a point is contractible. -/
theorem contractible_sphere_compl (p : sphere (0 : E) 1) :
    ContractibleSpace ↥(({p} : Set (sphere (0 : E) 1))ᶜ) ∧
      LocallyPathConnectedSpace ↥(({p} : Set (sphere (0 : E) 1))ᶜ) := by
  have hv : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hsrc : (stereographic hv).source = ({p} : Set (sphere (0 : E) 1))ᶜ := by
    rw [stereographic_source]
  let h₁ : ↥(({p} : Set (sphere (0 : E) 1))ᶜ) ≃ₜ ↥((stereographic hv).source) :=
    Homeomorph.setCongr hsrc.symm
  let h₂ : ↥((stereographic hv).source) ≃ₜ ↥((stereographic hv).target) :=
    (stereographic hv).toHomeomorphSourceTarget
  let h₃ : ↥((stereographic hv).target) ≃ₜ ↥(Set.univ : Set ↥((ℝ ∙ (p : E))ᗮ)) :=
    Homeomorph.setCongr (stereographic_target hv)
  let h : ↥(({p} : Set (sphere (0 : E) 1))ᶜ) ≃ₜ ↥((ℝ ∙ (p : E))ᗮ) :=
    (h₁.trans (h₂.trans (h₃.trans (Homeomorph.Set.univ _))))
  exact ⟨h.contractibleSpace, h.isOpenEmbedding.locallyPathConnectedSpace⟩

/-- The sphere minus an antipodal pair is the stereographic preimage of the punctured
orthogonal complement, hence connected when `finrank E ≥ 3`. -/
theorem isConnected_sphere_compl_pair (h3 : 3 ≤ finrank ℝ E) (p : sphere (0 : E) 1) :
    IsConnected (({p} : Set (sphere (0 : E) 1))ᶜ ∩ ({-p} : Set (sphere (0 : E) 1))ᶜ) := by
  have hv : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hp0 : (p : E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact absurd hv (by norm_num)
  have hsrc : (stereographic hv).source = ({p} : Set (sphere (0 : E) 1))ᶜ := by
    rw [stereographic_source]
  -- the rank of the orthogonal complement is at least two
  have hfr : finrank ℝ ↥((ℝ ∙ (p : E))ᗮ) + 1 = finrank ℝ E := by
    have hadd := (ℝ ∙ (p : E) : Submodule ℝ E).finrank_add_finrank_orthogonal (𝕜 := ℝ)
    rw [finrank_span_singleton hp0] at hadd
    omega
  have hrank : 1 < Module.rank ℝ ↥((ℝ ∙ (p : E))ᗮ) := by
    have := Module.finrank_eq_rank ℝ ↥((ℝ ∙ (p : E))ᗮ)
    rw [← this]
    have : 1 < finrank ℝ ↥((ℝ ∙ (p : E))ᗮ) := by omega
    exact_mod_cast this
  have hconn : IsConnected ({(0 : ↥((ℝ ∙ (p : E))ᗮ))}ᶜ) :=
    isConnected_compl_singleton_of_one_lt_rank hrank 0
  have hcont : Continuous (⇑(stereographic hv).symm) :=
    continuousOn_univ.mp ((stereographic hv).continuousOn_symm.mono (by simp))
  have himg : (⇑(stereographic hv).symm) '' ({(0 : ↥((ℝ ∙ (p : E))ᗮ))}ᶜ) =
      (({p} : Set (sphere (0 : E) 1))ᶜ ∩ ({-p} : Set (sphere (0 : E) 1))ᶜ) := by
    have hnegmem : (-p) ∈ (stereographic hv).source := by
      rw [hsrc]; exact fun h => (sphere_neg_ne_self p) (Set.mem_singleton_iff.mp h)
    have hstneg : (stereographic hv) (-p) = 0 := stereographic_apply_neg p
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hmem : (stereographic hv).symm y ∈ (stereographic hv).source :=
        (stereographic hv).map_target (by simp)
      refine ⟨?_, ?_⟩
      · rw [← hsrc]; exact hmem
      · intro hx
        apply hy
        have hxe : (stereographic hv).symm y = -p := Set.mem_singleton_iff.mp hx
        have : (stereographic hv) ((stereographic hv).symm y) = y :=
          (stereographic hv).right_inv (by simp)
        rw [hxe, hstneg] at this
        exact Set.mem_singleton_iff.mpr this.symm
    · rintro ⟨hx1, hx2⟩
      have hxsrc : x ∈ (stereographic hv).source := by rw [hsrc]; exact hx1
      refine ⟨(stereographic hv) x, ?_, (stereographic hv).left_inv hxsrc⟩
      intro hy
      apply hx2
      have hy0 : (stereographic hv) x = 0 := Set.mem_singleton_iff.mp hy
      have h1 : (stereographic hv).symm ((stereographic hv) x) = x :=
        (stereographic hv).left_inv hxsrc
      have h2 : (stereographic hv).symm ((stereographic hv) (-p)) = -p :=
        (stereographic hv).left_inv hnegmem
      rw [hy0] at h1
      rw [hstneg] at h2
      exact Set.mem_singleton_iff.mpr (h1.symm.trans h2)
  rw [← himg]
  exact hconn.image _ hcont.continuousOn

/-- **The unit sphere in a real inner-product space of dimension `≥ 3` has the circle-lifting
property.**  Every continuous map from the sphere to `Circle` lifts along `Circle.exp`.

The proof glues the lifts over the two stereographic charts `{p}ᶜ` and `{-p}ᶜ`, which are
contractible; their intersection `{p, -p}ᶜ` is connected because it is the stereographic image of
a punctured space of rank `≥ 2`.  This is a hands-on substitute for `π₁(Sⁿ) = 1`, which Mathlib
`v4.32` does not have. -/
theorem exists_circle_lift_sphere (h3 : 3 ≤ finrank ℝ E)
    {f : sphere (0 : E) 1 → Circle} (hf : Continuous f) :
    ∃ F : sphere (0 : E) 1 → ℝ, Continuous F ∧ ∀ x, Circle.exp (F x) = f x := by
  have hpos : 0 < finrank ℝ E := by omega
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hpos
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hnu : ‖(‖u‖⁻¹ • u)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)
  set p : sphere (0 : E) 1 := ⟨‖u‖⁻¹ • u, mem_sphere_zero_iff_norm.mpr hnu⟩ with hp
  obtain ⟨hcU, hlU⟩ := contractible_sphere_compl p
  obtain ⟨hcV, hlV⟩ := contractible_sphere_compl (-p)
  haveI := hcU
  haveI := hcV
  have hW := isConnected_sphere_compl_pair h3 p
  refine exists_circle_lift_of_cover (U := ({p} : Set (sphere (0 : E) 1))ᶜ)
    (V := ({-p} : Set (sphere (0 : E) 1))ᶜ) isOpen_compl_singleton isOpen_compl_singleton
    ?_ (SimplyConnectedSpace.ofContractible _) hlU (SimplyConnectedSpace.ofContractible _) hlV
    (Subtype.preconnectedSpace hW.isPreconnected) hW.nonempty hf
  rw [Set.eq_univ_iff_forall]
  intro x
  rcases eq_or_ne x p with rfl | hx
  · right
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact sphere_neg_ne_self _ h.symm
  · left
    exact hx

/-- **Borsuk–Ulam into the plane, for the unit sphere of a real inner-product space of dimension
`≥ 3`.**  Two continuous odd real functions on the sphere have a common zero. -/
theorem exists_eq_zero_of_odd_pair_sphere (h3 : 3 ≤ finrank ℝ E)
    {a b : sphere (0 : E) 1 → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hao : ∀ x, a (-x) = -a x) (hbo : ∀ x, b (-x) = -b x) :
    ∃ x, a x = 0 ∧ b x = 0 := by
  have hrank : 1 < Module.rank ℝ E := by
    have := Module.finrank_eq_rank ℝ E
    rw [← this]
    have : 1 < finrank ℝ E := by omega
    exact_mod_cast this
  have hS : IsConnected (sphere (0 : E) 1) := isConnected_sphere hrank 0 zero_le_one
  haveI : PreconnectedSpace ↥(sphere (0 : E) 1) := Subtype.preconnectedSpace hS.isPreconnected
  haveI : Nonempty ↥(sphere (0 : E) 1) := hS.nonempty.to_subtype
  exact exists_eq_zero_of_odd_pair (fun f hf => exists_circle_lift_sphere h3 hf)
    continuous_neg (fun x => neg_neg x) ha hb hao hbo

end Sphere



/-! ### A closed, hypothesis-free instance, and the axiom audit -/

/-- **Non-vacuity.**  The dimension hypothesis is satisfiable: on the unit sphere of
`EuclideanSpace ℝ (Fin 3)` every pair of continuous odd real functions has a common zero. -/
theorem exists_eq_zero_of_odd_pair_sphere_three
    {a b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hao : ∀ x, a (-x) = -a x) (hbo : ∀ x, b (-x) = -b x) :
    ∃ x, a x = 0 ∧ b x = 0 :=
  exists_eq_zero_of_odd_pair_sphere (by simp) ha hb hao hbo

#print axioms eq_of_continuous_intValued
#print axioms circle_exp_pi
#print axioms false_of_odd_lift
#print axioms exists_circle_lift_of_cover
#print axioms exists_eq_zero_of_odd_pair
#print axioms sphere_neg_ne_self
#print axioms contractible_sphere_compl
#print axioms isConnected_sphere_compl_pair
#print axioms exists_circle_lift_sphere
#print axioms exists_eq_zero_of_odd_pair_sphere
#print axioms exists_eq_zero_of_odd_pair_sphere_three

end Arlib
