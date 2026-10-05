/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationAffine

/-!
# The transverse-thinness bridge for the localisation needle

`Arlib.exists_needleIntegral_eq_zero_and_pos_affine` consumes a *transverse-thinness modulus*:
a sequence `δ k → 0` with

`∀ y ∈ D k, |g y - g (a + φ (y - a) • v)| ≤ δ k`,

i.e. the integrand varies by `o(1)` between a point of the `k`-th body of the localisation chain
and the point of the needle axis at the same height.  The localisation chain of
`Arlib.Convexity.LocalizationAssembly` delivers instead the *geometric* statement that the
intersection `⋂ k, C k` is collinear (`Arlib.exists_flat_cut_chain_collinear`).

This file bridges the two, and does so with **no metric decay hypothesis at all**: the only extra
input is that the bodies are compact.  The mechanism is the finite-intersection property, not a
diameter estimate — `Arlib.le_diam_of_sign_separated` shows no diameter decay is available, and
none is used.

## Main results

* `Arlib.eventually_subset_of_antitone_isCompact` — a decreasing sequence of compact sets is
  eventually contained in **any** open neighbourhood of its intersection.
* `Arlib.exists_tendsto_transverse_modulus` — hence, if every point of `⋂ k, C k` lies on the
  needle axis and `g` is bounded continuous, the explicit moduli
  `δ k = sSup {|g y - g (axis y)| : y ∈ C k}` tend to `0`.
* `Arlib.exists_tendsto_transverse_modulus_pair` — the same modulus can be taken to work for two
  integrands at once, which is what the equality form of the Localization Lemma needs.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` — **(G2c) and the thinness bridge
  combined**: the needle conclusions in general position, with the thinness hypothesis replaced
  by compactness of the bodies together with `⋂ k, D k ⊆ axis`.  The profile `W` it delivers is
  nonnegative with a **concave** `1/m`-th power, i.e. `W = ℓ^m` for a concave `ℓ` — the concave
  form of the Localization Lemma, which `Arlib.logConcaveOn_concaveNeedleDensity` shows is what
  every downstream consumer of a needle in this repository actually asks for.

## What is *not* proved here

Nothing shows that the bodies produced by `Arlib.exists_flat_cut_chain` are closed — they are
built by cutting with half-spaces, one of whose two sides is open.  Replacing that construction
by one with closed sides (or intersecting each body with its closure and checking the invariants
survive) is the remaining step, and it is a statement about the *chain*, not about the limit
passage.
-/

open MeasureTheory Set Filter Topology

namespace Arlib

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
  obtain ⟨u, hu⟩ := (hC 0).elim_finite_subfamily_closed (fun k => C k ∩ Uᶜ) hclosed hempty
  refine ⟨u.sup id, fun k hk => ?_⟩
  intro x hx
  by_contra hxU
  refine Set.eq_empty_iff_forall_notMem.mp hu x ⟨hanti (Nat.zero_le k) hx, ?_⟩
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

`Arlib.exists_needleIntegral_eq_zero_and_pos_affine` with its transverse-thinness hypothesis
discharged by `Arlib.exists_tendsto_transverse_modulus_pair`.  What is left to ask of the chain
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

/-- **Non-vacuity of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact`.**

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

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.eventually_subset_of_antitone_isCompact
#print axioms Arlib.exists_tendsto_transverse_modulus
#print axioms Arlib.exists_tendsto_transverse_modulus_pair
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_box
