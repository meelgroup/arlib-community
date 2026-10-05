/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleSlabChain
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleLimit
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Residue (F) of the Localization assembly: nondegeneracy, and the Euclidean transport

`Arlib.Convexity.LocalizationAssembly` lists two genuinely open residues of its assembly of the
Kannan–Lovász–Simonovits Localization Lemma.  This file closes **(F)**, which has two halves:

> The limit body must contain two distinct points — a chain collapsing to a point gives a
> degenerate needle, for which a profile on `(0,1)` is the wrong shape.  And the chain lives in
> `EuclideanSpace ℝ (Fin n)` while the needle theorems live in `Fin (m+1) → ℝ`, so a
> measure-preserving transport between them is still missing.

## What is proved here, unconditionally

**1. The transport (F, second half) — fully closed.**

`EuclideanSpace ℝ (Fin n)` is `WithLp 2 (Fin n → ℝ)`, and in current Mathlib `WithLp` is a
*structure*, so the two types are **not** definitionally equal and nothing here is unfolding.
Each transport is proved:

* `Arlib.preimage_toLp_eq_image_ofLp`, `Arlib.image_toLp_preimage_toLp`,
  `Arlib.preimage_ofLp_preimage_toLp` — the set-level bookkeeping.
* `Arlib.measurableSet_preimage_toLp_iff`, `Arlib.isCompact_preimage_toLp_iff`,
  `Arlib.convex_preimage_toLp_iff`, `Arlib.collinear_preimage_toLp_iff` — **iff** statements, so
  they transport hypotheses in *both* directions.  Collinearity goes through
  `Arlib.collinear_image_linearMap` (a collinear set has collinear linear image).
* `Arlib.volume_preimage_toLp` (`PiLp.volume_preserving_toLp`),
  `Arlib.setIntegral_preimage_toLp` (`MeasurePreserving.setIntegral_preimage_emb` with
  `Arlib.measurableEmbedding_toLp`).
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean` — the payload:
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` restated verbatim over
  `EuclideanSpace ℝ (Fin (m+1))`, which is where `Arlib.gaussianRestricted_isoperimetry` and
  `Arlib.MarkovChains.conductance_hitAndRun_ge` live.  No hypothesis and no conclusion changes
  shape.

**2. Nondegeneracy (F, first half) — closed modulo one explicit data hypothesis, and that
hypothesis is unavoidable.**

* `Arlib.abs_setIntegral_sub_measure_mul_le` — the elementary averaging estimate.
* `Arlib.exists_forall_abs_sub_le_of_chain_collapse` — if a decreasing chain of *compact* bodies
  has `⋂ k, D k ⊆ {p}`, a continuous `g` is uniformly within `η` of `g p` on all late bodies.
  Only the finite-intersection property is used (`Arlib.eventually_subset_of_antitone_isCompact`):
  no metric decay, no Hausdorff convergence, no rate — consistent with
  `Arlib.le_diam_of_sign_separated`, which forbids any diameter decay.
* `Arlib.le_apply_of_chain_collapse`, `Arlib.apply_le_of_chain_collapse`,
  `Arlib.apply_eq_zero_of_chain_collapse` — hence a collapse to `p` forces `g₁ p = 0` (from the
  invariant `∫_{D k} g₁ = 0`) and `ε ≤ g₂ p` (from `ε · vol (D k) ≤ ∫_{D k} g₂`).
* `Arlib.exists_ne_mem_iInter_of_chain` — **the headline**: those two are contradictory as soon as

      hsep : ∀ x, g₁ x = 0 → g₂ x < ε

  so under `hsep` the limit body contains two distinct points, which is exactly the nondegeneracy
  hypothesis `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` asks for.
* `Arlib.forall_lt_of_sign_separated` — `hsep` follows from slab separation of the two integrands,
  the same configuration `Arlib.le_diam_of_sign_separated` uses, *provided* the `g₁` side is
  strict (`g₁ < 0` above the level, not merely `≤ 0`).  With the non-strict form the argument
  breaks: `g₁` may vanish above the level, where nothing bounds `g₂`.  That gap is real, and is
  the reason `hsep` is stated directly rather than as slab separation.

**3. The composition.**  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep`
delivers the two conclusions of the equality-refined Localization Lemma from a localisation chain
in `EuclideanSpace ℝ (Fin (m+1))`, with **no** nondegeneracy hypothesis — only `hsep`.

## What is assumed

Exactly one thing, and it is an explicit hypothesis of the theorem that needs it, never a `def`,
a `structure` or a name asserting an unproved identity:

* **`hsep : ∀ x, g₁ x = 0 → g₂ x < ε`**, in `Arlib.exists_ne_mem_iInter_of_chain` and in the
  composed theorem.  This is a hypothesis on the *data*, not on the chain, and it cannot be
  dropped: the cutting scheme of `Arlib.exists_flat_cut_chain_collinear_compact` is free to
  produce a chain collapsing to a point.  `hsep` is the denial of the conjunction of the two
  consequences a collapse has for these invariants, hence the weakest hypothesis that this
  pointwise argument can use; it is *not* claimed to be the weakest possible hypothesis (see the
  docstring of `Arlib.exists_ne_mem_iInter_of_chain` for a counterexample to that stronger claim).

Nothing else is assumed.  Residue **(C)** of `Arlib.Convexity.LocalizationAssembly` (lower
semicontinuity) is untouched by this file, and the integrands are asked to be bounded continuous
exactly as `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` asks.

## Non-vacuity

Both hypothesis bundles carry witnesses, so neither theorem is vacuously true:

* `Arlib.exists_ne_mem_iInter_of_chain_witness` — the chain `[-1,1] ⊆ ℝ`, `g₁ x = x`,
  `g₂ x = x²`, `ε = 1/4`.
* `Arlib.exists_chain_euclidean_of_sep_data` and
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep_witness` — in
  `EuclideanSpace ℝ (Fin (m+1))`, the shrinking box `∏ [-ρ k i, ρ k i]` with `ρ k 0 = 1` and
  `ρ k i = 1/(k+1)` transversally, `g₁ Y = Y₀/(1+Y₀²)` (odd, so
  `Arlib.setIntegral_eq_zero_of_odd` kills every box mass by reflection — no Fubini and no
  one-dimensional computation) and `g₂ Y = min 1 (Y₀²)` with `ε = 1/32`
  (`Arlib.le_setIntegral_min_sq_coord`, a quarter-of-the-box comparison via
  `Arlib.volume_subBox_quarter`).  The limit body is collinear
  (`Arlib.collinear_iInter_box`), and `Arlib.exists_ne_mem_iInter_of_chain` then makes it
  nondegenerate — so the witness exercises the whole argument, not a shortcut around it.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.  See the `Axiom audit` section at the bottom.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### Averages along a collapsing chain -/

section Collapse

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- If `f` is within `η` of the constant `c` throughout `S`, then `∫_S f` is within
`η · μ S` of `c · μ S`. -/
theorem abs_setIntegral_sub_measure_mul_le {S : Set E} (hS : μ S ≠ ∞) {f : E → ℝ}
    (hf : IntegrableOn f S μ) {c η : ℝ} (hfc : ∀ x ∈ S, |f x - c| ≤ η) :
    |(∫ x in S, f x ∂μ) - (μ S).toReal * c| ≤ η * (μ S).toReal := by
  have hconst : IntegrableOn (fun _ : E => c) S μ := integrableOn_const hS
  have hsub : (∫ x in S, (f x - c) ∂μ) = (∫ x in S, f x ∂μ) - (μ S).toReal * c := by
    rw [integral_sub hf hconst, setIntegral_const, smul_eq_mul, measureReal_def]
  have hbd : ‖∫ x in S, (f x - c) ∂μ‖ ≤ η * μ.real S :=
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hS)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hfc x hx)
  rw [hsub, Real.norm_eq_abs, measureReal_def] at hbd
  exact hbd

end Collapse

/-! ### A chain that collapses to a point pins the integrands down at that point -/

section ChainCollapse

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] {μ : Measure E}

omit [MeasurableSpace E] in
/-- **A continuous function is nearly constant on the late bodies of a collapsing chain.**

If the decreasing chain of compact bodies `D` has `⋂ k, D k ⊆ {p}`, then for every `η > 0` all
sufficiently late bodies lie in `{y | |g y - g p| < η}` — the finite-intersection property
(`Arlib.eventually_subset_of_antitone_isCompact`), applied to the open set cut out by continuity
of `g`.  No metric decay and no rate. -/
theorem exists_forall_abs_sub_le_of_chain_collapse {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) {p : E} (hp : (⋂ k, D k) ⊆ {p})
    {g : E → ℝ} (hg : Continuous g) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ y ∈ D k, |g y - g p| ≤ η := by
  have hopen : IsOpen {y : E | |g y - g p| < η} :=
    isOpen_lt ((hg.sub continuous_const).abs) continuous_const
  have hsub : (⋂ k, D k) ⊆ {y : E | |g y - g p| < η} := by
    intro y hy
    have hyp : y = p := hp hy
    simp only [mem_setOf_eq, hyp, sub_self, abs_zero]
    exact hη
  obtain ⟨N, hN⟩ := eventually_subset_of_antitone_isCompact hDcomp hDmono hopen hsub
  exact ⟨N, fun k hk y hy => (hN k hk hy).le⟩

/-- **A lower bound on the normalised masses survives the collapse.**

If the chain collapses to `p` and `c · μ (D k) ≤ ∫_{D k} g` at every stage, then `c ≤ g p`. -/
theorem le_apply_of_chain_collapse {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) (hDpos : ∀ k, 0 < μ (D k)) (hDfin : ∀ k, μ (D k) ≠ ∞)
    {p : E} (hp : (⋂ k, D k) ⊆ {p}) {g : E → ℝ} (hg : Continuous g)
    (hint : ∀ k, IntegrableOn g (D k) μ)
    {c : ℝ} (hc : ∀ k, c * (μ (D k)).toReal ≤ ∫ y in D k, g y ∂μ) :
    c ≤ g p := by
  by_contra hcon
  rw [not_le] at hcon
  have hη : 0 < (c - g p) / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_forall_abs_sub_le_of_chain_collapse hDcomp hDmono hp hg hη
  have hb := abs_setIntegral_sub_measure_mul_le (hDfin N) (hint N) (hN N le_rfl)
  have hV : 0 < (μ (D N)).toReal := ENNReal.toReal_pos (hDpos N).ne' (hDfin N)
  have h1 := hc N
  have h2 := (abs_le.mp hb).2
  nlinarith

/-- The mirror of `Arlib.le_apply_of_chain_collapse`, for an upper bound on the masses. -/
theorem apply_le_of_chain_collapse {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) (hDpos : ∀ k, 0 < μ (D k)) (hDfin : ∀ k, μ (D k) ≠ ∞)
    {p : E} (hp : (⋂ k, D k) ⊆ {p}) {g : E → ℝ} (hg : Continuous g)
    (hint : ∀ k, IntegrableOn g (D k) μ)
    {c : ℝ} (hc : ∀ k, (∫ y in D k, g y ∂μ) ≤ c * (μ (D k)).toReal) :
    g p ≤ c := by
  have hneg : ∀ k, (-c) * (μ (D k)).toReal ≤ ∫ y in D k, (-g) y ∂μ := by
    intro k
    have h : (∫ y in D k, (-g) y ∂μ) = -∫ y in D k, g y ∂μ := by
      simp only [Pi.neg_apply, integral_neg]
    rw [h]
    have := hc k
    linarith
  have := le_apply_of_chain_collapse hDcomp hDmono hDpos hDfin hp hg.neg
    (fun k => (hint k).neg) hneg
  simpa using this

/-- **A chain with mean-zero `g₁` that collapses to a point forces `g₁` to vanish there.** -/
theorem apply_eq_zero_of_chain_collapse {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) (hDpos : ∀ k, 0 < μ (D k)) (hDfin : ∀ k, μ (D k) ≠ ∞)
    {p : E} (hp : (⋂ k, D k) ⊆ {p}) {g : E → ℝ} (hg : Continuous g)
    (hint : ∀ k, IntegrableOn g (D k) μ) (hzero : ∀ k, (∫ y in D k, g y ∂μ) = 0) :
    g p = 0 := by
  have hle : g p ≤ 0 :=
    apply_le_of_chain_collapse hDcomp hDmono hDpos hDfin hp hg hint
      (fun k => by rw [hzero k]; simp)
  have hge : (0 : ℝ) ≤ g p :=
    le_apply_of_chain_collapse hDcomp hDmono hDpos hDfin hp hg hint
      (fun k => by rw [hzero k]; simp)
  linarith

/-- **Nondegeneracy of the limit body of a localisation chain.**

This is the sharp form of residue **(F)**'s first half.  Let `D` be a decreasing chain of compact
bodies of positive finite measure carrying the two localisation invariants

* `∫_{D k} g₁ = 0` (the equality form's `g₁`-invariant), and
* `ε · μ (D k) ≤ ∫_{D k} g₂` (`Arlib.lt_setIntegral_of_perturbed`'s `g₂`-invariant),

with `g₁`, `g₂` continuous.  If the chain collapsed to a single point `p`, then averaging the two
invariants over the late bodies would force `g₁ p = 0` **and** `ε ≤ g₂ p`
(`Arlib.apply_eq_zero_of_chain_collapse`, `Arlib.le_apply_of_chain_collapse`).  So the single
hypothesis

    hsep : ∀ x, g₁ x = 0 → g₂ x < ε

already rules a collapse out, and `⋂ k, D k` contains two distinct points.

**What `hsep` is, exactly.**  A collapse to `p` has precisely two consequences that these two
invariants can see: `g₁ p = 0` and `ε ≤ g₂ p`.  `hsep` is the denial of their conjunction, so it
is the weakest hypothesis that rules a collapse out *by this pointwise argument*.  It is **not**
claimed to be the weakest hypothesis outright: other features of the data can also forbid a
collapse without implying `hsep` — e.g. `g₁ y = ‖y - p‖` has `g₁ p = 0` yet no chain collapsing to
`p` can keep `∫ g₁ = 0`, because `g₁ > 0` off `p`.

**It is genuinely a hypothesis on the data.**  The chain construction of
`Arlib.exists_flat_cut_chain_collinear_compact` is free to collapse: nothing in the cutting scheme
prevents it.  `Arlib.forall_lt_of_sign_separated` below shows that the slab-separation of
`Arlib.le_diam_of_sign_separated` — in its strict form on the `g₁` side — implies `hsep`. -/
theorem exists_ne_mem_iInter_of_chain {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) (hDpos : ∀ k, 0 < μ (D k)) (hDfin : ∀ k, μ (D k) ≠ ∞)
    {g₁ g₂ : E → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hint₁ : ∀ k, IntegrableOn g₁ (D k) μ) (hint₂ : ∀ k, IntegrableOn g₂ (D k) μ)
    (hzero : ∀ k, (∫ y in D k, g₁ y ∂μ) = 0)
    {ε : ℝ} (hge : ∀ k, ε * (μ (D k)).toReal ≤ ∫ y in D k, g₂ y ∂μ)
    (hsep : ∀ x, g₁ x = 0 → g₂ x < ε) :
    ∃ p ∈ ⋂ k, D k, ∃ q ∈ ⋂ k, D k, p ≠ q := by
  have hne : ∀ k, (D k).Nonempty := by
    intro k
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    have hk := hDpos k
    rw [hemp, measure_empty] at hk
    exact absurd hk (lt_irrefl 0)
  obtain ⟨p, hp⟩ : (⋂ k, D k).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed D hDmono hne (hDcomp 0)
      (fun k => (hDcomp k).isClosed)
  refine ⟨p, hp, ?_⟩
  by_contra hcon
  have hsingle : (⋂ k, D k) ⊆ {p} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hne'
    exact hcon ⟨y, hy, Ne.symm hne'⟩
  have h1 : g₁ p = 0 :=
    apply_eq_zero_of_chain_collapse hDcomp hDmono hDpos hDfin hsingle hg₁ hint₁ hzero
  have h2 : ε ≤ g₂ p :=
    le_apply_of_chain_collapse hDcomp hDmono hDpos hDfin hsingle hg₂ hint₂ hge
  exact absurd (hsep p h1) (not_lt.mpr h2)

end ChainCollapse

/-! ### The sign-separation sufficient condition, and non-vacuity -/

section SignSeparation

/-- **Strict slab separation implies the nondegeneracy hypothesis of
`Arlib.exists_ne_mem_iInter_of_chain`.**

`Arlib.le_diam_of_sign_separated` assumes `g₁ ≤ 0` above the level `a` of a functional `L` and
`g₂ ≤ 0` below the level `b > a`.  In its *strict* form on the `g₁` side — `g₁ < 0` above `a` — the
separation gives `hsep` outright: a zero of `g₁` has `L x ≤ a < b`, where `g₂` is nonpositive.

Nothing is assumed of `L` beyond being a function; in the intended application it is the
continuous linear functional of `Arlib.le_diam_of_sign_separated`. -/
theorem forall_lt_of_sign_separated {E : Type*} {g₁ g₂ : E → ℝ} {L : E → ℝ} {a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε) (hg₁ : ∀ x, a < L x → g₁ x < 0) (hg₂ : ∀ x, L x < b → g₂ x ≤ 0) :
    ∀ x, g₁ x = 0 → g₂ x < ε := by
  intro x hx
  have hLa : L x ≤ a := by
    by_contra h
    rw [not_le] at h
    exact absurd hx (ne_of_lt (hg₁ x h))
  exact lt_of_le_of_lt (hg₂ x (lt_of_le_of_lt hLa hab)) hε

/-- **Non-vacuity of `Arlib.exists_ne_mem_iInter_of_chain`.**

Every hypothesis of that theorem is met simultaneously by the constant chain `D k = [-1,1]` in
`ℝ`, the integrands `g₁ x = x` and `g₂ x = x²`, and `ε = 1/4`: the `g₁`-mean vanishes by symmetry,
`∫ x² = 2/3` beats `ε · vol = 1/2`, and the only zero of `g₁` is `0`, where `g₂` vanishes — so
`hsep` holds.  The conclusion is then genuinely produced by the theorem. -/
theorem exists_ne_mem_iInter_of_chain_witness :
    ∃ (D : ℕ → Set ℝ) (g₁ g₂ : ℝ → ℝ) (ε : ℝ),
      (∀ k, IsCompact (D k)) ∧ (∀ k, D (k + 1) ⊆ D k) ∧ (∀ k, 0 < volume (D k)) ∧
      (∀ k, volume (D k) ≠ ∞) ∧ Continuous g₁ ∧ Continuous g₂ ∧
      (∀ k, IntegrableOn g₁ (D k)) ∧ (∀ k, IntegrableOn g₂ (D k)) ∧
      (∀ k, (∫ y in D k, g₁ y) = 0) ∧ 0 < ε ∧
      (∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) ∧
      (∀ x, g₁ x = 0 → g₂ x < ε) ∧
      ∃ p ∈ ⋂ k, D k, ∃ q ∈ ⋂ k, D k, p ≠ q := by
  have hcomp : ∀ _ : ℕ, IsCompact (Icc (-1 : ℝ) 1) := fun _ => isCompact_Icc
  have hmono : ∀ _ : ℕ, Icc (-1 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := fun _ => Subset.rfl
  have hpos : ∀ _ : ℕ, 0 < volume (Icc (-1 : ℝ) 1) := by
    intro _; rw [Real.volume_Icc]; simp
  have hfin : ∀ _ : ℕ, volume (Icc (-1 : ℝ) 1) ≠ ∞ := by
    intro _; rw [Real.volume_Icc]; simp
  have hint₁ : ∀ _ : ℕ, IntegrableOn (fun x : ℝ => x) (Icc (-1 : ℝ) 1) volume := fun _ =>
    continuous_id.integrableOn_Icc
  have hint₂ : ∀ _ : ℕ, IntegrableOn (fun x : ℝ => x ^ 2) (Icc (-1 : ℝ) 1) volume := fun _ =>
    (continuous_pow 2).integrableOn_Icc
  have hzero : ∀ _ : ℕ, (∫ y in Icc (-1 : ℝ) 1, y) = 0 := by
    intro _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_id]
    norm_num
  have hge : ∀ _ : ℕ, (1 / 4 : ℝ) * (volume (Icc (-1 : ℝ) 1)).toReal
      ≤ ∫ y in Icc (-1 : ℝ) 1, y ^ 2 := by
    intro _
    rw [Real.volume_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_pow]
    norm_num
  have hsep : ∀ x : ℝ, x = 0 → x ^ 2 < 1 / 4 := by
    intro x hx
    subst hx
    norm_num
  exact ⟨fun _ => Icc (-1 : ℝ) 1, fun x => x, fun x => x ^ 2, 1 / 4, hcomp, hmono, hpos, hfin,
    continuous_id, continuous_pow 2, hint₁, hint₂, hzero, by norm_num, hge, hsep,
    exists_ne_mem_iInter_of_chain hcomp hmono hpos hfin continuous_id (continuous_pow 2)
      hint₁ hint₂ hzero hge hsep⟩

end SignSeparation

/-! ### Collinearity is carried by linear maps -/

section CollinearLinear

/-- The image of a collinear set under a linear map is collinear.  (Mathlib has this for
`AffineSubspace`s but not, at the time of writing, in this shape.) -/
theorem collinear_image_linearMap {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (f : V →ₗ[ℝ] W) {s : Set V} (h : Collinear ℝ s) : Collinear ℝ (f '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨f p₀, f v, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr⟩ := hv y hy
  refine ⟨r, ?_⟩
  simp only [vadd_eq_add] at hr ⊢
  rw [hr, map_add, map_smul]

end CollinearLinear

/-! ### Transport between `EuclideanSpace ℝ (Fin n)` and `Fin n → ℝ`

`EuclideanSpace ℝ (Fin n)` is `WithLp 2 (Fin n → ℝ)`, and `WithLp` is a *structure*, so nothing
below is definitional unfolding: each transport is proved.  The bridge is
`PiLp.volume_preserving_toLp`, together with the fact that `WithLp.toLp 2` and `WithLp.ofLp` are
mutually inverse, continuous, linear and measurable. -/

section Transport

variable {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}

/-- The `toLp`-preimage of a set of `EuclideanSpace ℝ (Fin n)` is its `ofLp`-image. -/
theorem preimage_toLp_eq_image_ofLp (S : Set (EuclideanSpace ℝ (Fin n))) :
    (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S
      = (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) '' S := by
  ext x
  constructor
  · exact fun hx => ⟨WithLp.toLp 2 x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- Pushing a `toLp`-preimage forward by `toLp` recovers the set. -/
theorem image_toLp_preimage_toLp (S : Set (EuclideanSpace ℝ (Fin n))) :
    (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ''
        ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S) = S :=
  (WithLp.toLp_surjective 2).image_preimage S

/-- Pulling a `toLp`-preimage back by `ofLp` recovers the set. -/
theorem preimage_ofLp_preimage_toLp (S : Set (EuclideanSpace ℝ (Fin n))) :
    (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) ⁻¹'
        ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S) = S := rfl

/-- `WithLp.toLp 2` is a measurable embedding. -/
theorem measurableEmbedding_toLp :
    MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding

/-- Measurability transports. -/
theorem measurableSet_preimage_toLp_iff :
    MeasurableSet ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S)
      ↔ MeasurableSet S := by
  constructor
  · intro h
    have := (WithLp.measurable_ofLp 2 (Fin n → ℝ)) h
    rwa [preimage_ofLp_preimage_toLp] at this
  · exact fun h => (WithLp.measurable_toLp 2 (Fin n → ℝ)) h

/-- Compactness transports. -/
theorem isCompact_preimage_toLp_iff :
    IsCompact ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S) ↔ IsCompact S := by
  constructor
  · intro h
    have := h.image (PiLp.continuous_toLp 2 fun _ : Fin n => ℝ)
    rwa [image_toLp_preimage_toLp] at this
  · intro h
    rw [preimage_toLp_eq_image_ofLp]
    exact h.image (PiLp.continuous_ofLp 2 fun _ : Fin n => ℝ)

/-- Convexity transports. -/
theorem convex_preimage_toLp_iff :
    Convex ℝ ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have := h.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    rwa [show ⇑(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap = WithLp.ofLp from rfl,
      preimage_ofLp_preimage_toLp] at this
  · intro h
    exact h.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap

/-- Collinearity transports. -/
theorem collinear_preimage_toLp_iff :
    Collinear ℝ ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S)
      ↔ Collinear ℝ S := by
  constructor
  · intro h
    have := collinear_image_linearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap h
    rwa [show ⇑(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap = WithLp.toLp 2 from rfl,
      image_toLp_preimage_toLp] at this
  · intro h
    rw [preimage_toLp_eq_image_ofLp]
    exact collinear_image_linearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap h

/-- Volume transports: `WithLp.toLp 2` is measure preserving
(`PiLp.volume_preserving_toLp`). -/
theorem volume_preimage_toLp (hS : NullMeasurableSet S) :
    volume ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S) = volume S :=
  (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hS

/-- Set integrals transport. -/
theorem setIntegral_preimage_toLp (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ y in (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S,
        g (WithLp.toLp 2 y)) = ∫ y in S, g y :=
  (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb measurableEmbedding_toLp g S

end Transport

/-! ### The needle theorem, transported to `EuclideanSpace` -/

section EuclideanNeedle

variable {m : ℕ}

/-- **`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain`, on `EuclideanSpace`.**

This is residue **(F)**'s second half.  The localisation chain of
`Arlib.exists_flat_cut_chain_collinear_compact` lives in `EuclideanSpace ℝ (Fin n)`, an inner
product space, while the needle theorems are proved over `Fin (m+1) → ℝ`.  Since `WithLp 2` is a
*structure*, the two are not definitionally equal; the transport lemmas of the previous section
identify them, and `PiLp.volume_preserving_toLp` says the identification preserves volume, so
neither hypothesis nor conclusion changes shape. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean (hm : m ≠ 0)
    {D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1)))} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {p q : EuclideanSpace ℝ (Fin (m + 1))} (hp : p ∈ ⋂ k, D k) (hq : q ∈ ⋂ k, D k) (hpq : p ≠ q)
    {g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  classical
  set F : ℕ → Set (Fin (m + 1) → ℝ) :=
    fun k => (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' D k with hF
  have hvol : ∀ k, volume (F k) = volume (D k) := fun k =>
    volume_preimage_toLp ((hDcomp k).isClosed.measurableSet).nullMeasurableSet
  have hFcomp : ∀ k, IsCompact (F k) := fun k => isCompact_preimage_toLp_iff.mpr (hDcomp k)
  have hFconv : ∀ k, Convex ℝ (F k) := fun k => convex_preimage_toLp_iff.mpr (hDconv k)
  have hFmono : ∀ k, F (k + 1) ⊆ F k := fun k => Set.preimage_mono (hDmono k)
  have hFpos : ∀ k, 0 < volume (F k) := fun k => by rw [hvol k]; exact hDpos k
  have hiInter : (⋂ k, F k)
      = (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' ⋂ k, D k := by
    rw [Set.preimage_iInter]
  have hFcol : Collinear ℝ (⋂ k, F k) := by
    rw [hiInter]; exact collinear_preimage_toLp_iff.mpr hcol
  have hmemF : ∀ (x : EuclideanSpace ℝ (Fin (m + 1))), x ∈ (⋂ k, D k) →
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
    rw [hF, setIntegral_preimage_toLp g₁ (D k)]
    exact hzero k
  have hgeF : ∀ k, ε * (volume (F k)).toReal ≤ ∫ y in F k, g₂ (WithLp.toLp 2 y) := by
    intro k
    rw [hvol k, hF, setIntegral_preimage_toLp g₂ (D k)]
    exact hge k
  obtain ⟨b, v, W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_chain hm hFcomp hFconv hFmono hFpos hFcol
      (hmemF p hp) (hmemF q hq) hpq' hcont₁ hcont₂ (fun x => hM₁ _) (fun x => hM₂ _)
      hzeroF hεpos hgeF
  refine ⟨WithLp.toLp 2 b, WithLp.toLp 2 v, W, hW0, hWsupp, hWint, hWc, ?_, ?_⟩
  · rw [← hW₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2
  · refine lt_of_lt_of_le hW₂ (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2

/-- **Residue (F), both halves at once.**

The equality-refined Localization Lemma's two conclusions, for a localisation chain given on
`EuclideanSpace ℝ (Fin (m+1))`, with **no** nondegeneracy hypothesis on the limit body: it is
derived from the data by `Arlib.exists_ne_mem_iInter_of_chain`.

The only residual hypothesis over
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean` is

    hsep : ∀ x, g₁ x = 0 → g₂ x < ε

which `Arlib.forall_lt_of_sign_separated` derives from strict slab separation of the two
integrands.  See `Arlib.exists_ne_mem_iInter_of_chain` for why this cannot be dropped. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep (hm : m ≠ 0)
    {D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1)))} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y)
    (hsep : ∀ x, g₁ x = 0 → g₂ x < ε) :
    ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    exists_ne_mem_iInter_of_chain hDcomp hDmono hDpos (fun k => (hDcomp k).measure_lt_top.ne)
      hg₁ hg₂ (fun k => hg₁.locallyIntegrable.integrableOn_isCompact (hDcomp k))
      (fun k => hg₂.locallyIntegrable.integrableOn_isCompact (hDcomp k)) hzero hge hsep
  exact exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean hm hDcomp hDconv hDmono
    hDpos hcol hp hq hpq hg₁ hg₂ hM₁ hM₂ hzero hεpos hge

end EuclideanNeedle

/-! ### Ingredients of the non-vacuity witness -/

section WitnessTools

/-- **An odd function has vanishing integral over a symmetric set.**

Only reflection invariance of the measure is used; no one-dimensional computation and no Fubini.
For an inner product space, the reflection is a linear isometry, so
`LinearIsometryEquiv.measurePreserving` supplies `hmp`. -/
theorem setIntegral_eq_zero_of_odd {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableNeg G] {μ : Measure G} (hmp : MeasurePreserving (fun x : G => -x) μ μ)
    {S : Set G} (hS : (fun x : G => -x) ⁻¹' S = S) {g : G → ℝ} (hodd : ∀ x, g (-x) = -g x) :
    (∫ x in S, g x ∂μ) = 0 := by
  have hemb : MeasurableEmbedding (fun x : G => -x) :=
    (MeasurableEquiv.neg G).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb g S
  rw [hS] at h
  have h2 : (∫ x in S, g (-x) ∂μ) = -∫ x in S, g x ∂μ := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  rw [h2] at h
  linarith

variable {m : ℕ}

/-- A set of `Fin (m+1) → ℝ` all of whose points have every coordinate but the `0`-th equal to
zero is collinear: it lies on the first coordinate axis. -/
theorem collinear_of_subset_axis {s : Set (Fin (m + 1) → ℝ)}
    (hs : ∀ y ∈ s, ∀ i : Fin (m + 1), i ≠ 0 → y i = 0) : Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨0, Pi.single 0 1, fun y hy => ⟨y 0, ?_⟩⟩
  simp only [vadd_eq_add, add_zero]
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · rw [hs y hy i hi]
    simp [Ne.symm hi]

/-- The volume of a box symmetric about the origin. -/
theorem volume_symmetricBox (ρ : Fin (m + 1) → ℝ) :
    volume (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i))
      = ∏ i : Fin (m + 1), ENNReal.ofReal (2 * ρ i) := by
  rw [volume_pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.volume_Icc]
  ring_nf

/-- A box symmetric about the origin is invariant under reflection. -/
theorem neg_preimage_symmetricBox (ρ : Fin (m + 1) → ℝ) :
    (fun x : Fin (m + 1) → ℝ => -x) ⁻¹' (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i))
      = Set.univ.pi fun i => Icc (-(ρ i)) (ρ i) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc, Pi.neg_apply]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith

/-- Cutting the `0`-th side of a unit-radius symmetric box down to `[1/2, 1]` divides its volume
by four. -/
theorem volume_subBox_quarter (ρ a : Fin (m + 1) → ℝ) (hρ : ρ 0 = 1) (ha0 : a 0 = 1 / 2)
    (ha : ∀ i : Fin m, a (Fin.succ i) = -(ρ (Fin.succ i))) :
    (volume (Set.univ.pi fun i => Icc (a i) (ρ i))).toReal
      = (1 / 4) * (volume (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i))).toReal := by
  have h1 : volume (Set.univ.pi fun i => Icc (a i) (ρ i))
      = ∏ i : Fin (m + 1), ENNReal.ofReal (ρ i - a i) := by
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun i _ => Real.volume_Icc
  have h2 : volume (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i))
      = ∏ i : Fin (m + 1), ENNReal.ofReal (ρ i - -(ρ i)) := by
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun i _ => Real.volume_Icc
  have e1 : (ENNReal.ofReal ((1 : ℝ) - 1 / 2)).toReal = 1 / 2 := by
    rw [ENNReal.toReal_ofReal] <;> norm_num
  have e2 : (ENNReal.ofReal ((1 : ℝ) - -1)).toReal = 2 := by
    rw [ENNReal.toReal_ofReal] <;> norm_num
  rw [h1, h2, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [ha, ha0, hρ]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, e1, e2]
  ring

/-- The intersection of a chain of boxes whose transverse half-widths tend to `0` is collinear. -/
theorem collinear_iInter_box (ρ : ℕ → Fin (m + 1) → ℝ)
    (hρ : ∀ i : Fin (m + 1), i ≠ 0 → ∀ k : ℕ, ρ k i ≤ 1 / ((k : ℝ) + 1)) :
    Collinear ℝ (⋂ k, Set.univ.pi fun i => Icc (-(ρ k i)) (ρ k i)) := by
  refine collinear_of_subset_axis fun y hy i hi => ?_
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
  have hyn := Set.mem_univ_pi.mp (Set.mem_iInter.mp hy n) i
  rw [Set.mem_Icc] at hyn
  have habs : |y i| ≤ ρ n i := abs_le.mpr ⟨hyn.1, hyn.2⟩
  have := hρ i hi n
  linarith

/-- **The `g₂`-mass bound for the witness box.**

On the box `∏ [-ρ i, ρ i]` with `ρ 0 = 1`, the integrand `min 1 (y₀²)` is at least `1/4` on the
sub-box where `y₀ ∈ [1/2, 1]`, which is a quarter of the volume
(`Arlib.volume_subBox_quarter`).  No exact integral is computed. -/
theorem le_setIntegral_min_sq_coord (ρ : Fin (m + 1) → ℝ) (hρ0 : ρ 0 = 1) :
    (1 / 16 : ℝ) * (volume (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i))).toReal
      ≤ ∫ y in Set.univ.pi fun i => Icc (-(ρ i)) (ρ i), min 1 ((y 0) ^ 2) := by
  classical
  set a : Fin (m + 1) → ℝ := fun i => if i = 0 then 1 / 2 else -(ρ i) with hadef
  have ha0 : a 0 = 1 / 2 := if_pos rfl
  have hasucc : ∀ i : Fin m, a (Fin.succ i) = -(ρ (Fin.succ i)) :=
    fun i => if_neg (Fin.succ_ne_zero i)
  have hf : Continuous fun y : Fin (m + 1) → ℝ => min 1 ((y 0) ^ 2) := by fun_prop
  have hTcomp : IsCompact (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hfint : IntegrableOn (fun y : Fin (m + 1) → ℝ => min 1 ((y 0) ^ 2))
      (Set.univ.pi fun i => Icc (-(ρ i)) (ρ i)) :=
    hf.locallyIntegrable.integrableOn_isCompact hTcomp
  have hsub : (Set.univ.pi fun i => Icc (a i) (ρ i))
      ⊆ Set.univ.pi fun i => Icc (-(ρ i)) (ρ i) := by
    intro y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    refine Set.Icc_subset_Icc_left ?_ (Set.mem_univ_pi.mp hy i)
    by_cases hi : i = 0
    · subst hi; rw [ha0, hρ0]; norm_num
    · rw [hadef]; simp [hi]
  have hSmeas : MeasurableSet (Set.univ.pi fun i => Icc (a i) (ρ i)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hSfin : volume (Set.univ.pi fun i => Icc (a i) (ρ i)) ≠ ∞ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne
  have hlow : ∀ y ∈ Set.univ.pi fun i => Icc (a i) (ρ i), (1 / 4 : ℝ) ≤ min 1 ((y 0) ^ 2) := by
    intro y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [Set.mem_Icc, ha0] at h0
    exact le_min (by norm_num) (by nlinarith [h0.1])
  have h1 : (1 / 4 : ℝ) * (volume (Set.univ.pi fun i => Icc (a i) (ρ i))).toReal
      ≤ ∫ y in Set.univ.pi fun i => Icc (a i) (ρ i), min 1 ((y 0) ^ 2) := by
    have := setIntegral_ge_of_const_le_real hSmeas hSfin hlow (hfint.mono_set hsub)
    rwa [measureReal_def] at this
  have h2 : (∫ y in Set.univ.pi fun i => Icc (a i) (ρ i), min 1 ((y 0) ^ 2))
      ≤ ∫ y in Set.univ.pi fun i => Icc (-(ρ i)) (ρ i), min 1 ((y 0) ^ 2) :=
    setIntegral_mono_set hfint
      (Filter.Eventually.of_forall fun y => le_min (by norm_num) (sq_nonneg _))
      hsub.eventuallyLE
  have h3 := volume_subBox_quarter ρ a hρ0 ha0 hasucc
  linarith

end WitnessTools

/-! ### Non-vacuity of the Euclidean needle theorems -/

section EuclideanWitness

variable {m : ℕ}

/-- **The witness data for
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep`.**

The chain is the shrinking box `∏ [-ρ k i, ρ k i]` with `ρ k 0 = 1` and `ρ k i = 1/(k+1)`
transversally, transported into `EuclideanSpace ℝ (Fin (m+1))`; the integrands are
`g₁ Y = Y₀/(1+Y₀²)` (odd, so all its box masses vanish by reflection) and `g₂ Y = min 1 (Y₀²)`
(nonnegative, at least `1/4` on a quarter of every box, and `0` exactly where `g₁` vanishes).
So `ε = 1/32` satisfies **both** the mass bound and the separation hypothesis `hsep`
simultaneously — which is the point: `hsep` is not vacuous, and it is compatible with a genuine
nondegenerate localisation chain. -/
theorem exists_chain_euclidean_of_sep_data :
    ∃ (D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1))))
      (g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (M ε : ℝ),
      (∀ k, IsCompact (D k)) ∧ (∀ k, Convex ℝ (D k)) ∧ (∀ k, D (k + 1) ⊆ D k) ∧
      (∀ k, 0 < volume (D k)) ∧ Collinear ℝ (⋂ k, D k) ∧
      Continuous g₁ ∧ Continuous g₂ ∧ (∀ x, |g₁ x| ≤ M) ∧ (∀ x, |g₂ x| ≤ M) ∧
      (∀ k, (∫ y in D k, g₁ y) = 0) ∧ 0 < ε ∧
      (∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) ∧
      (∀ x, g₁ x = 0 → g₂ x < ε) := by
  classical
  set ρ : ℕ → Fin (m + 1) → ℝ := fun k i => if i = 0 then 1 else 1 / ((k : ℝ) + 1) with hρdef
  have hρ0 : ∀ k, ρ k 0 = 1 := fun k => if_pos rfl
  have hρpos : ∀ k i, 0 < ρ k i := by
    intro k i
    rw [hρdef]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      positivity
  have hρmono : ∀ k i, ρ (k + 1) i ≤ ρ k i := by
    intro k i
    rw [hρdef]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      exact one_div_le_one_div_of_le h1 h2
  have hρtrans : ∀ i : Fin (m + 1), i ≠ 0 → ∀ k : ℕ, ρ k i ≤ 1 / ((k : ℝ) + 1) := by
    intro i hi k
    rw [hρdef]
    simp [hi]
  set T : ℕ → Set (Fin (m + 1) → ℝ) :=
    fun k => Set.univ.pi fun i => Icc (-(ρ k i)) (ρ k i) with hTdef
  set D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    fun k => (WithLp.ofLp : EuclideanSpace ℝ (Fin (m + 1)) → Fin (m + 1) → ℝ) ⁻¹' T k with hDdef
  have hpre : ∀ k, (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹' D k
      = T k := by
    intro k
    rw [hDdef]
    rfl
  have hTcomp : ∀ k, IsCompact (T k) := by
    intro k; rw [hTdef]; exact isCompact_univ_pi fun _ => isCompact_Icc
  have hDcomp : ∀ k, IsCompact (D k) := by
    intro k
    have h := isCompact_preimage_toLp_iff (S := D k)
    rw [hpre k] at h
    exact h.mp (hTcomp k)
  have hDconv : ∀ k, Convex ℝ (D k) := by
    intro k
    have h := convex_preimage_toLp_iff (S := D k)
    rw [hpre k] at h
    refine h.mp ?_
    rw [hTdef]
    exact convex_pi fun _ _ => convex_Icc _ _
  have hTmono : ∀ k, T (k + 1) ⊆ T k := by
    intro k y hy
    rw [hTdef] at hy ⊢
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    exact Set.Icc_subset_Icc (by linarith [hρmono k i]) (hρmono k i) hyi
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k; rw [hDdef]; exact Set.preimage_mono (hTmono k)
  have hvol : ∀ k, volume (D k) = volume (T k) := by
    intro k
    have h := volume_preimage_toLp (S := D k)
      ((hDcomp k).isClosed.measurableSet).nullMeasurableSet
    rw [hpre k] at h
    exact h.symm
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    rw [hvol k, hTdef, volume_symmetricBox, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (ENNReal.ofReal_pos.mpr (by linarith [hρpos k i])).ne'
  have hcol : Collinear ℝ (⋂ k, D k) := by
    refine collinear_preimage_toLp_iff.mp ?_
    have hIT : (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) ⁻¹'
        (⋂ k, D k) = ⋂ k, T k := by
      rw [Set.preimage_iInter]
      exact Set.iInter_congr hpre
    rw [hIT, hTdef]
    exact collinear_iInter_box ρ hρtrans
  have hc0 : Continuous fun Y : EuclideanSpace ℝ (Fin (m + 1)) => (Y 0 : ℝ) := by fun_prop
  have hcont₁ : Continuous fun Y : EuclideanSpace ℝ (Fin (m + 1)) => Y 0 / (1 + (Y 0) ^ 2) :=
    hc0.div (continuous_const.add (hc0.pow 2)) fun Y => by positivity
  have hcont₂ : Continuous fun Y : EuclideanSpace ℝ (Fin (m + 1)) => min 1 ((Y 0) ^ 2) :=
    continuous_const.min (hc0.pow 2)
  have hnegmp : MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) => -x) volume volume :=
    (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin (m + 1)))).measurePreserving
  have hDsymm : ∀ k, (fun x : EuclideanSpace ℝ (Fin (m + 1)) => -x) ⁻¹' D k = D k := by
    intro k
    ext x
    have hbox := Set.ext_iff.mp (neg_preimage_symmetricBox (ρ k)) (WithLp.ofLp x)
    simp only [hDdef, hTdef, Set.mem_preimage] at hbox ⊢
    exact hbox
  refine ⟨D, fun Y => Y 0 / (1 + (Y 0) ^ 2), fun Y => min 1 ((Y 0) ^ 2), 1, 1 / 32,
    hDcomp, hDconv, hDmono, hDpos, hcol, hcont₁, hcont₂, ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · intro Y
    show |Y 0 / (1 + (Y 0) ^ 2)| ≤ 1
    have hden : (0 : ℝ) < 1 + (Y 0) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    nlinarith [sq_abs (Y 0), abs_nonneg (Y 0)]
  · intro Y
    show |min 1 ((Y 0) ^ 2)| ≤ 1
    rw [abs_le]
    exact ⟨by nlinarith [le_min (show (0 : ℝ) ≤ 1 by norm_num) (sq_nonneg (Y 0))],
      min_le_left _ _⟩
  · intro k
    refine setIntegral_eq_zero_of_odd hnegmp (hDsymm k) fun x => ?_
    show (-x) 0 / (1 + ((-x) 0) ^ 2) = -(x 0 / (1 + (x 0) ^ 2))
    have hneg : ((-x : EuclideanSpace ℝ (Fin (m + 1))) 0 : ℝ) = -(x 0) := rfl
    rw [hneg, neg_sq, neg_div]
  · intro k
    rw [hvol k, ← setIntegral_preimage_toLp (fun Y : EuclideanSpace ℝ (Fin (m + 1)) =>
      min 1 ((Y 0) ^ 2)) (D k), hpre k, hTdef]
    have hkey := le_setIntegral_min_sq_coord (ρ k) (hρ0 k)
    have hnn : (0 : ℝ) ≤ (volume (Set.univ.pi fun i => Icc (-(ρ k i)) (ρ k i))).toReal :=
      ENNReal.toReal_nonneg
    calc (1 / 32 : ℝ) * (volume (Set.univ.pi fun i => Icc (-(ρ k i)) (ρ k i))).toReal
        ≤ 1 / 16 * (volume (Set.univ.pi fun i => Icc (-(ρ k i)) (ρ k i))).toReal := by linarith
      _ ≤ _ := hkey
  · intro Y hY
    have hY' : (Y 0 : ℝ) / (1 + (Y 0) ^ 2) = 0 := hY
    have hden : (0 : ℝ) < 1 + (Y 0) ^ 2 := by positivity
    have h0 : (Y 0 : ℝ) = 0 := by
      rcases div_eq_zero_iff.mp hY' with h | h
      · exact h
      · exact absurd h hden.ne'
    show min 1 ((Y 0) ^ 2) < 1 / 32
    rw [h0]
    norm_num

/-- **Non-vacuity of
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep`.**

Every hypothesis of that theorem — including the data hypothesis `hsep`, which is the whole
residual content of residue **(F)** — is met simultaneously by the chain and integrands of
`Arlib.exists_chain_euclidean_of_sep_data`, and the conclusion is then genuinely produced by the
theorem.  In particular the needle profile `W` that comes out is nonzero, since its `g₂`-integral
is positive. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep_witness
    (hm : m ≠ 0) :
    ∃ (D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1))))
      (g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (M ε : ℝ),
      (∀ k, IsCompact (D k)) ∧ (∀ k, Convex ℝ (D k)) ∧ (∀ k, D (k + 1) ⊆ D k) ∧
      (∀ k, 0 < volume (D k)) ∧ Collinear ℝ (⋂ k, D k) ∧
      Continuous g₁ ∧ Continuous g₂ ∧ (∀ x, |g₁ x| ≤ M) ∧ (∀ x, |g₂ x| ≤ M) ∧
      (∀ k, (∫ y in D k, g₁ y) = 0) ∧ 0 < ε ∧
      (∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) ∧
      (∀ x, g₁ x = 0 → g₂ x < ε) ∧
      ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), (∀ t, 0 ≤ W t) ∧
        (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
        ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
        (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
        0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  obtain ⟨D, g₁, g₂, M, ε, hcomp, hconv, hmono, hpos, hcol, hc₁, hc₂, hM₁, hM₂, hzero, hεpos,
    hge, hsep⟩ := exists_chain_euclidean_of_sep_data (m := m)
  exact ⟨D, g₁, g₂, M, ε, hcomp, hconv, hmono, hpos, hcol, hc₁, hc₂, hM₁, hM₂, hzero, hεpos,
    hge, hsep,
    exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep hm hcomp hconv hmono
      hpos hcol hc₁ hc₂ hM₁ hM₂ hzero hεpos hge hsep⟩

end EuclideanWitness

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.abs_setIntegral_sub_measure_mul_le
#print axioms Arlib.exists_forall_abs_sub_le_of_chain_collapse
#print axioms Arlib.le_apply_of_chain_collapse
#print axioms Arlib.apply_le_of_chain_collapse
#print axioms Arlib.apply_eq_zero_of_chain_collapse
#print axioms Arlib.exists_ne_mem_iInter_of_chain
#print axioms Arlib.forall_lt_of_sign_separated
#print axioms Arlib.exists_ne_mem_iInter_of_chain_witness
#print axioms Arlib.collinear_image_linearMap
#print axioms Arlib.preimage_toLp_eq_image_ofLp
#print axioms Arlib.image_toLp_preimage_toLp
#print axioms Arlib.preimage_ofLp_preimage_toLp
#print axioms Arlib.measurableEmbedding_toLp
#print axioms Arlib.measurableSet_preimage_toLp_iff
#print axioms Arlib.isCompact_preimage_toLp_iff
#print axioms Arlib.convex_preimage_toLp_iff
#print axioms Arlib.collinear_preimage_toLp_iff
#print axioms Arlib.volume_preimage_toLp
#print axioms Arlib.setIntegral_preimage_toLp
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep
#print axioms Arlib.setIntegral_eq_zero_of_odd
#print axioms Arlib.collinear_of_subset_axis
#print axioms Arlib.volume_symmetricBox
#print axioms Arlib.neg_preimage_symmetricBox
#print axioms Arlib.volume_subBox_quarter
#print axioms Arlib.collinear_iInter_box
#print axioms Arlib.le_setIntegral_min_sq_coord
#print axioms Arlib.exists_chain_euclidean_of_sep_data
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep_witness
