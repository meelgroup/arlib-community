/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationTransport
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.HlocFromLocalization

/-!
# The chain and the needle, composed — and why the integrands cannot be merely measurable

`Arlib.gaussianRestricted_isoperimetry_of_localization`
(`Arlib/Convexity/HlocFromLocalization.lean:882`) proves Cousins–Vempala's `thm:iso` from one
residual binder `hLoc`, the Localization Lemma applied to

`g₁ = 1_{S₁}h − A·h`   and   `g₂ = (d/σ)·A·1_{S₂}h − 1_{S₃}h`

for **merely measurable** `S₁ S₂ S₃`.  `AUDIT.md:147-149` records two residuals of the
localisation stack standing between it and `hLoc`: **(C)** the continuity requirement on the
integrands and **(F)** the `v ≠ 0` nondegeneracy of the needle direction.

This file closes **(F)** outright and shows **(C)** is not a missing approximation step but a
genuine obstruction at the shape `hLoc` asks for.

## 1. (F), and the missing composition — `Arlib.exists_needle_of_compact_convex`

Two halves of the stack were never joined.  `Arlib.exists_flat_cut_chain_collinear_compact_ge`
(`LocalizationClosed.lean:219`) turns a compact convex body into a chain; the needle theorems of
`Arlib.Convexity.NeedleSlabChain` / `Arlib.Convexity.LocalizationTransport` turn a chain into a
needle.  Nothing composed them, so the localisation stack had no single entry point taking a body
to a needle.  `Arlib.exists_needle_of_compact_convex` is that entry point.

Along the way `v ≠ 0` is recovered.  It is **not** derivable after the fact from
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep`: that theorem's
conclusion is satisfied by a degenerate needle.  The clause is present one level down —
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab`
(`NeedleSlabAffine.lean:227`) delivers `φ v = 1` — and is *discarded* by the `-` pattern in the
proof of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain`
(`NeedleSlabChain.lean:288`).  So the composition below is a replay that keeps it, weakened to
`v ≠ 0` (which is what survives the transport to `EuclideanSpace`, `φ` being unavailable there).

`Arlib.exists_needle_of_compact_convex_witness` is the non-vacuity check: the closed unit ball
with `g₁ x = ⟪e₀,x⟫·max 0 (1−‖x‖)` and `g₂ x = ⟪e₀,x⟫²·max 0 (1−‖x‖)` meets every hypothesis at
once, `hsep` included, with `∫_K g₁ = 0` by oddness and `∫_K g₂ > 0` genuinely positive.

## 2. (C) is an obstruction, not a gap — §"Needle integrals are not almost-everywhere invariants"

Two theorems, both about the *hyperplane* `{x | ⟪e_j, x⟫ = 0}`, which is Lebesgue-null and
contains the whole coordinate axis `t ↦ t • e_i` for `i ≠ j`:

* `Arlib.exists_null_measurableSet_needleIntegral_eq_one` — a measurable `S` with `volume S = 0`,
  hence `∫_T 1_S = 0` for **every** `T`, together with a needle `(b, v)` with `v ≠ 0` and a
  profile `W` meeting every clause `hLoc` imposes on it, for which the needle integral
  `∫ W · 1_S ∘ needleMap b v` equals `1`.  Modifying an integrand on a null set leaves every
  hypothesis of the Localization Lemma untouched and moves its conclusion by `1`.  Therefore no
  argument that controls `1_{S₁}` only through its almost-everywhere class — `L¹` density, Lusin,
  Vitali–Carathéodory, in-measure approximation — can produce `hLoc`.  This is Route 2 refuted.

* `Arlib.exists_transverse_oscillation_eq_one` — for that same `S` and **every** body of positive
  volume, however thin, some point of the body has transverse oscillation exactly `1`.  The
  moduli `δ k` of `Arlib.exists_tendsto_transverse_modulus`
  (`LocalizationTransverse.lean:112`) are therefore `≥ 1` at every stage of every chain of
  positive-volume bodies, so they do not tend to `0`.  That lemma is the *unique* place the
  localisation limit passage consumes continuity — it is a uniform transverse-oscillation bound,
  not a dominated-convergence hypothesis — and it fails for indicators by a fixed constant.  This
  is Route 1 refuted.

Neither theorem says the Localization Lemma is false for measurable integrands; a needle is a
null set, so an integrand cannot be arranged to defeat *every* needle (Fubini forbids a null set
meeting every line in positive length).  What they say is that the two routes available to this
repository are closed, and that `Arlib.Convexity.LocalizationLSC`'s boundary — `S` open for the
positivity slot, an unremovable `η`-slack for the equality slot — is where the approximation
route genuinely stops.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.  Nothing below is named for a statement it does not prove.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### The needle direction is nonzero — residual (F) -/

section NonDegenerate

variable {m : ℕ}

/-- **`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` with `v ≠ 0` kept.**

Identical to that theorem except that the nondegeneracy of the needle direction, which is
available as `φ v = 1` from
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` and discarded there, is
retained and weakened to `v ≠ 0`.  Only `v ≠ 0` survives the transport to `EuclideanSpace`, where
the height functional `φ` has no counterpart, and `v ≠ 0` is exactly the clause `hLoc` asks for. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain_ne_zero (hm : m ≠ 0)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ ⋂ k, D k) (hq : q ∈ ⋂ k, D k) (hpq : p ≠ q)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧
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
  obtain ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab hm hDconv hDcomp hDmono
      hDpos hl0 hu1 hslab hspan hl hu hcol hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  refine ⟨b, v, W, ?_, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩
  intro hv
  rw [hv, map_zero] at hφv
  exact zero_ne_one hφv

/-- **The `v ≠ 0` form, on `EuclideanSpace`.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean` with the nondegeneracy
clause retained.  The transport is the one of `Arlib.Convexity.LocalizationTransport`; `v ≠ 0`
crosses it because `WithLp.toLp` is injective and sends `0` to `0`. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_ne_zero (hm : m ≠ 0)
    {D : ℕ → Set (EuclideanSpace ℝ (Fin (m + 1)))} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {p q : EuclideanSpace ℝ (Fin (m + 1))} (hp : p ∈ ⋂ k, D k) (hq : q ∈ ⋂ k, D k) (hpq : p ≠ q)
    {g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧
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
  obtain ⟨b, v, W, hv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_chain_ne_zero hm hFcomp hFconv hFmono hFpos
      hFcol (hmemF p hp) (hmemF q hq) hpq' hcont₁ hcont₂ (fun x => hM₁ _) (fun x => hM₂ _)
      hzeroF hεpos hgeF
  refine ⟨WithLp.toLp 2 b, WithLp.toLp 2 v, W, ?_, hW0, hWsupp, hWint, hWc, ?_, ?_⟩
  · intro hzero'
    exact hv (WithLp.toLp_injective 2 (by rw [hzero']; simp))
  · rw [← hW₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2
  · refine lt_of_lt_of_le hW₂ (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    congr 2

end NonDegenerate

/-! ### The composition: from a compact convex body to a needle -/

section Composition

variable {m : ℕ}

/-- **The Localization Lemma for bounded continuous integrable integrands, from a body.**

The two halves of the localisation stack, joined.  From a *compact convex* body `K` of
`EuclideanSpace ℝ (Fin (m+1))` carrying `∫_K g₁ = 0` and `ε · vol K < ∫_K g₂`,
`Arlib.exists_flat_cut_chain_collinear_compact_ge` builds a chain with those invariants and a
collinear intersection, and
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_ne_zero` turns the chain
into a needle.  Neither step existed as a composite before: the stack had no entry point taking a
body to a needle.

The conclusion carries **every** clause `hLoc` imposes on `(v, W)` — `v ≠ 0`, nonnegativity,
support in `[0,1]`, integrability, concavity of `W ^ (1/m)` on `Ioo 0 1`, the vanishing needle
mass of `g₁` and the positive needle mass of `g₂` — in the stack's raw shape, which
`Arlib.hloc_of_localization` is built to consume.

The hypotheses are those of the two halves and nothing more:

* `Continuous g₁`, `Continuous g₂` with a common bound `M` — residual **(C)**, and the §2
  theorems of this file show it cannot be dropped by approximation;
* `Integrable g₁`, `Integrable g₂` — what the cutting scheme of
  `Arlib.exists_flat_cut_chain` asks for, and what Lovász–Simonovits ask for;
* `hsep : ∀ x, g₁ x = 0 → g₂ x < ε` — the nondegeneracy input of
  `Arlib.exists_ne_mem_iInter_of_chain`; without it the cutting scheme may collapse to a point.
-/
theorem exists_needle_of_compact_convex (hm : m ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsCompact K) (hKconv : Convex ℝ K)
    {g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hi₁ : Integrable g₁) (hi₂ : Integrable g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : (∫ x in K, g₁ x) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hKpos : ε * (volume K).toReal < ∫ x in K, g₂ x)
    (hsep : ∀ x, g₁ x = 0 → g₂ x < ε) :
    ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  obtain ⟨D, _, hDmono, hDinv, hDcol⟩ :=
    exists_flat_cut_chain_collinear_compact_ge (n := m + 1) (by omega) hi₁ hi₂ hK hKconv hzero
      hKpos
  have hDcomp : ∀ k, IsCompact (D k) := fun k => (hDinv k).1
  have hDconv : ∀ k, Convex ℝ (D k) := fun k => (hDinv k).2.1
  have hDpos : ∀ k, 0 < volume (D k) := fun k => (hDinv k).2.2.2.1
  have hDzero : ∀ k, (∫ y in D k, g₁ y) = 0 := fun k => (hDinv k).2.2.2.2.1
  have hDge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y := fun k => (hDinv k).2.2.2.2.2
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    exists_ne_mem_iInter_of_chain hDcomp hDmono hDpos (fun k => (hDcomp k).measure_lt_top.ne)
      hg₁ hg₂ (fun k => hi₁.integrableOn) (fun k => hi₂.integrableOn) hDzero hDge hsep
  exact exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_ne_zero hm hDcomp hDconv
    hDmono hDpos hDcol hp hq hpq hg₁ hg₂ hM₁ hM₂ hDzero hεpos hDge

/-- **Non-vacuity of `Arlib.exists_needle_of_compact_convex`.**

Every hypothesis of that theorem is met simultaneously, and by *nondegenerate* data: the body is
the closed unit ball, and the integrands are

`g₁ x = ⟪e₀, x⟫ · ψ x`,   `g₂ x = ⟪e₀, x⟫² · ψ x`,   `ψ x = max 0 (1 − ‖x‖)`,

which are continuous, bounded by `1`, and integrable because `ψ` has compact support.  `g₁` is
**odd** and the ball is symmetric, so `∫_K g₁ = 0` exactly; `g₂` is nonnegative and strictly
positive on a nonempty open set, so `∫_K g₂ > 0` and `ε` can be taken to be half the average.
The data hypothesis `hsep` holds for the sharpest possible reason: `g₁ x = 0` forces
`⟪e₀, x⟫ = 0` or `ψ x = 0`, and either makes `g₂ x` vanish. -/
theorem exists_needle_of_compact_convex_witness (hm : m ≠ 0) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin (m + 1))))
      (g₁ g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (M ε : ℝ),
      IsCompact K ∧ Convex ℝ K ∧ Continuous g₁ ∧ Continuous g₂ ∧
      Integrable g₁ ∧ Integrable g₂ ∧ (∀ x, |g₁ x| ≤ M) ∧ (∀ x, |g₂ x| ≤ M) ∧
      (∫ x in K, g₁ x) = 0 ∧ 0 < ε ∧ ε * (volume K).toReal < ∫ x in K, g₂ x ∧
      (∀ x, g₁ x = 0 → g₂ x < ε) ∧
      ∃ (b v : EuclideanSpace ℝ (Fin (m + 1))) (W : ℝ → ℝ), v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧
        (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
        ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
        (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
        0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  classical
  set e₀ : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single 0 (1 : ℝ) with he₀def
  set c : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := innerSL ℝ e₀ with hcdef
  set ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x => max 0 (1 - ‖x‖) with hψdef
  set g₁ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x => c x * ψ x with hg₁def
  set g₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x => (c x) ^ 2 * ψ x with hg₂def
  set K : Set (EuclideanSpace ℝ (Fin (m + 1))) := Metric.closedBall 0 1 with hKdef
  -- `e₀` is a unit vector, so `|c x| ≤ ‖x‖`.
  have he₀sq : ‖e₀‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact inner_single_one_self 0
  have he₀ : ‖e₀‖ = 1 := by nlinarith [norm_nonneg e₀]
  have hcabs : ∀ x, |c x| ≤ ‖x‖ := by
    intro x
    have := abs_real_inner_le_norm e₀ x
    rw [he₀, one_mul] at this
    exact this
  -- basic facts about the bump `ψ`
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => le_max_left _ _
  have hψzero : ∀ x, 1 ≤ ‖x‖ → ψ x = 0 := by
    intro x hx; rw [hψdef]; exact max_eq_left (by linarith)
  have hψval : ∀ x, ‖x‖ < 1 → ψ x = 1 - ‖x‖ := by
    intro x hx; rw [hψdef]; exact max_eq_right (by linarith)
  have hψc : Continuous ψ := by
    rw [hψdef]; exact continuous_const.max (continuous_const.sub continuous_norm)
  have hψneg : ∀ x, ψ (-x) = ψ x := by intro x; rw [hψdef]; simp
  -- continuity, compact support and integrability
  have hg₁c : Continuous g₁ := by rw [hg₁def]; exact c.continuous.mul hψc
  have hg₂c : Continuous g₂ := by rw [hg₂def]; exact (c.continuous.pow 2).mul hψc
  have hcs : ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, (∀ x, 1 ≤ ‖x‖ → f x = 0) →
      HasCompactSupport f := by
    intro f hf
    refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      fun x hx => hf x ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  have hi₁ : Integrable g₁ :=
    hg₁c.integrable_of_hasCompactSupport
      (hcs g₁ fun x hx => by rw [hg₁def]; simp only; rw [hψzero x hx, mul_zero])
  have hi₂ : Integrable g₂ :=
    hg₂c.integrable_of_hasCompactSupport
      (hcs g₂ fun x hx => by rw [hg₂def]; simp only; rw [hψzero x hx, mul_zero])
  -- both integrands are bounded by `1`
  have hM₁ : ∀ x, |g₁ x| ≤ 1 := by
    intro x
    rw [hg₁def]
    simp only
    rw [abs_mul, abs_of_nonneg (hψ0 x)]
    by_cases h : 1 ≤ ‖x‖
    · rw [hψzero x h, mul_zero]; norm_num
    · rw [hψval x (lt_of_not_ge h)]
      nlinarith [hcabs x, abs_nonneg (c x), norm_nonneg x]
  have hM₂ : ∀ x, |g₂ x| ≤ 1 := by
    intro x
    rw [hg₂def]
    simp only
    rw [abs_mul, abs_of_nonneg (hψ0 x), abs_of_nonneg (sq_nonneg (c x))]
    have hsq : (c x) ^ 2 ≤ ‖x‖ ^ 2 := by
      have := hcabs x
      nlinarith [abs_nonneg (c x), sq_abs (c x), norm_nonneg x]
    by_cases h : 1 ≤ ‖x‖
    · rw [hψzero x h, mul_zero]; norm_num
    · rw [hψval x (lt_of_not_ge h)]
      nlinarith [sq_nonneg (c x), norm_nonneg x]
  -- `K` is a compact convex symmetric body of positive finite volume
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKvolpos : 0 < volume K :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos)
      (measure_mono Metric.ball_subset_closedBall)
  have hKvolfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hKreal : 0 < (volume K).toReal := ENNReal.toReal_pos hKvolpos.ne' hKvolfin
  -- `g₁` is odd and `K` symmetric, so its mass vanishes exactly
  have hg₁odd : ∀ x, g₁ (-x) = -g₁ x := by
    intro x
    rw [hg₁def]
    simp only
    rw [hψneg x, map_neg, neg_mul]
  have hKsymm : (fun x : EuclideanSpace ℝ (Fin (m + 1)) => -x) ⁻¹' K = K := by
    ext x
    simp [hKdef, Metric.mem_closedBall, dist_zero_right]
  have hzero : (∫ x in K, g₁ x) = 0 :=
    setIntegral_eq_zero_of_odd (Measure.measurePreserving_neg volume) hKsymm hg₁odd
  -- `g₂` is nonnegative and positive on a nonempty open subset of `K`
  have hg₂nonneg : ∀ x, 0 ≤ g₂ x := by
    intro x; rw [hg₂def]; exact mul_nonneg (sq_nonneg _) (hψ0 x)
  have hUopen : IsOpen ({x : EuclideanSpace ℝ (Fin (m + 1)) | c x ≠ 0} ∩ Metric.ball 0 1) :=
    (isOpen_ne.preimage c.continuous).inter Metric.isOpen_ball
  have hx₀c : c ((1 / 2 : ℝ) • e₀) = 1 / 2 := by
    rw [map_smul, smul_eq_mul, hcdef]
    show (1 / 2 : ℝ) * inner ℝ e₀ e₀ = 1 / 2
    rw [he₀def, inner_single_one_self 0, mul_one]
  have hx₀n : ‖(1 / 2 : ℝ) • e₀‖ = 1 / 2 := by
    rw [norm_smul, he₀, mul_one, Real.norm_eq_abs]; norm_num
  have hUne : ({x : EuclideanSpace ℝ (Fin (m + 1)) | c x ≠ 0} ∩ Metric.ball 0 1).Nonempty := by
    refine ⟨(1 / 2 : ℝ) • e₀, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, hx₀c]; norm_num
    · rw [Metric.mem_ball, dist_zero_right, hx₀n]; norm_num
  have hUsub : ({x : EuclideanSpace ℝ (Fin (m + 1)) | c x ≠ 0} ∩ Metric.ball 0 1)
      ⊆ Function.support g₂ ∩ K := by
    rintro x ⟨hx1, hx2⟩
    rw [Metric.mem_ball, dist_zero_right] at hx2
    refine ⟨?_, ?_⟩
    · rw [Function.mem_support, hg₂def]
      simp only
      rw [hψval x hx2]
      have hx1' : c x ≠ 0 := hx1
      have h1 : (0 : ℝ) < (c x) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx1'))
      have h2 : (0 : ℝ) < 1 - ‖x‖ := by linarith
      exact ne_of_gt (mul_pos h1 h2)
    · rw [hKdef, Metric.mem_closedBall, dist_zero_right]; linarith
  have hsuppos : 0 < volume (Function.support g₂ ∩ K) :=
    lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hUsub)
  have hpos : 0 < ∫ x in K, g₂ x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall hg₂nonneg) hi₂.integrableOn]
    exact hsuppos
  -- take `ε` to be half the average of `g₂` over `K`
  set ε : ℝ := (∫ x in K, g₂ x) / (2 * (volume K).toReal) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos hpos (by linarith)
  have hhalf : ε * (volume K).toReal = (∫ x in K, g₂ x) / 2 := by
    rw [hεdef, div_mul_eq_mul_div, mul_comm (2 : ℝ) ((volume K).toReal), ← div_div,
      mul_div_assoc, div_self hKreal.ne', mul_one]
  have hεK : ε * (volume K).toReal < ∫ x in K, g₂ x := by rw [hhalf]; linarith
  have hsep : ∀ x, g₁ x = 0 → g₂ x < ε := by
    intro x hx
    have hg₂x : g₂ x = 0 := by
      rw [hg₁def] at hx
      simp only at hx
      rcases mul_eq_zero.mp hx with h | h
      · rw [hg₂def]; simp only; rw [h]; ring
      · rw [hg₂def]; simp only; rw [h, mul_zero]
    rw [hg₂x]; exact hεpos
  exact ⟨K, g₁, g₂, 1, ε, hK, hKconv, hg₁c, hg₂c, hi₁, hi₂, hM₁, hM₂, hzero, hεpos, hεK, hsep,
    exists_needle_of_compact_convex hm hK hKconv hg₁c hg₂c hi₁ hi₂ hM₁ hM₂ hzero hεpos hεK hsep⟩

end Composition

/-! ### Needle integrals are not almost-everywhere invariants — residual (C) -/

section NotAeInvariant

variable {n : ℕ}

/-- **A null measurable set whose needle mass is `1`.**

Take `S` the hyperplane `{x | ⟪e_j, x⟫ = 0}` and the needle `t ↦ 0 + t • e_i` for `i ≠ j`, which
lies entirely inside `S`, and `W = 1_{[0,1]}`.

* `volume S = 0`, so `∫_T 1_S = 0` for **every** set `T`: at the level of `ℝⁿ`-integrals — which
  is the *only* level at which `hLoc`'s hypotheses see `S₁, S₂, S₃` — the data `1_S` and the data
  `0` are indistinguishable.
* `W` satisfies every clause `hLoc` imposes on the profile: nonnegative, supported in `[0,1]`,
  integrable, with `W ^ (1/(n−1))` concave on `Ioo 0 1` (it is constantly `1` there).
* `v ≠ 0`.
* Yet the needle mass `∫ W · 1_S ∘ needleMap b v` is `1`, while the needle mass of `0` is `0`.

**Consequence.**  Replacing an integrand by an almost-everywhere equal one preserves every
hypothesis of the Localization Lemma and moves its conclusion by `1`.  So no argument that
controls `1_{S₁}` only through its almost-everywhere class can produce `hLoc`: not `L¹`-density
of continuous functions, not Lusin's theorem, not Vitali–Carathéodory, not any regularisation
that is accurate only in measure.  Continuous approximants must be compared to `1_{S₁}`
*pointwise*, which is why `Arlib.Convexity.LocalizationLSC` proceeds by monotone minorants and
stops where monotone minorants stop — at lower semicontinuity, i.e. at `S₁` open. -/
theorem exists_null_measurableSet_needleIntegral_eq_one (hn : 2 ≤ n) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin n))) (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
      MeasurableSet S ∧ volume S = 0 ∧
      (∀ T : Set (EuclideanSpace ℝ (Fin n)), (∫ x in T, S.indicator (fun _ => (1 : ℝ)) x) = 0) ∧
      v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
      Integrable W ∧
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
      Integrable (fun t => W t * S.indicator (fun _ => (1 : ℝ)) (needleMap b v t)) ∧
      (∫ t : ℝ, W t * S.indicator (fun _ => (1 : ℝ)) (needleMap b v t)) = 1 ∧
      (∫ t : ℝ, W t * (0 : ℝ)) = 0 := by
  classical
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, by omega⟩ with hj
  have hij : j ≠ i := by
    simp only [hi, hj, Ne, Fin.mk.injEq]
    omega
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ) with hv
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ e with hL
  set S : Set (EuclideanSpace ℝ (Fin n)) := {x | L x = 0} with hS
  set W : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) with hW
  -- `L` is nonzero, since `L e = 1`.
  have hLe : L e = 1 := inner_single_one_self j
  have hLne : L ≠ 0 := by
    intro h
    rw [h] at hLe
    exact one_ne_zero hLe.symm
  -- the hyperplane is measurable and null
  have hSmeas : MeasurableSet S := by
    have : S = L ⁻¹' {0} := rfl
    rw [this]
    exact (measurableSet_singleton (0 : ℝ)).preimage L.continuous.measurable
  have hSnull : volume S = 0 := measure_hyperplane_eq_zero volume hLne 0
  -- every set integral of `1_S` vanishes
  have hTzero : ∀ T : Set (EuclideanSpace ℝ (Fin n)),
      (∫ x in T, S.indicator (fun _ => (1 : ℝ)) x) = 0 := by
    intro T
    rw [integral_indicator hSmeas]
    refine setIntegral_measure_zero _ ?_
    rw [Measure.restrict_apply hSmeas]
    exact measure_mono_null Set.inter_subset_left hSnull
  -- the needle lies inside the hyperplane
  have hLv : L v = 0 := inner_single_one_ne hij
  have hmem : ∀ t : ℝ, needleMap (0 : EuclideanSpace ℝ (Fin n)) v t ∈ S := by
    intro t
    show L (needleMap (0 : EuclideanSpace ℝ (Fin n)) v t) = 0
    rw [needleMap_apply, zero_add, map_smul, smul_eq_mul, hLv, mul_zero]
  -- the two integrands coincide with `W`
  have hprod : (fun t => W t * S.indicator (fun _ => (1 : ℝ))
      (needleMap (0 : EuclideanSpace ℝ (Fin n)) v t)) = W := by
    funext t
    rw [Set.indicator_of_mem (hmem t), mul_one]
  -- `W` is integrable with integral one
  have hWint : Integrable W := by
    rw [hW]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp [Real.volume_Icc]))
  have hWintegral : (∫ t : ℝ, W t) = 1 := by
    rw [hW, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Real.volume_Icc]
    simp
  -- `W` is nonnegative and supported in `[0,1]`
  have hW0 : ∀ t, 0 ≤ W t := by
    intro t
    rw [hW]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hWsupp : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0 := fun t ht => by
    rw [hW]; exact Set.indicator_of_notMem ht _
  -- `W ^ (1/(n-1))` is constantly `1` on `Ioo 0 1`, hence concave there
  have hWone : ∀ t ∈ Set.Ioo (0 : ℝ) 1, W t ^ (1 / ((n : ℝ) - 1)) = 1 := by
    intro t ht
    rw [hW, Set.indicator_of_mem (Set.Ioo_subset_Icc_self ht), Real.one_rpow]
  have hWconc : ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) := by
    refine ⟨convex_Ioo 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have hmemc : a • x + b • y ∈ Set.Ioo (0 : ℝ) 1 := convex_Ioo (0 : ℝ) 1 hx hy ha hb hab
    show a • (W x ^ (1 / ((n : ℝ) - 1))) + b • (W y ^ (1 / ((n : ℝ) - 1)))
        ≤ W (a • x + b • y) ^ (1 / ((n : ℝ) - 1))
    rw [hWone x hx, hWone y hy, hWone _ hmemc]
    simp only [smul_eq_mul, mul_one]
    linarith
  refine ⟨S, 0, v, W, hSmeas, hSnull, hTzero, ?_, hW0, hWsupp, hWint, hWconc, ?_, ?_, ?_⟩
  · intro hv0
    have : L v = 0 := by rw [hv0, map_zero]
    have h1 : inner ℝ v v = (1 : ℝ) := inner_single_one_self i
    rw [hv0] at h1
    simp at h1
  · rw [hprod]; exact hWint
  · rw [hprod]; exact hWintegral
  · simp

/-- **The transverse oscillation of an indicator is `1` on every body of positive volume.**

`Arlib.exists_tendsto_transverse_modulus` (`LocalizationTransverse.lean:112`) is the unique place
where the localisation limit passage consumes continuity of the integrands, and it consumes it as
a *uniform transverse-oscillation bound*: the moduli

`δ k = sSup {|g y − g (a + φ (y − a) • v)| : y ∈ C k}`

must tend to `0`.  For `g` the indicator of the hyperplane `{x | ⟪e_j, x⟫ = 0}` and the axis
`t ↦ t • e_i` (`i ≠ j`), which lies inside that hyperplane, this fails by a fixed constant: the
axis point of *every* `y` is in the hyperplane, so `g` takes the value `1` there, while a body of
positive volume cannot be contained in the null hyperplane and hence contains a point where `g`
is `0`.  So `δ k ≥ 1` for **every** body of **every** chain of positive-volume bodies, no matter
how thin, and for **every** height functional `φ`.

This is the precise refutation of the route "weaken `Continuous` to `Measurable` + bounded in
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`": the hypothesis is not a convenience
of the proof, and no dominated-convergence argument replaces it. -/
theorem exists_transverse_oscillation_eq_one (hn : 2 ≤ n) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n)),
      MeasurableSet S ∧ volume S = 0 ∧ v ≠ 0 ∧
      ∀ (C : Set (EuclideanSpace ℝ (Fin n))), 0 < volume C →
        ∀ a ∈ S, ∀ φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ, ∃ y ∈ C,
          |S.indicator (fun _ => (1 : ℝ)) y
            - S.indicator (fun _ => (1 : ℝ)) (a + φ (y - a) • v)| = 1 := by
  classical
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, by omega⟩ with hj
  have hij : j ≠ i := by
    simp only [hi, hj, Ne, Fin.mk.injEq]
    omega
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ) with hv
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ e with hL
  set S : Set (EuclideanSpace ℝ (Fin n)) := {x | L x = 0} with hS
  have hLe : L e = 1 := inner_single_one_self j
  have hLne : L ≠ 0 := by
    intro h
    rw [h] at hLe
    exact one_ne_zero hLe.symm
  have hSmeas : MeasurableSet S := by
    have : S = L ⁻¹' {0} := rfl
    rw [this]
    exact (measurableSet_singleton (0 : ℝ)).preimage L.continuous.measurable
  have hSnull : volume S = 0 := measure_hyperplane_eq_zero volume hLne 0
  have hLv : L v = 0 := inner_single_one_ne hij
  refine ⟨S, v, hSmeas, hSnull, ?_, ?_⟩
  · intro hv0
    have h1 : inner ℝ v v = (1 : ℝ) := inner_single_one_self i
    rw [hv0] at h1
    simp at h1
  · intro C hC a haS φ
    -- a body of positive volume is not contained in the null hyperplane
    have hnsub : ¬ C ⊆ S := by
      intro hsub
      exact absurd (measure_mono_null hsub hSnull) hC.ne'
    obtain ⟨y, hyC, hyS⟩ := Set.not_subset.mp hnsub
    have hLa : L a = 0 := haS
    have haxis : a + φ (y - a) • v ∈ S := by
      show L (a + φ (y - a) • v) = 0
      rw [map_add, map_smul, smul_eq_mul, hLv, mul_zero, add_zero, hLa]
    refine ⟨y, hyC, ?_⟩
    rw [Set.indicator_of_notMem hyS, Set.indicator_of_mem haxis]
    norm_num

end NotAeInvariant

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_ne_zero
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_ne_zero
#print axioms Arlib.exists_needle_of_compact_convex
#print axioms Arlib.exists_needle_of_compact_convex_witness
#print axioms Arlib.exists_null_measurableSet_needleIntegral_eq_one
#print axioms Arlib.exists_transverse_oscillation_eq_one
