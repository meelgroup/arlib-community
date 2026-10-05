/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatioIsoBridge

/-!
# The weighted cross-ratio isoperimetry of Lee's book §10.6 — and a refutation of `hthm21`

**Read this first: the statement this file was written to prove is false, and the file proves it
is false.**  `Arlib.thm21_book` does not exist here and cannot exist anywhere.  What does exist
is the refutation, the corrected statement, the bridge rebuilt on the corrected statement, and
three bricks of Lee's mollified route (*Optimization book*, §10.6, `thm:har_weighted_iso`).

## The refutation

`Arlib.hIso_of_thm21` and `Arlib.conductance_hitAndRun_ge_of_thm21`
(`Arlib/Convexity/CrossRatioIsoBridge.lean:436`) carry a binder `hthm21` quantifying over
**arbitrary** measurable `U₁, U₂` — with no clause placing them inside `K`.

`Arlib.not_thm21_book` refutes that binder, verbatim, at `n = 1`, `K = Metric.closedBall 0 1`.
The mechanism is `Arlib.one_le_crossRatioDist_of_notMem`: `crossRatioDist` is a ratio of norms,
so for `u ∉ K` and `v ∈ interior K` the chord parameters satisfy `0 < a ≤ 1 < b` and

    d_K(u,v) = (b − a)/(a(b − 1)) ≥ 1,   since   (b − a) − a(b − 1) = b(1 − a) ≥ 0.

Hence `min 1 (d_K(u,v)) / 3 = 1/3` for **every** such pair, and the chord hypothesis collapses to
the global bound `g ≤ 1/3` that Theorem 2.1 already assumes: it carries no geometric information
at all (`Arlib.chord_bound_of_notMem`).  The witness is then immediate — `U₁` a ball of volume
`vol K / 2` far outside `K`, `U₂` a ball of relative volume `9/10` inside `K`, `g ≡ 1/3`,
`A = 1/2` — and the conclusion would assert `vol K / 6 ≤ vol K / 10`.

`K` here is convex, closed, bounded, measurable and contains a unit ball, so it meets every
structural hypothesis of `Arlib.conductance_hitAndRun_ge_of_thm21`: the refutation lands at a
**legitimate call site**, not on a degenerate body.

`Arlib.false_of_hIso_of_thm21_binder` certifies that the refuted proposition really is that
binder and not a transcription of it: it feeds one and the same term to `Arlib.hIso_of_thm21`
and to `Arlib.not_thm21_book`, so any drift in either direction would fail to typecheck.

**Lovász–Vempala's Theorem 2.1 is not touched.**  Its `S₁, S₂, S₃` partition `K`.  The missing
clauses are exactly `U₁ ⊆ K` and `U₂ ⊆ K`, and they are exactly what
`Arlib.hIso_measurable_of_thm21` has in scope (`hT₁K`, `hT₂K`) at the only two places it uses the
binder.

## The repair, and the bridge rebuilt on it

`hthm21sub` is `hthm21` with `U₁ ⊆ K → U₂ ⊆ K →` inserted after the measurability clauses.

* `Arlib.hIso_measurable_of_thm21_sub` — `Arlib.hIso_measurable_of_thm21` rerun on `hthm21sub`.
* `Arlib.hIso_book` — **deliverable 2**: the `hIso` binder of
  `Arlib.MarkovChains.conductance_hitAndRun_ge`, verbatim, from `hthm21sub`.
* `Arlib.conductance_hitAndRun_ge_book` — **deliverable 3**: Theorem 4.2 with `hIso` discharged,
  leaving `hLem41` and `hthm21sub`.

The proofs are the originals with the two subset arguments passed through; the copying is forced
by the one-agent-per-file discipline.  **`Arlib.hIso_of_thm21` and
`Arlib.conductance_hitAndRun_ge_of_thm21` should be treated as dead**: their binder is refuted, so
nothing can ever be composed through them.

## The route's bricks

* `Arlib.needle_iso_masses` — the closing algebra of `Arlib.needle_iso`, stripped of all measure
  theory: four masses, one weight integral, two numeric bounds.
* `Arlib.needle_iso_weight` — **`Arlib.needle_iso` at function weights.**  This answers the
  question the brief asked to settle before assuming: the one-dimensional core *does* generalise
  from indicator sets to weights, and cheaply.  `∫_{Zᵢ} D` becomes `∫ fᵢ·D`, the third weight is
  `f₃ = 1 − f₁ − f₂` (not an independent datum), and `Arlib.oneDim_crossRatio_partition` is
  applied at the **supports** `Yᵢ = {t ∈ [α,β] | fᵢ t ≠ 0}`.  All three comparisons then move the
  right way at once: `∫f₁·D ≤ ∫_{Y₁}D`, `∫f₂·D ≤ ∫_{Y₂}D`, `∫_{Y₃}D ≤ ∫f₃·D`.
* `Arlib.needle_iso_of_chord_weight` — the same on a needle inside the body, with the chord
  hypothesis asked at the **enlarged supports** `N₁, N₂`.  Both transport lemmas
  (`Arlib.three_mul_sSup_le_crossRatioDist`, `Arlib.needle_crossRatio_transfer`) are stated for
  arbitrary sets, so they apply unchanged.
* `Arlib.bookMollifier` and its five lemmas — `f_T(x) = max{0, 1 − T·d(x,S)}`.  Continuous,
  in `[0,1]`, equal to `1` on `S` (so a **majorant** of `1_S`, making `f₃` a **minorant** of
  `1_{S₃}` — the direction the strict-inequality slot needs), supported within `1/T` of `S`, with
  disjoint supports for separated sets, and converging pointwise to `1_S` for `S` closed
  nonempty.

## Where the route stops, and why

**Step 5 of the route — the chord hypothesis at the enlarged supports — is not discharged, and
it is harder than a continuity-of-`crossRatioDist` estimate.**  It is isolated as the `hchord`
hypothesis of `Arlib.needle_iso_of_chord_weight`, quantified over `N₁ × N₂` rather than
`U₁ × U₂`.  Transferring it needs, for `u ∈ N₁`, `v ∈ N₂` and `x ∈ K` on the chord through
`u, v`, a bound on `g x` — and the given hypothesis bounds `g` only on chords through pairs in
`U₁ × U₂`.  The point `x` need not lie on any such chord, and for a merely **measurable** `g`
nothing relates its value at `x` to its values on nearby chords.  This is a statement about `g`,
not only about the cross-ratio distance.

**The measurable-`g` slot is an independent obstruction.**  `g` rides in the strict-inequality
integrand `g₂ = A·g·1_K − f₃`, and every localisation entry point in this repository
(`Arlib.exists_needle_of_compact_convex`, and `Arlib.Convexity.LocalizationLSC` at its weakest)
needs that integrand approximated **from below** by a continuous or lower semicontinuous
function.  For a measurable `g` no continuous minorant recovers `∫_K g`: for `V` a fat Cantor set
a continuous `φ` with `0 ≤ φ ≤ 1_V` vanishes on the dense complement of `V`, hence vanishes.
This is the same wall `Arlib.Convexity.LocalizationLSC` documents, met from the weight side
rather than the set side, and it is not removed by the mollification, which touches only `S₁` and
`S₂`.

Consequently a `Continuous g` version of the corrected Theorem 2.1 would still **not** feed
`Arlib.hIso_book`, which reduces an arbitrary `h` to **simple** minorants, not continuous ones.

## What is assumed

**Nothing.**  Every declaration below is a `theorem` except `Arlib.bookMollifier` (a formula) and
the private `Arlib.farPoint` (a point); neither is a `structure`, a `class`, or a named `Prop`,
and neither claims a semantic identity it does not prove.  No theorem here takes the Localization
Lemma, Theorem 2.1, or any part of either as a hypothesis, apart from the three explicitly named
`hthm21sub` binders of the repaired bridge, which are written out inline at their declarations.
-/

namespace Arlib

open MeasureTheory Set

open scoped NNReal ENNReal

/-! ### The cross-ratio distance from a point *outside* the body -/

section Outside

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-- **The chord parameter of a point outside a convex body is strictly positive.**

If `u ∉ K` while `v ∈ K`, the parameter set `{t | lineMap u v t ∈ K}` is a nonempty compact
convex subset of `ℝ` that misses `0` and contains `1`, so its infimum — which is attained,
`K` being closed — is strictly positive. -/
theorem chordLow_pos_of_notMem (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∉ K) (hv : v ∈ K) :
    0 < chordLow K u v := by
  have hne : (chordParam K u v).Nonempty := ⟨1, one_mem_chordParam hv⟩
  have hbb : BddBelow (chordParam K u v) := bddBelow_chordParam hKb huv
  have hmem : chordLow K u v ∈ chordParam K u v :=
    (isClosed_chordParam hKcl).csInf_mem hne hbb
  rcases le_or_gt (chordLow K u v) 0 with h | h
  · exfalso
    have h0 : (0 : ℝ) ∈ chordParam K u v :=
      ((convex_chordParam hKc).ordConnected).out hmem (one_mem_chordParam hv)
        ⟨h, zero_le_one⟩
    exact hu (by simpa using (mem_chordParam.mp h0))
  · exact h

/-- **The cross-ratio distance seen from outside the body is at least `1`.**

For `u ∉ K` and `v` in the *interior* of a compact convex `K`, the chord parameters satisfy
`0 < a ≤ 1 < b` (`a ≤ 1` because `1` is a parameter, `a > 0` because `0` is not), and

    d_K(u,v) = (b − a) / (a·(b − 1)),   with   (b − a) − a·(b − 1) = b·(1 − a) ≥ 0.

**This is the fact that refutes the ambient statement below**: the chord hypothesis of
Lovász–Vempala's Theorem 2.1 reads `g x ≤ min 1 (d_K(u,v)) / 3`, and the `min` is pinned at `1`
for every pair with `u` outside `K`.  The hypothesis therefore says nothing at all beyond the
global bound `g ≤ 1/3`, and cannot control the geometry it is meant to control. -/
theorem one_le_crossRatioDist_of_notMem (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∉ K) (hv : v ∈ interior K) :
    1 ≤ crossRatioDist K u v := by
  have hvK : v ∈ K := interior_subset hv
  have hb : 1 < chordHigh K u v := one_lt_chordHigh_of_mem_interior hKb huv hv
  have ha1 : chordLow K u v ≤ 1 :=
    csInf_le (bddBelow_chordParam hKb huv) (one_mem_chordParam hvK)
  have ha0 : 0 < chordLow K u v := chordLow_pos_of_notMem hKc hKcl hKb huv hu hvK
  have hd : (0 : ℝ) < dist u v := dist_pos.mpr huv
  set a := chordLow K u v with hadef
  set b := chordHigh K u v with hbdef
  have hdd : dist u v * dist u v ≠ 0 := by positivity
  have hform : crossRatioDist K u v = (b - a) / (a * (b - 1)) := by
    unfold crossRatioDist chordStart chordEnd
    rw [dist_lineMap_lineMap', dist_lineMap_left, dist_lineMap_right,
      abs_of_nonpos (by linarith : a - b ≤ 0), abs_of_pos ha0,
      abs_of_nonpos (by linarith : (1 : ℝ) - b ≤ 0)]
    rw [show dist u v * (-(a - b) * dist u v)
          = dist u v * dist u v * (b - a) by ring,
      show a * dist u v * (-(1 - b) * dist u v)
          = dist u v * dist u v * (a * (b - 1)) by ring,
      mul_div_mul_left _ _ hdd]
  rw [hform, le_div_iff₀ (by nlinarith : (0 : ℝ) < a * (b - 1))]
  nlinarith

/-- **The chord hypothesis of Theorem 2.1 is free when `U₁` misses the body.**

If no point of `U₁` lies in `K` and `U₂` sits in the interior of `K`, then
`min 1 (d_K(u,v)) = 1` for every cross pair, so the chord bound reduces to the global bound
`g ≤ 1/3` on `K` — which Theorem 2.1 assumes anyway.  The hypothesis carries no geometric
information whatsoever in this configuration. -/
theorem chord_bound_of_notMem (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {U₁ U₂ : Set E}
    (hU₁ : ∀ u ∈ U₁, u ∉ K) (hU₂ : U₂ ⊆ interior K)
    {g : E → ℝ} (hg3 : ∀ x ∈ K, g x ≤ 1 / 3) :
    ∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → E) r) →
      g x ≤ min 1 (crossRatioDist K u v) / 3 := by
  intro u hu v hv x hx _
  have huK : u ∉ K := hU₁ u hu
  have hvI : v ∈ interior K := hU₂ hv
  have huv : u ≠ v := fun h => huK (h ▸ interior_subset hvI)
  rw [min_eq_left (one_le_crossRatioDist_of_notMem hKc hKcl hKb huv huK hvI)]
  exact hg3 x hx

end Outside

/-! ### The refutation of the ambient statement `hthm21`

`Arlib.hIso_of_thm21` and `Arlib.conductance_hitAndRun_ge_of_thm21`
(`Arlib/Convexity/CrossRatioIsoBridge.lean:436`) carry a binder `hthm21` that quantifies over
**arbitrary** measurable `U₁, U₂`, with no clause placing them inside `K`.  The theorem below
refutes that binder at `n = 1`, `K = closedBall 0 1` — a body meeting every structural
hypothesis of `Arlib.conductance_hitAndRun_ge_of_thm21` (convex, closed, bounded, measurable,
containing a unit ball), so the refutation lands at a *legitimate call site* and is not an
artefact of a degenerate `K`.

The witness is the configuration analysed above: `U₁` a ball of the right volume placed **far
outside** `K`, `U₂` a ball of relative volume `9/10` inside `K`, `g ≡ 1/3`, `A = 1/2`.  Every
hypothesis holds — the chord clause by `Arlib.chord_bound_of_notMem` — while the conclusion
would assert `vol K / 6 ≤ vol K / 10`.

**What this does and does not say.**  It says the `hthm21` binder as printed is *unprovable*, so
`Arlib.hIso_of_thm21` can never be run to completion in its present form.  It says nothing
against Lovász–Vempala's Theorem 2.1 itself, whose `S₁, S₂, S₃` are a *partition of `K`*: the
two subset clauses `U₁ ⊆ K`, `U₂ ⊆ K` are exactly what is missing, and they are exactly what
`Arlib.hIso_measurable_of_thm21` supplies at the only place the binder is used (`hT₁K`, `hT₂K`).
The corrected binder is therefore a drop-in replacement downstream. -/

section Refutation

open Metric

/-- The far-away centre of the outside ball: the point of `EuclideanSpace ℝ (Fin 1)` at
distance `10` from the origin along the single coordinate axis. -/
private noncomputable def farPoint : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single (0 : Fin 1) (10 : ℝ)

private theorem norm_farPoint : ‖farPoint‖ = 10 := by
  rw [farPoint, PiLp.norm_single, Real.norm_eq_abs]
  norm_num

/-- **The ambient statement `hthm21` of `Arlib.conductance_hitAndRun_ge_of_thm21` is false.**

Stated verbatim — the binder's own hypothesis order and shape — at `n = 1` and
`K = Metric.closedBall 0 1`.  See the section docstring for what is and is not refuted; the
short version is that the binder omits `U₁ ⊆ K` and `U₂ ⊆ K`. -/
theorem not_thm21_book :
    ¬ ∀ (g : EuclideanSpace ℝ (Fin 1) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin 1))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 1)) r) →
        g x ≤ min 1 (crossRatioDist (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 →
        (volume U₁).toReal
            = A * (volume (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).toReal →
        A * (∫ x in closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, g x)
          ≤ (volume ((closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 \ U₁) \ U₂)).toReal := by
  intro hthm21
  set E := EuclideanSpace ℝ (Fin 1)
  set K : Set E := closedBall (0 : E) 1 with hKdef
  set U₁ : Set E := closedBall farPoint (1 / 2) with hU₁def
  set U₂ : Set E := closedBall (0 : E) (9 / 10) with hU₂def
  have hrank : Module.finrank ℝ E = 1 := by
    simp [E]
  -- volumes
  have hV0 : 0 < volume K := measure_closedBall_pos volume (0 : E) one_pos
  have hVtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hVR : 0 < (volume K).toReal := ENNReal.toReal_pos hV0.ne' hVtop
  have hU₁vol : (volume U₁).toReal = 1 / 2 * (volume K).toReal := by
    rw [hU₁def, hKdef, Measure.addHaar_closedBall' volume farPoint (by norm_num : (0:ℝ) ≤ 1/2),
      hrank, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hU₂vol : (volume U₂).toReal = 9 / 10 * (volume K).toReal := by
    rw [hU₂def, hKdef, Measure.addHaar_closedBall' volume (0 : E) (by norm_num : (0:ℝ) ≤ 9/10),
      hrank, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  -- geometry
  have hU₂sub : U₂ ⊆ K := closedBall_subset_closedBall (by norm_num)
  have hU₂int : U₂ ⊆ interior K := by
    rw [hKdef, interior_closedBall (0 : E) one_ne_zero]
    exact closedBall_subset_ball (by norm_num)
  have hfar : ∀ u ∈ U₁, (19 : ℝ) / 2 ≤ ‖u‖ := by
    intro u hu
    have h1 : dist u farPoint ≤ 1 / 2 := by rw [hU₁def] at hu; exact hu
    have h2 : ‖farPoint‖ - ‖u‖ ≤ dist u farPoint := by
      rw [dist_eq_norm, ← norm_neg (u - farPoint), neg_sub]
      exact norm_sub_norm_le _ _
    rw [norm_farPoint] at h2
    linarith
  have hU₁out : ∀ u ∈ U₁, u ∉ K := by
    intro u hu hmem
    have h1 : ‖u‖ ≤ 1 := by
      rw [hKdef, mem_closedBall, dist_zero_right] at hmem; exact hmem
    have := hfar u hu
    linarith
  have hdisj : Disjoint U₁ U₂ := by
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    have h1 : ‖x‖ ≤ 9 / 10 := by
      rw [hU₂def, mem_closedBall, dist_zero_right] at hx₂; exact hx₂
    have := hfar x hx₁
    linarith
  -- the two set identities
  have hdiff₁ : K \ U₁ = K := by
    refine Set.Subset.antisymm Set.sdiff_subset fun x hx => ⟨hx, fun hx₁ => hU₁out x hx₁ hx⟩
  have hQ : (K \ U₁) \ U₂ = K \ U₂ := by rw [hdiff₁]
  have hQvol : (volume ((K \ U₁) \ U₂)).toReal = 1 / 10 * (volume K).toReal := by
    rw [hQ, measure_sdiff hU₂sub measurableSet_closedBall.nullMeasurableSet
      (ne_top_of_le_ne_top hVtop (measure_mono hU₂sub)),
      ENNReal.toReal_sub_of_le (measure_mono hU₂sub) hVtop, hU₂vol]
    ring
  -- the integral of the constant weight
  have hint : (∫ _x in K, (1 / 3 : ℝ)) = 1 / 3 * (volume K).toReal := by
    rw [setIntegral_const, smul_eq_mul, Measure.real]
    ring
  -- every hypothesis is met
  have hmain := hthm21 (fun _ => (1 / 3 : ℝ)) U₁ U₂ measurable_const
    measurableSet_closedBall measurableSet_closedBall hdisj (fun _ => by norm_num)
    (fun _ _ => le_rfl)
    (chord_bound_of_notMem (convex_closedBall _ _) isClosed_closedBall
      (isBounded_closedBall) hU₁out hU₂int (fun _ _ => le_rfl))
    (1 / 2) (by norm_num) le_rfl (by rw [hU₁vol])
  rw [hint, hQvol] at hmain
  linarith

/-- **The proposition refuted above *is* the `hthm21` binder of `Arlib.hIso_of_thm21`**, not a
lookalike.

The hypothesis is written out, and the proof then feeds the *same term* to both
`Arlib.hIso_of_thm21` and `Arlib.not_thm21_book`.  So the write-out is checked in both
directions: had it drifted from the binder of `Arlib.hIso_of_thm21` in any respect — hypothesis
order, implicit/explicit status, the shape of any clause — the first line would not typecheck,
and had it drifted from `Arlib.not_thm21_book` the second would not.

Conclusion: the binder is **unprovable**, so `Arlib.hIso_of_thm21` and
`Arlib.conductance_hitAndRun_ge_of_thm21`, which carries the same binder, can never be run to
completion.  (`hK0` and `hKtop` need not be true for this; they are binders of
`Arlib.hIso_of_thm21` and only their presence matters.) -/
theorem false_of_hIso_of_thm21_binder
    (hKb : Bornology.IsBounded (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1))
    (hKm : MeasurableSet (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1))
    (hK0 : volume (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) ≠ 0)
    (hKtop : volume (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) ≠ ⊤)
    (hthm21 : ∀ (g : EuclideanSpace ℝ (Fin 1) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin 1))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 1)) r) →
        g x ≤ min 1 (crossRatioDist (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 →
        (volume U₁).toReal
            = A * (volume (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).toReal →
        A * (∫ x in closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, g x)
          ≤ (volume ((closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 \ U₁) \ U₂)).toReal) :
    False := by
  have _hIso := hIso_of_thm21 hKb hKm hK0 hKtop hthm21
  exact not_thm21_book hthm21

end Refutation

/-! ### The corrected binder, and the bridge rebuilt on it

`Arlib.not_thm21_book` leaves `Arlib.hIso_of_thm21` and
`Arlib.conductance_hitAndRun_ge_of_thm21` with a hypothesis nobody can supply.  This section
repairs the chain by rerunning it against `hthm21sub` — the same statement with `U₁ ⊆ K` and
`U₂ ⊆ K` inserted after the measurability clauses.

Nothing is lost downstream.  `Arlib.hIso_measurable_of_thm21` applies its binder at exactly two
places, and in both the sets are `T₁, T₂` with `hT₁K : T₁ ⊆ K`, `hT₂K : T₂ ⊆ K` already in
scope; the proofs below are the originals with those two arguments passed through.  The
one-agent-per-file discipline is why they are copied rather than edited in place. -/

section Corrected

variable {n : ℕ}

/-- **The `hIso` conclusion for measurable `h`, from the *corrected* Theorem 2.1 binder.**

`Arlib.hIso_measurable_of_thm21` with `hthm21` replaced by `hthm21sub`; the proof is the
original, with `hT₁K` and `hT₂K` supplied at the two application sites (in the swapped branch,
in the swapped order). -/
theorem hIso_measurable_of_thm21_sub {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hthm21sub : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) → (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 → (volume U₁).toReal = A * (volume K).toReal →
        A * (∫ x in K, g x) ≤ (volume ((K \ U₁) \ U₂)).toReal)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhm : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    {T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K)
    (hdisj : Disjoint T₁ T₂)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
        min (uniformOn volume K T₁) (uniformOn volume K T₂)
      ≤ uniformOn volume K ((K \ T₁) \ T₂) := by
  have hQsub : (K \ T₁) \ T₂ ⊆ K := Set.sdiff_subset.trans Set.sdiff_subset
  have hQm : MeasurableSet ((K \ T₁) \ T₂) := (hKm.diff hT₁).diff hT₂
  have hT₁top : volume T₁ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₁K)
  have hT₂top : volume T₂ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₂K)
  have hQtop : volume ((K \ T₁) \ T₂) ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hQsub)
  have hVR : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKtop.lt_top⟩
  have hInt : IntegrableOn h K volume := by
    refine Integrable.mono' (integrable_const (1 / 3 : ℝ)) hhm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hKm]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
    exact hh3 x hx
  have conv : ∀ W : Set (EuclideanSpace ℝ (Fin n)), volume W ≠ ⊤ →
      (volume W).toReal / (volume K).toReal * (∫ x in K, h x)
        ≤ (volume ((K \ T₁) \ T₂)).toReal →
      ENNReal.ofReal (∫ x in K, h x) * volume W
        ≤ volume ((K \ T₁) \ T₂) * volume K := by
    intro W hWtop hreal
    have h2 := mul_le_mul_of_nonneg_right hreal hVR.le
    have h3 : (volume W).toReal / (volume K).toReal * (∫ x in K, h x) * (volume K).toReal
        = (volume W).toReal * (∫ x in K, h x) := by
      field_simp
    rw [h3] at h2
    have h4 := ENNReal.ofReal_le_ofReal h2
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hWtop, ENNReal.ofReal_toReal hQtop,
      ENNReal.ofReal_toReal hKtop] at h4
    calc ENNReal.ofReal (∫ x in K, h x) * volume W
        = volume W * ENNReal.ofReal (∫ x in K, h x) := mul_comm _ _
      _ ≤ _ := h4
  have key : ENNReal.ofReal (∫ x in K, h x) * min (volume T₁) (volume T₂)
      ≤ volume ((K \ T₁) \ T₂) * volume K := by
    have hhalf := two_mul_min_measure_le hT₂ hT₁K hT₂K hdisj
    rcases le_total (volume T₁) (volume T₂) with hmin | hmin
    · have hminEq : min (volume T₁) (volume T₂) = volume T₁ := min_eq_left hmin
      rw [hminEq] at hhalf ⊢
      have hA0 : 0 ≤ (volume T₁).toReal / (volume K).toReal :=
        div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hAhalf : (volume T₁).toReal / (volume K).toReal ≤ 1 / 2 := by
        have h4 := ENNReal.toReal_mono hKtop hhalf
        rw [div_le_iff₀ hVR]
        simp only [ENNReal.toReal_mul] at h4
        norm_num at h4 ⊢
        linarith
      have hmass : (volume T₁).toReal
          = (volume T₁).toReal / (volume K).toReal * (volume K).toReal := by field_simp
      exact conv T₁ hT₁top
        (hthm21sub h T₁ T₂ hhm hT₁ hT₂ hT₁K hT₂K hdisj hh0 hh3 hchord _ hA0 hAhalf hmass)
    · have hminEq : min (volume T₁) (volume T₂) = volume T₂ := min_eq_right hmin
      rw [hminEq] at hhalf ⊢
      have hA0 : 0 ≤ (volume T₂).toReal / (volume K).toReal :=
        div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hAhalf : (volume T₂).toReal / (volume K).toReal ≤ 1 / 2 := by
        have h4 := ENNReal.toReal_mono hKtop hhalf
        rw [div_le_iff₀ hVR]
        simp only [ENNReal.toReal_mul] at h4
        norm_num at h4 ⊢
        linarith
      have hmass : (volume T₂).toReal
          = (volume T₂).toReal / (volume K).toReal * (volume K).toReal := by field_simp
      have hswap := hthm21sub h T₂ T₁ hhm hT₂ hT₁ hT₂K hT₁K hdisj.symm hh0 hh3
        (chord_bound_comm hKb hT₁K hT₂K hdisj hchord) _ hA0 hAhalf hmass
      rw [show (K \ T₂) \ T₁ = (K \ T₁) \ T₂ from _root_.sdiff_sdiff_comm] at hswap
      exact conv T₂ hT₂top hswap
  have hπT₁ : uniformOn volume K T₁ = volume T₁ / volume K := by
    rw [uniformOn_apply volume hKm hT₁, Set.inter_eq_left.mpr hT₁K]
  have hπT₂ : uniformOn volume K T₂ = volume T₂ / volume K := by
    rw [uniformOn_apply volume hKm hT₂, Set.inter_eq_left.mpr hT₂K]
  have hπQ : uniformOn volume K ((K \ T₁) \ T₂) = volume ((K \ T₁) \ T₂) / volume K := by
    rw [uniformOn_apply volume hKm hQm, Set.inter_eq_left.mpr hQsub]
  rw [lintegral_ofReal_uniformOn hInt hh0, hπT₁, hπT₂, hπQ, min_div_div, div_eq_mul_inv,
    div_eq_mul_inv]
  calc (volume K)⁻¹ * ENNReal.ofReal (∫ x in K, h x)
        * (min (volume T₁) (volume T₂) * (volume K)⁻¹)
      = ENNReal.ofReal (∫ x in K, h x) * min (volume T₁) (volume T₂)
          * ((volume K)⁻¹ * (volume K)⁻¹) := by ring
    _ ≤ volume ((K \ T₁) \ T₂) * volume K * ((volume K)⁻¹ * (volume K)⁻¹) := by gcongr
    _ = volume ((K \ T₁) \ T₂) * (volume K)⁻¹ * (volume K * (volume K)⁻¹) := by ring
    _ = volume ((K \ T₁) \ T₂) * (volume K)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hK0 hKtop, mul_one]

/-- **The `hIso` binder of `Arlib.MarkovChains.conductance_hitAndRun_ge`, from the corrected
Theorem 2.1 binder.**

`Arlib.hIso_of_thm21` with `hthm21` replaced by `hthm21sub`.  The proof is the original: the
`Measurable h` clause is removed by approximating `ofReal ∘ h` from below by simple functions,
every hypothesis on `h` being an upper bound and hence inherited by minorants. -/
theorem hIso_book {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hthm21sub : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) → (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 → (volume U₁).toReal = A * (volume K).toReal →
        A * (∫ x in K, g x) ≤ (volume ((K \ U₁) \ U₂)).toReal) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) := by
  intro h T₁ T₂ hh0 hh3 hT₁ hT₂ hT₁K hT₂K hdisj hchord
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    isProbabilityMeasure_uniformOn volume hK0 hKtop
  have main : ∀ φ : SimpleFunc (EuclideanSpace ℝ (Fin n)) ℝ≥0,
      (∀ x, ((φ x : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (h x)) →
      (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (uniformOn volume K)
          * min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) := by
    intro φ hφ
    have hgh : ∀ x, ((φ x : ℝ≥0) : ℝ) ≤ h x := by
      intro x
      have hx := hφ x
      rw [← ENNReal.ofReal_coe_nnreal] at hx
      exact (ENNReal.ofReal_le_ofReal_iff (hh0 x)).mp hx
    have hcore := hIso_measurable_of_thm21_sub (h := fun x => ((φ x : ℝ≥0) : ℝ)) hKb hKm hK0
      hKtop hthm21sub (measurable_coe_nnreal_real.comp φ.measurable)
      (fun x => (φ x).coe_nonneg) (fun x hx => (hgh x).trans (hh3 x hx))
      hT₁ hT₂ hT₁K hT₂K hdisj
      (fun u hu v hv x hx hex => (hgh x).trans (hchord u hu v hv x hx hex))
    have heq : (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (uniformOn volume K)
        = ∫⁻ x, ENNReal.ofReal ((φ x : ℝ≥0) : ℝ) ∂(uniformOn volume K) := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      exact lintegral_congr fun x => by simp
    rw [heq]
    exact hcore
  rcases eq_or_ne (min (uniformOn volume K T₁) (uniformOn volume K T₂)) 0 with hm0 | hm0
  · rw [hm0, mul_zero]
    exact zero_le
  · rw [← ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inr (measure_ne_top _ _)),
      lintegral_eq_nnreal]
    refine iSup₂_le fun φ hφ => ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inr (measure_ne_top _ _))]
    exact main φ hφ

open MarkovChains in
/-- **Theorem 4.2 of Lovász–Vempala, with `hIso` replaced by the *corrected* Theorem 2.1
binder.**

`Arlib.conductance_hitAndRun_ge_of_thm21` rerun on `hthm21sub`.  Residual binders: `hLem41`
(owned elsewhere) and `hthm21sub`.  Unlike the original, `hthm21sub` is not refuted by
`Arlib.not_thm21_book`, so this composition is the one a future proof of Theorem 2.1 should be
pointed at. -/
theorem conductance_hitAndRun_ge_book (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hthm21sub : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) → (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 → (volume U₁).toReal = A * (volume K).toReal →
        A * (∫ x in K, g x) ≤ (volume ((K \ U₁) \ U₂)).toReal) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  exact conductance_hitAndRun_ge hn hKc hKcl hKm hKb hball hD hLem41
    (hIso_book hKb hKm hK0 hKtop hthm21sub)

end Corrected

/-! ### The one-dimensional core, with continuous weights in place of indicators

Lee's book runs the localisation lemma at the *continuous* triple
`f₁ = max(0, 1 − T·d(·,S₁))`, `f₂ = max(0, 1 − T·d(·,S₂))`, `f₃ = 1 − f₁ − f₂` rather than at the
indicators of `S₁, S₂, S₃`.  That is not a cosmetic change: `Arlib.needle_iso` — the
one-dimensional theorem the localisation conclusion is contradicted against — reads its three
masses off *sets*, and the mollified route produces them as *integrals against weights*.

This section is the answer to "does the one-dimensional core generalise?".  It does, and the
generalisation is cheap, because the only place the sets are used is
`Arlib.oneDim_crossRatio_partition`, which can be applied to the **supports**
`Yᵢ = {t ∈ [α,β] | fᵢ t ≠ 0}` instead:

* `∫ f₁·D ≤ ∫_{Y₁} D` and `∫ f₂·D ≤ ∫_{Y₂} D`, since `0 ≤ fᵢ ≤ 1` and `fᵢ` vanishes off `Yᵢ`;
* `∫_{Y₃} D ≤ ∫ f₃·D`, since `f₃ = 1` on `Y₃` and `f₃ ≥ 0` throughout;

so the isoperimetric inequality at the supports implies the one at the weights, in the right
direction on all three terms at once.  The remaining argument is pure algebra in the four
masses, isolated as `Arlib.needle_iso_masses`.

The cross condition is correspondingly asked at the **supports**, `f₁ s ≠ 0` and `f₂ t ≠ 0`,
not at `S₁` and `S₂`.  That is exactly step 5 of the route, and it is where the mollified
argument has to pay: see the closing section. -/

section OneDimWeighted

/-- **The closing algebra of `Arlib.needle_iso`, isolated from the sets.**

Given four masses `T = T₁ + T₂ + T₃` with `T₂, T₃ ≥ 0`, a weight integral `I ≤ M·T`, the
one-dimensional isoperimetric inequality `3M·T₁T₂ ≤ T·T₃`, the mass equation `T₁ = A·T` and the
two numeric bounds `M ≤ 1/3`, `A ≤ 1/2`, one gets `A·I ≤ T₃`.

This is the tail of `Arlib.needle_iso` verbatim, with every measure-theoretic hypothesis
stripped: from `T₃ < A·I` one gets `T₃ < M·T₁`, hence `3T₂ < T`, hence
`T₃ > (1 − 1/2 − 1/3)T`, and `M > 3` — contradicting `M ≤ 1/3`.  Extracting it is what lets the
weighted form below reuse the argument without reproving it. -/
theorem needle_iso_masses {T T₁ T₂ T₃ I A M : ℝ}
    (hT0 : 0 ≤ T) (hT₃0 : 0 ≤ T₃)
    (hsum : T = T₁ + T₂ + T₃) (hGD : I ≤ M * T)
    (hiso : 3 * M * (T₁ * T₂) ≤ T * T₃)
    (hM0 : 0 ≤ M) (hM3 : M ≤ 1 / 3) (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmass : T₁ = A * T) :
    A * I ≤ T₃ := by
  by_contra hcon'
  have hcon : T₃ < A * I := not_le.mp hcon'
  have hAMT : T₃ < A * (M * T) := lt_of_lt_of_le hcon (by nlinarith)
  have hTpos : 0 < T := by
    rcases hT0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hApos : 0 < A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hMpos : 0 < M := by
    rcases hM0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hT₁pos : 0 < T₁ := by rw [hmass]; positivity
  have hkey : 3 * T₂ < T := by
    have h1 : 3 * M * (T₁ * T₂) < M * T₁ * T := by nlinarith
    have h2 : 0 < M * T₁ := mul_pos hMpos hT₁pos
    nlinarith
  nlinarith

variable {D f₁ f₂ f₃ G : ℝ → ℝ} {α β : ℝ}

/-- A weight bounded between `0` and `1` times an integrable nonnegative `D` is integrable on
every measurable piece of `[α, β]`: it is dominated by `D`. -/
theorem integrableOn_weight_mul (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t)
    (hDint : IntegrableOn D (Set.Icc α β)) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc α β) :
    IntegrableOn (fun t => f t * D t) S := by
  have hDS : IntegrableOn D S := hDint.mono_set hSsub
  refine Integrable.mono' hDS (hfm.aestronglyMeasurable.mul hDS.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' hS]
  filter_upwards with t ht
  have hD := hD0 t (hSsub ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 t) hD)]
  nlinarith [hf1 t]

/-- **A weight vanishing off `Y` integrates to at most the mass of `Y`.**  The `≤`-half of the
support comparison: `∫_{[α,β]} f·D ≤ ∫_Y D` when `0 ≤ f ≤ 1` and `f = 0` on `[α,β] ∖ Y`. -/
theorem setIntegral_weight_le_of_support
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hDint : IntegrableOn D (Set.Icc α β))
    {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1)
    {Y : Set ℝ} (hY : MeasurableSet Y) (hYsub : Y ⊆ Set.Icc α β)
    (hoff : ∀ t ∈ Set.Icc α β, t ∉ Y → f t = 0) :
    (∫ t in Set.Icc α β, f t * D t) ≤ ∫ t in Y, D t := by
  have hYc : MeasurableSet (Set.Icc α β \ Y) := measurableSet_Icc.diff hY
  have hint₁ : IntegrableOn (fun t => f t * D t) Y :=
    integrableOn_weight_mul hD0 hDint hfm hf0 hf1 hY hYsub
  have hint₂ : IntegrableOn (fun t => f t * D t) (Set.Icc α β \ Y) :=
    integrableOn_weight_mul hD0 hDint hfm hf0 hf1 hYc Set.sdiff_subset
  have hunion : Set.Icc α β = Y ∪ (Set.Icc α β \ Y) := (Set.union_sdiff_cancel hYsub).symm
  have hzero : (∫ t in Set.Icc α β \ Y, f t * D t) = 0 := by
    rw [setIntegral_congr_fun hYc (g := fun _ => (0 : ℝ)) fun t ht => by
      rw [hoff t ht.1 ht.2, zero_mul]]
    exact integral_zero _ _
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right hYc hint₁ hint₂, hzero, add_zero]
  refine setIntegral_mono_on hint₁ (hDint.mono_set hYsub) hY fun t ht => ?_
  nlinarith [hf1 t, hf0 t, hD0 t (hYsub ht)]

/-- **A weight at least `1` on `Y` integrates to at least the mass of `Y`.**  The `≥`-half:
`∫_Y D ≤ ∫_{[α,β]} f·D` when `0 ≤ f` on `[α,β]` and `1 ≤ f` on `Y`. -/
theorem setIntegral_le_setIntegral_weight
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hDint : IntegrableOn D (Set.Icc α β))
    {f : ℝ → ℝ} (hfD : IntegrableOn (fun t => f t * D t) (Set.Icc α β))
    (hf0 : ∀ t ∈ Set.Icc α β, 0 ≤ f t)
    {Y : Set ℝ} (hY : MeasurableSet Y) (hYsub : Y ⊆ Set.Icc α β)
    (hfY : ∀ t ∈ Y, 1 ≤ f t) :
    (∫ t in Y, D t) ≤ ∫ t in Set.Icc α β, f t * D t := by
  have hYc : MeasurableSet (Set.Icc α β \ Y) := measurableSet_Icc.diff hY
  have hunion : Set.Icc α β = Y ∪ (Set.Icc α β \ Y) := (Set.union_sdiff_cancel hYsub).symm
  have hnn : 0 ≤ ∫ t in Set.Icc α β \ Y, f t * D t :=
    setIntegral_nonneg hYc fun t ht =>
      mul_nonneg (hf0 t ht.1) (hD0 t ht.1)
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right hYc
    (hfD.mono_set hYsub) (hfD.mono_set Set.sdiff_subset)]
  have hmain : (∫ t in Y, D t) ≤ ∫ t in Y, f t * D t := by
    refine setIntegral_mono_on (hDint.mono_set hYsub)
      (hfD.mono_set hYsub) hY fun t ht => ?_
    nlinarith [hfY t ht, hD0 t (hYsub ht)]
  linarith

variable {A M : ℝ}

/-- **`Arlib.needle_iso` with the three sets replaced by two continuous weights.**

`f₁, f₂` are nonnegative, bounded by `1`, and have **disjoint supports** (`hdisj`); the third
weight is `f₃ = 1 − f₁ − f₂`, exactly as in Lee's book §10.6, and is therefore *not* an
independent datum.  `hmass` is the mass equation at the weight, `∫ f₁·D = A·∫ D`, and `hcross`
is the cross-ratio separation asked at the **supports** of `f₁` and `f₂`.

The conclusion is `A·∫G·D ≤ ∫ f₃·D`, which is what the mollified localisation route needs and
what `Arlib.needle_iso` cannot supply, its masses being read off sets.

**No hypothesis of `Arlib.needle_iso` is lost and none is added beyond the three weight
clauses.**  In particular `A ≤ 1/2` and `M ≤ 1/3` are still needed, and are still needed for the
same reason: they are the two numeric inputs of `Arlib.needle_iso_masses`. -/
theorem needle_iso_weight (hαβ : α ≤ β)
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGM : ∀ t ∈ Set.Icc α β, G t ≤ M) (hM0 : 0 ≤ M) (hM3 : M ≤ 1 / 3)
    (hGDint : IntervalIntegrable (fun t => G t * D t) volume α β)
    (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁0 : ∀ t, 0 ≤ f₁ t) (hf₂0 : ∀ t, 0 ≤ f₂ t)
    (hf₁1 : ∀ t, f₁ t ≤ 1) (hf₂1 : ∀ t, f₂ t ≤ 1)
    (hdisj : ∀ t, f₁ t = 0 ∨ f₂ t = 0)
    (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmass : (∫ t in Set.Icc α β, f₁ t * D t) = A * ∫ t in α..β, D t)
    (hcross : ∀ s ∈ Set.Icc α β, f₁ s ≠ 0 → ∀ t ∈ Set.Icc α β, f₂ t ≠ 0 →
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) :
    A * (∫ t in α..β, G t * D t) ≤ ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t := by
  classical
  have hDIcc : IntegrableOn D (Set.Icc α β) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hDint
  have hTeq : (∫ t in Set.Icc α β, D t) = ∫ t in α..β, D t := by
    rw [intervalIntegral.integral_of_le hαβ, integral_Icc_eq_integral_Ioc]
  -- the supports, and the partition they induce
  set Y₁ : Set ℝ := Set.Icc α β ∩ {t | f₁ t ≠ 0} with hY₁def
  set Y₂ : Set ℝ := Set.Icc α β ∩ {t | f₂ t ≠ 0} with hY₂def
  set Y₃ : Set ℝ := Set.Icc α β \ (Y₁ ∪ Y₂) with hY₃def
  have hsub₁ : Y₁ ⊆ Set.Icc α β := Set.inter_subset_left
  have hsub₂ : Y₂ ⊆ Set.Icc α β := Set.inter_subset_left
  have hsub₃ : Y₃ ⊆ Set.Icc α β := Set.sdiff_subset
  have hm₁ : MeasurableSet Y₁ :=
    measurableSet_Icc.inter (hf₁m (measurableSet_singleton (0 : ℝ)).compl)
  have hm₂ : MeasurableSet Y₂ :=
    measurableSet_Icc.inter (hf₂m (measurableSet_singleton (0 : ℝ)).compl)
  have hm₃ : MeasurableSet Y₃ := measurableSet_Icc.diff (hm₁.union hm₂)
  have hoff₁ : ∀ t ∈ Set.Icc α β, t ∉ Y₁ → f₁ t = 0 := by
    intro t ht hnt
    by_contra hne
    exact hnt ⟨ht, hne⟩
  have hoff₂ : ∀ t ∈ Set.Icc α β, t ∉ Y₂ → f₂ t = 0 := by
    intro t ht hnt
    by_contra hne
    exact hnt ⟨ht, hne⟩
  have hpart : IsPartition3 (Set.Icc α β) Y₁ Y₂ Y₃ := by
    refine ⟨Set.union_sdiff_cancel (Set.union_subset hsub₁ hsub₂), ?_, ?_, ?_⟩
    · refine Set.disjoint_left.mpr fun t ht₁ ht₂ => ?_
      rcases hdisj t with h | h
      exacts [ht₁.2 h, ht₂.2 h]
    · exact Set.disjoint_left.mpr fun t ht₁ ht₃ => ht₃.2 (Or.inl ht₁)
    · exact Set.disjoint_left.mpr fun t ht₂ ht₃ => ht₃.2 (Or.inr ht₂)
  -- the one-dimensional inequality at the supports
  have hiso := oneDim_crossRatio_partition (c := 3 * M) hαβ hD0 hlc hDint hpart hm₁ hm₂ hm₃
    (fun s hs t ht => hcross s hs.1 hs.2 t ht.1 ht.2)
  -- integrability of the three weighted integrands
  have hf₁D : IntegrableOn (fun t => f₁ t * D t) (Set.Icc α β) :=
    integrableOn_weight_mul hD0 hDIcc hf₁m hf₁0 hf₁1 measurableSet_Icc Set.Subset.rfl
  have hf₂D : IntegrableOn (fun t => f₂ t * D t) (Set.Icc α β) :=
    integrableOn_weight_mul hD0 hDIcc hf₂m hf₂0 hf₂1 measurableSet_Icc Set.Subset.rfl
  have heq₃ : (fun t => (1 - f₁ t - f₂ t) * D t)
      = fun t => D t - f₁ t * D t - f₂ t * D t := by funext t; ring
  have hf₃D : IntegrableOn (fun t => (1 - f₁ t - f₂ t) * D t) (Set.Icc α β) := by
    rw [heq₃]; exact (hDIcc.sub hf₁D).sub hf₂D
  -- the third mass is what is left over
  have hsplit : (∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t)
      = (∫ t in Set.Icc α β, D t) - (∫ t in Set.Icc α β, f₁ t * D t)
        - ∫ t in Set.Icc α β, f₂ t * D t := by
    have hint₁ : IntegrableOn (fun t => D t - f₁ t * D t) (Set.Icc α β) := hDIcc.sub hf₁D
    rw [heq₃, integral_sub hint₁ hf₂D, integral_sub hDIcc hf₁D]
  -- `f₃ = 1 − f₁ − f₂` is nonnegative, and equals `1` off both supports
  have hf₃0 : ∀ t ∈ Set.Icc α β, 0 ≤ 1 - f₁ t - f₂ t := by
    intro t _
    rcases hdisj t with h | h
    · rw [h]; linarith [hf₂1 t]
    · rw [h]; linarith [hf₁1 t]
  have hf₃Y : ∀ t ∈ Y₃, 1 ≤ 1 - f₁ t - f₂ t := by
    intro t ht
    rw [hoff₁ t ht.1 fun h => ht.2 (Or.inl h), hoff₂ t ht.1 fun h => ht.2 (Or.inr h)]
    norm_num
  -- the three mass comparisons, one per part
  have hcmp₁ : (∫ t in Set.Icc α β, f₁ t * D t) ≤ ∫ t in Y₁, D t :=
    setIntegral_weight_le_of_support hD0 hDIcc hf₁m hf₁0 hf₁1 hm₁ hsub₁ hoff₁
  have hcmp₂ : (∫ t in Set.Icc α β, f₂ t * D t) ≤ ∫ t in Y₂, D t :=
    setIntegral_weight_le_of_support hD0 hDIcc hf₂m hf₂0 hf₂1 hm₂ hsub₂ hoff₂
  have hcmp₃ : (∫ t in Y₃, D t) ≤ ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t :=
    setIntegral_le_setIntegral_weight hD0 hDIcc hf₃D hf₃0 hm₃ hsub₃ hf₃Y
  -- nonnegativity bookkeeping
  have hT0 : 0 ≤ ∫ t in α..β, D t := intervalIntegral.integral_nonneg hαβ fun t ht => hD0 t ht
  have hT₁0 : 0 ≤ ∫ t in Set.Icc α β, f₁ t * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht => mul_nonneg (hf₁0 t) (hD0 t ht)
  have hT₂0 : 0 ≤ ∫ t in Set.Icc α β, f₂ t * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht => mul_nonneg (hf₂0 t) (hD0 t ht)
  have hT₃0 : 0 ≤ ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht => mul_nonneg (hf₃0 t ht) (hD0 t ht)
  have hY₁0 : 0 ≤ ∫ t in Y₁, D t := setIntegral_nonneg hm₁ fun t ht => hD0 t (hsub₁ ht)
  -- the isoperimetric inequality, transferred from the supports to the weights
  have hisoW : 3 * M * ((∫ t in Set.Icc α β, f₁ t * D t) * ∫ t in Set.Icc α β, f₂ t * D t)
      ≤ (∫ t in α..β, D t) * ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t := by
    have hstep : 3 * M * ((∫ t in Set.Icc α β, f₁ t * D t) * ∫ t in Set.Icc α β, f₂ t * D t)
        ≤ 3 * M * ((∫ t in Y₁, D t) * ∫ t in Y₂, D t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hcmp₁ hcmp₂ hT₂0 hY₁0) (by linarith)
    have hstep' : (∫ t in α..β, D t) * ∫ t in Y₃, D t
        ≤ (∫ t in α..β, D t) * ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t :=
      mul_le_mul_of_nonneg_left hcmp₃ hT0
    linarith [hiso]
  -- the average of `G` against `D`
  have hGD : (∫ t in α..β, G t * D t) ≤ M * ∫ t in α..β, D t := by
    have hmono : (∫ t in α..β, G t * D t) ≤ ∫ t in α..β, M * D t :=
      intervalIntegral.integral_mono_on hαβ hGDint (hDint.const_mul M)
        fun t ht => mul_le_mul_of_nonneg_right (hGM t ht) (hD0 t ht)
    rwa [intervalIntegral.integral_const_mul] at hmono
  have hsum : (∫ t in α..β, D t) = (∫ t in Set.Icc α β, f₁ t * D t)
      + (∫ t in Set.Icc α β, f₂ t * D t) + ∫ t in Set.Icc α β, (1 - f₁ t - f₂ t) * D t := by
    rw [← hTeq]; linarith [hsplit]
  exact needle_iso_masses hT0 hT₃0 hsum hGD hisoW hM0 hM3 hA0 hA hmass

end OneDimWeighted

/-! ### The weighted needle inside the body, with the chord bound at the *enlarged* supports

`Arlib.needle_iso_of_chord` transports the chord hypothesis from the ambient body to the needle,
at cross pairs lying in `T₁` and `T₂`.  The mollified route puts the mass not on `T₁, T₂` but on
weights supported in *neighbourhoods* `N₁ ⊇ S₁`, `N₂ ⊇ S₂`, and the cross pairs it produces lie
in those neighbourhoods.  So the chord hypothesis has to hold there.

`Arlib.needle_iso_of_chord_weight` below is exactly that statement: `Arlib.needle_iso_of_chord`
with the sets replaced by weights and the chord bound **asked at `N₁ × N₂`**.  Every step of the
transport — `Arlib.three_mul_sSup_le_crossRatioDist` and `Arlib.needle_crossRatio_transfer` —
goes through verbatim, since both are stated for arbitrary sets.

**This is where step 5 of the book's route is isolated, and it is not discharged here.**  Going
from the hypothesis at `U₁ × U₂` to the hypothesis at `N₁ × N₂` is a genuine ambient statement
about `crossRatioDist` *and* about `g`, and see the closing section for why it is out of reach
for a merely measurable `g`. -/

section NeedleWeighted

variable {n : ℕ}

/-- **`Arlib.needle_iso_of_chord` with continuous weights, and the chord bound at the enlarged
supports `N₁, N₂`.**

`f₁, f₂` are nonnegative, bounded by `1`, supported in the disjoint sets `N₁, N₂`; the third
weight is `1 − f₁ − f₂`.  `hchord` is the Theorem 2.1 chord bound quantified over `N₁ × N₂`,
which is strictly more than Theorem 2.1 assumes and is exactly the extra strength the mollified
route needs.

Given a needle `t ↦ p + t·e` mapping `[α,β]` into `K`, a log-concave weight `D ≥ 0`, and the
mass equation `∫ f₁∘γ·D = A·∫D` with `0 ≤ A ≤ 1/2`, the conclusion is

    A · ∫_α^β h(γ t)·D(t) dt  ≤  ∫_{[α,β]} (1 − f₁(γ t) − f₂(γ t))·D(t) dt.

Note that no measurability or topology is asked of `N₁, N₂` at all: they enter only through
`hchord`, `hdisjN` and the two support clauses. -/
theorem needle_iso_of_chord_weight {K N₁ N₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hdisjN : Disjoint N₁ N₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ N₁, ∀ v ∈ N₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁0 : ∀ x, 0 ≤ f₁ x) (hf₂0 : ∀ x, 0 ≤ f₂ x)
    (hf₁1 : ∀ x, f₁ x ≤ 1) (hf₂1 : ∀ x, f₂ x ≤ 1)
    (hsupp₁ : ∀ x, f₁ x ≠ 0 → x ∈ N₁) (hsupp₂ : ∀ x, f₂ x ≠ 0 → x ∈ N₂)
    {p e : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hαβ : α ≤ β)
    (hseg : ∀ r ∈ Set.Icc α β, needleMap p e r ∈ K)
    {D : ℝ → ℝ} (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGDint : IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmass : (∫ t in Set.Icc α β, f₁ (needleMap p e t) * D t) = A * ∫ t in α..β, D t) :
    A * (∫ t in α..β, h (needleMap p e t) * D t)
      ≤ ∫ t in Set.Icc α β,
          (1 - f₁ (needleMap p e t) - f₂ (needleMap p e t)) * D t := by
  classical
  have hcont : Continuous (needleMap p e) := by
    show Continuous fun t : ℝ => p + t • e
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hmeas : Measurable (needleMap p e) := hcont.measurable
  -- the supremum of `h` along the needle
  set M := sSup ((fun r => h (needleMap p e r)) '' Set.Icc α β) with hMdef
  have hIccne : (Set.Icc α β).Nonempty := Set.nonempty_Icc.mpr hαβ
  have hbdd : BddAbove ((fun r => h (needleMap p e r)) '' Set.Icc α β) := by
    refine ⟨1 / 3, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hGM : ∀ r ∈ Set.Icc α β, h (needleMap p e r) ≤ M := fun r hr =>
    le_csSup hbdd ⟨r, hr, rfl⟩
  have hM3 : M ≤ 1 / 3 := by
    refine csSup_le (hIccne.image _) ?_
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hM0 : 0 ≤ M := le_trans (hh0 _) (hGM α ⟨le_rfl, hαβ⟩)
  -- the two weights have disjoint supports along the needle
  have hdisj : ∀ t : ℝ, f₁ (needleMap p e t) = 0 ∨ f₂ (needleMap p e t) = 0 := by
    intro t
    by_contra hcon
    rw [not_or] at hcon
    exact Set.disjoint_left.mp hdisjN (hsupp₁ _ hcon.1) (hsupp₂ _ hcon.2)
  -- the cross condition, transported from the chord hypothesis at `N₁ × N₂`
  have hcross : ∀ s ∈ Set.Icc α β, f₁ (needleMap p e s) ≠ 0 →
      ∀ t ∈ Set.Icc α β, f₂ (needleMap p e t) ≠ 0 →
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
    intro s hs hs1 t ht ht2
    have hsN : needleMap p e s ∈ N₁ := hsupp₁ _ hs1
    have htN : needleMap p e t ∈ N₂ := hsupp₂ _ ht2
    have hsK : needleMap p e s ∈ K := hseg s hs
    have htK : needleMap p e t ∈ K := hseg t ht
    have hnee : needleMap p e s ≠ needleMap p e t := fun heq =>
      Set.disjoint_left.mp hdisjN hsN (heq ▸ htN)
    have hst : s ≠ t := fun heq => hnee (by rw [heq])
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      refine needle_crossRatio_transfer hKb hs.1 hlt ht.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) hsK htK hnee ?_
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hsN htN hst
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      refine needle_crossRatio_transfer hKb ht.1 hgt hs.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) htK hsK (Ne.symm hnee) ?_
      rw [crossRatioDist_comm hKb (Ne.symm hnee) htK hsK]
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hsN htN hst
  exact needle_iso_weight hαβ hD0 hlc hDint hGM hM0 hM3 hGDint
    (hf₁m.comp hmeas) (hf₂m.comp hmeas)
    (fun t => hf₁0 _) (fun t => hf₂0 _) (fun t => hf₁1 _) (fun t => hf₂1 _)
    hdisj hA0 hA hmass hcross

end NeedleWeighted

/-! ### The book's mollifier

Lee's book §10.6 replaces the indicators of `S₁, S₂` by

    fᵢ(x) = max{0, 1 − T·d(x, Sᵢ)},   f₃ = 1 − f₁ − f₂,

and it is worth being explicit about which way these approximate, because the direction is what
makes the argument work and it is easy to get backwards.  `fᵢ` equals `1` **on** `Sᵢ` and is
positive just outside, so it is a **majorant** of `1_{Sᵢ}`; hence `f₃ = 1 − f₁ − f₂` is a
**minorant** of `1_{S₃}`.  That is the right direction: `f₃` sits in the strict-inequality slot,
where a minorant preserves `∫ f₃ < A·∫ h`.

Everything below is unconditional and elementary.  The support clause is the one the previous
section consumes: `fᵢ ≠ 0` forces `d(x, Sᵢ) < 1/T`, so `Arlib.needle_iso_of_chord_weight` may be
run with `Nᵢ` the open `1/T`-neighbourhood of `Sᵢ`. -/

section Mollifier

open Metric

variable {E : Type*} [PseudoMetricSpace E] {S S₁ S₂ : Set E} {T : ℝ} {x : E}

/-- **Lee's mollifier** `f_T(x) = max{0, 1 − T·d(x,S)}`: a continuous majorant of `1_S`,
supported in the `1/T`-neighbourhood of `S`. -/
noncomputable def bookMollifier (S : Set E) (T : ℝ) (x : E) : ℝ :=
  max 0 (1 - T * Metric.infDist x S)

theorem continuous_bookMollifier (S : Set E) (T : ℝ) : Continuous (bookMollifier S T) :=
  continuous_const.max (continuous_const.sub
    (continuous_const.mul (Metric.continuous_infDist_pt S)))

theorem bookMollifier_nonneg (S : Set E) (T : ℝ) (x : E) : 0 ≤ bookMollifier S T x :=
  le_max_left _ _

theorem bookMollifier_le_one (hT : 0 ≤ T) : bookMollifier S T x ≤ 1 :=
  max_le zero_le_one (by nlinarith [Metric.infDist_nonneg (s := S) (x := x)])

/-- **The mollifier is a majorant of the indicator**: it is `1` on `S`. -/
theorem bookMollifier_of_mem (hx : x ∈ S) : bookMollifier S T x = 1 := by
  rw [bookMollifier, Metric.infDist_zero_of_mem hx, mul_zero, sub_zero, max_eq_right zero_le_one]

/-- **The support clause.**  A point where the mollifier does not vanish lies within `1/T` of
`S`.  This is what lets `Arlib.needle_iso_of_chord_weight` be run at the neighbourhoods. -/
theorem infDist_lt_of_bookMollifier_ne_zero (hT : 0 < T) (hx : bookMollifier S T x ≠ 0) :
    Metric.infDist x S < 1 / T := by
  by_contra hcon
  rw [not_lt, div_le_iff₀ hT] at hcon
  rw [bookMollifier] at hx
  exact hx (max_eq_left (by nlinarith))

/-- **Disjoint supports.**  If every point of `S₁` is at distance at least `δ` from every point
of `S₂`, and `2/T < δ`, then the two mollifiers never both fire.  This is the hypothesis
`hdisj`/`hdisjN` of the weighted needle theorems, and it is why the sets must be separated —
which inner regularisation of two disjoint *compact* sets supplies.

Both sets must be **nonempty**: `Metric.infDist x ∅ = 0`, so the mollifier of the empty set is
identically `1`, and the statement is simply false without the clause. -/
theorem bookMollifier_disjoint (hT : 0 < T) {δ : ℝ} (hδ : 2 / T < δ)
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂, δ ≤ dist u v) (x : E) :
    bookMollifier S₁ T x = 0 ∨ bookMollifier S₂ T x = 0 := by
  by_contra hcon
  rw [not_or] at hcon
  have h₁ := infDist_lt_of_bookMollifier_ne_zero hT hcon.1
  have h₂ := infDist_lt_of_bookMollifier_ne_zero hT hcon.2
  obtain ⟨u, hu, hxu⟩ := (Metric.infDist_lt_iff hne₁).mp h₁
  obtain ⟨v, hv, hxv⟩ := (Metric.infDist_lt_iff hne₂).mp h₂
  have hd : dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
  rw [dist_comm u x] at hd
  have hsuv := hsep u hu v hv
  have h2 : (2 : ℝ) / T = 1 / T + 1 / T := by ring
  linarith

/-- **The pointwise limit.**  For `S` closed and nonempty, `f_T(x) → 1_S(x)` as `T → ∞`: on `S`
the mollifier is identically `1`, and off a *closed* `S` the distance is positive, so the
mollifier is eventually `0`.  Closedness is exactly what is needed and is exactly what inner
regularisation supplies. -/
theorem tendsto_bookMollifier (hS : IsClosed S) (hne : S.Nonempty) (x : E) :
    Filter.Tendsto (fun T : ℝ => bookMollifier S T x) Filter.atTop
      (nhds (S.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with T
    exact (bookMollifier_of_mem hx).symm
  · rw [Set.indicator_of_notMem hx]
    have hpos : 0 < Metric.infDist x S := (hS.notMem_iff_infDist_pos hne).mp hx
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop (1 / Metric.infDist x S)] with T hT
    have hTpos : 0 < T := lt_of_le_of_lt (by positivity) hT
    have h1 : 1 < T * Metric.infDist x S := by
      rw [div_lt_iff₀ hpos] at hT
      linarith
    rw [bookMollifier]
    exact (max_eq_left (by linarith)).symm

end Mollifier

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.chordLow_pos_of_notMem
#print axioms Arlib.one_le_crossRatioDist_of_notMem
#print axioms Arlib.chord_bound_of_notMem
#print axioms Arlib.norm_farPoint
#print axioms Arlib.not_thm21_book
#print axioms Arlib.false_of_hIso_of_thm21_binder
#print axioms Arlib.hIso_measurable_of_thm21_sub
#print axioms Arlib.hIso_book
#print axioms Arlib.conductance_hitAndRun_ge_book
#print axioms Arlib.needle_iso_masses
#print axioms Arlib.integrableOn_weight_mul
#print axioms Arlib.setIntegral_weight_le_of_support
#print axioms Arlib.setIntegral_le_setIntegral_weight
#print axioms Arlib.needle_iso_weight
#print axioms Arlib.needle_iso_of_chord_weight
#print axioms Arlib.continuous_bookMollifier
#print axioms Arlib.bookMollifier_nonneg
#print axioms Arlib.bookMollifier_le_one
#print axioms Arlib.bookMollifier_of_mem
#print axioms Arlib.infDist_lt_of_bookMollifier_ne_zero
#print axioms Arlib.bookMollifier_disjoint
#print axioms Arlib.tendsto_bookMollifier
