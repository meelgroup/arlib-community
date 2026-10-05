/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLimit

/-!
# The needle limit of the localisation bisection: a negative answer, and what survives

This file attacks the limit passage of the Lovász–Simonovits localisation argument — the step
that `Arlib.Convexity.LocalizationLemma` calls **(G2)** and that
`Arlib.Convexity.LocalizationLimit` narrowed down to a weak-convergence statement plus a
"concave-to-affine" reduction.

The concrete question it settles is the one the whole programme had reduced to:

> the bisection cut of `Arlib.exists_halfSpace_cut_pos` is available in **every** direction
> (`Arlib.exists_halfSpace_bisecting` leaves the direction free, and needs no Borsuk–Ulam), so
> can one choose the direction *adaptively* — always cutting the current body's longest axis —
> and force the bodies of the chain to shrink, so that the recursion is well-founded and the
> limit is a needle?

The module docstring of `Arlib.Convexity.LocalizationLemma` asserts exactly this, in the
sentence "a standard argument (always cut the current body's longest axis in half) makes the
diameters decay geometrically".

## The answer: no.  Provably, and for a reason that has nothing to do with the cut positions

The bisection recursion maintains exactly one invariant: `0 < ∫_C g` and `0 < ∫_C h`.  That
invariant **by itself** bounds the diameter of `C` from below, whatever `C` is:

`Arlib.le_diam_of_sign_separated` — if `g ≤ 0` on the halfspace `{a < L}` and `h ≤ 0` on the
halfspace `{L < b}` for some continuous linear functional `L` and `a < b`, then *every*
measurable bounded `C` with `0 < ∫_C g` and `0 < ∫_C h` has `Metric.diam C ≥ (b - a)/‖L‖`.

The proof is three lines: `0 < ∫_C g` forces `C` to meet `{L ≤ a}` (otherwise `g ≤ 0` on `C`),
`0 < ∫_C h` forces `C` to meet `{b ≤ L}`, and a set meeting both spans the slab.  No convexity,
no boundedness, no dimension, no hypothesis on how `C` was produced.

Such configurations exist: `Arlib.gapG`, `Arlib.gapH` are explicit integrable functions on
`ℝ × ℝ` — `stepLeft(x)·1_{[0,1)}(y)` and `stepRight(x)·1_{[0,1)}(y)`, where `stepLeft` is `1` on
`[0,1)` and `-1/2` on `[1,2)`, and `stepRight` is `1` on `[2,3)` and `-1/2` on `[1,2)` — whose
masses over the box `Arlib.gapBox = [0,3] × [0,1]` are both `1/2 > 0`
(`Arlib.integral_gapG_gapBox`, `Arlib.integral_gapH_gapBox`), and for which the constant of the
bound is `1` (`Arlib.one_le_diam_of_gap_pos`).

Consequently `Arlib.one_le_diam_bisection_chain`: instantiating `Arlib.exists_bisection_chain`
at this data, **for every sequence of nonzero cut directions and at every depth**, every body of
the chain has diameter at least `1`, while its `g`-mass has already decayed to `2^{-k}/2`.
Because the direction sequence is universally quantified, this covers adaptive rules: any rule
for choosing the `k`-th direction — longest axis, or anything else — realises *some* sequence,
and the bound holds for it.  Granting a two-measure ham-sandwich cut ((G1)) would not help
either: it only widens the choice of successors, and the bound holds for both of them.

The example is two-dimensional on purpose, so that the direction of the cut is a genuine choice.

## What this means for the shape of the limit

The obstruction is not an artefact; it is the localisation lemma's own conclusion showing
through.  A needle is a *segment* with a weight `ℓ^{n-1}`, and the needle produced from data
whose positive parts are separated by a slab of width `b - a` must itself cross that slab.  So
the correct degeneracy to aim for is **transverse thinness**, not small diameter: the bodies must
become thin in the `n-1` directions orthogonal to a spanning chord while keeping their length.

Two results here make that precise from the two sides.

*The length survives.*  `Arlib.exists_pair_dist_ge_of_tendsto_hausdorffDist` and its convex form
`Arlib.exists_segment_subset_of_tendsto_hausdorffDist`: if every `C n` inside a fixed compact
`K` contains a chord of length `≥ r` and `C n → D` in Hausdorff distance, then `D` contains two
points at distance `≥ r`, and if `D` is convex the whole segment between them.  So the limit
body of the chain carries a needle of length at least the gap — never a point.

*The naive limit is inadmissible.*  `Arlib.setIntegral_iInter_eq_zero_of_tendsto`: for a
decreasing sequence of measurable sets whose `g`-masses tend to `0`, the intersection has
`g`-mass `0`.  The bisection chain's `g`-masses are exactly `2^{-k}·∫_K g → 0`, so `⋂ C k`
fails the invariant.  The needle can therefore only come from a **renormalised** limit
(`(vol C_k)^{-1}∫_{C_k}`), never from the set-theoretic limit — which is precisely why the
missing item is the weak-convergence statement and not a compactness statement.

## What is proved here

* `Arlib.exists_mem_apply_le_of_setIntegral_pos`, `Arlib.exists_mem_le_apply_of_setIntegral_pos`
  — positive mass forces the set into the halfspace where the integrand is not `≤ 0`.
* `Arlib.exists_pair_apply_sub_ge_of_sign_separated`,
  `Arlib.exists_pair_dist_ge_of_sign_separated`, `Arlib.le_diam_of_sign_separated` — the
  obstruction, in functional, metric and diameter form, for an arbitrary normed space.
* `Arlib.gapG`, `Arlib.gapH`, `Arlib.gapBox` and their basic properties — the planar witness.
* `Arlib.exists_pair_one_le_dist_of_gap_pos`, `Arlib.one_le_diam_of_gap_pos`,
  `Arlib.one_le_diam_bisection_chain` — the obstruction, concretely, and applied to the chain.
* `Arlib.exists_infinite_bisection_chain` — the bisection chain run to infinite depth as one
  nested sequence (`Arlib.exists_bisection_chain` only gives each finite depth separately).
* `Arlib.setIntegral_iInter_eq_zero_of_tendsto` — the limit leaves the family.
* `Arlib.exists_subseq_hausdorff_limit_bisection_chain` — **item 1**: the chain, inside a compact
  convex `K`, has a subsequence of closures converging in Hausdorff distance to a nonempty
  compact convex `D ⊆ K` (Blaschke, via `Arlib.exists_subseq_tendsto_hausdorffDist_convex`).
* `Arlib.mem_of_tendsto_of_tendsto_hausdorffDist`,
  `Arlib.exists_pair_dist_ge_of_tendsto_hausdorffDist`,
  `Arlib.exists_segment_subset_of_tendsto_hausdorffDist` — the needle's length survives the
  limit.
* `Arlib.bisection_chain_gapBox` — all of the above at once on the planar witness.

## What is *not* proved here, stated exactly

The remaining gap in (G2) is now a **single** statement, and it is not the one previously
recorded:

> Given `K` compact convex in `ℝⁿ` with `0 < ∫_K g`, `0 < ∫_K h`, produce a sequence of
> **directions** `L : ℕ → (ℝⁿ →L[ℝ] ℝ)` such that the bisection chain `C` of
> `Arlib.exists_infinite_bisection_chain` satisfies
> `Metric.hausdorffDist (closure (C k)) (segment ℝ a b) → 0` for some `a, b` — i.e. the bodies
> become thin **transverse** to a spanning chord, their length being bounded below by
> `Arlib.le_diam_of_sign_separated` in any case.

Nothing in this file, or in the repository, proves that such a direction sequence exists, and
this file gives no reason to believe the "longest axis" rule produces one: the cut *position* is
forced by the mass-bisection, so the retained side can be nearly all of the current body in
every direction at once.  Whether transverse thinness is forcible is open here.

Only after that would the weak-convergence statement of `Arlib.Convexity.LocalizationLimit`
(item (i) there) and the renormalised profile from `Arlib.concaveOn_limit_slice_profile` come
into play.

## Where the limit passage now lives

The "renormalised limit" this file argues is the only admissible one is carried out in
`Arlib.Convexity.NeedleProfile` (fixed unit slab) and, for a chain whose slab **shrinks** to the
needle's, in `Arlib.Convexity.NeedleSlab`:
`Arlib.tendsto_average_setIntegral_of_rescaledProfile` is the same limit passage with the `k`-th
body allowed to occupy its own slab `[l k, u k]`, subject only to `l k → 0` and `u k → 1`.  That
is what removes the rigidity recorded as item (E) of `Arlib.Convexity.LocalizationAssembly` — a
localisation chain shrinks in *every* direction, so it cannot keep a constant height range, and
the fixed-slab form asks it to.  `Arlib.Convexity.NeedleSlabAffine` carries that to general
position and `Arlib.Convexity.NeedleSlabChain` shows every decreasing chain of compact convex
bodies with a nondegenerate intersection satisfies the relaxed hypotheses.

Nothing in this file changed; the transverse-thinness target it identifies above is exactly what
those files consume.

## Honesty note

This file contains **no** `def`/`structure`/`class`/`Prop` asserting the Localization Lemma, the
isoperimetric inequality or Dyer–Frieze, and no theorem below takes any of them as a hypothesis.
The six `def`s (`Arlib.icoConst`, `Arlib.stepLeft`, `Arlib.stepRight`, `Arlib.gapG`,
`Arlib.gapH`, `Arlib.gapBox`) are plain explicit formulas — piecewise-constant functions and a
box — and every property attributed to them is proved. `Arlib.brunn_slice_sharp` is not used
here, so no section-nonemptiness hypothesis is incurred.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Metric Bornology
open scoped ENNReal Topology

namespace Arlib

/-! ### The sign-separation obstruction -/

section SignSeparation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable {μ : Measure E}

/-- If `f ≤ 0` everywhere on the open halfspace `{a < L}` and `∫_C f > 0`, then `C` must reach
into the closed halfspace `{L ≤ a}`. -/
theorem exists_mem_apply_le_of_setIntegral_pos {f : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a : ℝ} (hf : ∀ x, a < L x → f x ≤ 0) (hpos : 0 < ∫ x in C, f x ∂μ) :
    ∃ x ∈ C, L x ≤ a := by
  by_contra hcon
  push Not at hcon
  exact absurd hpos (not_lt.2 (setIntegral_nonpos hC fun x hx => hf x (hcon x hx)))

/-- If `f ≤ 0` everywhere on the open halfspace `{L < b}` and `∫_C f > 0`, then `C` must reach
into the closed halfspace `{b ≤ L}`. -/
theorem exists_mem_le_apply_of_setIntegral_pos {f : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {b : ℝ} (hf : ∀ x, L x < b → f x ≤ 0) (hpos : 0 < ∫ x in C, f x ∂μ) :
    ∃ y ∈ C, b ≤ L y := by
  by_contra hcon
  push Not at hcon
  exact absurd hpos (not_lt.2 (setIntegral_nonpos hC fun x hx => hf x (hcon x hx)))

/-- **The sign-separation obstruction, in the linear functional.**

Suppose `g` is nonpositive on `{a < L}` and `h` is nonpositive on `{L < b}`.  Then *any*
measurable set carrying positive `g`-mass **and** positive `h`-mass contains two points whose
`L`-values differ by at least `b - a`.

Nothing about convexity, boundedness or dimension is used. -/
theorem exists_pair_apply_sub_ge_of_sign_separated {g h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) {L : E →L[ℝ] ℝ} {a b : ℝ}
    (hg : ∀ x, a < L x → g x ≤ 0) (hh : ∀ x, L x < b → h x ≤ 0)
    (hgC : 0 < ∫ x in C, g x ∂μ) (hhC : 0 < ∫ x in C, h x ∂μ) :
    ∃ x ∈ C, ∃ y ∈ C, b - a ≤ L y - L x := by
  obtain ⟨x, hxC, hx⟩ := exists_mem_apply_le_of_setIntegral_pos hC hg hgC
  obtain ⟨y, hyC, hy⟩ := exists_mem_le_apply_of_setIntegral_pos hC hh hhC
  exact ⟨x, hxC, y, hyC, by linarith⟩

/-- **The sign-separation obstruction, metric form.**

Under the hypotheses of `Arlib.exists_pair_apply_sub_ge_of_sign_separated`, any set carrying
positive `g`- and `h`-mass has two points at distance at least `(b - a)/‖L‖`. -/
theorem exists_pair_dist_ge_of_sign_separated {g h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) {L : E →L[ℝ] ℝ} {a b : ℝ}
    (hg : ∀ x, a < L x → g x ≤ 0) (hh : ∀ x, L x < b → h x ≤ 0)
    (hgC : 0 < ∫ x in C, g x ∂μ) (hhC : 0 < ∫ x in C, h x ∂μ) :
    ∃ x ∈ C, ∃ y ∈ C, (b - a) / ‖L‖ ≤ dist x y := by
  obtain ⟨x, hxC, y, hyC, hxy⟩ :=
    exists_pair_apply_sub_ge_of_sign_separated hC hg hh hgC hhC
  refine ⟨x, hxC, y, hyC, ?_⟩
  rcases le_or_gt (b - a) 0 with hba | hba
  · exact (div_nonpos_of_nonpos_of_nonneg hba (norm_nonneg L)).trans dist_nonneg
  · have hnorm : L y - L x ≤ ‖L‖ * dist x y := by
      have h1 : L y - L x = L (y - x) := by rw [map_sub]
      have h2 : ‖L (y - x)‖ ≤ ‖L‖ * ‖y - x‖ := L.le_opNorm _
      have h3 : ‖y - x‖ = dist x y := by rw [← dist_eq_norm, dist_comm]
      calc L y - L x = L (y - x) := h1
        _ ≤ ‖L (y - x)‖ := le_abs_self _
        _ ≤ ‖L‖ * ‖y - x‖ := h2
        _ = ‖L‖ * dist x y := by rw [h3]
    have hLpos : 0 < ‖L‖ := by
      rcases (norm_nonneg L).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hnorm; simp at hnorm; linarith
    rw [div_le_iff₀ hLpos]
    linarith [hnorm, mul_comm ‖L‖ (dist x y)]

/-- **The sign-separation obstruction, diameter form.**

Under the hypotheses of `Arlib.exists_pair_apply_sub_ge_of_sign_separated`, any bounded set
carrying positive `g`- and `h`-mass has diameter at least `(b - a)/‖L‖`.  This is a lower bound
that **no** cutting scheme can beat, because every body it produces satisfies exactly these two
positivity constraints. -/
theorem le_diam_of_sign_separated {g h : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hCb : IsBounded C) {L : E →L[ℝ] ℝ} {a b : ℝ}
    (hg : ∀ x, a < L x → g x ≤ 0) (hh : ∀ x, L x < b → h x ≤ 0)
    (hgC : 0 < ∫ x in C, g x ∂μ) (hhC : 0 < ∫ x in C, h x ∂μ) :
    (b - a) / ‖L‖ ≤ Metric.diam C := by
  obtain ⟨x, hxC, y, hyC, hxy⟩ :=
    exists_pair_dist_ge_of_sign_separated hC hg hh hgC hhC
  exact hxy.trans (dist_le_diam_of_mem hCb hxC hyC)

end SignSeparation

/-! ### A two-dimensional witness: the obstruction is not vacuous -/

section Witness

/-- Indicator of `[a,b)` with constant value `c`.  A plain explicit function. -/
noncomputable def icoConst (a b c : ℝ) : ℝ → ℝ := (Ico a b).indicator (fun _ => c)

theorem integrable_icoConst (a b c : ℝ) : Integrable (icoConst a b c) := by
  rw [icoConst, integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by simp)

theorem icoConst_nonneg {a b c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ icoConst a b c x :=
  Set.indicator_nonneg (fun _ _ => hc) x

theorem icoConst_of_lt {a b c : ℝ} {x : ℝ} (hx : x < a) : icoConst a b c x = 0 :=
  Set.indicator_of_notMem (fun hmem => absurd hmem.1 (not_le.2 hx)) _

theorem icoConst_of_ge {a b c : ℝ} {x : ℝ} (hx : b ≤ x) : icoConst a b c x = 0 :=
  Set.indicator_of_notMem (fun hmem => absurd hmem.2 (not_lt.2 hx)) _

/-- The left profile: `1` on `[0,1)`, `-1/2` on `[1,2)`, `0` elsewhere. -/
noncomputable def stepLeft : ℝ → ℝ := fun x => icoConst 0 1 1 x - icoConst 1 2 (1/2) x

/-- The right profile: `1` on `[2,3)`, `-1/2` on `[1,2)`, `0` elsewhere. -/
noncomputable def stepRight : ℝ → ℝ := fun x => icoConst 2 3 1 x - icoConst 1 2 (1/2) x

theorem integrable_stepLeft : Integrable stepLeft :=
  (integrable_icoConst 0 1 1).sub (integrable_icoConst 1 2 (1/2))

theorem integrable_stepRight : Integrable stepRight :=
  (integrable_icoConst 2 3 1).sub (integrable_icoConst 1 2 (1/2))

/-- `stepLeft` is nonpositive to the right of `1`: its only positive part sits in `[0,1)`. -/
theorem stepLeft_nonpos {x : ℝ} (hx : 1 ≤ x) : stepLeft x ≤ 0 := by
  have h : icoConst 0 1 1 x = 0 := icoConst_of_ge hx
  have h2 : 0 ≤ icoConst 1 2 (1/2) x := icoConst_nonneg (by norm_num) x
  simp only [stepLeft, h]
  linarith

/-- `stepRight` is nonpositive to the left of `2`: its only positive part sits in `[2,3)`. -/
theorem stepRight_nonpos {x : ℝ} (hx : x < 2) : stepRight x ≤ 0 := by
  have h : icoConst 2 3 1 x = 0 := icoConst_of_lt hx
  have h2 : 0 ≤ icoConst 1 2 (1/2) x := icoConst_nonneg (by norm_num) x
  simp only [stepRight, h]
  linarith

theorem Ico_subset_Icc_of_le {p q a b : ℝ} (hpa : p ≤ a) (hbq : b ≤ q) :
    Ico a b ⊆ Icc p q :=
  fun _ hx => ⟨hpa.trans hx.1, hx.2.le.trans hbq⟩

theorem integral_icoConst_of_subset {S : Set ℝ} {a b c : ℝ} (hS : Ico a b ⊆ S) (hab : a ≤ b) :
    ∫ x in S, icoConst a b c x = (b - a) * c := by
  rw [icoConst, setIntegral_indicator measurableSet_Ico,
    Set.inter_eq_self_of_subset_right hS, setIntegral_const, measureReal_def, Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul]

theorem integral_stepLeft : ∫ x in Icc (0:ℝ) 3, stepLeft x = 1/2 := by
  simp only [stepLeft]
  rw [integral_sub (integrable_icoConst 0 1 1).restrict (integrable_icoConst 1 2 (1/2)).restrict,
    integral_icoConst_of_subset (Ico_subset_Icc_of_le (by norm_num) (by norm_num)) (by norm_num),
    integral_icoConst_of_subset (Ico_subset_Icc_of_le (by norm_num) (by norm_num)) (by norm_num)]
  norm_num

theorem integral_stepRight : ∫ x in Icc (0:ℝ) 3, stepRight x = 1/2 := by
  simp only [stepRight]
  rw [integral_sub (integrable_icoConst 2 3 1).restrict (integrable_icoConst 1 2 (1/2)).restrict,
    integral_icoConst_of_subset (Ico_subset_Icc_of_le (by norm_num) (by norm_num)) (by norm_num),
    integral_icoConst_of_subset (Ico_subset_Icc_of_le (by norm_num) (by norm_num)) (by norm_num)]
  norm_num

/-- The planar left integrand `gapG (x, y) = stepLeft x · 1_{[0,1)}(y)`. -/
noncomputable def gapG : ℝ × ℝ → ℝ := fun z => stepLeft z.1 * icoConst 0 1 1 z.2

/-- The planar right integrand `gapH (x, y) = stepRight x · 1_{[0,1)}(y)`. -/
noncomputable def gapH : ℝ × ℝ → ℝ := fun z => stepRight z.1 * icoConst 0 1 1 z.2

/-- The box `[0,3] × [0,1]`, a compact convex measurable set on which both `gapG` and `gapH`
have positive mass. -/
def gapBox : Set (ℝ × ℝ) := Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) 1

theorem measurableSet_gapBox : MeasurableSet gapBox :=
  measurableSet_Icc.prod measurableSet_Icc

theorem convex_gapBox : Convex ℝ gapBox :=
  (convex_Icc (0:ℝ) 3).prod (convex_Icc (0:ℝ) 1)

theorem isCompact_gapBox : IsCompact gapBox :=
  isCompact_Icc.prod isCompact_Icc

theorem isBounded_gapBox : IsBounded gapBox := isCompact_gapBox.isBounded

theorem integrable_gapG : Integrable gapG := by
  show Integrable (fun z : ℝ × ℝ => stepLeft z.1 * icoConst 0 1 1 z.2)
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.Integrable.mul_prod integrable_stepLeft (integrable_icoConst 0 1 1)

theorem integrable_gapH : Integrable gapH := by
  show Integrable (fun z : ℝ × ℝ => stepRight z.1 * icoConst 0 1 1 z.2)
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.Integrable.mul_prod integrable_stepRight (integrable_icoConst 0 1 1)

theorem integral_gapG_gapBox : ∫ z in gapBox, gapG z = 1/2 := by
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) 1, stepLeft z.1 * icoConst 0 1 1 z.2 = 1/2
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepLeft,
    integral_icoConst_of_subset (a := 0) (b := 1) (c := 1) Set.Ico_subset_Icc_self (by norm_num)]
  norm_num

theorem integral_gapH_gapBox : ∫ z in gapBox, gapH z = 1/2 := by
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) 1, stepRight z.1 * icoConst 0 1 1 z.2 = 1/2
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepRight,
    integral_icoConst_of_subset (a := 0) (b := 1) (c := 1) Set.Ico_subset_Icc_self (by norm_num)]
  norm_num

theorem gapG_nonpos {z : ℝ × ℝ} (hz : 1 ≤ z.1) : gapG z ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (stepLeft_nonpos hz) (icoConst_nonneg (by norm_num) _)

theorem gapH_nonpos {z : ℝ × ℝ} (hz : z.1 < 2) : gapH z ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (stepRight_nonpos hz) (icoConst_nonneg (by norm_num) _)

/-- **The diameter obstruction, concretely, in the plane.**

For the explicit planar integrands `Arlib.gapG`, `Arlib.gapH`, *every* measurable set carrying
positive mass for both contains two points at distance at least `1`.

Both are integrable, and the box `Arlib.gapBox` does carry positive mass for both
(`Arlib.integral_gapG_gapBox`, `Arlib.integral_gapH_gapBox`), so the configuration is genuine. -/
theorem exists_pair_one_le_dist_of_gap_pos {C : Set (ℝ × ℝ)} (hC : MeasurableSet C)
    (hg : 0 < ∫ z in C, gapG z) (hh : 0 < ∫ z in C, gapH z) :
    ∃ x ∈ C, ∃ y ∈ C, 1 ≤ dist x y := by
  obtain ⟨x, hxC, y, hyC, hxy⟩ :=
    exists_pair_apply_sub_ge_of_sign_separated (μ := (volume : Measure (ℝ × ℝ)))
      (L := ContinuousLinearMap.fst ℝ ℝ ℝ) (a := 1) (b := 2) hC
      (fun z hz => gapG_nonpos (le_of_lt hz)) (fun z hz => gapH_nonpos hz) hg hh
  refine ⟨x, hxC, y, hyC, ?_⟩
  have hx' : (ContinuousLinearMap.fst ℝ ℝ ℝ) x = x.1 := rfl
  have hy' : (ContinuousLinearMap.fst ℝ ℝ ℝ) y = y.1 := rfl
  rw [hx', hy'] at hxy
  have h1 : (1:ℝ) ≤ y.1 - x.1 := by linarith
  have h2 : (1:ℝ) ≤ dist x.1 y.1 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact h1.trans (le_abs_self _)
  exact h2.trans (le_max_left _ _)

/-- **The diameter obstruction, diameter form, in the plane.** -/
theorem one_le_diam_of_gap_pos {C : Set (ℝ × ℝ)} (hC : MeasurableSet C) (hCb : IsBounded C)
    (hg : 0 < ∫ z in C, gapG z) (hh : 0 < ∫ z in C, gapH z) :
    1 ≤ Metric.diam C := by
  obtain ⟨x, hxC, y, hyC, hxy⟩ := exists_pair_one_le_dist_of_gap_pos hC hg hh
  exact hxy.trans (dist_le_diam_of_mem hCb hxC hyC)

/-- **The bisection chain never becomes thin, in any sequence of directions.**

Run `Arlib.exists_bisection_chain` on the planar data `Arlib.gapG`, `Arlib.gapH`,
`Arlib.gapBox` with an **arbitrary** sequence of nonzero cut directions `L`.  Every body of the
resulting chain — at every depth, for every choice of directions, and for whichever of the two
sides the argument is forced to keep — has diameter at least `1`, while its `gapG`-mass has
decayed to `2^{-k}/2`.

Since `L` is universally quantified, this covers *adaptive* direction choice as well: any rule
for picking the `k`-th direction, however it depends on the history, produces some sequence `L`,
and the bound holds for that sequence.  Cutting orthogonal to the longest axis is one such rule.

So the "always cut the current body's longest axis in half, and the diameters decay
geometrically" step is **false as stated** for the bisection recursion. -/
theorem one_le_diam_bisection_chain (L : ℕ → ((ℝ × ℝ) →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0) (N : ℕ) :
    ∃ C : ℕ → Set (ℝ × ℝ), C 0 = gapBox ∧
      (∀ k, k < N → ∃ (s : ℝ) (side : Bool), C (k + 1) = C k ∩ halfSpace (L k) s side) ∧
      (∀ k, k ≤ N → MeasurableSet (C k) ∧ IsBounded (C k) ∧ Convex ℝ (C k) ∧
        ∫ z in C k, gapG z = (1/2) / 2 ^ k ∧ 0 < ∫ z in C k, gapH z ∧
        1 ≤ Metric.diam (C k)) := by
  haveI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hgpos : (0:ℝ) < ∫ z in gapBox, gapG z := by rw [integral_gapG_gapBox]; norm_num
  have hhpos : (0:ℝ) < ∫ z in gapBox, gapH z := by rw [integral_gapH_gapBox]; norm_num
  obtain ⟨C, hC0, hCstep, hCinv⟩ :=
    exists_bisection_chain integrable_gapG integrable_gapH L hL measurableSet_gapBox
      isBounded_gapBox hgpos hhpos N
  refine ⟨C, hC0, hCstep, fun k hk => ?_⟩
  obtain ⟨hm, hb, hc, hgk, hhk⟩ := hCinv k hk
  have hgk' : ∫ z in C k, gapG z = (1/2) / 2 ^ k := by rw [hgk, integral_gapG_gapBox]
  have hgpos' : (0:ℝ) < ∫ z in C k, gapG z := by
    rw [hgk']; positivity
  exact ⟨hm, hb, hc convex_gapBox, hgk', hhk, one_le_diam_of_gap_pos hm hb hgpos' hhk⟩

end Witness

/-! ### The bisection chain, run forever, and its limit body -/

section InfiniteChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The bisection chain, run to infinite depth.**

`Arlib.exists_bisection_chain` produces, for each finite depth `N`, a chain of length `N`.  Here
the same construction is run as a single infinite nested sequence: a decreasing `C : ℕ → Set E`
with `C 0 = K`, each `C k` measurable, convex whenever `K` is, with `g`-mass exactly `2^{-k}`
of `K`'s and `h`-mass still positive.

The dependent choice is done by `choose` on a total successor function (the successor is the
identity on inputs that fail the invariant, which never occurs along the chain). -/
theorem exists_infinite_bisection_chain {g h : E → ℝ} (hg : Integrable g μ) (hh : Integrable h μ)
    (L : ℕ → (E →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0) {K : Set E} (hK : MeasurableSet K)
    (hKb : IsBounded K) (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ) :
    ∃ C : ℕ → Set E, C 0 = K ∧ (∀ k, C (k + 1) ⊆ C k) ∧
      ∀ k, MeasurableSet (C k) ∧ C k ⊆ K ∧ (Convex ℝ K → Convex ℝ (C k)) ∧
        (∫ x in C k, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ k ∧ 0 < ∫ x in C k, h x ∂μ := by
  classical
  have hstep : ∀ (k : ℕ) (C : Set E), ∃ D : Set E,
      MeasurableSet C → C ⊆ K → (Convex ℝ K → Convex ℝ C) →
      (∫ x in C, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ k → 0 < ∫ x in C, h x ∂μ →
      (D ⊆ C ∧ MeasurableSet D ∧ D ⊆ K ∧ (Convex ℝ K → Convex ℝ D) ∧
        (∫ x in D, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ (k + 1) ∧ 0 < ∫ x in D, h x ∂μ) := by
    intro k C
    by_cases hyp : MeasurableSet C ∧ C ⊆ K ∧ (Convex ℝ K → Convex ℝ C) ∧
        (∫ x in C, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ k ∧ 0 < ∫ x in C, h x ∂μ
    · obtain ⟨hCm, hCK, hCc, hCg, hCh⟩ := hyp
      have hCb : IsBounded C := hKb.subset hCK
      have hgC : 0 < ∫ x in C, g x ∂μ := by rw [hCg]; exact div_pos hgK (by positivity)
      obtain ⟨s, side, hDm, hDsub, hDc, hDg, _, hDh⟩ :=
        exists_halfSpace_cut_pos hg.integrableOn hh.integrableOn hCm hCb (hL k) hgC hCh
      refine ⟨C ∩ halfSpace (L k) s side, fun _ _ _ _ _ =>
        ⟨hDsub, hDm, hDsub.trans hCK, fun hc => hDc (hCc hc), ?_, hDh⟩⟩
      rw [hDg, hCg, pow_succ]; ring
    · exact ⟨C, fun h1 h2 h3 h4 h5 => absurd ⟨h1, h2, h3, h4, h5⟩ hyp⟩
  choose F hF using hstep
  refine ⟨fun k => Nat.rec K (fun j c => F j c) k, rfl, ?_, ?_⟩
  · intro k
    have hinv : ∀ j : ℕ, MeasurableSet (Nat.rec K (fun j c => F j c) j : Set E) ∧
        (Nat.rec K (fun j c => F j c) j : Set E) ⊆ K ∧
        (Convex ℝ K → Convex ℝ (Nat.rec K (fun j c => F j c) j : Set E)) ∧
        (∫ x in (Nat.rec K (fun j c => F j c) j : Set E), g x ∂μ)
          = (∫ x in K, g x ∂μ) / 2 ^ j ∧
        0 < ∫ x in (Nat.rec K (fun j c => F j c) j : Set E), h x ∂μ := by
      intro j
      induction j with
      | zero => exact ⟨hK, Subset.rfl, fun hc => hc, by simp, hhK⟩
      | succ j ih =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih
        obtain ⟨-, hb, hc, hd, he, hf⟩ := hF j _ h1 h2 h3 h4 h5
        exact ⟨hb, hc, hd, he, hf⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv k
    exact (hF k _ h1 h2 h3 h4 h5).1
  · intro k
    induction k with
    | zero => exact ⟨hK, Subset.rfl, fun hc => hc, by simp, hhK⟩
    | succ j ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      obtain ⟨-, hb, hc, hd, he, hf⟩ := hF j _ h1 h2 h3 h4 h5
      exact ⟨hb, hc, hd, he, hf⟩

/-- **The limit body of a bisection chain carries no `g`-mass.**

If `C` is any decreasing sequence of measurable sets whose `g`-masses tend to `0`, then the
intersection has `g`-mass `0`.  Applied to the bisection chain (`g`-mass `2^{-k}·∫_K g`), this
says the naive infinite limit `⋂ C k` **leaves the family**: the invariant `0 < ∫ g` that every
finite stage satisfies fails in the limit.

Together with the diameter bound of `Arlib.one_le_diam_bisection_chain`, this pins the shape of
what a limit argument can possibly deliver: the bodies stay fat, and the limit is not admissible,
so the needle must be extracted from a *renormalised* limit, never from `⋂ C k` itself. -/
theorem setIntegral_iInter_eq_zero_of_tendsto {g : E → ℝ} (hg : Integrable g μ)
    {C : ℕ → Set E} (hCm : ∀ k, MeasurableSet (C k)) (hmono : ∀ k, C (k + 1) ⊆ C k)
    (hlim : Tendsto (fun k => ∫ x in C k, g x ∂μ) atTop (𝓝 0)) :
    ∫ x in ⋂ k, C k, g x ∂μ = 0 := by
  have hanti : ∀ {i j : ℕ}, i ≤ j → C j ⊆ C i := by
    intro i j hij
    induction j with
    | zero => rw [Nat.le_zero.mp hij]
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · exact (hmono j).trans (ih (Nat.lt_succ_iff.mp hlt))
      · rw [heq]
  have hImeas : MeasurableSet (⋂ k, C k) := MeasurableSet.iInter hCm
  have hptw : ∀ x, Tendsto (fun k => (C k).indicator g x) atTop
      (𝓝 ((⋂ k, C k).indicator g x)) := by
    intro x
    by_cases hx : x ∈ ⋂ k, C k
    · have : ∀ k, (C k).indicator g x = (⋂ k, C k).indicator g x := by
        intro k
        rw [Set.indicator_of_mem (Set.mem_iInter.mp hx k), Set.indicator_of_mem hx]
      simpa only [this] using tendsto_const_nhds
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀, x ∉ C k₀ := by
        by_contra hcon
        push Not at hcon
        exact hx (Set.mem_iInter.mpr hcon)
      rw [Set.indicator_of_notMem hx]
      refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
      exact Set.indicator_of_notMem (fun hmem => hk₀ (hanti hk hmem)) _
  have hdom : ∀ k, ∀ᵐ x ∂μ, ‖(C k).indicator g x‖ ≤ ‖g x‖ :=
    fun k => Eventually.of_forall fun x => by
      simpa using norm_indicator_le_abs (C k) g x
  have hconv : Tendsto (fun k => ∫ x, (C k).indicator g x ∂μ) atTop
      (𝓝 (∫ x, (⋂ k, C k).indicator g x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun k => hg.aestronglyMeasurable.indicator (hCm k)) hg.norm hdom
      (Eventually.of_forall hptw)
  have heq1 : ∀ k, ∫ x, (C k).indicator g x ∂μ = ∫ x in C k, g x ∂μ :=
    fun k => integral_indicator (hCm k)
  have heq2 : ∫ x, (⋂ k, C k).indicator g x ∂μ = ∫ x in ⋂ k, C k, g x ∂μ :=
    integral_indicator hImeas
  rw [← heq2]
  simp only [heq1] at hconv
  exact tendsto_nhds_unique hconv hlim

/-- **Item 1, delivered: the infinite bisection chain has a Hausdorff-convergent subsequence,
with a nonempty compact convex limit body inside `K`.**

Combining `Arlib.exists_infinite_bisection_chain` with Blaschke selection
(`Arlib.exists_subseq_tendsto_hausdorffDist_convex`), applied to the closures of the chain (the
open side of a cut makes `C k` itself non-closed, and `closure` changes neither convexity nor
containment in `K`).

The theorem also records the two facts that constrain what the limit can be:
`∫_{⋂ C k} g = 0` (the limit leaves the family, `Arlib.setIntegral_iInter_eq_zero_of_tendsto`),
and, for the planar witness, `1 ≤ diam (C k)` for all `k`
(`Arlib.one_le_diam_bisection_chain`) — so the limit body `D` need not be, and in general is
not, degenerate. -/
theorem exists_subseq_hausdorff_limit_bisection_chain {g h : E → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ) (L : ℕ → (E →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ) :
    ∃ C : ℕ → Set E, C 0 = K ∧ (∀ k, C (k + 1) ⊆ C k) ∧
      (∀ k, MeasurableSet (C k) ∧ (C k).Nonempty ∧ C k ⊆ K ∧ Convex ℝ (C k) ∧
        (∫ x in C k, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ k ∧ 0 < ∫ x in C k, h x ∂μ) ∧
      (∫ x in ⋂ k, C k, g x ∂μ) = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ D : Set E, D.Nonempty ∧ IsCompact D ∧ Convex ℝ D ∧ D ⊆ K ∧
        Tendsto (fun n => hausdorffDist (closure (C (φ n))) D) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hmono, hinv⟩ :=
    exists_infinite_bisection_chain hg hh L hL hKm hK.isBounded hgK hhK
  have hne : ∀ k, (C k).Nonempty := by
    intro k
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have := (hinv k).2.2.2.2
    rw [hempty, setIntegral_empty] at this
    exact lt_irrefl 0 this
  have hfull : ∀ k, MeasurableSet (C k) ∧ (C k).Nonempty ∧ C k ⊆ K ∧ Convex ℝ (C k) ∧
      (∫ x in C k, g x ∂μ) = (∫ x in K, g x ∂μ) / 2 ^ k ∧ 0 < ∫ x in C k, h x ∂μ := by
    intro k
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv k
    exact ⟨h1, hne k, h2, h3 hKc, h4, h5⟩
  have hzero : (∫ x in ⋂ k, C k, g x ∂μ) = 0 := by
    refine setIntegral_iInter_eq_zero_of_tendsto hg (fun k => (hinv k).1) hmono ?_
    have h2 : Tendsto (fun k : ℕ => ((1:ℝ)/2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 := h2.const_mul (∫ x in K, g x ∂μ)
    rw [mul_zero] at h3
    have h4 : Tendsto (fun k : ℕ => (∫ x in K, g x ∂μ) / 2 ^ k) atTop (𝓝 0) := by
      simpa [div_pow, mul_one_div, div_eq_mul_inv] using h3
    exact h4.congr fun k => ((hinv k).2.2.2.1).symm
  obtain ⟨φ, hφ, D, hDne, hDcpt, hDconv, hDK, hDlim⟩ :=
    exists_subseq_tendsto_hausdorffDist_convex hK
      (C := fun k => closure (C k))
      (fun k => (hne k).mono subset_closure)
      (fun k => hK.of_isClosed_subset isClosed_closure
        (closure_minimal (hfull k).2.2.1 hK.isClosed))
      (fun k => (hfull k).2.2.2.1.closure)
      (fun k => closure_minimal (hfull k).2.2.1 hK.isClosed)
  exact ⟨C, hC0, hmono, hfull, hzero, φ, hφ, D, hDne, hDcpt, hDconv, hDK, hDlim⟩

end InfiniteChain

/-! ### What does survive the limit: the needle's length -/

section LimitSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A limit of points of `C n` lies in a Hausdorff limit `D` of the `C n`. -/
theorem mem_of_tendsto_of_tendsto_hausdorffDist {C : ℕ → Set E} {D : Set E}
    (hne : ∀ n, (C n).Nonempty) (hbdd : ∀ n, IsBounded (C n)) (hDne : D.Nonempty)
    (hDbdd : IsBounded D) (hDcl : IsClosed D)
    {u : ℕ → E} (hu : ∀ n, u n ∈ C n) {a : E} (ha : Tendsto u atTop (𝓝 a))
    (hlim : Tendsto (fun n => hausdorffDist (C n) D) atTop (𝓝 0)) : a ∈ D := by
  rw [hDcl.mem_iff_infDist_zero hDne]
  refine le_antisymm ?_ infDist_nonneg
  have key : ∀ n, infDist a D ≤ hausdorffDist (C n) D + dist (u n) a := by
    intro n
    have hEne : hausdorffEDist (C n) D ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded (hne n) hDne (hbdd n) hDbdd
    calc infDist a D ≤ infDist (u n) D + dist a (u n) := infDist_le_infDist_add_dist
      _ ≤ hausdorffDist (C n) D + dist (u n) a := by
          rw [dist_comm a (u n)]
          exact add_le_add (infDist_le_hausdorffDist_of_mem (hu n) hEne) le_rfl
  have hdist : Tendsto (fun n => dist (u n) a) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp ha
  have hsum : Tendsto (fun n => hausdorffDist (C n) D + dist (u n) a) atTop (𝓝 0) := by
    simpa using hlim.add hdist
  exact ge_of_tendsto hsum (Eventually.of_forall key)

/-- **A chord of length `r` present at every stage survives the Hausdorff limit.**

If every `C n` (all inside a fixed compact `K`) contains two points at distance at least `r`, and
`C n → D` in Hausdorff distance, then `D` contains two points at distance at least `r`.  If `D`
is moreover convex, the whole segment between them lies in `D`.

This is the *positive* half of the limit passage, and it is the half the sign-separation
obstruction predicts: the invariant `0 < ∫ g`, `0 < ∫ h` forces a spanning chord at every stage
(`Arlib.exists_pair_dist_ge_of_sign_separated`), and that chord is inherited by the limit body.
The limiting **needle is therefore never shorter than the gap** between the supports of `g` and
`h` — a needle of positive length, not a point. -/
theorem exists_pair_dist_ge_of_tendsto_hausdorffDist {C : ℕ → Set E} {D K : Set E}
    (hK : IsCompact K) (hCK : ∀ n, C n ⊆ K) (hne : ∀ n, (C n).Nonempty)
    (hDne : D.Nonempty) (hDcpt : IsCompact D)
    (hlim : Tendsto (fun n => hausdorffDist (C n) D) atTop (𝓝 0))
    {r : ℝ} (hr : ∀ n, ∃ x ∈ C n, ∃ y ∈ C n, r ≤ dist x y) :
    ∃ x ∈ D, ∃ y ∈ D, r ≤ dist x y := by
  choose u hu v hv hd using hr
  obtain ⟨a, -, φ₁, hφ₁, hua⟩ := hK.tendsto_subseq (x := u) (fun n => hCK n (hu n))
  obtain ⟨b, -, φ₂, hφ₂, hvb⟩ :=
    hK.tendsto_subseq (x := fun n => v (φ₁ n)) (fun n => hCK _ (hv _))
  have hφ : StrictMono (φ₁ ∘ φ₂) := hφ₁.comp hφ₂
  have hlim' : Tendsto (fun n => hausdorffDist (C (φ₁ (φ₂ n))) D) atTop (𝓝 0) :=
    hlim.comp hφ.tendsto_atTop
  have hua' : Tendsto (fun n => u (φ₁ (φ₂ n))) atTop (𝓝 a) := hua.comp hφ₂.tendsto_atTop
  have hvb' : Tendsto (fun n => v (φ₁ (φ₂ n))) atTop (𝓝 b) := hvb
  have haD : a ∈ D :=
    mem_of_tendsto_of_tendsto_hausdorffDist (C := fun n => C (φ₁ (φ₂ n)))
      (fun n => hne _) (fun n => hK.isBounded.subset (hCK _)) hDne hDcpt.isBounded
      hDcpt.isClosed (fun n => hu _) hua' hlim'
  have hbD : b ∈ D :=
    mem_of_tendsto_of_tendsto_hausdorffDist (C := fun n => C (φ₁ (φ₂ n)))
      (fun n => hne _) (fun n => hK.isBounded.subset (hCK _)) hDne hDcpt.isBounded
      hDcpt.isClosed (fun n => hv _) hvb' hlim'
  refine ⟨a, haD, b, hbD, ?_⟩
  exact ge_of_tendsto (hua'.dist hvb') (Eventually.of_forall fun n => hd _)

/-- The convex form: the limit body contains a whole **segment** of length at least `r`. -/
theorem exists_segment_subset_of_tendsto_hausdorffDist {C : ℕ → Set E} {D K : Set E}
    (hK : IsCompact K) (hCK : ∀ n, C n ⊆ K) (hne : ∀ n, (C n).Nonempty)
    (hDne : D.Nonempty) (hDcpt : IsCompact D) (hDconv : Convex ℝ D)
    (hlim : Tendsto (fun n => hausdorffDist (C n) D) atTop (𝓝 0))
    {r : ℝ} (hr : ∀ n, ∃ x ∈ C n, ∃ y ∈ C n, r ≤ dist x y) :
    ∃ x ∈ D, ∃ y ∈ D, r ≤ dist x y ∧ segment ℝ x y ⊆ D := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    exists_pair_dist_ge_of_tendsto_hausdorffDist hK hCK hne hDne hDcpt hlim hr
  exact ⟨x, hx, y, hy, hxy, hDconv.segment_subset hx hy⟩

end LimitSegment

/-! ### The planar capstone -/

section PlanarCapstone

/-- **Everything above, on one concrete configuration.**

For the planar data `Arlib.gapG`, `Arlib.gapH` on the box `Arlib.gapBox = [0,3] × [0,1]`, and
for an **arbitrary** sequence `L` of cut directions (so, in particular, for any adaptive rule),
the infinite bisection chain `C` satisfies simultaneously:

* every stage is measurable, nonempty, convex, inside the box, with `g`-mass exactly `2^{-k}/2`
  and positive `h`-mass — the localisation invariant, at every depth;
* **every stage has diameter at least `1`.**  The bodies never become small: adaptive choice of
  the cut direction cannot make them shrink, because the invariant itself forbids it;
* the naive limit `⋂ C k` has `g`-mass `0` — the limit **leaves** the family;
* a subsequence of the closures converges in Hausdorff distance to a nonempty compact convex
  `D ⊆ gapBox` which contains an honest **segment of length at least `1`**.

So the limit body is a genuine needle-carrier of positive length, and the only thing that can
still degenerate in the limit is the body's extent *transverse* to that segment.  Driving the
diameter to zero — the step that a naive reading of the localisation argument asks for — is
impossible. -/
theorem bisection_chain_gapBox (L : ℕ → ((ℝ × ℝ) →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0) :
    ∃ C : ℕ → Set (ℝ × ℝ), C 0 = gapBox ∧ (∀ k, C (k + 1) ⊆ C k) ∧
      (∀ k, MeasurableSet (C k) ∧ (C k).Nonempty ∧ C k ⊆ gapBox ∧ Convex ℝ (C k) ∧
        (∫ z in C k, gapG z) = (1/2) / 2 ^ k ∧ 0 < ∫ z in C k, gapH z ∧
        1 ≤ Metric.diam (C k)) ∧
      (∫ z in ⋂ k, C k, gapG z) = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ D : Set (ℝ × ℝ), D.Nonempty ∧ IsCompact D ∧ Convex ℝ D ∧
        D ⊆ gapBox ∧ Tendsto (fun n => hausdorffDist (closure (C (φ n))) D) atTop (𝓝 0) ∧
        ∃ x ∈ D, ∃ y ∈ D, 1 ≤ dist x y ∧ segment ℝ x y ⊆ D := by
  haveI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hgpos : (0:ℝ) < ∫ z in gapBox, gapG z := by rw [integral_gapG_gapBox]; norm_num
  have hhpos : (0:ℝ) < ∫ z in gapBox, gapH z := by rw [integral_gapH_gapBox]; norm_num
  obtain ⟨C, hC0, hmono, hinv, hzero, φ, hφ, D, hDne, hDcpt, hDconv, hDK, hDlim⟩ :=
    exists_subseq_hausdorff_limit_bisection_chain integrable_gapG integrable_gapH L hL
      isCompact_gapBox measurableSet_gapBox convex_gapBox hgpos hhpos
  have hfull : ∀ k, MeasurableSet (C k) ∧ (C k).Nonempty ∧ C k ⊆ gapBox ∧ Convex ℝ (C k) ∧
      (∫ z in C k, gapG z) = (1/2) / 2 ^ k ∧ 0 < ∫ z in C k, gapH z ∧
      1 ≤ Metric.diam (C k) := by
    intro k
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv k
    have h5' : (∫ z in C k, gapG z) = (1/2) / 2 ^ k := by rw [h5, integral_gapG_gapBox]
    have hgk : (0:ℝ) < ∫ z in C k, gapG z := by rw [h5']; positivity
    exact ⟨h1, h2, h3, h4, h5', h6,
      one_le_diam_of_gap_pos h1 (isBounded_gapBox.subset h3) hgk h6⟩
  refine ⟨C, hC0, hmono, hfull, hzero, φ, hφ, D, hDne, hDcpt, hDconv, hDK, hDlim, ?_⟩
  refine exists_segment_subset_of_tendsto_hausdorffDist (K := gapBox) isCompact_gapBox
    (fun n => closure_minimal (hfull (φ n)).2.2.1 isCompact_gapBox.isClosed)
    (fun n => ((hfull (φ n)).2.1).mono subset_closure) hDne hDcpt hDconv hDlim ?_
  intro n
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    exists_pair_one_le_dist_of_gap_pos (hfull (φ n)).1
      (by rw [(hfull (φ n)).2.2.2.2.1]; positivity) (hfull (φ n)).2.2.2.2.2.1
  exact ⟨x, subset_closure hx, y, subset_closure hy, hxy⟩

end PlanarCapstone

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`.  There are
no `axiom` declarations, no `sorry` and no `native_decide` anywhere in this file. -/

#print axioms exists_mem_apply_le_of_setIntegral_pos
#print axioms exists_mem_le_apply_of_setIntegral_pos
#print axioms exists_pair_apply_sub_ge_of_sign_separated
#print axioms exists_pair_dist_ge_of_sign_separated
#print axioms le_diam_of_sign_separated
#print axioms integrable_icoConst
#print axioms icoConst_nonneg
#print axioms icoConst_of_lt
#print axioms icoConst_of_ge
#print axioms integrable_stepLeft
#print axioms integrable_stepRight
#print axioms stepLeft_nonpos
#print axioms stepRight_nonpos
#print axioms Ico_subset_Icc_of_le
#print axioms integral_icoConst_of_subset
#print axioms integral_stepLeft
#print axioms integral_stepRight
#print axioms measurableSet_gapBox
#print axioms convex_gapBox
#print axioms isCompact_gapBox
#print axioms isBounded_gapBox
#print axioms integrable_gapG
#print axioms integrable_gapH
#print axioms integral_gapG_gapBox
#print axioms integral_gapH_gapBox
#print axioms gapG_nonpos
#print axioms gapH_nonpos
#print axioms exists_pair_one_le_dist_of_gap_pos
#print axioms one_le_diam_of_gap_pos
#print axioms one_le_diam_bisection_chain
#print axioms exists_infinite_bisection_chain
#print axioms setIntegral_iInter_eq_zero_of_tendsto
#print axioms exists_subseq_hausdorff_limit_bisection_chain
#print axioms mem_of_tendsto_of_tendsto_hausdorffDist
#print axioms exists_pair_dist_ge_of_tendsto_hausdorffDist
#print axioms exists_segment_subset_of_tendsto_hausdorffDist
#print axioms bisection_chain_gapBox

end Arlib
