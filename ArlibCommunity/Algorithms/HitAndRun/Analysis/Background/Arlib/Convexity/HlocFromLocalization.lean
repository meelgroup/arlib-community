/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.SharpIsoperimetryConcave

/-!
# `hloc` from the localization stack: the three shape gaps, closed

`Arlib.gaussianRestricted_isoperimetry_concave`
(`Arlib/Convexity/SharpIsoperimetryConcave.lean:435`) proves Cousins–Vempala's `thm:iso` at the
sharp constant `d/σ` from **one** residual `∀`-binder, `hloc`: the Localization Lemma of
Lovász–Simonovits (KLS 1995, Corollary 2.4, equality form) applied to
`g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h` (`vol3_journal.tex:479–493`).

What the localization stack of this repository delivers
(`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`,
`Arlib/Convexity/LocalizationClosed.lean:376`, and its siblings in
`Arlib.Convexity.LocalizationAffine`, `Arlib.Convexity.NeedleSlab*`,
`Arlib.Convexity.NeedleSlabChain`) has a *different shape* from what `hloc` asks for.  This file
closes the three differences, and nothing else.

## Main results

* `Arlib.hloc_of_localization` — **`hloc`, verbatim, from the stack's raw needle.**
* `Arlib.hloc_ge_of_localization_ge` — the same three gaps closed for the `≥`-form of `hloc`
  (see "A second finding" below); ready for the consumer-side weakening.
* `Arlib.gaussianRestricted_isoperimetry_of_localization` — `thm:iso` with **no one-dimensional
  residual binder left**: only `hLoc`, the Localization Lemma itself.
* `Arlib.gaussianRestricted_isoperimetry_of_localization_witness` — non-vacuity.
* `Arlib.hloc_antecedent_false_of_isoperimetry` — a finding: `hloc`'s antecedent is refuted by
  the theorem's own conclusion, so **no witness can satisfy it genuinely**.
* `Arlib.needle_masses_contradiction_ge`, `Arlib.needle_masses_contradiction_ge'` — a second
  finding: `hloc`'s **equality may be weakened to `≥`** without touching the consumer's proof.

## The three shape gaps, and how each is closed

**Gap 1 — `Ioo 0 1` to `Icc α β`.**  The stack delivers `ConcaveOn ℝ (Ioo 0 1) (W ^ (1/(n−1)))`;
`hloc` wants `ConcaveOn ℝ (Icc α β) l`.  `Arlib.concaveOn_Icc_extendZero` extends a nonnegative
concave function from the open to the closed interval **by the value `0` at the endpoints**, which
is concave because a nonnegative concave function already dominates the chords to its endpoints
(`Arlib.concaveOn_Ioo_left_endpoint_le`, `Arlib.concaveOn_Ioo_right_endpoint_le`: a limit of the
concavity inequality along `s → α⁺`, resp. `s → β⁻`).  No hypothesis beyond nonnegativity is
needed — in particular no boundedness and no continuity at the endpoints.

The extension changes `l` only on the two-point set `{α, β}`, which is Lebesgue-null, so no
integral moves.  This is said explicitly, not left implicit:
`Arlib.ae_eq_of_forall_ne_pair` and `Arlib.integral_congr_off_pair` are the lemmas that carry it,
and they are used at every place where `l ^ (n−1)` is traded for the rescaled profile.

**Gap 2 — `φ`-normalised axis to arclength.**  The stack's axis is `t ↦ b + t • v` with `φ v = 1`,
not `‖v‖ = 1`.  Put `c := ‖v‖`, `e := c⁻¹ • v`, and reparameterise: `needleMap b v t =
needleMap b e (c*t)` (`Arlib.needleMap_smul_left`), the profile becomes `s ↦ W (c⁻¹ * s)`, and the
interval becomes `[0, c]`.

**The Jacobian is the single positive constant `c = ‖v‖`, and it genuinely cancels.**
`Arlib.integral_needle_rescale` proves `∫ s, V s · u (needleMap b e s) = c · ∫ t, W t · u
(needleMap b v t)` for *every* integrand `u`, so the **same** factor `c` multiplies all four needle
masses.  In the first conclusion it cancels because the identity is `c·J₁ = A·(c·J)` obtained from
`J₁ = A·J`; in the second because `c > 0` and `c·J₃ < c·(d/σ·A·J₂) = d/σ·A·(c·J₂)`.  Verified, not
assumed: see the last two bullets of the proof of `Arlib.hloc_of_localization`.

The degenerate case `v = 0` is **not** handled here — it is excluded by the `v ≠ 0` clause of the
binder, which is residual **(F)** (the limit body must contain two distinct points; a chain
collapsing to a point gives a degenerate needle).  This is the honest place for it: `‖e‖ = 1` is
simply false when `v = 0`, so no reparameterisation exists.

**Gap 3 — full-line integrals to interval and set integrals.**  The stack states `∫ t : ℝ`;
`hloc` wants `∫ t in α..β` (orientation-sensitive) and `∫ t in γ ⁻¹' Sᵢ ∩ Icc α β` (a set
integral).  `Arlib.setIntegral_needle_of_profile` and `Arlib.intervalIntegral_needle_of_profile`
bridge both, using `intervalIntegral.integral_of_le` for the orientation and the profile's
**support** for the truncation.

## What is assumed — the residual binder `hLoc`, clause by clause

`hLoc` is the Localization Lemma applied to *our* `g₁`, `g₂`.  It is a plain `∀`-binder of
`Arlib.hloc_of_localization` and of
`Arlib.gaussianRestricted_isoperimetry_of_localization`; there is no `def … : Prop` packaging it,
no `structure`, and no `axiom`.  **Every clause is in the stack's pre-gap shape**, never in
`hloc`'s post-gap shape — otherwise this file would prove nothing.  Provenance:

| clause | status |
|---|---|
| `v ≠ 0` | **(F)** nondegeneracy — `LocalizationAssembly.lean:188` |
| `∀ t, 0 ≤ W t` | delivered by the stack |
| `∀ t ∉ Icc 0 1, W t = 0` | **(S)**, a stack *API* gap — see below |
| `ConcaveOn ℝ (Ioo 0 1) (W ^ (1/(n−1)))` | delivered by the stack |
| `Integrable (fun t => W t * h (needleMap b v t))` | **(I)**, a stack *API* gap — see below |
| `∫ t : ℝ, W t · g₁(needleMap b v t) = 0` | delivered, **but only for continuous `g₁`** — **(C)** |
| `0 < ∫ t : ℝ, W t · g₂(needleMap b v t)` | delivered, **but only for continuous `g₂`** — **(C)** |
| ambient space `EuclideanSpace ℝ (Fin n)` | **(F)** transport — the stack lives in `Fin (m+1) → ℝ` |

**Why residual (C) bites here, and it is the single most important fact about this file.**
Our `g₁ = 1_{S₁}h − A·h` is built from the **indicator of a merely measurable set**, hence is
**not continuous** — and the stack's needle theorems
(`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`,
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain`) ask their integrands to be
*bounded continuous*.  That is residual **(C)**, lower semicontinuity,
`LocalizationAssembly.lean:184`.  So this file is a **reduction, not an unconditional theorem**:
it removes the one-dimensional shape mismatch and leaves the analytic content of localization
exactly where it was.

**(C) is worse than "an approximation step not yet carried out."**  A needle is a Lebesgue-null
set of `ℝⁿ`, and a measurable set is only determined up to null sets, so no `L¹`-approximation of
`1_{S₁}` can control a needle integral.  Approximation from below by continuous minorants requires
`1_{S₁}` to be *lower* semicontinuous, i.e. `S₁` open; for `S₁` a fat Cantor set every continuous
minorant of `1_{S₁}` is `≤ 0` (its complement is dense), so the approximation route is not merely
hard but **false** beyond lower semicontinuity.  See `Arlib.Convexity.LocalizationLSC`.

**Why `hLoc` is *one* binder rather than separate `(C)` and `(F)` binders.**  Invoking the stack's
theorems literally is impossible in a way that no re-shaping fixes: they live in `Fin (m+1) → ℝ`
(that is (F)), they demand continuous integrands (that is (C)), and they consume a *compact* chain,
so one would additionally have to truncate `ℝⁿ` to a compact body while preserving `∫ g₁ = 0`
**exactly** — which is itself part of (C)'s approximation step.  Joining (C) and (F) at the point
of use, in the shape the stack delivers, is the honest formulation; splitting them would produce
two binders neither of which is separately consumable.

**(S) support, a stack API gap, not a mathematical gap.**  `W t = 0` for `t ∉ [0,1]` is *true* of
the constructed profile and *provable* from `Arlib.exists_subseq_tendsto_normalised_slice_profile'`
(`Arlib/Convexity/ConcaveSelection.lean:546`), whose conclusion exposes `W` as the pointwise limit
of the normalised slice profiles, and those vanish off the slab
(`Arlib/Convexity/ConcaveSelection.lean:422`).  It is **discarded** by the existential of
`Arlib.exists_needleIntegral_eq_zero_and_pos` (`Arlib/Convexity/LocalizationAffine.lean:273`) and
of every theorem downstream of it.  Without it Gap 3 is unclosable: `∫ t : ℝ` is not `∫ t in [α,β]`
for a profile with mass outside the slab.  The fix belongs in those files, not here.

**(I) integrability, the same character.**  `Integrable (fun t => W t * h (needleMap b v t))` is
established inside the limit passage (`Arlib.tendsto_average_setIntegral_of_profile`, dominated
convergence against `1_{[0,1]}·B·M`) but is not exposed either.  It is needed twice: `hloc`'s own
conclusion contains an `IntervalIntegrable` clause, and splitting `∫ W·g₁∘γ` into its `1_{S₁}h` and
`A·h` parts needs both parts integrable.  One clause suffices: `h ≥ 0`, so the three indicator
pieces are dominated by it (`Arlib.integrable_profile_mul_indicator_needle`).

Note that **no measurability of `h` on the needle is assumed anywhere**, and none is available —
`h` is only integrable on `ℝⁿ`, and the needle is null there.  The indicator pieces are handled by
rewriting `t ↦ W t · 1_S(γ t)·h(γ t)` as `(γ ⁻¹' S).indicator (t ↦ W t · h(γ t))`, whose
integrability follows from clause **(I)** and measurability of the *set* `γ ⁻¹' S` alone.

## The dimension restriction `2 ≤ n`

The stack's needle theorems carry `hm : m ≠ 0` with ambient dimension `m + 1 = n`, and the profile
identity `l ^ (n−1) = W` needs `(n−1) ≠ 0`.  So the results here require `2 ≤ n`, strictly more
than the `0 < n` of `Arlib.gaussianRestricted_isoperimetry_concave`.  `n = 1` is excluded: there
the "needle" is the whole space and localization is vacuous, so a separate (easier) argument would
be needed.

## Non-vacuity, and a finding about it

`AUDIT.md` check 4 prefers a witness in which `hloc`'s antecedent is genuinely *satisfied* rather
than vacuously discharged.  **That preference is unachievable here, provably.**
`Arlib.hloc_antecedent_false_of_isoperimetry` shows the antecedent of `hloc` — `∫_{S₁}h = A∫h`
together with `∫_{S₃}h < (d/σ)A∫_{S₂}h` — contradicts the conclusion of `thm:iso` outright, given
only `0 < ∫h`.  So for *any* data satisfying the theorem's other hypotheses the antecedent is
false, and every witness is necessarily vacuous.  `hloc` is a proof-by-contradiction hypothesis;
that is its nature, not a defect of the witness.

`Arlib.gaussianRestricted_isoperimetry_of_localization_witness` therefore discharges `hLoc` by that
route, from the conclusion `Arlib.gaussianRestricted_isoperimetry_concave` already delivers for the
witness data of `Arlib.gaussianRestricted_isoperimetry_concave_witness`.  It is a strict
improvement on that witness in one respect: the vacuity is now *derived* from the theorem rather
than arranged by hand-tuning `d`.

## A second finding: `hloc`'s equality can be weakened to `≥`

`Arlib.needle_masses_contradiction` (`Arlib/Convexity/SharpIsoperimetry.lean:176`) is the arithmetic
core that closes Cousins–Vempala's proof.  It consumes `I₁ = A·I` **only** through the step
`c·(A·I)·I₂ = c·I₁·I₂`, and that step needs the equality in only one direction.
`Arlib.needle_masses_contradiction_ge` proves the contradiction from `A·I ≤ I₁` given `0 ≤ c` and
`0 ≤ I₂`; `Arlib.needle_masses_contradiction_ge'` derives `0 ≤ c` from `0 ≤ I₃` and `0 < A`, so the
*only* extra side conditions are `0 ≤ I₂` and `0 ≤ I₃`, both immediate from the needle density
being nonnegative.

This matters because the monotone-approximation route to (C) (increasing continuous minorants of
`1_{S₁}` for `S₁` open) delivers exactly `A·I ≤ I₁` and not the equality.  It does **not** by itself
close (C): the needle moves with the approximation index.  But the slack is harmless if the *same*
re-centred constant `A_j` is used in `g₂` as in `g₁`, since the contradiction then closes at `A_j`.
Nothing in this file depends on the weakening; it is stated and proved here so that the consumer
side can use it, and so that the claim is machine-checked rather than asserted.

## What this file does **not** do

It proves no part of the Localization Lemma, closes neither (C) nor (F), and does not edit
`Arlib.Convexity.SharpIsoperimetryConcave`.  It imports only that file — deliberately no
`Localization*` module — so that its own build target is independent of the localization stack.
-/

open MeasureTheory Set Filter

open scoped Topology

namespace Arlib

/-! ### Gap 1: extending a nonnegative concave function from `Ioo` to `Icc` -/

section EndpointExtension

/-- **A nonnegative concave function on an open interval already dominates the chord to its left
endpoint.**

If `g` is concave and nonnegative on `Ioo α β` and `y ∈ Ioo α β`, then for every convex
combination with strictly positive weights `a • α + b • y` we have `b * g y ≤ g (a*α + b*y)` —
even though `α ∉ Ioo α β`, so `g α` is not constrained at all.  This is the fact that makes the
extension of `g` to `Icc α β` **by the value `0` at the endpoints** concave.

The proof is a limit: for `s` slightly to the right of `α` the point `z = a*α + b*y` lies strictly
between `s` and `y`, concavity on `Ioo α β` gives `((z-s)/(y-s)) * g y ≤ g z` (discarding the
nonnegative `g s` term), and `(z-s)/(y-s) → b` as `s → α⁺`. -/
theorem concaveOn_Ioo_left_endpoint_le {α β : ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Set.Ioo α β) g) (hg0 : ∀ t ∈ Set.Ioo α β, 0 ≤ g t)
    {y : ℝ} (hy : y ∈ Set.Ioo α β) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    b * g y ≤ g (a * α + b * y) := by
  obtain ⟨hyα, hyβ⟩ := hy
  set z : ℝ := a * α + b * y with hzdef
  have hzα : α < z := by
    have h1 : b * α < b * y := mul_lt_mul_of_pos_left hyα hb
    have h2 : a * α + b * α = α := by linear_combination α * hab
    rw [hzdef]; linarith
  have hzy : z < y := by
    have h1 : a * α < a * y := mul_lt_mul_of_pos_left hyα ha
    have h2 : a * y + b * y = y := by linear_combination y * hab
    rw [hzdef]; linarith
  have hzβ : z < β := lt_trans hzy hyβ
  have hstep : ∀ s ∈ Set.Ioo α z, (z - s) / (y - s) * g y ≤ g z := by
    intro s hs
    obtain ⟨hsα, hsz⟩ := hs
    have hsy : s < y := lt_trans hsz hzy
    have hys : (0 : ℝ) < y - s := by linarith
    set lam : ℝ := (y - z) / (y - s) with hlamdef
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hys.le
    have hmu : 1 - lam = (z - s) / (y - s) := by
      rw [hlamdef]; field_simp; ring
    have hmu0 : (0 : ℝ) ≤ 1 - lam := by rw [hmu]; positivity
    have hcomb : lam * s + (1 - lam) * y = z := by
      rw [hmu, hlamdef]; field_simp; ring
    have hkey := hg.2 (Set.mem_Ioo.mpr ⟨hsα, lt_trans hsz hzβ⟩) (Set.mem_Ioo.mpr ⟨hyα, hyβ⟩)
      hlam0 hmu0 (by ring)
    simp only [smul_eq_mul] at hkey
    rw [hcomb] at hkey
    have hgs : 0 ≤ g s := hg0 s ⟨hsα, lt_trans hsz hzβ⟩
    have : (1 - lam) * g y ≤ g z := by nlinarith
    rwa [hmu] at this
  have hyα' : (0 : ℝ) < y - α := by linarith
  have htend : Filter.Tendsto (fun s : ℝ => (z - s) / (y - s) * g y) (𝓝[>] α)
      (𝓝 ((z - α) / (y - α) * g y)) := by
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (((continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by simpa using hyα'.ne')).mul continuousAt_const)
  have heq : (z - α) / (y - α) = b := by
    have hne : y - α ≠ 0 := by linarith
    rw [hzdef, div_eq_iff hne]
    linear_combination α * hab
  rw [heq] at htend
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hzα] with s hs using hstep s hs

/-- **The right-endpoint counterpart of `Arlib.concaveOn_Ioo_left_endpoint_le`.** -/
theorem concaveOn_Ioo_right_endpoint_le {α β : ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Set.Ioo α β) g) (hg0 : ∀ t ∈ Set.Ioo α β, 0 ≤ g t)
    {y : ℝ} (hy : y ∈ Set.Ioo α β) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    b * g y ≤ g (a * β + b * y) := by
  obtain ⟨hyα, hyβ⟩ := hy
  set z : ℝ := a * β + b * y with hzdef
  have hzβ : z < β := by
    have h1 : b * y < b * β := mul_lt_mul_of_pos_left hyβ hb
    have h2 : a * β + b * β = β := by linear_combination β * hab
    rw [hzdef]; linarith
  have hyz : y < z := by
    have h1 : a * y < a * β := mul_lt_mul_of_pos_left hyβ ha
    have h2 : a * y + b * y = y := by linear_combination y * hab
    rw [hzdef]; linarith
  have hzα : α < z := lt_trans hyα hyz
  have hstep : ∀ s ∈ Set.Ioo z β, (s - z) / (s - y) * g y ≤ g z := by
    intro s hs
    obtain ⟨hzs, hsβ⟩ := hs
    have hys : y < s := lt_trans hyz hzs
    have hsy : (0 : ℝ) < s - y := by linarith
    set lam : ℝ := (z - y) / (s - y) with hlamdef
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hsy.le
    have hmu : 1 - lam = (s - z) / (s - y) := by
      rw [hlamdef]; field_simp; ring
    have hmu0 : (0 : ℝ) ≤ 1 - lam := by rw [hmu]; positivity
    have hcomb : lam * s + (1 - lam) * y = z := by
      rw [hmu, hlamdef]; field_simp; ring
    have hkey := hg.2 (Set.mem_Ioo.mpr ⟨lt_trans hzα hzs, hsβ⟩) (Set.mem_Ioo.mpr ⟨hyα, hyβ⟩)
      hlam0 hmu0 (by ring)
    simp only [smul_eq_mul] at hkey
    rw [hcomb] at hkey
    have hgs : 0 ≤ g s := hg0 s ⟨lt_trans hzα hzs, hsβ⟩
    have : (1 - lam) * g y ≤ g z := by nlinarith
    rwa [hmu] at this
  have hβy : (0 : ℝ) < β - y := by linarith
  have htend : Filter.Tendsto (fun s : ℝ => (s - z) / (s - y) * g y) (𝓝[<] β)
      (𝓝 ((β - z) / (β - y) * g y)) := by
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (by simpa using hβy.ne')).mul continuousAt_const)
  have heq : (β - z) / (β - y) = b := by
    have hne : β - y ≠ 0 := by linarith
    rw [hzdef, div_eq_iff hne]
    linear_combination (-β) * hab
  rw [heq] at htend
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT hzβ] with s hs using hstep s hs

/-- A strict convex combination of a point of `Icc α β` with a point of `Ioo α β` lies in
`Ioo α β`. -/
theorem mem_Ioo_of_mem_Icc_of_mem_Ioo {α β x y : ℝ} (hx : x ∈ Set.Icc α β)
    (hy : y ∈ Set.Ioo α β) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * x + b * y ∈ Set.Ioo α β := by
  obtain ⟨hxα, hxβ⟩ := hx
  obtain ⟨hyα, hyβ⟩ := hy
  have hαa : a * α ≤ a * x := mul_le_mul_of_nonneg_left hxα ha.le
  have hαb : b * α < b * y := mul_lt_mul_of_pos_left hyα hb
  have hβa : a * x ≤ a * β := mul_le_mul_of_nonneg_left hxβ ha.le
  have hβb : b * y < b * β := mul_lt_mul_of_pos_left hyβ hb
  have hsα : a * α + b * α = α := by linear_combination α * hab
  have hsβ : a * β + b * β = β := by linear_combination β * hab
  exact ⟨by linarith, by linarith⟩

/-- **Gap 1, closed: a nonnegative concave function on `Ioo α β` extends to a concave function on
`Icc α β` by giving it the value `0` at the two endpoints.**

No hypothesis beyond concavity and nonnegativity on the *open* interval is needed; the extension
is concave on the closed interval because `Arlib.concaveOn_Ioo_left_endpoint_le` and
`Arlib.concaveOn_Ioo_right_endpoint_le` say a nonnegative concave function already dominates the
chords to its endpoints.  The extension is again nonnegative
(`Arlib.nonneg_extendZero_of_nonneg`), and it differs from the original function only on the
two-point — hence Lebesgue-null — set `{α, β}`, so no integral changes. -/
theorem concaveOn_Icc_extendZero {α β : ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Set.Ioo α β) g) (hg0 : ∀ t ∈ Set.Ioo α β, 0 ≤ g t) :
    ConcaveOn ℝ (Set.Icc α β) (fun t => if t ∈ Set.Ioo α β then g t else 0) := by
  have hl0 : ∀ t : ℝ, 0 ≤ (if t ∈ Set.Ioo α β then g t else 0) := by
    intro t
    by_cases ht : t ∈ Set.Ioo α β
    · rw [if_pos ht]; exact hg0 t ht
    · rw [if_neg ht]
  refine ⟨convex_Icc α β, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1]; simp
  rcases hb.eq_or_lt with hb0 | hb0
  · have ha1 : a = 1 := by linarith
    rw [← hb0, ha1]; simp
  by_cases hyo : y ∈ Set.Ioo α β
  · have hzo : a * x + b * y ∈ Set.Ioo α β :=
      mem_Ioo_of_mem_Icc_of_mem_Ioo hx hyo ha0 hb0 hab
    by_cases hxo : x ∈ Set.Ioo α β
    · have hkey := hg.2 hxo hyo ha hb hab
      simp only [smul_eq_mul] at hkey
      rw [if_pos hxo, if_pos hyo, if_pos hzo]
      exact hkey
    · -- `x` is an endpoint of `Icc α β`
      rw [if_neg hxo, if_pos hyo, if_pos hzo, mul_zero, zero_add]
      rcases eq_or_lt_of_le hx.1 with hxα | hxα
      · have hxa : x = α := hxα.symm
        have hkey := concaveOn_Ioo_left_endpoint_le hg hg0 hyo ha0 hb0 hab
        rwa [← hxa] at hkey
      · have hxb : x = β := by
          by_contra hne
          exact hxo ⟨hxα, lt_of_le_of_ne hx.2 hne⟩
        have hkey := concaveOn_Ioo_right_endpoint_le hg hg0 hyo ha0 hb0 hab
        rwa [← hxb] at hkey
  · by_cases hxo : x ∈ Set.Ioo α β
    · have hzo : a * x + b * y ∈ Set.Ioo α β := by
        have h := mem_Ioo_of_mem_Icc_of_mem_Ioo hy hxo hb0 ha0 (by linarith)
        rwa [add_comm (b * y) (a * x)] at h
      rw [if_neg hyo, if_pos hxo, if_pos hzo, mul_zero, add_zero]
      rcases eq_or_lt_of_le hy.1 with hyα | hyα
      · have hya : y = α := hyα.symm
        have hkey := concaveOn_Ioo_left_endpoint_le hg hg0 hxo hb0 ha0 (by linarith)
        rw [← hya, add_comm (b * y) (a * x)] at hkey
        exact hkey
      · have hyb : y = β := by
          by_contra hne
          exact hyo ⟨hyα, lt_of_le_of_ne hy.2 hne⟩
        have hkey := concaveOn_Ioo_right_endpoint_le hg hg0 hxo hb0 ha0 (by linarith)
        rw [← hyb, add_comm (b * y) (a * x)] at hkey
        exact hkey
    · rw [if_neg hxo, if_neg hyo, mul_zero, mul_zero, add_zero]
      exact hl0 _

/-- The extension by zero of a nonnegative function is nonnegative — everywhere, not only on
`Icc α β`. -/
theorem nonneg_extendZero_of_nonneg {α β : ℝ} {g : ℝ → ℝ} (hg0 : ∀ t ∈ Set.Ioo α β, 0 ≤ g t)
    (t : ℝ) : 0 ≤ (if t ∈ Set.Ioo α β then g t else 0) := by
  by_cases ht : t ∈ Set.Ioo α β
  · rw [if_pos ht]; exact hg0 t ht
  · rw [if_neg ht]

end EndpointExtension

/-! ### Two null-set utilities -/

section NullSet

/-- Two functions that agree off a two-point set are almost everywhere equal for Lebesgue
measure. -/
theorem ae_eq_of_forall_ne_pair {x y : ℝ} {F G : ℝ → ℝ}
    (h : ∀ t : ℝ, t ≠ x → t ≠ y → F t = G t) : F =ᵐ[volume] G := by
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨({x, y} : Set ℝ)ᶜ, ?_, ?_⟩
  · rw [mem_ae_iff, compl_compl]
    exact ((Set.finite_singleton y).insert x).measure_zero volume
  · intro t ht
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact h t ht.1 ht.2

/-- The integral form of `Arlib.ae_eq_of_forall_ne_pair`. -/
theorem integral_congr_off_pair {x y : ℝ} {F G : ℝ → ℝ}
    (h : ∀ t : ℝ, t ≠ x → t ≠ y → F t = G t) : (∫ t : ℝ, F t) = ∫ t : ℝ, G t :=
  integral_congr_ae (ae_eq_of_forall_ne_pair h)

end NullSet

/-! ### Gap 2: the arclength reparameterisation of the needle -/

section Reparameterisation

variable {n : ℕ}

/-- The needle map is continuous. -/
theorem continuous_needleMap (p e : EuclideanSpace ℝ (Fin n)) :
    Continuous (needleMap p e) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- **Rescaling the direction and the parameter together leaves the axis unchanged.**  This is the
whole content of the arclength reparameterisation: the localization stack normalises its direction
`v` by `φ v = 1`, while `hloc` demands `‖e‖ = 1`, and the two axes are the same set of points
traversed at different speeds. -/
theorem needleMap_smul_left (p e : EuclideanSpace ℝ (Fin n)) (c t : ℝ) :
    needleMap p (c • e) t = needleMap p e (c * t) := by
  simp only [needleMap_apply, smul_smul, mul_comm]

/-- **The Jacobian of the arclength reparameterisation is the single positive constant `c`.**

Reparameterising the needle `t ↦ p + t • (c • e)` by arclength multiplies every needle integral by
exactly `c`.  Since `c > 0`, this factor cancels out of an equality with `0` on one side and out of
a strict inequality between two such integrals alike. -/
theorem integral_needle_rescale {c : ℝ} (hc : 0 < c) (V : ℝ → ℝ)
    (p e : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ s : ℝ, V s * u (needleMap p e s))
      = c * ∫ t : ℝ, V (c * t) * u (needleMap p (c • e) t) := by
  have h := Measure.integral_comp_mul_left (fun s : ℝ => V s * u (needleMap p e s)) c
  simp only [needleMap_smul_left]
  rw [h, abs_of_pos (inv_pos.mpr hc), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- `Arlib.integral_needle_rescale` in the form used below: the rescaled profile is
`s ↦ W (c⁻¹ * s)`. -/
theorem integral_needle_rescale' {c : ℝ} (hc : 0 < c) (W : ℝ → ℝ)
    (p e : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ s : ℝ, W (c⁻¹ * s) * u (needleMap p e s))
      = c * ∫ t : ℝ, W t * u (needleMap p (c • e) t) := by
  rw [integral_needle_rescale hc (fun s => W (c⁻¹ * s)) p e u]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Integrability transports along the arclength reparameterisation. -/
theorem integrable_needle_rescale {c : ℝ} (hc : 0 < c) {W : ℝ → ℝ}
    {p v : EuclideanSpace ℝ (Fin n)} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hint : Integrable (fun t => W t * u (needleMap p v t))) :
    Integrable (fun s => W (c⁻¹ * s) * u (needleMap p (c⁻¹ • v) s)) := by
  have h := hint.comp_mul_left' (R := c⁻¹) (inv_ne_zero hc.ne')
  simpa only [needleMap_smul_left] using h

end Reparameterisation

/-! ### Gap 3: full-line integrals become interval and set integrals -/

section SupportedProfile

variable {n : ℕ}

/-- **Gap 3, closed for set integrals.**

If `V` vanishes off `Icc 0 c` and `L` agrees with `V` on `Ioo 0 c` and vanishes off `Icc 0 c`,
then the *set* integral of `L · (h ∘ γ)` over `γ ⁻¹' S ∩ Icc 0 c` is the *full-line* integral of
`V · (1_S h) ∘ γ`.  The two endpoints, where `L` and `V` may disagree, form a Lebesgue-null
set. -/
theorem setIntegral_needle_of_profile {c : ℝ} {V L : ℝ → ℝ}
    (hV0 : ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) c → V s = 0)
    (hL : ∀ s ∈ Set.Ioo (0 : ℝ) c, L s = V s)
    (p e : EuclideanSpace ℝ (Fin n)) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ s in needleMap p e ⁻¹' S ∩ Set.Icc (0 : ℝ) c, L s * h (needleMap p e s))
      = ∫ s : ℝ, V s * S.indicator h (needleMap p e s) := by
  have hmeas : MeasurableSet (needleMap p e ⁻¹' S ∩ Set.Icc (0 : ℝ) c) :=
    ((continuous_needleMap p e).measurable hS).inter measurableSet_Icc
  rw [← integral_indicator hmeas]
  refine integral_congr_off_pair (x := 0) (y := c) fun t ht0 htc => ?_
  by_cases htI : t ∈ Set.Icc (0 : ℝ) c
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) c :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htc⟩
    by_cases hmem : needleMap p e t ∈ S
    · rw [Set.indicator_of_mem
        (show t ∈ needleMap p e ⁻¹' S ∩ Set.Icc (0 : ℝ) c from ⟨hmem, htI⟩),
        Set.indicator_of_mem hmem, hL t htIoo]
    · rw [Set.indicator_of_notMem
        (show t ∉ needleMap p e ⁻¹' S ∩ Set.Icc (0 : ℝ) c from fun hc' => hmem hc'.1),
        Set.indicator_of_notMem hmem, mul_zero]
  · rw [Set.indicator_of_notMem
      (show t ∉ needleMap p e ⁻¹' S ∩ Set.Icc (0 : ℝ) c from fun hc' => htI hc'.2),
      hV0 t htI, zero_mul]

/-- **Gap 3, closed for the interval integral.**  Same statement with `S = univ` and the
orientation-sensitive `∫ t in 0..c`. -/
theorem intervalIntegral_needle_of_profile {c : ℝ} (hc : 0 ≤ c) {V L : ℝ → ℝ}
    (hV0 : ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) c → V s = 0)
    (hL : ∀ s ∈ Set.Ioo (0 : ℝ) c, L s = V s)
    (p e : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ s in (0 : ℝ)..c, L s * h (needleMap p e s))
      = ∫ s : ℝ, V s * h (needleMap p e s) := by
  rw [intervalIntegral.integral_of_le hc, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_off_pair (x := 0) (y := c) fun t ht0 htc => ?_
  by_cases htI : t ∈ Set.Icc (0 : ℝ) c
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) c :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htc⟩
    rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) c from ⟨htIoo.1, htI.2⟩), hL t htIoo]
  · have hnot : t ∉ Set.Ioc (0 : ℝ) c := fun hmem => htI ⟨hmem.1.le, hmem.2⟩
    rw [Set.indicator_of_notMem hnot, hV0 t htI, zero_mul]

end SupportedProfile

/-! ### Route (a): the closing contradiction needs only `A·I ≤ I₁`, not the equality -/

section RouteA

/-- **`Arlib.needle_masses_contradiction` with the equality `I₁ = A·I` weakened to the inequality
`A·I ≤ I₁`.**

`Arlib.needle_masses_contradiction` (`Arlib/Convexity/SharpIsoperimetry.lean:176`) closes
Cousins–Vempala's proof from `I₁ = A·I`, `I₃ < c·A·I₂` and `c·(I₁·I₂) ≤ I·I₃` by the chain

  `I·I₃ < I·(c·A·I₂) = c·(A·I)·I₂ = c·(I₁·I₂) ≤ I·I₃`,

whose only use of the equality is the middle step `c·(A·I)·I₂ = c·I₁·I₂`.  That step needs the
equality only in the direction `c·I₂·(A·I) ≤ c·I₂·I₁`, which follows from `A·I ≤ I₁` as soon as
`c·I₂ ≥ 0`.  Hence **the equality in `hloc` may be weakened to `≥` at the cost of `0 ≤ c` and
`0 ≤ I₂`, both of which hold at the call site** (`c = d/σ`, and `I₂ = ∫ D` for a nonnegative
needle density `D`).  This lemma is that claim, machine-checked. -/
theorem needle_masses_contradiction_ge {I I₁ I₂ I₃ A c : ℝ} (hIpos : 0 < I)
    (hc : 0 ≤ c) (hI₂ : 0 ≤ I₂) (hge : A * I ≤ I₁) (hlt : I₃ < c * A * I₂)
    (hiso : c * (I₁ * I₂) ≤ I * I₃) : False := by
  have hstep : I * I₃ < I * (c * A * I₂) := mul_lt_mul_of_pos_left hlt hIpos
  have hmono : c * I₂ * (A * I) ≤ c * I₂ * I₁ :=
    mul_le_mul_of_nonneg_left hge (mul_nonneg hc hI₂)
  have hrw : I * (c * A * I₂) = c * I₂ * (A * I) := by ring
  have hrw2 : c * I₂ * I₁ = c * (I₁ * I₂) := by ring
  linarith

/-- **The side condition `0 ≤ c` of `Arlib.needle_masses_contradiction_ge` is itself derivable.**

At the call site `I₃` is an integral of a nonnegative density, so `0 ≤ I₃`; together with
`I₃ < c·A·I₂`, `0 < A` and `0 ≤ I₂` this forces `0 < c`.  So weakening `hloc`'s equality to `≥`
costs **only** `0 ≤ I₂` and `0 ≤ I₃`, both immediate from `D ≥ 0`. -/
theorem needle_masses_contradiction_ge' {I I₁ I₂ I₃ A c : ℝ} (hIpos : 0 < I)
    (hA : 0 < A) (hI₂ : 0 ≤ I₂) (hI₃ : 0 ≤ I₃) (hge : A * I ≤ I₁)
    (hlt : I₃ < c * A * I₂) (hiso : c * (I₁ * I₂) ≤ I * I₃) : False := by
  have hc : 0 ≤ c := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_nonneg hA.le hI₂]
  exact needle_masses_contradiction_ge hIpos hc hI₂ hge hlt hiso

end RouteA

/-! ### The assembly: `hloc` from the localization stack's needle -/

section Assembly

variable {n : ℕ}

/-- The rescaling of `Arlib.integral_needle_rescale'` with `c = ‖v‖`: the arclength
reparameterisation. -/
theorem integral_needle_rescale_norm {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    (W : ℝ → ℝ) (b : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ s : ℝ, W (‖v‖⁻¹ * s) * u (needleMap b (‖v‖⁻¹ • v) s))
      = ‖v‖ * ∫ t : ℝ, W t * u (needleMap b v t) := by
  have hc : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hve : ‖v‖ • (‖v‖⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [integral_needle_rescale' hc W b (‖v‖⁻¹ • v) u, hve]

/-- Multiplying a profile by the indicator of a set is the same as restricting the profile to the
preimage of that set along the needle. -/
theorem profile_mul_indicator_needle {W : ℝ → ℝ} {b v : EuclideanSpace ℝ (Fin n)}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    (fun t => W t * S.indicator h (needleMap b v t))
      = (needleMap b v ⁻¹' S).indicator (fun t => W t * h (needleMap b v t)) := by
  funext t
  by_cases hm : needleMap b v t ∈ S
  · rw [Set.indicator_of_mem hm,
      Set.indicator_of_mem (show t ∈ needleMap b v ⁻¹' S from hm)]
  · rw [Set.indicator_of_notMem hm,
      Set.indicator_of_notMem (show t ∉ needleMap b v ⁻¹' S from hm), mul_zero]

/-- The needle mass of `1_S · h` is integrable whenever the needle mass of `h` is. -/
theorem integrable_profile_mul_indicator_needle {W : ℝ → ℝ} {b v : EuclideanSpace ℝ (Fin n)}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hWint : Integrable (fun t => W t * h (needleMap b v t)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    Integrable (fun t => W t * S.indicator h (needleMap b v t)) := by
  rw [profile_mul_indicator_needle S]
  exact hWint.indicator ((continuous_needleMap b v).measurable hS)

/-- The support of the rescaled profile `s ↦ W (c⁻¹ * s)` is `Icc 0 c`. -/
theorem rescaled_profile_support {c : ℝ} (hc : 0 < c) {W : ℝ → ℝ}
    (hWsupp : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) :
    ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) c → W (c⁻¹ * s) = 0 := by
  intro s hs
  refine hWsupp _ fun hmem => hs ⟨?_, ?_⟩
  · have h1 : 0 ≤ c * (c⁻¹ * s) := mul_nonneg hc.le hmem.1
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h1
  · have h2 : c * (c⁻¹ * s) ≤ c * 1 := mul_le_mul_of_nonneg_left hmem.2 hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, mul_one] at h2

/-- **Gaps 1 and 2 combined at the level of the profile.**

From the localization stack's profile `W` — nonnegative, with `W ^ (1/(n−1))` concave on the
*open* unit interval — the arclength-reparameterised, endpoint-extended profile `L` is produced:
nonnegative everywhere, concave on the *closed* interval `Icc 0 c`, with `L ^ (n−1)` equal to the
rescaled `W` on `Ioo 0 c` and identically `0` off `Icc 0 c`.  The `(n−1)`-st power recovers `W`
exactly because `W ≥ 0`, and `n ≥ 2` makes `n − 1 ≠ 0`. -/
theorem exists_concave_profile_of_localization (hn : 2 ≤ n) {c : ℝ} (hc : 0 < c)
    {W : ℝ → ℝ} (hW0 : ∀ t, 0 ≤ W t)
    (hWconc : ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1)))) :
    ∃ L : ℝ → ℝ, (∀ t, 0 ≤ L t) ∧ ConcaveOn ℝ (Set.Icc (0 : ℝ) c) L ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) c, L s ^ (n - 1) = W (c⁻¹ * s)) ∧
      (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) c → L s ^ (n - 1) = 0) := by
  have hnm : n - 1 ≠ 0 := by omega
  have hcast : (1 : ℝ) / ((n : ℝ) - 1) = (((n - 1 : ℕ) : ℝ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, one_div]
  have hmemIoo : ∀ s ∈ Set.Ioo (0 : ℝ) c, c⁻¹ * s ∈ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    refine ⟨mul_pos (inv_pos.mpr hc) hs.1, ?_⟩
    have hlt := mul_lt_mul_of_pos_left hs.2 (inv_pos.mpr hc)
    rwa [inv_mul_cancel₀ hc.ne'] at hlt
  have hVconc : ConcaveOn ℝ (Set.Ioo (0 : ℝ) c)
      (fun s => W (c⁻¹ * s) ^ (1 / ((n : ℝ) - 1))) := by
    refine ⟨convex_Ioo 0 c, ?_⟩
    intro x hx y hy a bb ha hbb hab
    have hkey := hWconc.2 (hmemIoo x hx) (hmemIoo y hy) ha hbb hab
    simp only [smul_eq_mul] at hkey ⊢
    have hlin : c⁻¹ * (a * x + bb * y) = a * (c⁻¹ * x) + bb * (c⁻¹ * y) := by ring
    rw [hlin]
    exact hkey
  have hVnn : ∀ s ∈ Set.Ioo (0 : ℝ) c, 0 ≤ W (c⁻¹ * s) ^ (1 / ((n : ℝ) - 1)) :=
    fun s _ => Real.rpow_nonneg (hW0 _) _
  refine ⟨fun s => if s ∈ Set.Ioo (0 : ℝ) c then W (c⁻¹ * s) ^ (1 / ((n : ℝ) - 1)) else 0,
    nonneg_extendZero_of_nonneg hVnn, concaveOn_Icc_extendZero hVconc hVnn, ?_, ?_⟩
  · intro s hs
    simp only [if_pos hs, hcast]
    exact Real.rpow_inv_natCast_pow (hW0 _) hnm
  · intro s hs
    have hs' : s ∉ Set.Ioo (0 : ℝ) c := fun hmem => hs (Set.Ioo_subset_Icc_self hmem)
    simp only [if_neg hs']
    exact zero_pow hnm

/-- **The three shape gaps closed: `hloc` from the localization stack's needle.**

The hypothesis `hLoc` is the Localization Lemma *as the stack of this repository delivers it*,
applied to `g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`:

* the direction `v` is **not** normalised (`v ≠ 0` only),
* the profile `W` is concave *after* taking the `(n−1)`-st root, and only on the **open**
  interval `Ioo 0 1`,
* the two conclusions are **full-line** integrals `∫ t : ℝ`.

The conclusion is `hloc` exactly as
`Arlib.gaussianRestricted_isoperimetry_concave` prints it: arclength-parameterised (`‖e‖ = 1`),
concave on a **closed** interval `Icc α β`, with **interval and set** integrals.

See the module docstring for the provenance of every clause of `hLoc`. -/
theorem hloc_of_localization (hn : 2 ≤ n) {σ d : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hLoc : ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
        v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
        ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
        Integrable (fun t => W t * h (needleMap b v t)) ∧
        (∫ t : ℝ, W t * (S₁.indicator h (needleMap b v t) - A * h (needleMap b v t))) = 0 ∧
        0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
              - S₃.indicator h (needleMap b v t))) :
    ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (l : ℝ → ℝ) (α β : ℝ),
        ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ l t) ∧
        ConcaveOn ℝ (Set.Icc α β) l ∧
        IntervalIntegrable
          (fun t => l t ^ (n - 1) * h (needleMap p e t)) volume α β ∧
        (∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          = A * ∫ t in α..β, l t ^ (n - 1) * h (needleMap p e t) ∧
        (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t) := by
  intro A hA h1 h2
  obtain ⟨b, v, W, hv0, hW0, hWsupp, hWconc, hWint, hI₁, hI₂⟩ := hLoc A hA h1 h2
  have hc : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨L, hLnn, hLconc, hLpow, hLoff⟩ := exists_concave_profile_of_localization hn hc hW0 hWconc
  have hVsupp := rescaled_profile_support hc hWsupp
  have he1 : ‖(‖v‖⁻¹ • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
  -- gap 3 + gap 2, for the three set integrals
  have hconv : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      (∫ s in needleMap b (‖v‖⁻¹ • v) ⁻¹' S ∩ Set.Icc (0 : ℝ) ‖v‖,
          L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s))
        = ‖v‖ * ∫ t : ℝ, W t * S.indicator h (needleMap b v t) := by
    intro S hS
    rw [setIntegral_needle_of_profile (V := fun s => W (‖v‖⁻¹ * s))
      (L := fun s => L s ^ (n - 1)) hVsupp hLpow b (‖v‖⁻¹ • v) hS h]
    exact integral_needle_rescale_norm hv0 W b (S.indicator h)
  -- gap 3 + gap 2, for the interval integral
  have hconv0 : (∫ s in (0 : ℝ)..‖v‖, L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s))
      = ‖v‖ * ∫ t : ℝ, W t * h (needleMap b v t) := by
    rw [intervalIntegral_needle_of_profile hc.le (V := fun s => W (‖v‖⁻¹ * s))
      (L := fun s => L s ^ (n - 1)) hVsupp hLpow b (‖v‖⁻¹ • v) h]
    exact integral_needle_rescale_norm hv0 W b h
  -- splitting the two localization conclusions into their three needle masses
  have hsplit1 : (∫ t : ℝ, W t * S₁.indicator h (needleMap b v t))
      = A * ∫ t : ℝ, W t * h (needleMap b v t) := by
    have heq : (fun t => W t * (S₁.indicator h (needleMap b v t) - A * h (needleMap b v t)))
        = fun t => W t * S₁.indicator h (needleMap b v t)
          - A * (W t * h (needleMap b v t)) := by
      funext t; ring
    rw [heq, integral_sub (integrable_profile_mul_indicator_needle hWint hS₁)
      (hWint.const_mul A), integral_const_mul] at hI₁
    linarith
  have hsplit2 : (∫ t : ℝ, W t * S₃.indicator h (needleMap b v t))
      < d / σ * A * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t) := by
    have heq : (fun t => W t * (d / σ * A * S₂.indicator h (needleMap b v t)
          - S₃.indicator h (needleMap b v t)))
        = fun t => d / σ * A * (W t * S₂.indicator h (needleMap b v t))
          - W t * S₃.indicator h (needleMap b v t) := by
      funext t; ring
    rw [heq, integral_sub ((integrable_profile_mul_indicator_needle hWint hS₂).const_mul _)
      (integrable_profile_mul_indicator_needle hWint hS₃), integral_const_mul] at hI₂
    linarith
  -- integrability of the arclength-parameterised needle density
  have hVint : Integrable
      (fun s => W (‖v‖⁻¹ * s) * h (needleMap b (‖v‖⁻¹ • v) s)) :=
    integrable_needle_rescale hc hWint
  have hLint : IntervalIntegrable
      (fun s => L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s)) volume 0 ‖v‖ := by
    refine (hVint.congr ?_).intervalIntegrable
    refine ae_eq_of_forall_ne_pair (x := 0) (y := ‖v‖) fun t ht0 htc => ?_
    by_cases htI : t ∈ Set.Icc (0 : ℝ) ‖v‖
    · rw [hLpow t ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htc⟩]
    · rw [hVsupp t htI, hLoff t htI]
  refine ⟨b, ‖v‖⁻¹ • v, L, 0, ‖v‖, he1, hc.le, fun t _ => hLnn t, hLconc, hLint, ?_, ?_⟩
  · rw [hconv S₁ hS₁, hconv0, hsplit1]; ring
  · rw [hconv S₃ hS₃, hconv S₂ hS₂]
    have hstep := mul_lt_mul_of_pos_left hsplit2 hc
    have hrw : ‖v‖ * (d / σ * A * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t))
        = d / σ * A * (‖v‖ * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t)) := by ring
    linarith

/-- **The `≥`-form of `Arlib.hloc_of_localization`, ready for route (a).**

`Arlib.needle_masses_contradiction_ge` shows the consumer's closing contradiction needs only
`A·I ≤ I₁`, not the equality.  This is the corresponding shape bridge: the three gaps are closed
for a binder whose first antecedent is `A·∫h ≤ ∫_{S₁}h` and whose first conclusion is
`A·I ≤ I₁`.

The point of the weakening is that the `≥`-form binder is dischargeable from the *continuous*
localization theorems whenever `S₁`, `S₂` are open and `S₃` is closed, with **no** approximation
slack: pick a continuous `0 ≤ φ ≤ 1_{S₁}` with `∫φh = A∫h` *exactly* (scale a good enough
minorant down; possible because `A∫h ≤ ∫_{S₁}h`), a continuous `ψ ≤ 1_{S₂}` and a continuous
`χ ≥ 1_{S₃}` close enough that `∫((d/σ)Aψ − χ)h > 0`.  The single needle the equality-form
localization returns for `g₁ = (φ − A)h`, `g₂ = ((d/σ)Aψ − χ)h` then satisfies
`I₁ ≥ ∫Wφh∘γ = A·I` and `(d/σ)A·I₂ − I₃ ≥ ∫Wg₂∘γ > 0`.  The needle does **not** move with the
approximation index, because the same `A` is used throughout.  That argument is *not* formalised
here — it belongs to residual (C) — but it is the reason this shape is the useful one. -/
theorem hloc_ge_of_localization_ge (hn : 2 ≤ n) {σ d : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hLoc : ∀ A : ℝ, 0 < A →
      A * (∫ x, h x) ≤ ∫ x in S₁, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
        v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
        ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
        Integrable (fun t => W t * h (needleMap b v t)) ∧
        A * (∫ t : ℝ, W t * h (needleMap b v t))
          ≤ ∫ t : ℝ, W t * S₁.indicator h (needleMap b v t) ∧
        0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
              - S₃.indicator h (needleMap b v t))) :
    ∀ A : ℝ, 0 < A →
      A * (∫ x, h x) ≤ ∫ x in S₁, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (l : ℝ → ℝ) (α β : ℝ),
        ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ l t) ∧
        ConcaveOn ℝ (Set.Icc α β) l ∧
        IntervalIntegrable
          (fun t => l t ^ (n - 1) * h (needleMap p e t)) volume α β ∧
        A * (∫ t in α..β, l t ^ (n - 1) * h (needleMap p e t))
          ≤ ∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t) ∧
        (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t) := by
  intro A hA h1 h2
  obtain ⟨b, v, W, hv0, hW0, hWsupp, hWconc, hWint, hI₁, hI₂⟩ := hLoc A hA h1 h2
  have hc : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨L, hLnn, hLconc, hLpow, hLoff⟩ := exists_concave_profile_of_localization hn hc hW0 hWconc
  have hVsupp := rescaled_profile_support hc hWsupp
  have he1 : ‖(‖v‖⁻¹ • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
  have hconv : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      (∫ s in needleMap b (‖v‖⁻¹ • v) ⁻¹' S ∩ Set.Icc (0 : ℝ) ‖v‖,
          L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s))
        = ‖v‖ * ∫ t : ℝ, W t * S.indicator h (needleMap b v t) := by
    intro S hS
    rw [setIntegral_needle_of_profile (V := fun s => W (‖v‖⁻¹ * s))
      (L := fun s => L s ^ (n - 1)) hVsupp hLpow b (‖v‖⁻¹ • v) hS h]
    exact integral_needle_rescale_norm hv0 W b (S.indicator h)
  have hconv0 : (∫ s in (0 : ℝ)..‖v‖, L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s))
      = ‖v‖ * ∫ t : ℝ, W t * h (needleMap b v t) := by
    rw [intervalIntegral_needle_of_profile hc.le (V := fun s => W (‖v‖⁻¹ * s))
      (L := fun s => L s ^ (n - 1)) hVsupp hLpow b (‖v‖⁻¹ • v) h]
    exact integral_needle_rescale_norm hv0 W b h
  have hsplit2 : (∫ t : ℝ, W t * S₃.indicator h (needleMap b v t))
      < d / σ * A * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t) := by
    have heq : (fun t => W t * (d / σ * A * S₂.indicator h (needleMap b v t)
          - S₃.indicator h (needleMap b v t)))
        = fun t => d / σ * A * (W t * S₂.indicator h (needleMap b v t))
          - W t * S₃.indicator h (needleMap b v t) := by
      funext t; ring
    rw [heq, integral_sub ((integrable_profile_mul_indicator_needle hWint hS₂).const_mul _)
      (integrable_profile_mul_indicator_needle hWint hS₃), integral_const_mul] at hI₂
    linarith
  have hVint : Integrable
      (fun s => W (‖v‖⁻¹ * s) * h (needleMap b (‖v‖⁻¹ • v) s)) :=
    integrable_needle_rescale hc hWint
  have hLint : IntervalIntegrable
      (fun s => L s ^ (n - 1) * h (needleMap b (‖v‖⁻¹ • v) s)) volume 0 ‖v‖ := by
    refine (hVint.congr ?_).intervalIntegrable
    refine ae_eq_of_forall_ne_pair (x := 0) (y := ‖v‖) fun t ht0 htc => ?_
    by_cases htI : t ∈ Set.Icc (0 : ℝ) ‖v‖
    · rw [hLpow t ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htc⟩]
    · rw [hVsupp t htI, hLoff t htI]
  refine ⟨b, ‖v‖⁻¹ • v, L, 0, ‖v‖, he1, hc.le, fun t _ => hLnn t, hLconc, hLint, ?_, ?_⟩
  · rw [hconv S₁ hS₁, hconv0]
    have hstep := mul_le_mul_of_nonneg_left hI₁ hc.le
    have hrw : ‖v‖ * (A * ∫ t : ℝ, W t * h (needleMap b v t))
        = A * (‖v‖ * ∫ t : ℝ, W t * h (needleMap b v t)) := by ring
    linarith
  · rw [hconv S₃ hS₃, hconv S₂ hS₂]
    have hstep := mul_lt_mul_of_pos_left hsplit2 hc
    have hrw : ‖v‖ * (d / σ * A * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t))
        = d / σ * A * (‖v‖ * ∫ t : ℝ, W t * S₂.indicator h (needleMap b v t)) := by ring
    linarith

end Assembly

/-! ### The payoff: `thm:iso` with no one-dimensional residual -/

section Payoff

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` with no one-dimensional residual binder at all.**

`Arlib.gaussianRestricted_isoperimetry_concave` with its single residual `hloc` supplied by
`Arlib.hloc_of_localization`.  What is left is `hLoc`: the Localization Lemma applied to
`g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`, **in the raw shape the localization
stack of this repository delivers** — un-normalised direction, profile concave only after a root
and only on the open interval, full-line integrals.  Every gap between that shape and the shape
`thm:iso` consumes is closed here.

Requires `2 ≤ n`; see the module docstring. -/
theorem gaussianRestricted_isoperimetry_of_localization (hn : 2 ≤ n) {σ d : ℝ} (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v)
    (hLoc : ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
        v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
        ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
        Integrable (fun t => W t * h (needleMap b v t)) ∧
        (∫ t : ℝ, W t * (S₁.indicator h (needleMap b v t) - A * h (needleMap b v t))) = 0 ∧
        0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
              - S₃.indicator h (needleMap b v t))) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x :=
  gaussianRestricted_isoperimetry_concave (by omega) hσ hf₀ hfc hh hpart hS₁ hS₂ hS₃ hmass hsep
    (hloc_of_localization hn hS₁ hS₂ hS₃ hLoc)

end Payoff

/-! ### Every witness for `hloc` is necessarily vacuous -/

section Vacuity

variable {n : ℕ}

/-- **`hloc`'s antecedent is refuted by `thm:iso`'s own conclusion.**

`hloc` (and `hLoc`) is a *proof-by-contradiction* hypothesis: its antecedent asserts the failure of
the very conclusion the theorem establishes.  Concretely, `∫_{S₁}h = A·∫h` and
`∫_{S₃}h < (d/σ)A·∫_{S₂}h`, multiplied by `∫h > 0`, give

  `(∫h)(∫_{S₃}h) < (d/σ)(∫_{S₁}h)(∫_{S₂}h)`,

the exact negation of the conclusion.

**Consequence for `AUDIT.md` check 4.**  For *any* data satisfying all the other hypotheses of
`Arlib.gaussianRestricted_isoperimetry_of_localization` — in particular any data for which the
theorem's conclusion holds — the antecedent of `hLoc` is **false**.  So a non-vacuity witness whose
`hloc` antecedent is genuinely *satisfied* does not exist, and the preference stated in `AUDIT.md`
is unachievable here for a principled reason, not for lack of effort.  This lemma is that
statement, machine-checked. -/
theorem hloc_antecedent_false_of_isoperimetry {σ d A : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hmass : 0 < ∫ x, h x)
    (hconc : d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x)
    (h1 : (∫ x in S₁, h x) = A * ∫ x, h x)
    (h2 : (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x) : False := by
  have hstep : (∫ x, h x) * ∫ x in S₃, h x < (∫ x, h x) * (d / σ * A * ∫ x in S₂, h x) :=
    mul_lt_mul_of_pos_left h2 hmass
  have hrw : (∫ x, h x) * (d / σ * A * ∫ x in S₂, h x)
      = d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by rw [h1]; ring
  linarith

/-- **Non-vacuity witness for `Arlib.gaussianRestricted_isoperimetry_of_localization`.**

Every hypothesis, `hLoc` included, is satisfiable simultaneously, at parameters where the
conclusion is a *strictly positive* lower bound.  The data is that of
`Arlib.gaussianRestricted_isoperimetry_concave_witness`; `hLoc` is discharged by
`Arlib.hloc_antecedent_false_of_isoperimetry` from the conclusion that
`Arlib.gaussianRestricted_isoperimetry_concave` already delivers for that data.

The witness is **vacuous in `hLoc`, and provably necessarily so** — see
`Arlib.hloc_antecedent_false_of_isoperimetry`. -/
theorem gaussianRestricted_isoperimetry_of_localization_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      (∀ A : ℝ, 0 < A →
        (∫ x in S₁, h x) = A * ∫ x, h x →
        (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
        ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
          v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
          ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
          Integrable (fun t => W t * h (needleMap b v t)) ∧
          (∫ t : ℝ, W t * (S₁.indicator h (needleMap b v t) - A * h (needleMap b v t))) = 0 ∧
          0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
                - S₃.indicator h (needleMap b v t))) ∧
      0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
  obtain ⟨f, h, S₁, S₂, S₃, σ, d, hσ, hd, hf₀, hfc, hh, hpart, hS₁, hS₂, hS₃, hmass, hsep,
    hloc, hpos⟩ := gaussianRestricted_isoperimetry_concave_witness (n := n) (by omega)
  have hconc := gaussianRestricted_isoperimetry_concave (by omega) hσ hf₀ hfc hh hpart
    hS₁ hS₂ hS₃ hmass hsep hloc
  exact ⟨f, h, S₁, S₂, S₃, σ, d, hσ, hd, hf₀, hfc, hh, hpart, hS₁, hS₂, hS₃, hmass, hsep,
    fun A hA h1 h2 =>
      absurd h2 (fun h2' => hloc_antecedent_false_of_isoperimetry hmass hconc h1 h2'), hpos⟩

end Vacuity

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.concaveOn_Ioo_left_endpoint_le
#print axioms Arlib.concaveOn_Ioo_right_endpoint_le
#print axioms Arlib.concaveOn_Icc_extendZero
#print axioms Arlib.integral_needle_rescale
#print axioms Arlib.setIntegral_needle_of_profile
#print axioms Arlib.intervalIntegral_needle_of_profile
#print axioms Arlib.exists_concave_profile_of_localization
#print axioms Arlib.needle_masses_contradiction_ge
#print axioms Arlib.needle_masses_contradiction_ge'
#print axioms Arlib.hloc_antecedent_false_of_isoperimetry
#print axioms Arlib.hloc_of_localization
#print axioms Arlib.hloc_ge_of_localization_ge
#print axioms Arlib.gaussianRestricted_isoperimetry_of_localization
#print axioms Arlib.gaussianRestricted_isoperimetry_of_localization_witness
