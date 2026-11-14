/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Convex.Measure
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationLSC
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.WeightedIsoBook

/-!
# The weighted cross-ratio isoperimetry for a **lower semicontinuous** weight

`ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` is the `hIso` binder of
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge` (`HitAndRunConductance.lean`) with one
clause added — `LowerSemicontinuous h` — and nothing else changed.
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_transfer_of_localization` is Theorem 4.2 with that binder
**discharged**: `hIso` — the paper's Theorem 2.1 — no longer appears, and the residual binders are

* `hLem41` — Lemma 4.1, owned elsewhere in this repository;
* `hloc` — the Localization Lemma for **continuous** integrands on the body `K`, delivering a
  needle *inside* `K` with a log-concave profile (`α ≤ β`, `needleMap p e '' [α,β] ⊆ K`,
  `LogConcaveOn (Icc α β) D`), `g₁`'s needle mass zero and `g₂`'s needle mass positive;
* `htrans` — the **chord transfer**: for a **continuous** weight, the chord bound assumed at
  pairs of `T₁ × T₂` holds up to an arbitrarily small additive `ε` at pairs lying in small
  neighbourhoods of **nonempty** compact subsets of `T₁ ∩ interior K` and `T₂ ∩ interior K`.
  Two clauses are load-bearing rather than decorative, and dropping either makes the binder
  *false*, hence every theorem below vacuous.  Nonemptiness: `Metric.infDist x ∅ = 0`, so without
  it the binder quantifies over every point of the space, including points outside `K` where
  `crossRatioDist` is negative.  Continuity of the weight: see
  `ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_continuous_transfer_of_localization`, whose docstring carries
  an explicit refutation of the merely-lower-semicontinuous version in `K = [0,1]²` — lower
  semicontinuity controls a weight from below, and the transfer needs control from above.
  With both clauses the binder is satisfiable: the zero weight meets the chord hypothesis and the
  transfer conclusion for every body and every disjoint pair
  (`ArlibCommunity.Foundations.Convex.chord_bound_zero`, `ArlibCommunity.Foundations.Convex.exists_transfer_radius_zero`).

Everything else is proved here: the inner regularisation, the mollification, the normalisation,
the constant bookkeeping, the passage from the needle back to a contradiction, and the
instantiation at the paper's own weight.

## Why the weight is lower semicontinuous and the transfer binder is not

A lower semicontinuous weight is what the conductance call site produces, and it is admitted
here in two independent places — the localisation and the transfer — by two *different*
mechanisms, because only one of them tolerates it as a hypothesis.

**In the localisation, semicontinuity is admitted directly.**  Lee's book states the Localization
Lemma for **lower semicontinuous** integrands
(`optimizationbook/ball_walk.tex:1076`, Kannan–Lovász–Simonovits), and its proof opens by
reducing to the continuous case: the integrands are limits of monotone increasing sequences of
continuous functions, and both a strict inequality `∫ g > 0` and the conclusion survive the
passage.  That reduction is already formalised in this repository —
`ArlibCommunity.Foundations.Convex.exists_continuous_le_setIntegral_pos` (`LocalizationLSC.lean`), built on the Lipschitz
inf-convolution minorants — and this file uses it directly: the second integrand is lower
semicontinuous, a continuous minorant with positive `K`-integral is extracted, `hloc` is called on
the *minorant*, and the needle conclusion is inherited by the original because the profile `D` is
nonnegative.  Only `g₂` needs this; `g₁` is continuous outright, which matters, because the
equality slot `∫_K g₁ = 0` is *not* preserved by monotone approximation
(`ArlibCommunity.Foundations.Convex.exists_continuous_setIntegral_eq_zero` degrades it to an `η`-slack).

**In the transfer, semicontinuity is *not* admitted — it is approximated away.**  The `htrans`
binder quantifies over continuous weights only, and the lower semicontinuous case is derived:
the weight is truncated at `1/3` (invisible on `K`) and replaced by its Lipschitz inf-convolution
minorants `ArlibCommunity.Foundations.Convex.lipschitzMinorant`, each continuous, nonnegative, `≤ 1/3` and below the weight,
so each inherits the chord bound; the conclusion `A·∫_K h ≤ vol(S₃)` is a closed inequality, and
`ArlibCommunity.Foundations.Convex.tendsto_setIntegral_lipschitzMinorant` passes to the limit.  This is not a stylistic
choice: quantifying `htrans` over lower semicontinuous weights makes it false, with a two-point
counterexample recorded at
`ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_continuous_transfer_of_localization`.

The gain is not cosmetic: it is exactly what the conductance call site needs.  Theorem 4.2
instantiates `hIso` at `g x = stepRadius K (63/64) x / (48·D·√n)`, which `ArlibCommunity.Foundations.MarkovChainTheory.stepRadius_concaveOn`
makes concave on `K`, hence continuous only on `interior K` (`ArlibCommunity.Foundations.MarkovChainTheory.continuousOn_stepRadius`) — a
concave function on a closed body may jump at the boundary.  `1_{interior K}·g` is lower
semicontinuous (`ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_continuousOn`), lies below `g`, and agrees
with `g` almost everywhere because the frontier of a convex body is null; so it inherits the chord
bound and the `1/3` bound and keeps Lemma 3.4's average.  That is the *entire* difference between
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_tv_lsc` and the original.

## What the mollified route buys, and where it still stops

The previous file on this route (`ArlibCommunity/Foundations/Convex/CrossRatioIsoperimetry/Analysis/WeightedIsoBook.lean`) stops at two walls.  The
first is gone; the second is reshaped, not removed.

**Wall 1 — the measurable-weight slot — is gone.**
`ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_transfer_of_localization` hands the Localization Lemma the pair

    g₁ = c·f_T(·,C₁) − A',    g₂ = A'·w − (1 − c·f_T(·,C₁) − f_T(·,C₂)),

and **neither integrand contains an indicator**: `1_K` never appears, because the equality slot is
normalised by a *constant* `A'` and the localisation runs on the body `K` itself; `1_{T₁}` and
`1_{S₃}` never appear, because the mollifier replaces them.  `g₁` is globally continuous and `g₂`
is lower semicontinuous, so the fat-Cantor obstruction — "no continuous minorant recovers `∫_K g`
for measurable `g`" — is never met: nothing measurable is ever approximated.

Two devices make the bookkeeping exact rather than asymptotic, and both matter:

* the mass equation is arranged **by construction** — `c := vol C₁ / ∫_K f_T(·,C₁) ∈ (0,1]`, so
  `∫_K c·f_T(·,C₁) = vol C₁ = A'·vol K` holds identically.  No convergence of
  `vol(N(C₁,1/T))` to `vol C₁` is needed, hence no limit of needles is taken, and `A' ≤ A ≤ 1/2`
  is immediate rather than delicate;
* the third weight `1 − c·f₁ − f₂` is *not* asked to be a pointwise minorant of `1_{S₃}` (it is
  not one, for `c < 1`); only its integral is used, and `∫_K(1 − c·f₁ − f₂) ≤ vol K − vol C₁ −
  vol C₂` is exact.

**Wall 2 — the chord transfer — is not removed, only reshaped.**  Two things stop it from being
asked in the naive form, and both are about `crossRatioDist`, not about `h`.

*It cannot be exact.*  `d_K(u,v)` is strictly smaller than `d_K(u',v')` at some nearby pairs, so
the conclusion at the enlarged supports is strictly stronger than the hypothesis at `T₁ × T₂`;
continuity of `h` closes an `ε`, never a strict gap.

*It cannot be asked at sets touching the boundary, at any fixed radius.*  In `K = [0,1]²` put
`u = (2/5, ζ)`, `v = (1/2, ζ)` and `v' = (1/2, ρ)` with `0 < ζ ≪ ρ`.  The chord through `u, v`
is the whole horizontal segment at height `ζ`, with chord parameters `a = −4`, `b = 6`, so
`d_K(u,v) = (b−a)/((−a)(b−1)) = 1/2` and the bound `h ≤ 1/6` bites along that entire segment.
The chord through `u, v'` instead dives out of the bottom edge at `a = −ζ/(ρ−ζ)`, giving
`d_K(u,v') = (6 + ζ/(ρ−ζ))·(ρ−ζ)/(5ζ) → ∞`; at `ζ/ρ` small enough `min 1 (d_K(u,v'))/3 = 1/3`
and the hypothesis at `(u,v')` carries no information at all.  So a perturbation of size `ρ−ζ`
moves `min 1 d_K` from `1/2` to its maximum — and `ρ−ζ` may be arbitrarily large compared with
the depth `ζ` of the points.  `crossRatioDist` therefore admits **no** modulus of continuity
uniform in the distance to `∂K`, and a transfer radius has to be chosen *after*, and small
relative to, that distance.

That is exactly the shape of `htrans`: compacts **inside the interior** first, radius `ρ` after
them.  Both restrictions are supplied here: `ArlibCommunity.Foundations.Convex.exists_isCompact_subset_inter_interior` lands
the compacts inside `interior K` (the frontier of a convex body is null, so nothing is lost in
measure), and `ArlibCommunity.Foundations.Convex.exists_sep_of_disjoint_isCompact` plus
`IsCompact.exists_thickening_subset_open` keep the neighbourhoods disjoint and inside `K`.

The `ε` is affordable because the whole argument is a contradiction with a *strictly positive*
slack `e₀ = A·∫_K h − vol((K∖T₁)∖T₂)`, and the file spends it explicitly: the weight actually
carried to the needle is the trimmed

    w = min (1/3) (max 0 (h − 3ε)),

which satisfies the chord bound at the neighbourhoods **exactly** (because
`h ≤ min 1 d_K/3 + ε` gives `h − 3ε ≤ min 1 d_K/3 − 2ε`), is globally bounded by `1/3`
(needed: `ArlibCommunity.Foundations.Convex.integrableOn_weight_mul` wants a weight in `[0,1]` on all of `ℝ`, and `h ≤ 1/3`
only holds on `K`), is lower semicontinuous whenever `h` is, and loses only `3ε·vol K` in the
ambient integral.  The three losses — `η` from the inner regularisation, `3ε·vol K` from the
trimming, and the gap between `A'` and `A` — are budgeted against `e₀` as `η = e₀/8`,
`ε = e₀/(6·vol K)`.

## What is *not* here

* **`htrans` is not discharged.**  It is a statement about `crossRatioDist`, not about `h`: it
  needs the chord endpoints `chordLow`/`chordHigh` to vary continuously (indeed with a uniform
  modulus) over pairs of points at a positive distance from `∂K` and from each other.  This
  repository has no continuity result for `chordLow`/`chordHigh` at all.  The quantitative form
  is available by an elementary cone argument — if `B(u,σ) ⊆ K` and `B(v,σ) ⊆ K` then
  `conv({q} ∪ B(u,σ)) ⊆ K` pins the exit point of any nearby line to within `O(ρ·ℓ/σ)` — but it
  is a self-contained convex-geometry development, not a corollary of anything present.
* **`hloc` is not discharged.**  `ArlibCommunity.Foundations.Convex.exists_needle_of_compact_convex`
  (`LocalizationMeasurable.lean`) proves the Localization Lemma for continuous integrands
  from a compact convex body, but its conclusion **drops the clause that the needle lies in the
  body**, which `ArlibCommunity.Foundations.Convex.needle_iso_of_chord_weight` requires.  The clause is recoverable — the
  needle is the axis of `⋂ k, D k ⊆ K`, and `ArlibCommunity.Foundations.Convex.exists_mem_iInter_height` produces a point of
  `⋂ k, D k` at every height in `[0,1]` — but recovering it means replaying
  `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear` and its transport to
  `EuclideanSpace` with the extra conclusion.  `hloc` also asks for `D` log-concave on `Icc α β`,
  where the stack delivers `ConcaveOn ℝ (Ioo 0 1) (W ^ (1/m))`.

## The binder checks

Nothing here is eyeballed against the source.  `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_hIso_copy`
feeds this file's copy of the `hIso` binder *verbatim* to
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge`, so the copy is the real binder;
`ArlibCommunity.Foundations.Convex.hIso_continuous_of_hIso` and `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous_of_hIso` feed that same copy
to the two restricted statements, so each is that binder with exactly one clause inserted; and
`ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_hIso_copy_via_lsc` reproves the *original* theorem's statement
through the 375-line replay, so the replay neither weakened the conclusion nor strengthened any
other hypothesis.

## Honesty

No `sorry`, no `axiom`, no `structure`, no `class`, no `native_decide`.  Every declaration is a
`theorem`; there is no `def` in this file.  The theorems carry `htrans`, `hloc` and `hLem41` as
explicit binders and claim nothing beyond them.
-/

open ArlibCommunity.Foundations.Convex

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

open MeasureTheory Set

open scoped NNReal ENNReal

/-! ### Two measure-theoretic preliminaries -/

section Prelim

variable {E : Type*} [MetricSpace E]

/-- **Disjoint nonempty compacts are uniformly separated.**  This is the input of
`ArlibCommunity.Foundations.Convex.bookMollifier_disjoint`, and it is why the two sets have to be inner-regularised by
compacts before they are mollified. -/
theorem exists_sep_of_disjoint_isCompact {C₁ C₂ : Set E}
    (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hdisj : Disjoint C₁ C₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ C₁, ∀ v ∈ C₂, δ ≤ dist u v := by
  obtain ⟨u₀, hu₀, hmin⟩ :=
    h₁.exists_isMinOn hne₁ (Metric.continuous_infDist_pt C₂).continuousOn
  refine ⟨Metric.infDist u₀ C₂, ?_, fun u hu v hv => ?_⟩
  · refine (h₂.isClosed.notMem_iff_infDist_pos hne₂).mp ?_
    exact fun hmem => Set.disjoint_left.mp hdisj hu₀ hmem
  · exact le_trans (hmin hu) (Metric.infDist_le_dist_of_mem hv)

/-- **Inner regularisation inside the interior.**  A measurable subset `T` of a closed convex
body is exhausted, in measure, by compact subsets of `T ∩ interior K`: the part of `T` outside
the interior lies in the frontier, which a convex body's frontier being null makes negligible.

Landing the compacts *inside the interior* — not merely inside `K` — is what the chord transfer
of the mollified route needs: the cross-ratio distance is continuous only at pairs of points
whose chord meets the interior. -/
theorem exists_isCompact_subset_inter_interior {n : ℕ}
    {K T : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hT : MeasurableSet T) (hTK : T ⊆ K) (hTtop : volume T ≠ ⊤)
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C ∧ C ⊆ T ∧ C ⊆ interior K ∧
      volume T < volume C + η := by
  have hnull : volume (T \ interior K) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (hKc.addHaar_frontier volume)
    rw [hKcl.frontier_eq]
    exact ⟨hTK hx.1, hx.2⟩
  have hTeq : volume (T ∩ interior K) = volume T := by
    have h : volume (T ∩ interior K) + volume (T \ interior K) = volume T :=
      measure_inter_add_sdiff T isOpen_interior.measurableSet
    rw [hnull, add_zero] at h
    exact h
  obtain ⟨C, hCsub, hCcomp, hClt⟩ :=
    (hT.inter isOpen_interior.measurableSet).exists_isCompact_lt_add
      (by rw [hTeq]; exact hTtop) hη
  exact ⟨C, hCcomp, hCsub.trans Set.inter_subset_left, hCsub.trans Set.inter_subset_right,
    by rw [← hTeq]; exact hClt⟩

variable {n : ℕ}

/-- **The three-way partition of `K` in measure.**  `T₁`, `T₂` and `(K ∖ T₁) ∖ T₂` exhaust `K`
and are pairwise disjoint, so their measures add up. -/
theorem measure_add_add_sdiff_sdiff {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K)
    (hdisj : Disjoint T₁ T₂) :
    volume T₁ + (volume T₂ + volume ((K \ T₁) \ T₂)) = volume K := by
  have hunion : K = T₁ ∪ (T₂ ∪ ((K \ T₁) \ T₂)) := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases h1 : x ∈ T₁
      · exact Or.inl h1
      by_cases h2 : x ∈ T₂
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨⟨hx, h1⟩, h2⟩)
    · rintro (h1 | h2 | h3)
      exacts [hT₁K h1, hT₂K h2, h3.1.1]
  have hd₂ : Disjoint T₂ ((K \ T₁) \ T₂) :=
    Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx
  have hd₁ : Disjoint T₁ (T₂ ∪ ((K \ T₁) \ T₂)) := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rcases hx' with h2 | h3
    exacts [Set.disjoint_left.mp hdisj hx h2, h3.1.2 hx]
  have hQm : MeasurableSet ((K \ T₁) \ T₂) := (hKm.diff hT₁).diff hT₂
  calc volume T₁ + (volume T₂ + volume ((K \ T₁) \ T₂))
      = volume (T₁ ∪ (T₂ ∪ ((K \ T₁) \ T₂))) := by
        rw [measure_union hd₁ (hT₂.union hQm), measure_union hd₂ hQm]
    _ = volume K := by rw [← hunion]

/-- **`1_S · f` is lower semicontinuous for `S` open and `f` continuous *on `S`*.**

`ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_isOpen` (`LocalizationLSC.lean`) asks for `f`
continuous on the whole space; the weight this file has to feed to the localisation is concave on
a body, hence continuous only on its interior, so the hypothesis has to be the relative one.  The
proof is the same: `S ∩ f ⁻¹' (y, ∞)` is open for `S` open and `f` continuous on `S`. -/
theorem lowerSemicontinuous_indicator_of_continuousOn {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsOpen S) {f : X → ℝ} (hf : ContinuousOn f S)
    (hf0 : ∀ x ∈ S, 0 ≤ f x) :
    LowerSemicontinuous (S.indicator f) := by
  intro x y hy
  by_cases hx : x ∈ S
  · have hfx : y < f x := by rwa [Set.indicator_of_mem hx] at hy
    have hopen : IsOpen (S ∩ f ⁻¹' Set.Ioi y) := hf.isOpen_inter_preimage hS isOpen_Ioi
    filter_upwards [hopen.mem_nhds ⟨hx, hfx⟩] with x' hx'
    rw [Set.indicator_of_mem hx'.1]
    exact hx'.2
  · have hy0 : y < 0 := by rwa [Set.indicator_of_notMem hx] at hy
    refine Filter.Eventually.of_forall fun x' => ?_
    show y < S.indicator f x'
    by_cases hmem : x' ∈ S
    · rw [Set.indicator_of_mem hmem]; exact lt_of_lt_of_le hy0 (hf0 x' hmem)
    · rw [Set.indicator_of_notMem hmem]; exact hy0

/-- **A nonnegative constant multiple of a lower semicontinuous function is lower
semicontinuous.**  Mathlib has `LowerSemicontinuous.add`, `.sup` and `.inf`, but no scalar
multiple; this is the missing one, and the sign hypothesis is essential (a negative multiple is
*upper* semicontinuous). -/
theorem lowerSemicontinuous_const_mul {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : LowerSemicontinuous f) {c : ℝ} (hc : 0 ≤ c) :
    LowerSemicontinuous fun x => c * f x := by
  rcases hc.lt_or_eq with hcpos | hc0
  · intro x y hy
    have hy0 : y < c * f x := hy
    have hy' : y / c < f x := by
      rw [div_lt_iff₀ hcpos]
      linarith only [hy0]
    filter_upwards [hf x (y / c) hy'] with x' hx'
    have hx'' : y / c < f x' := hx'
    rw [div_lt_iff₀ hcpos] at hx''
    show y < c * f x'
    linarith only [hx'']
  · simp only [← hc0, zero_mul]
    exact continuous_const.lowerSemicontinuous

/-- The mollifier of a compact set `C ⊆ K` has `K`-integral at least the volume of `C`: it is
`1` on `C` and nonnegative elsewhere. -/
theorem measureReal_le_setIntegral_bookMollifier {K C : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hCm : MeasurableSet C) (hCK : C ⊆ K) {Tm : ℝ} :
    (volume C).toReal ≤ ∫ x in K, bookMollifier C Tm x := by
  have hcont : Continuous (bookMollifier C Tm) := continuous_bookMollifier C Tm
  have hint : IntegrableOn (bookMollifier C Tm) K := hcont.continuousOn.integrableOn_compact hK
  have h1 : (∫ x in C, bookMollifier C Tm x) ≤ ∫ x in K, bookMollifier C Tm x :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall (bookMollifier_nonneg C Tm))
      hCK.eventuallyLE
  have h2 : (∫ x in C, bookMollifier C Tm x) = (volume C).toReal := by
    rw [setIntegral_congr_fun hCm (g := fun _ => (1 : ℝ))
      (fun x hx => bookMollifier_of_mem hx), setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  linarith

/-- The mollifier has `K`-integral at most the volume of `K`: it is bounded by `1`. -/
theorem setIntegral_bookMollifier_le {K C : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) {Tm : ℝ} (hTm : 0 ≤ Tm) :
    (∫ x in K, bookMollifier C Tm x) ≤ (volume K).toReal := by
  have hcont : Continuous (bookMollifier C Tm) := continuous_bookMollifier C Tm
  have hint : IntegrableOn (bookMollifier C Tm) K := hcont.continuousOn.integrableOn_compact hK
  have h1 : (∫ x in K, bookMollifier C Tm x) ≤ ∫ _x in K, (1 : ℝ) :=
    setIntegral_mono_on hint (integrableOn_const hK.measure_lt_top.ne)
      hK.measurableSet fun x _ => bookMollifier_le_one hTm
  rwa [setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def] at h1

end Prelim

/-! ### The mollified route, at a continuous weight -/

section Core

variable {n : ℕ}

/-- **The weighted cross-ratio isoperimetric inequality for a continuous weight, from the
Localization Lemma and the chord transfer.**

This is Lee's `thm:har_weighted_iso` (*Optimization book*, §10.6) run on the mollified data, in
the real-valued form `A·∫_K h ≤ vol((K ∖ T₁) ∖ T₂)`, for a **continuous** weight `h`.

Two hypotheses are binders rather than proofs:

* `hloc` — the Localization Lemma of Kannan–Lovász–Simonovits for **continuous** integrands on
  the body `K`, in the shape the needle theorems of this repository consume: it returns a needle
  *inside* `K` carrying a log-concave profile, with `g₁`'s needle mass zero and `g₂`'s positive.
* `htrans` — the **chord transfer**: the chord bound, known at pairs of `T₁ × T₂`, holds up to an
  arbitrarily small additive `ε` at pairs in small neighbourhoods of compact subsets of
  `T₁ ∩ interior K` and `T₂ ∩ interior K`.

Everything else is discharged: the inner regularisation, the mollification, the constant
bookkeeping, and the passage from the needle to the contradiction.  The mollified weights are
`c·f_T(·, C₁)` and `f_T(·, C₂)` of `ArlibCommunity.Foundations.Convex.bookMollifier`, with `c ≤ 1` a normalisation chosen so
that the mass equation `∫_K c·f₁ = A'·vol K` holds *by construction* — this is why no
convergence of `vol(N(C₁, 1/T))` to `vol C₁` is needed, and why no limit of needles is taken.

Note that the two integrands handed to `hloc` are **globally continuous**: no indicator survives
the mollification, which is the whole reason Lee mollifies. -/
theorem iso_lowerSemicontinuous_of_transfer_of_localization
    {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : LowerSemicontinuous h)
    (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K)
    (hdisj : Disjoint T₁ T₂)
    (htrans : ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact C₁ → IsCompact C₂ → C₁ ⊆ T₁ → C₂ ⊆ T₂ →
      C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
        ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
          (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
          h x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmassK : (volume T₁).toReal = A * (volume K).toReal) :
    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal := by
  classical
  by_contra hcon'
  have hcon := not_le.mp hcon'
  -- `K` is a compact body of finite positive volume
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hKtop : volume K ≠ ⊤ := hKcomp.measure_lt_top.ne
  have hV0 : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
  have hT₁top : volume T₁ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₁K)
  have hT₂top : volume T₂ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₂K)
  have hQtop : volume ((K \ T₁) \ T₂) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono (Set.sdiff_subset.trans Set.sdiff_subset))
  -- the four real masses
  obtain ⟨V, hVdef⟩ : ∃ r : ℝ, (volume K).toReal = r := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁def⟩ : ∃ r : ℝ, (volume T₁).toReal = r := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂def⟩ : ∃ r : ℝ, (volume T₂).toReal = r := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ r : ℝ, (volume ((K \ T₁) \ T₂)).toReal = r := ⟨_, rfl⟩
  rw [hVdef] at hV0
  rw [hQdef] at hcon
  have hQ0 : 0 ≤ Q := hQdef ▸ ENNReal.toReal_nonneg
  have ht₁0 : 0 ≤ t₁ := ht₁def ▸ ENNReal.toReal_nonneg
  have ht₂0 : 0 ≤ t₂ := ht₂def ▸ ENNReal.toReal_nonneg
  have hmass : t₁ = A * V := by rw [← ht₁def, ← hVdef]; exact hmassK
  have hsum : t₁ + (t₂ + Q) = V := by
    rw [← ht₁def, ← ht₂def, ← hQdef, ← hVdef,
      ← ENNReal.toReal_add hT₂top hQtop, ← ENNReal.toReal_add hT₁top (by finiteness)]
    exact congrArg ENNReal.toReal (measure_add_add_sdiff_sdiff hKm hT₁ hT₂ hT₁K hT₂K hdisj)
  -- the average of `h`
  have hhm : Measurable h := hhc.measurable
  have hhint : IntegrableOn h K :=
    Measure.integrableOn_of_bounded (M := 1 / 3) hKtop hhm.aestronglyMeasurable (by
      rw [ae_restrict_iff' hKm]
      filter_upwards with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
      exact hh3 x hx)
  obtain ⟨I, hIdef⟩ : ∃ r : ℝ, (∫ x in K, h x) = r := ⟨_, rfl⟩
  rw [hIdef] at hcon
  have hI0 : 0 ≤ I := hIdef ▸ setIntegral_nonneg hKm fun x _ => hh0 x
  have hI3 : I ≤ V / 3 := by
    have hmono := setIntegral_mono_on hhint (integrableOn_const hKtop) hKm
      fun x hx => hh3 x hx
    rw [hIdef, setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, hVdef] at hmono
    linarith
  -- positivity of `A`, of `I`, and of the mass of `T₂`
  have hAI : 0 < A * I := lt_of_le_of_lt hQ0 hcon
  have hApos : 0 < A := by nlinarith
  have hIpos : 0 < I := by nlinarith
  have ht₂pos : V / 3 < t₂ := by nlinarith
  -- the slack, and the two small parameters it buys
  obtain ⟨e₀, he₀def⟩ : ∃ r : ℝ, A * I - Q = r := ⟨_, rfl⟩
  have he₀ : 0 < e₀ := by rw [← he₀def]; linarith
  have he₀le : e₀ ≤ A * I := by rw [← he₀def]; linarith
  obtain ⟨η, hηdef⟩ : ∃ r : ℝ, e₀ / 8 = r := ⟨_, rfl⟩
  obtain ⟨ep, hepdef⟩ : ∃ r : ℝ, e₀ / (6 * V) = r := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [← hηdef]; positivity
  have hep0 : 0 < ep := by rw [← hepdef]; positivity
  have hepV : ep * V = e₀ / 6 := by rw [← hepdef]; field_simp
  have hηt₁ : η < t₁ := by
    rw [← hηdef, hmass]
    nlinarith
  have hηt₂ : η < t₂ := by
    rw [← hηdef]
    nlinarith
  -- inner regularisation, inside the interior
  obtain ⟨C₁, hC₁comp, hC₁T, hC₁int, hC₁vol⟩ :=
    exists_isCompact_subset_inter_interior hKc hKcl hT₁ hT₁K hT₁top
      (ENNReal.ofReal_pos.mpr hη0).ne'
  obtain ⟨C₂, hC₂comp, hC₂T, hC₂int, hC₂vol⟩ :=
    exists_isCompact_subset_inter_interior hKc hKcl hT₂ hT₂K hT₂top
      (ENNReal.ofReal_pos.mpr hη0).ne'
  have hC₁top : volume C₁ ≠ ⊤ := ne_top_of_le_ne_top hT₁top (measure_mono hC₁T)
  have hC₂top : volume C₂ ≠ ⊤ := ne_top_of_le_ne_top hT₂top (measure_mono hC₂T)
  obtain ⟨c₁, hc₁def⟩ : ∃ r : ℝ, (volume C₁).toReal = r := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂def⟩ : ∃ r : ℝ, (volume C₂).toReal = r := ⟨_, rfl⟩
  have hc₁ : t₁ < c₁ + η := by
    have hlt := (ENNReal.toReal_lt_toReal hT₁top
      (ENNReal.add_ne_top.mpr ⟨hC₁top, ENNReal.ofReal_ne_top⟩)).mpr hC₁vol
    rwa [ENNReal.toReal_add hC₁top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη0.le,
      ht₁def, hc₁def] at hlt
  have hc₂ : t₂ < c₂ + η := by
    have hlt := (ENNReal.toReal_lt_toReal hT₂top
      (ENNReal.add_ne_top.mpr ⟨hC₂top, ENNReal.ofReal_ne_top⟩)).mpr hC₂vol
    rwa [ENNReal.toReal_add hC₂top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη0.le,
      ht₂def, hc₂def] at hlt
  have hc₁pos : 0 < c₁ := by linarith
  have hc₂pos : 0 < c₂ := by linarith
  have hC₁ne : C₁.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [measure_empty, ENNReal.toReal_zero] at hc₁def
    linarith [hc₁def ▸ hc₁pos]
  have hC₂ne : C₂.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [measure_empty, ENNReal.toReal_zero] at hc₂def
    linarith [hc₂def ▸ hc₂pos]
  -- the separation of the two compacts, their distance to the boundary, and the transfer radius
  obtain ⟨δ, hδ0, hsep⟩ := exists_sep_of_disjoint_isCompact hC₁comp hC₂comp hC₁ne hC₂ne
    (Set.disjoint_of_subset hC₁T hC₂T hdisj)
  obtain ⟨σ, hσ0, hσsub⟩ := (hC₁comp.union hC₂comp).exists_thickening_subset_open
    isOpen_interior (Set.union_subset hC₁int hC₂int)
  obtain ⟨ρ, hρ0, htr⟩ := htrans ep hep0 C₁ C₂ hC₁comp hC₂comp hC₁T hC₂T hC₁int hC₂int
    hC₁ne hC₂ne
  obtain ⟨r, hrdef⟩ : ∃ s : ℝ, min (min ρ (δ / 3)) σ = s := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [← hrdef]; exact lt_min (lt_min hρ0 (by positivity)) hσ0
  have hrρ : r ≤ ρ := by rw [← hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrδ : r ≤ δ / 3 := by rw [← hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hrσ : r ≤ σ := by rw [← hrdef]; exact min_le_right _ _
  -- the two neighbourhoods sit inside `K` and are disjoint
  have hNK : ∀ x : EuclideanSpace ℝ (Fin n), Metric.infDist x C₁ < r ∨ Metric.infDist x C₂ < r →
      x ∈ K := by
    rintro x (hx | hx)
    · obtain ⟨z, hz, hxz⟩ := (Metric.infDist_lt_iff hC₁ne).mp hx
      exact interior_subset (hσsub (Metric.mem_thickening_iff.mpr
        ⟨z, Or.inl hz, lt_of_lt_of_le hxz hrσ⟩))
    · obtain ⟨z, hz, hxz⟩ := (Metric.infDist_lt_iff hC₂ne).mp hx
      exact interior_subset (hσsub (Metric.mem_thickening_iff.mpr
        ⟨z, Or.inr hz, lt_of_lt_of_le hxz hrσ⟩))
  have hNdisj : Disjoint {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₁ < r}
      {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₂ < r} := by
    refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
    obtain ⟨u, hu, hxu⟩ := (Metric.infDist_lt_iff hC₁ne).mp hx1
    obtain ⟨v, hv, hxv⟩ := (Metric.infDist_lt_iff hC₂ne).mp hx2
    have hd := hsep u hu v hv
    have htri : dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
    rw [dist_comm u x] at htri
    linarith only [hd, htri, hxu, hxv, hrδ, hδ0]
  -- the mollifiers
  obtain ⟨Tm, hTmdef⟩ : ∃ s : ℝ, 1 / r = s := ⟨_, rfl⟩
  have hTm0 : 0 < Tm := by rw [← hTmdef]; positivity
  have hTminv : 1 / Tm = r := by rw [← hTmdef]; field_simp
  have hF₁c : Continuous (bookMollifier C₁ Tm) := continuous_bookMollifier _ _
  have hF₂c : Continuous (bookMollifier C₂ Tm) := continuous_bookMollifier _ _
  have hF₁0 : ∀ x, 0 ≤ bookMollifier C₁ Tm x := bookMollifier_nonneg _ _
  have hF₂0 : ∀ x, 0 ≤ bookMollifier C₂ Tm x := bookMollifier_nonneg _ _
  have hF₁1 : ∀ x, bookMollifier C₁ Tm x ≤ 1 := fun _ => bookMollifier_le_one hTm0.le
  have hF₂1 : ∀ x, bookMollifier C₂ Tm x ≤ 1 := fun _ => bookMollifier_le_one hTm0.le
  have h2Tm : 2 / Tm < δ := by
    have h2 : (2 : ℝ) / Tm = 2 * (1 / Tm) := by ring
    rw [h2, hTminv]
    linarith only [hrδ, hδ0]
  have hFdisj : ∀ x, bookMollifier C₁ Tm x = 0 ∨ bookMollifier C₂ Tm x = 0 :=
    bookMollifier_disjoint hTm0 h2Tm hC₁ne hC₂ne hsep
  have hsupp₁ : ∀ x, bookMollifier C₁ Tm x ≠ 0 → Metric.infDist x C₁ < r := by
    intro x hx
    have hlt := infDist_lt_of_bookMollifier_ne_zero hTm0 hx
    rwa [hTminv] at hlt
  have hsupp₂ : ∀ x, bookMollifier C₂ Tm x ≠ 0 → Metric.infDist x C₂ < r := by
    intro x hx
    have hlt := infDist_lt_of_bookMollifier_ne_zero hTm0 hx
    rwa [hTminv] at hlt
  -- the trimmed weight `w = min (1/3) (max 0 (h − 3ε))`, which obeys the chord bound exactly
  obtain ⟨w, hwdef⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (fun x => min (1 / 3 : ℝ) (max 0 (h x - 3 * ep))) = f := ⟨_, rfl⟩
  have hwapp : ∀ x, w x = min (1 / 3 : ℝ) (max 0 (h x - 3 * ep)) := fun x => by rw [← hwdef]
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    rw [hwapp]; exact le_min (by norm_num) (le_max_left _ _)
  have hw3 : ∀ x, w x ≤ 1 / 3 := fun x => by rw [hwapp]; exact min_le_left _ _
  have hwlsc : LowerSemicontinuous w := by
    rw [← hwdef]
    have h1 : LowerSemicontinuous fun x : EuclideanSpace ℝ (Fin n) => h x + -(3 * ep) :=
      hhc.add continuous_const.lowerSemicontinuous
    have h1' : LowerSemicontinuous fun x : EuclideanSpace ℝ (Fin n) => h x - 3 * ep := by
      simpa [sub_eq_add_neg] using h1
    have h2 : LowerSemicontinuous
        fun x : EuclideanSpace ℝ (Fin n) => max 0 (h x - 3 * ep) :=
      (continuous_const.lowerSemicontinuous
        (f := fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))).sup h1'
    exact (continuous_const.lowerSemicontinuous
      (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 / 3 : ℝ))).inf h2
  have hwm : Measurable w := hwlsc.measurable
  have hwge : ∀ x ∈ K, h x - 3 * ep ≤ w x := by
    intro x hx
    rw [hwapp]
    exact le_min (by linarith only [hh3 x hx, hep0]) (le_max_right _ _)
  have hwle : ∀ x, w x ≤ max 0 (h x - 3 * ep) := fun x => by rw [hwapp]; exact min_le_right _ _
  -- the normalisation making the mass equation hold by construction
  obtain ⟨J₁, hJ₁def⟩ : ∃ s : ℝ, (∫ x in K, bookMollifier C₁ Tm x) = s := ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂def⟩ : ∃ s : ℝ, (∫ x in K, bookMollifier C₂ Tm x) = s := ⟨_, rfl⟩
  have hJ₁ge : c₁ ≤ J₁ := by
    rw [← hJ₁def, ← hc₁def]
    exact measureReal_le_setIntegral_bookMollifier hKcomp hC₁comp.measurableSet
      (hC₁T.trans hT₁K)
  have hJ₂ge : c₂ ≤ J₂ := by
    rw [← hJ₂def, ← hc₂def]
    exact measureReal_le_setIntegral_bookMollifier hKcomp hC₂comp.measurableSet
      (hC₂T.trans hT₂K)
  have hJ₁pos : 0 < J₁ := lt_of_lt_of_le hc₁pos hJ₁ge
  obtain ⟨cc, hccdef⟩ : ∃ s : ℝ, c₁ / J₁ = s := ⟨_, rfl⟩
  have hcc0 : 0 < cc := by rw [← hccdef]; positivity
  have hcc1 : cc ≤ 1 := by rw [← hccdef, div_le_one hJ₁pos]; exact hJ₁ge
  have hccF₁ : ∀ x, cc * bookMollifier C₁ Tm x ≤ 1 := fun x => by
    have hx := mul_le_mul hcc1 (hF₁1 x) (hF₁0 x) zero_le_one
    linarith only [hx]
  have hccJ : cc * J₁ = c₁ := by rw [← hccdef]; field_simp
  obtain ⟨A', hA'def⟩ : ∃ s : ℝ, c₁ / V = s := ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := by rw [← hA'def]; positivity
  have hA'V : A' * V = c₁ := by rw [← hA'def]; field_simp
  have hc₁t₁ : c₁ ≤ t₁ := by
    rw [← hc₁def, ← ht₁def]
    exact ENNReal.toReal_mono hT₁top (measure_mono hC₁T)
  have hA'le : A' ≤ A := by
    rw [← hA'def, div_le_iff₀ hV0]
    rw [hmass] at hc₁t₁
    linarith only [hc₁t₁]
  have hA'half : A' ≤ 1 / 2 := le_trans hA'le hA
  have hA'ge : A - η / V ≤ A' := by
    rw [← hA'def, le_div_iff₀ hV0]
    have hrw : (A - η / V) * V = A * V - η := by field_simp
    rw [hrw, ← hmass]
    linarith only [hc₁]
  -- the two integrands: both globally continuous
  obtain ⟨g₁, hg₁def⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (fun x => cc * bookMollifier C₁ Tm x - A') = f := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂def⟩ : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (fun x => A' * w x
        - (1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x)) = f := ⟨_, rfl⟩
  have hg₁app : ∀ x, g₁ x = cc * bookMollifier C₁ Tm x - A' := fun x => by rw [← hg₁def]
  have hg₂app : ∀ x, g₂ x
      = A' * w x - (1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x) := fun x => by
    rw [← hg₂def]
  have hg₁c : Continuous g₁ := by
    rw [← hg₁def]; exact (continuous_const.mul hF₁c).sub continuous_const
  have hg₂lsc : LowerSemicontinuous g₂ := by
    rw [← hg₂def]
    exact (lowerSemicontinuous_const_mul hwlsc hA'0).add
      (((continuous_const.sub (continuous_const.mul hF₁c)).sub hF₂c).neg).lowerSemicontinuous
  have hg₂eq' : ∀ x, A' * w x
      + -(1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x) = g₂ x := fun x => by
    rw [hg₂app]; ring
  -- the third weight is a genuine weight: `0 ≤ 1 − c·f₁ − f₂ ≤ 1`
  have hf₃0 : ∀ x, 0 ≤ 1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x := by
    intro x
    rcases hFdisj x with hz | hz
    · rw [hz, mul_zero, sub_zero]; linarith only [hF₂1 x]
    · rw [hz, sub_zero]; linarith only [hccF₁ x]
  have hf₃1 : ∀ x, 1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x ≤ 1 := by
    intro x
    have h1 : 0 ≤ cc * bookMollifier C₁ Tm x := mul_nonneg hcc0.le (hF₁0 x)
    linarith only [h1, hF₂0 x]
  -- the ambient integrals
  have hsubint : ∀ f g : EuclideanSpace ℝ (Fin n) → ℝ, IntegrableOn f K → IntegrableOn g K →
      (∫ x in K, (f x - g x)) = (∫ x in K, f x) - ∫ x in K, g x :=
    fun f g hf hg => integral_sub hf hg
  have hsubint' : ∀ f g : EuclideanSpace ℝ (Fin n) → ℝ, IntegrableOn f K → IntegrableOn g K →
      IntegrableOn (fun x => f x - g x) K :=
    fun _ _ hf hg => hf.sub hg
  have hintF₁ : IntegrableOn (fun x => cc * bookMollifier C₁ Tm x) K :=
    (continuous_const.mul hF₁c).continuousOn.integrableOn_compact hKcomp
  have hintF₂ : IntegrableOn (bookMollifier C₂ Tm) K :=
    hF₂c.continuousOn.integrableOn_compact hKcomp
  have hwint : IntegrableOn w K :=
    Measure.integrableOn_of_bounded (M := 1 / 3) hKtop hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
        exact hw3 x)
  have hzero : (∫ x in K, g₁ x) = 0 := by
    rw [setIntegral_congr_fun hKm (fun x _ => hg₁app x),
      integral_sub hintF₁ (integrableOn_const hKtop), integral_const_mul, setIntegral_const,
      smul_eq_mul, MeasureTheory.measureReal_def, hVdef, hJ₁def, hccJ]
    linarith only [hA'V]
  obtain ⟨Iw, hIwdef⟩ : ∃ s : ℝ, (∫ x in K, w x) = s := ⟨_, rfl⟩
  have hwK : I - 3 * ep * V ≤ Iw := by
    have hmono : (∫ x in K, (h x - 3 * ep)) ≤ ∫ x in K, w x :=
      setIntegral_mono_on (hhint.sub (integrableOn_const hKtop)) hwint hKm
        fun x hx => hwge x hx
    rw [integral_sub hhint (integrableOn_const hKtop), setIntegral_const, smul_eq_mul,
      MeasureTheory.measureReal_def, hVdef, hIdef, hIwdef] at hmono
    linarith only [hmono]
  have hg₂eq : (∫ x in K, g₂ x) = A' * Iw - (V - c₁ - J₂) := by
    have hf₃int : IntegrableOn
        (fun x => 1 - cc * bookMollifier C₁ Tm x - bookMollifier C₂ Tm x) K :=
      ((integrableOn_const hKtop).sub hintF₁).sub hintF₂
    rw [setIntegral_congr_fun hKm (fun x _ => hg₂app x),
      integral_sub (hwint.const_mul A') hf₃int, integral_const_mul, hIwdef]
    congr 1
    have h1 : IntegrableOn (fun x => (1 : ℝ) - cc * bookMollifier C₁ Tm x) K :=
      hsubint' _ _ (integrableOn_const hKtop) hintF₁
    rw [hsubint (fun x => (1 : ℝ) - cc * bookMollifier C₁ Tm x) (bookMollifier C₂ Tm) h1 hintF₂,
      hsubint (fun _ => (1 : ℝ)) (fun x => cc * bookMollifier C₁ Tm x)
        (integrableOn_const hKtop) hintF₁,
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def, hVdef, hJ₁def, hJ₂def, hccJ]
  -- the strict inequality at the ambient level
  have h3epV : 3 * ep * V = e₀ / 2 := by
    have hrw : 3 * ep * V = 3 * (ep * V) := by ring
    rw [hrw, hepV]; ring
  have hIw0 : 0 ≤ I - 3 * ep * V := by
    rw [h3epV]
    have hAI2 : A * I ≤ 1 / 2 * I := mul_le_mul_of_nonneg_right hA hI0
    linarith only [hAI2, he₀le, hI0]
  have hprod : (A - η / V) * (I - 3 * ep * V) ≤ A' * Iw :=
    mul_le_mul hA'ge hwK hIw0 hA'0
  have hb1 : η / V * I ≤ η / 3 := by
    have hηV : 0 ≤ η / V := by positivity
    have hstep := mul_le_mul_of_nonneg_left hI3 hηV
    have hrw : η / V * (V / 3) = η / 3 := by field_simp
    linarith only [hrw ▸ hstep]
  have hb2 : 3 * A * ep * V ≤ e₀ / 4 := by
    have hrw : 3 * A * ep * V = 3 * A * (ep * V) := by ring
    rw [hrw, hepV]
    have hAe : A * e₀ ≤ 1 / 2 * e₀ := mul_le_mul_of_nonneg_right hA he₀.le
    linarith only [hAe, he₀]
  have hb3 : 0 ≤ 3 * (η / V) * ep * V := by positivity
  have hexp : (A - η / V) * (I - 3 * ep * V)
      = A * I - 3 * A * ep * V - η / V * I + 3 * (η / V) * ep * V := by ring
  have hposi : 0 < ∫ x in K, g₂ x := by
    rw [hg₂eq]
    have hlow : A * I - e₀ / 4 - η / 3 ≤ A' * Iw := by
      rw [hexp] at hprod
      linarith only [hprod, hb1, hb2, hb3]
    have hup : V - c₁ - J₂ ≤ Q + 2 * η := by
      linarith only [hc₁, hc₂, hJ₂ge, hsum]
    have hηe : η = e₀ / 8 := hηdef.symm
    linarith only [hlow, hup, hηe, he₀def, he₀]
  -- the second integrand is bounded, so it has a continuous minorant with positive integral
  have hg₂bd : ∀ x, |g₂ x| ≤ 1 := by
    intro x
    have h1 : 0 ≤ A' * w x := mul_nonneg hA'0 (hw0 x)
    have h2 : A' * w x ≤ 1 / 2 * (1 / 3) :=
      mul_le_mul hA'half (hw3 x) (hw0 x) (by norm_num)
    have h3 := hf₃0 x
    have h4 := hf₃1 x
    rw [hg₂app, abs_le]
    constructor <;> linarith only [h1, h2, h3, h4]
  obtain ⟨φ, hφc, hφle, hφb, hφpos⟩ :=
    exists_continuous_le_setIntegral_pos (μ := volume) hKtop hg₂lsc hg₂bd hposi
  -- the needle
  obtain ⟨p, e, α, β, D, hαβ, hseg, hD0, hlcD, hDint, hzeroN, hposNφ⟩ :=
    hloc g₁ φ hg₁c hφc hzero hφpos
  have hDIcc : IntegrableOn D (Set.Icc α β) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hDint
  have hneedlec : Continuous (needleMap p e) := by
    show Continuous fun t : ℝ => p + t • e
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hwt : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ 1) →
      IntegrableOn (fun t => f (needleMap p e t) * D t) (Set.Icc α β) := by
    intro f hfm hf0 hf1
    exact integrableOn_weight_mul hD0 hDIcc (hfm.comp hneedlec.measurable) (fun t => hf0 _)
      (fun t => hf1 _) measurableSet_Icc Set.Subset.rfl
  have hIccInt : ∀ f : ℝ → ℝ, (∫ t in Set.Icc α β, f t) = ∫ t in α..β, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hαβ, integral_Icc_eq_integral_Ioc]
  have hint_cF₁ : IntegrableOn
      (fun t => cc * bookMollifier C₁ Tm (needleMap p e t) * D t) (Set.Icc α β) :=
    hwt _ ((measurable_const.mul hF₁c.measurable)) (fun x => mul_nonneg hcc0.le (hF₁0 x))
      hccF₁
  have hint_w : IntegrableOn (fun t => w (needleMap p e t) * D t) (Set.Icc α β) :=
    hwt _ hwm hw0 (fun x => by linarith only [hw3 x])
  have hint_f₃ : IntegrableOn (fun t =>
      (1 - cc * bookMollifier C₁ Tm (needleMap p e t)
        - bookMollifier C₂ Tm (needleMap p e t)) * D t) (Set.Icc α β) :=
    hwt _ ((measurable_const.sub (measurable_const.mul hF₁c.measurable)).sub hF₂c.measurable)
      hf₃0 hf₃1
  -- the positivity passes from the minorant to `g₂` on the needle, `D` being nonnegative
  have hbdD : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), Measurable f → (∀ x, |f x| ≤ 1) →
      IntegrableOn (fun t => f (needleMap p e t) * D t) (Set.Icc α β) := by
    intro f hfm hfb
    refine Integrable.mono' hDIcc
      (((hfm.comp hneedlec.measurable).aestronglyMeasurable).mul
        hDIcc.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    have hD := hD0 t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hD]
    have hstep := mul_le_mul_of_nonneg_right (hfb (needleMap p e t)) hD
    linarith only [hstep]
  have hposN : 0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t :=
    lt_of_lt_of_le hposNφ
      (setIntegral_mono_on (hbdD φ hφc.measurable hφb) (hbdD g₂ hg₂lsc.measurable hg₂bd)
        measurableSet_Icc fun t ht => mul_le_mul_of_nonneg_right (hφle _) (hD0 t ht))
  -- the mass equation and the strict inequality, transported to the needle
  have hsplit₁ : (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t)
      = (∫ t in Set.Icc α β, cc * bookMollifier C₁ Tm (needleMap p e t) * D t)
        - A' * ∫ t in Set.Icc α β, D t := by
    have hcongr : ∀ t, g₁ (needleMap p e t) * D t
        = cc * bookMollifier C₁ Tm (needleMap p e t) * D t - A' * D t := by
      intro t; rw [hg₁app]; ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hcongr t),
      integral_sub hint_cF₁ (hDIcc.const_mul A'), integral_const_mul]
  have hmassN : (∫ t in Set.Icc α β, cc * bookMollifier C₁ Tm (needleMap p e t) * D t)
      = A' * ∫ t in α..β, D t := by
    rw [← hIccInt D]
    rw [hsplit₁] at hzeroN
    linarith only [hzeroN]
  have hsplit₂ : (∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t)
      = A' * (∫ t in Set.Icc α β, w (needleMap p e t) * D t)
        - ∫ t in Set.Icc α β, (1 - cc * bookMollifier C₁ Tm (needleMap p e t)
            - bookMollifier C₂ Tm (needleMap p e t)) * D t := by
    have hcongr : ∀ t, g₂ (needleMap p e t) * D t
        = A' * (w (needleMap p e t) * D t)
          - (1 - cc * bookMollifier C₁ Tm (needleMap p e t)
              - bookMollifier C₂ Tm (needleMap p e t)) * D t := by
      intro t; rw [hg₂app]; ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hcongr t),
      integral_sub (hint_w.const_mul A') hint_f₃, integral_const_mul]
  -- the chord bound at the enlarged supports, for the trimmed weight
  have hchordN : ∀ u ∈ {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₁ < r},
      ∀ v ∈ {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₂ < r}, ∀ x ∈ K,
      (∃ s : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) s) →
      w x ≤ min 1 (crossRatioDist K u v) / 3 := by
    intro u hu v hv x hx hex
    have hb := htr u (lt_of_lt_of_le hu hrρ) v (lt_of_lt_of_le hv hrρ) x hx hex
    have huv : u ≠ v := fun heq =>
      Set.disjoint_left.mp hNdisj hu (heq ▸ hv)
    have hnn : 0 ≤ min 1 (crossRatioDist K u v) / 3 := by
      have hcr := crossRatioDist_nonneg hKb huv (hNK u (Or.inl hu)) (hNK v (Or.inr hv))
      have hm : 0 ≤ min 1 (crossRatioDist K u v) := le_min zero_le_one hcr
      linarith only [hm]
    rcases le_or_gt (h x - 3 * ep) 0 with hle | hlt
    · calc w x ≤ max 0 (h x - 3 * ep) := hwle x
        _ = 0 := max_eq_left hle
        _ ≤ _ := hnn
    · calc w x ≤ max 0 (h x - 3 * ep) := hwle x
        _ = h x - 3 * ep := max_eq_right hlt.le
        _ ≤ min 1 (crossRatioDist K u v) / 3 := by linarith only [hb, hep0]
  -- the one-dimensional theorem, and the contradiction
  have hGDint : IntervalIntegrable (fun t => w (needleMap p e t) * D t) volume α β :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mpr hint_w
  have hkey := needle_iso_of_chord_weight (K := K)
    (N₁ := {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₁ < r})
    (N₂ := {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x C₂ < r}) hKb hNdisj
    (h := w) hw0 (fun x _ => hw3 x) hchordN
    (f₁ := fun x => cc * bookMollifier C₁ Tm x) (f₂ := bookMollifier C₂ Tm)
    (measurable_const.mul hF₁c.measurable) hF₂c.measurable
    (fun x => mul_nonneg hcc0.le (hF₁0 x)) hF₂0
    hccF₁ hF₂1
    (fun x hx => hsupp₁ x fun hz => hx (by rw [hz, mul_zero])) hsupp₂
    hαβ hseg hD0 hlcD hDint hGDint hA'0 hA'half hmassN
  rw [← hIccInt (fun t => w (needleMap p e t) * D t)] at hkey
  rw [hsplit₂] at hposN
  linarith only [hkey, hposN]

/-- **The same conclusion for a lower semicontinuous weight, from the transfer at *continuous*
weights only.**

The transfer binder cannot be quantified over lower semicontinuous weights: it is then **false**.
In `K = [0,1]²` take `U₁ = {(2/5,1/2)}`, `U₂ = {(1/2,1/2)}` (compact, disjoint, inside the
interior — nothing in the binder asks for positive measure) and
`g = 1_W · (1/3)` with `W = (4/5,1) × (1/2,3/5)` open, so `g` is lower semicontinuous by
`ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_isOpen`.  The chord through the pair is the segment
`y = 1/2`, which misses `W`, so the chord hypothesis holds vacuously.  But for every `ρ > 0` the
perturbed pair `((2/5,1/2), (1/2,1/2+δ))` with `δ < min(ρ, 1/60)` has the *same* chord parameters
`a = −4`, `b = 6`, hence `d_K = 1/2`, while its chord passes through `(9/10, 1/2+5δ) ∈ W`, where
`g = 1/3 > 1/6 + 1/8`.  So at `ε = 1/8` no radius works.  The mechanism is that lower
semicontinuity controls a weight from *below*, and the transfer needs control from above.

The lower semicontinuous case is therefore **derived**, not assumed: the weight is truncated at
`1/3` (which changes nothing on `K`) and approximated from below by its Lipschitz inf-convolution
minorants (`ArlibCommunity.Foundations.Convex.lipschitzMinorant`), each of which is *continuous*, nonnegative, bounded by
`1/3` and below `h`, hence inherits the chord bound; the conclusion is a closed inequality in
`∫_K`, and `ArlibCommunity.Foundations.Convex.tendsto_setIntegral_lipschitzMinorant` passes to the limit. -/
theorem iso_lowerSemicontinuous_of_continuous_transfer_of_localization
    {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : LowerSemicontinuous h)
    (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K)
    (hdisj : Disjoint T₁ T₂)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    (htrans : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ T₁ → C₂ ⊆ T₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmassK : (volume T₁).toReal = A * (volume K).toReal) :
    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal := by
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hKtop : volume K ≠ ⊤ := hKcomp.measure_lt_top.ne
  -- truncate at `1/3`: nothing changes on `K`, and the truncation is globally bounded
  have hh'lsc : LowerSemicontinuous fun x => min (h x) (1 / 3 : ℝ) :=
    hhc.inf continuous_const.lowerSemicontinuous
  have hh'0 : ∀ x, 0 ≤ min (h x) (1 / 3 : ℝ) := fun x => le_min (hh0 x) (by norm_num)
  have hh'3 : ∀ x, min (h x) (1 / 3 : ℝ) ≤ 1 / 3 := fun x => min_le_right _ _
  have hh'le : ∀ x, min (h x) (1 / 3 : ℝ) ≤ h x := fun x => min_le_left _ _
  have hh'eq : ∀ x ∈ K, min (h x) (1 / 3 : ℝ) = h x := fun x hx => min_eq_left (hh3 x hx)
  have hbd : ∀ x, |min (h x) (1 / 3 : ℝ)| ≤ 1 / 3 := fun x =>
    abs_le.mpr ⟨by linarith only [hh'0 x], hh'3 x⟩
  -- every Lipschitz minorant is a continuous weight obeying the same bounds
  have hkey : ∀ k : ℕ, A * (∫ x in K, lipschitzMinorant (fun x => min (h x) (1 / 3 : ℝ)) k x)
      ≤ (volume ((K \ T₁) \ T₂)).toReal := by
    intro k
    have hcont := continuous_lipschitzMinorant hh'0 k
    have hnn : ∀ x, 0 ≤ lipschitzMinorant (fun x => min (h x) (1 / 3 : ℝ)) k x :=
      le_lipschitzMinorant hh'0 k
    have hle : ∀ x, lipschitzMinorant (fun x => min (h x) (1 / 3 : ℝ)) k x
        ≤ min (h x) (1 / 3 : ℝ) := lipschitzMinorant_le hh'0 k
    have h3 : ∀ x ∈ K, lipschitzMinorant (fun x => min (h x) (1 / 3 : ℝ)) k x ≤ 1 / 3 :=
      fun x _ => le_trans (hle x) (hh'3 x)
    have hch : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        lipschitzMinorant (fun x => min (h x) (1 / 3 : ℝ)) k x
          ≤ min 1 (crossRatioDist K u v) / 3 := fun u hu v hv x hx hex =>
      le_trans (le_trans (hle x) (hh'le x)) (hchord u hu v hv x hx hex)
    exact iso_lowerSemicontinuous_of_transfer_of_localization hKc hKcl hKm hKb hK0
      hcont.lowerSemicontinuous hnn h3 hT₁ hT₂ hT₁K hT₂K hdisj
      (htrans _ hcont hnn h3 hch) hloc hA0 hA hmassK
  -- and the minorants exhaust the integral
  have hlim := tendsto_setIntegral_lipschitzMinorant (μ := volume) hKtop hh'lsc hbd
  have hlimA := hlim.const_mul A
  have hfinal : A * (∫ x in K, min (h x) (1 / 3 : ℝ))
      ≤ (volume ((K \ T₁) \ T₂)).toReal :=
    le_of_tendsto hlimA (Filter.Eventually.of_forall hkey)
  rwa [setIntegral_congr_fun hKm fun x hx => hh'eq x hx] at hfinal

end Core

/-! ### Non-vacuity of the transfer binder

`ArlibCommunity.Foundations.Convex.bookMollifier_disjoint`'s docstring records the trap: `Metric.infDist x ∅ = 0`, so a
transfer binder that allowed `C₁ = ∅` would demand the chord bound at **every** `u` of the space,
including points outside `K`, where `crossRatioDist` is *negative*
(`ArlibCommunity.Foundations.Convex.one_le_crossRatioDist_of_notMem` is about `u ∉ K` with `chordLow > 0`, and there
`(b−a)/((−a)(b−1))` changes sign) — no nonnegative weight can satisfy that, and the binder would
be unsatisfiable, hence the theorems built on it vacuous.  The `C₁.Nonempty`, `C₂.Nonempty`
clauses are therefore load-bearing, and the two theorems below certify that with them the binder
is satisfiable: the zero weight meets both the chord hypothesis and the transfer conclusion, for
every body and every pair of disjoint subsets. -/

section Witness

variable {n : ℕ}

/-- The zero weight satisfies the chord hypothesis of Theorem 2.1, for any disjoint `U₁, U₂ ⊆ K`:
the right-hand side is nonnegative because `crossRatioDist` is, at distinct points of `K`. -/
theorem chord_bound_zero {K U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hU₁K : U₁ ⊆ K) (hU₂K : U₂ ⊆ K) (hdisj : Disjoint U₁ U₂) :
    ∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      (0 : ℝ) ≤ min 1 (crossRatioDist K u v) / 3 := by
  intro u hu v hv _ _ _
  have huv : u ≠ v := fun heq => Set.disjoint_left.mp hdisj hu (heq ▸ hv)
  have hcr := crossRatioDist_nonneg hKb huv (hU₁K hu) (hU₂K hv)
  have hm : 0 ≤ min 1 (crossRatioDist K u v) := le_min zero_le_one hcr
  linarith only [hm]

/-- **The transfer conclusion holds outright for the zero weight**, with the radius produced from
the separation of the two compacts and their distance to `∂K` — the same two ingredients the main
proof uses.  Together with `ArlibCommunity.Foundations.Convex.chord_bound_zero` this shows the `htrans` binder of
`ArlibCommunity.Foundations.Convex.hIso_continuous` is satisfiable, so neither that binder nor the theorems built on it are
vacuous for want of a witness. -/
theorem exists_transfer_radius_zero {K U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hdisj : Disjoint U₁ U₂)
    {ε : ℝ} (hε : 0 < ε) {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂) (hC₁U : C₁ ⊆ U₁) (hC₂U : C₂ ⊆ U₂)
    (hC₁int : C₁ ⊆ interior K) (hC₂int : C₂ ⊆ interior K)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
      ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        (0 : ℝ) ≤ min 1 (crossRatioDist K u v) / 3 + ε := by
  obtain ⟨δ, hδ0, hsep⟩ := exists_sep_of_disjoint_isCompact hC₁ hC₂ hne₁ hne₂
    (Set.disjoint_of_subset hC₁U hC₂U hdisj)
  obtain ⟨σ, hσ0, hσsub⟩ := (hC₁.union hC₂).exists_thickening_subset_open isOpen_interior
    (Set.union_subset hC₁int hC₂int)
  refine ⟨min (δ / 3) σ, lt_min (by positivity) hσ0, fun u hu v hv x _ _ => ?_⟩
  have hrδ : min (δ / 3) σ ≤ δ / 3 := min_le_left _ _
  have hrσ : min (δ / 3) σ ≤ σ := min_le_right _ _
  obtain ⟨z₁, hz₁, huz₁⟩ := (Metric.infDist_lt_iff hne₁).mp hu
  obtain ⟨z₂, hz₂, hvz₂⟩ := (Metric.infDist_lt_iff hne₂).mp hv
  have huK : u ∈ K :=
    interior_subset (hσsub (Metric.mem_thickening_iff.mpr
      ⟨z₁, Or.inl hz₁, lt_of_lt_of_le huz₁ hrσ⟩))
  have hvK : v ∈ K :=
    interior_subset (hσsub (Metric.mem_thickening_iff.mpr
      ⟨z₂, Or.inr hz₂, lt_of_lt_of_le hvz₂ hrσ⟩))
  have huv : u ≠ v := by
    rintro rfl
    have hd := hsep z₁ hz₁ z₂ hz₂
    have htri : dist z₁ z₂ ≤ dist z₁ u + dist u z₂ := dist_triangle _ _ _
    rw [dist_comm z₁ u] at htri
    linarith only [hd, htri, huz₁, hvz₂, hrδ, hδ0]
  have hcr := crossRatioDist_nonneg hKb huv huK hvK
  have hm : 0 ≤ min 1 (crossRatioDist K u v) := le_min zero_le_one hcr
  linarith only [hm, hε]

end Witness

/-! ### The `hIso` binder of the conductance theorem, at a continuous weight -/

section HIso

variable {n : ℕ}

/-- **The `hIso` binder of `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge`, with the weight
restricted to be continuous.**

Every clause of that binder (`HitAndRunConductance.lean`) is here verbatim — the two
subset clauses `T₁ ⊆ K`, `T₂ ⊆ K` included, without which the statement is *false*
(`ArlibCommunity.Foundations.Convex.not_crossRatioIso_printed`) — with the single clause `Continuous h` inserted after the two set
arguments.

`Continuous h` rather than `ConcaveOn ℝ K h`: the localisation entry points of this repository
ask for integrands continuous on the *whole space*, and a concave function on `K` is continuous
only on `interior K`.  See the closing section for what that costs at the conductance call site.

The two ambient binders `htrans` and `hloc` are those of
`ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_transfer_of_localization`, quantified over the weight and the two sets
so that they can be instantiated in both orders — the proof calls the core theorem once at
`(T₁, T₂)` and once at `(T₂, T₁)`, which is how `min (π T₁) (π T₂)` is covered. -/
theorem hIso_lowerSemicontinuous {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (htrans : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) := by
  intro h T₁ T₂ hhc hh0 hh3 hT₁ hT₂ hT₁K hT₂K hdisj hchord
  have hQsub : (K \ T₁) \ T₂ ⊆ K := Set.sdiff_subset.trans Set.sdiff_subset
  have hQm : MeasurableSet ((K \ T₁) \ T₂) := (hKm.diff hT₁).diff hT₂
  have hT₁top : volume T₁ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₁K)
  have hT₂top : volume T₂ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₂K)
  have hQtop : volume ((K \ T₁) \ T₂) ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hQsub)
  have hVR : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hInt : IntegrableOn h K volume :=
    Measure.integrableOn_of_bounded (M := 1 / 3) hKtop hhc.measurable.aestronglyMeasurable (by
      rw [ae_restrict_iff' hKm]
      filter_upwards with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
      exact hh3 x hx)
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
        (iso_lowerSemicontinuous_of_continuous_transfer_of_localization hKc hKcl hKm hKb hK0
          hhc hh0 hh3 hT₁ hT₂ hT₁K hT₂K hdisj hchord
          (fun g hgc hg0 hg3 hgch =>
            htrans g T₁ T₂ hgc hg0 hg3 hT₁ hT₂ hT₁K hT₂K hdisj hgch)
          hloc hA0 hAhalf hmass)
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
      have hchord' := chord_bound_comm hKb hT₁K hT₂K hdisj hchord
      have hswap := iso_lowerSemicontinuous_of_continuous_transfer_of_localization
        hKc hKcl hKm hKb hK0 hhc hh0 hh3 hT₂ hT₁ hT₂K hT₁K hdisj.symm hchord'
        (fun g hgc hg0 hg3 hgch =>
          htrans g T₂ T₁ hgc hg0 hg3 hT₂ hT₁ hT₂K hT₁K hdisj.symm hgch)
        hloc hA0 hAhalf hmass
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

/-- **The `hIso` binder at a continuous weight** — `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` specialised
along `Continuous.lowerSemicontinuous`.  This is the form the brief asked for; the lower
semicontinuous form above is strictly more general, and is the one the conductance call site
needs, `stepRadius` being continuous only on `interior K`. -/
theorem hIso_continuous {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (htrans : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) :=
  fun h T₁ T₂ hhc =>
    hIso_lowerSemicontinuous hKc hKcl hKm hKb hK0 hKtop htrans hloc h T₁ T₂
      hhc.lowerSemicontinuous

end HIso

/-! ### The binder check

Two theorems certify, mechanically, that the conclusion of `ArlibCommunity.Foundations.Convex.hIso_continuous` is the `hIso`
binder of `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge` (`HitAndRunConductance.lean`)
with the single clause `Continuous h` inserted, and nothing else changed — in particular with
`T₁ ⊆ K` and `T₂ ⊆ K` still present, without which the statement is false
(`ArlibCommunity.Foundations.Convex.not_crossRatioIso_printed`).

The copy of the binder written out in `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge_of_hIso_copy` is fed
*verbatim* to `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance_hitAndRun_ge`, so any drift between the copy and
the real binder would fail to typecheck; and `ArlibCommunity.Foundations.Convex.hIso_continuous_of_hIso` feeds the same copy
to the restricted statement, so any drift between the copy and `ArlibCommunity.Foundations.Convex.hIso_continuous` would fail
to typecheck as well.  This is the check that `ArlibCommunity.Foundations.Convex.false_of_crossRatioIso_binder` performs for
the refuted binder, run in the positive direction. -/

section BinderCheck

variable {n : ℕ}


/-- **The restricted statement is that same binder with `Continuous h` inserted**: the full
binder, applied to a continuous weight, *is* the conclusion of `ArlibCommunity.Foundations.Convex.hIso_continuous`.  The
continuity hypothesis is discarded on the right, which is what makes this a check rather than a
theorem with content. -/
theorem hIso_continuous_of_hIso {K : Set (EuclideanSpace ℝ (Fin n))}
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) :=
  fun h T₁ T₂ _ => hIso h T₁ T₂

/-- **The lower semicontinuous statement is the same binder with `LowerSemicontinuous h`
inserted**: the full binder, applied to a lower semicontinuous weight, *is* the conclusion of
`ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous`. -/
theorem hIso_lowerSemicontinuous_of_hIso {K : Set (EuclideanSpace ℝ (Fin n))}
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) :=
  fun h T₁ T₂ _ => hIso h T₁ T₂

end BinderCheck

/-! ### The conductance theorem at the lower semicontinuous `hIso` -/

section Conductance

variable {n : ℕ}








end Conductance

end ArlibCommunity.Foundations.Convex

/-! ### Axiom profile -/

section AxiomCheck

#print axioms ArlibCommunity.Foundations.Convex.exists_sep_of_disjoint_isCompact
#print axioms ArlibCommunity.Foundations.Convex.exists_isCompact_subset_inter_interior
#print axioms ArlibCommunity.Foundations.Convex.measure_add_add_sdiff_sdiff
#print axioms ArlibCommunity.Foundations.Convex.measureReal_le_setIntegral_bookMollifier
#print axioms ArlibCommunity.Foundations.Convex.setIntegral_bookMollifier_le
#print axioms ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_transfer_of_localization
#print axioms ArlibCommunity.Foundations.Convex.iso_lowerSemicontinuous_of_continuous_transfer_of_localization
#print axioms ArlibCommunity.Foundations.Convex.chord_bound_zero
#print axioms ArlibCommunity.Foundations.Convex.exists_transfer_radius_zero
#print axioms ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous
#print axioms ArlibCommunity.Foundations.Convex.hIso_continuous
#print axioms ArlibCommunity.Foundations.Convex.hIso_continuous_of_hIso
#print axioms ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous_of_hIso
#print axioms ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_continuousOn
#print axioms ArlibCommunity.Foundations.Convex.lowerSemicontinuous_const_mul

end AxiomCheck
