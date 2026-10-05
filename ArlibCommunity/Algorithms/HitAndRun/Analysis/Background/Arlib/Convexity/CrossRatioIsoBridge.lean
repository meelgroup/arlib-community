/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LovaszVempalaIso
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunConductance

/-!
# From Theorem 2.1's conclusion to the `hIso` binder: the encoding gap, closed

`Arlib.thm21_of_localization` (`Arlib/Convexity/LovaszVempalaIso.lean:733`) proves
Lovász–Vempala Theorem 2.1 in **ℝ**, against **Lebesgue measure**, with the small mass written
as an explicit scalar `A`:

    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal,   given
    (volume T₁).toReal = A * (volume K).toReal,  0 ≤ A,  A ≤ 1/2.

`Arlib.MarkovChains.conductance_hitAndRun_ge`
(`Arlib/MarkovChains/Continuous/HitAndRunConductance.lean:999`) consumes it in **ℝ≥0∞**,
against the **uniform probability measure** `Arlib.uniformOn volume K`, with the small mass
written as a `min`:

    (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K))
        * min (uniformOn volume K T₁) (uniformOn volume K T₂)
      ≤ uniformOn volume K ((K \ T₁) \ T₂).

This file proves the **second from the first** — it closes the encoding differences and nothing
else.  Only that one direction is proved: `hthm21 ⟹ hIso`.  The converse is *not* proved and is
not immediate, because `hmassK` pins `A` to `U₁`, which may be the larger of the two pieces,
where the `min`-form is the weaker statement.

## Main results

* `Arlib.chord_bound_comm` — **the chord hypothesis is symmetric in `T₁` and `T₂`**, which is
  what licenses the WLOG that turns `A` into a `min`.
* `Arlib.two_mul_min_measure_le` — `2·min(vol T₁, vol T₂) ≤ vol K` for disjoint measurable
  `T₁, T₂ ⊆ K`, which is what discharges `A ≤ 1/2` instead of assuming it.
* `Arlib.hIso_measurable_of_thm21` — the `hIso` conclusion for **measurable** `h`.
* `Arlib.hIso_of_thm21` — **the `hIso` binder, verbatim, for arbitrary `h`**, measurable or
  not.  This is the deliverable: it can be `exact`-ed into the `hIso` slot of
  `conductance_hitAndRun_ge`.
* `Arlib.conductance_hitAndRun_ge_of_thm21` — Theorem 4.2 with `hIso` replaced by the
  Theorem 2.1 hypothesis, carrying `hLem41` verbatim.

## Gap 1 — the scalar `A` versus `min (π T₁) (π T₂)`

`hmassK` pins `A` to the relative mass of `T₁`, so the source theorem is *asymmetric*: it
bounds `A·∫h` with `A` read off `T₁`, whereas the target wants the **smaller** of the two
masses.  The repair is a WLOG, and the WLOG is legitimate only because every hypothesis of
`thm21_of_localization` other than `hmassK` is symmetric under `T₁ ↔ T₂`:

* `hT₁`, `hT₂` (measurability) — literally symmetric;
* `hdisj : Disjoint T₁ T₂` — `Disjoint.symm`;
* the conclusion's set — `(K \ T₁) \ T₂ = (K \ T₂) \ T₁` by `sdiff_sdiff_comm`;
* `hchord` — **not** literally symmetric, since it reads `∀ u ∈ T₁, ∀ v ∈ T₂` and mentions
  `crossRatioDist K u v` in that order.  `Arlib.chord_bound_comm` proves it is symmetric
  anyway, from two facts: `Arlib.crossRatioDist_comm` (`CrossRatio.lean:375`) and the affine
  identity `lineMap v u (1−r) = lineMap u v r` (`AffineMap.lineMap_apply_one_sub`), so the
  chords through the pair are the same set of points traversed backwards.  Disjointness
  supplies the `u ≠ v` that `crossRatioDist_comm` requires, and the two `⊆ K` hypotheses — which
  `hIso` carries but `thm21_of_localization` does not — supply its membership arguments.

**No hypothesis is genuinely asymmetric.**  That is a positive finding: the swap is sound.

## Gap 2 — `A ≤ 1/2` is discharged, not assumed

`T₁` and `T₂` are disjoint measurable subsets of `K`, so `vol T₁ + vol T₂ = vol (T₁ ∪ T₂) ≤
vol K` and the smaller of the two is at most `vol K / 2` (`Arlib.two_mul_min_measure_le`).
Since the WLOG has already arranged that `A` is the *smaller* relative mass, `A ≤ 1/2` follows.
Without the WLOG it would be unavailable: `A ≤ 1/2` is simply false when `T₁` is the larger
piece.  So gaps 1 and 2 are one gap, and the `min` in the target is not cosmetic — it is what
makes the source theorem applicable at all.

## Gap 3 — ℝ versus ℝ≥0∞, and the normalisation

`uniformOn volume K = (volume K)⁻¹ • volume.restrict K` (`Arlib.uniformOn_def`), so with
`V := volume K` and `Q := (K \ T₁) \ T₂`:

* `∫⁻ x, ofReal (h x) ∂π = V⁻¹ * ∫⁻ x in K, ofReal (h x)` (`lintegral_smul_measure`);
* `π T = volume T / V` for measurable `T ⊆ K` (`Arlib.uniformOn_apply`, `Set.inter_eq_left`);
* `min (a/V) (b/V) = min a b / V`, since division by a fixed scalar is monotone.

**The `V` denominators do not fully cancel, and it is worth being explicit about that** rather
than assuming they do.  The target reads

    (V⁻¹ · I) · (min(vol T₁, vol T₂) · V⁻¹)  ≤  vol Q · V⁻¹,     I := ∫⁻ x in K, ofReal (h x),

i.e. after one cancellation `I · min(vol T₁, vol T₂) · V⁻¹ ≤ vol Q`, i.e.
`I · min(vol T₁, vol T₂) ≤ vol Q · V`.  The source gives `A·∫_K h ≤ (vol Q).toReal` with
`A = min(vol T₁, vol T₂).toReal / V.toReal`; multiplying by `V.toReal > 0` gives exactly that.
So **one** factor of `V` survives, absorbed into `A`.  A "both denominators cancel" reading
would be wrong by a factor of `V`.

The passage `ofReal (∫ x in K, h x) = ∫⁻ x in K, ofReal (h x)` is
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, which needs `h` **integrable on `K`** and
nonnegative.  Integrability is free here: `h` is bounded by `1/3` on `K` and `volume K < ⊤`.
Nonnegativity is a hypothesis of `hIso` already.  `volume K ≠ 0` and `volume K ≠ ⊤` are added as
hypotheses of the bridge; they are exactly the guards `uniformOn` needs to be a probability
measure, and at the conductance call site they follow from the inball and the circumball.

## Gap 3′ — `h` need not be measurable, and the binder says so

`hIso` quantifies over **every** `h : EuclideanSpace ℝ (Fin n) → ℝ`, with no measurability
clause; `Arlib.not_hIso_two_measurable` (`LovaszVempalaIsoFalse.lean:347`) records that adding
one does not rescue the printed statement, so the clause was deliberately left out.  But
`∫ x in K, h x` is Bochner and returns the junk value `0` for a non-integrable `h`, so the ℝ↔ℝ≥0∞
bridge of Gap 3 is available only for measurable `h`.  A measurable-only lemma **cannot** be
passed to `conductance_hitAndRun_ge` by `exact`, so this is not a caveat that may be left
standing.

It is removed by approximation from below.  Mathlib defines `∫⁻` as a supremum over simple
minorants (`MeasureTheory.lintegral_eq_nnreal`), and every hypothesis `hIso` places on `h` —
`0 ≤ h`, `h ≤ 1/3` on `K`, and the chord bound — is an **upper** bound, hence inherited by every
minorant.  So `hIso` for arbitrary `h` follows from `hIso` for the measurable functions
`x ↦ (φ x : ℝ)`, `φ : _ →ₛ ℝ≥0` ranging over simple minorants of `ofReal ∘ h`, by taking the
supremum.  `Arlib.hIso_of_thm21` is that argument, and it is why the hypothesis `hthm21` below
may carry a `Measurable g` binder for free: the caller supplying it from
`thm21_of_localization` simply ignores that argument.
-/

namespace Arlib

open MeasureTheory Set

open scoped NNReal ENNReal

variable {n : ℕ}

/-! ## Gap 1: the chord hypothesis is symmetric

The one hypothesis of `Arlib.thm21_of_localization` whose symmetry is not immediate.  A chord
from `u ∈ T₂` to `v ∈ T₁` is the chord from `v` to `u` traversed backwards — parameter `r`
becoming `1 − r` — and `crossRatioDist` does not see the direction. -/

/-- **The chord bound of Theorem 2.1 is symmetric in `T₁` and `T₂`.**

`Arlib.crossRatioDist_comm` needs `u ≠ v` and both points in `K`; disjointness gives the first
and the two `⊆ K` hypotheses give the second.  Note that `thm21_of_localization` does not itself
require `T₁ ⊆ K` or `T₂ ⊆ K`, but the `hIso` binder does, so nothing is added to the caller. -/
theorem chord_bound_comm {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3) :
    ∀ u ∈ T₂, ∀ v ∈ T₁, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3 := by
  rintro u hu v hv x hx ⟨r, hr⟩
  have hne : v ≠ u := by
    rintro rfl
    exact (Set.disjoint_left.mp hdisj hv) hu
  have hkey := hchord v hv u hu x hx ⟨1 - r, by
    rw [AffineMap.lineMap_apply_one_sub]; exact hr⟩
  rwa [crossRatioDist_comm hKb hne (hT₁K hv) (hT₂K hu)] at hkey

/-! ## Gap 2: the smaller piece has relative mass at most `1/2` -/

/-- **Two disjoint measurable subsets of `K` cannot both have more than half its volume.**

This is what discharges `Arlib.thm21_of_localization`'s hypothesis `A ≤ 1/2` once the WLOG of
Gap 1 has arranged for `A` to be the *smaller* of the two relative masses.  Without the WLOG the
hypothesis is unavailable, and indeed false when `T₁` is the larger piece. -/
theorem two_mul_min_measure_le {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hT₂ : MeasurableSet T₂) (hT₁K : T₁ ⊆ K) (hT₂K : T₂ ⊆ K) (hdisj : Disjoint T₁ T₂) :
    2 * min (volume T₁) (volume T₂) ≤ volume K := by
  have hunion : volume T₁ + volume T₂ = volume (T₁ ∪ T₂) := (measure_union hdisj hT₂).symm
  have hle : volume (T₁ ∪ T₂) ≤ volume K := measure_mono (Set.union_subset hT₁K hT₂K)
  calc 2 * min (volume T₁) (volume T₂)
      = min (volume T₁) (volume T₂) + min (volume T₁) (volume T₂) := by
        rw [two_mul]
    _ ≤ volume T₁ + volume T₂ := by gcongr <;> [exact min_le_left _ _; exact min_le_right _ _]
    _ = volume (T₁ ∪ T₂) := hunion
    _ ≤ volume K := hle

/-! ## Gap 3: the two normalisation lemmas

Both are unconditional bookkeeping about `Arlib.uniformOn`; neither mentions Theorem 2.1. -/

/-- **Division by a fixed scalar commutes with `min`** in `ℝ≥0∞`.  This is what turns
`min (π T₁) (π T₂)` — a min of two ratios — into `min (vol T₁) (vol T₂) / vol K`, so that the
source theorem's scalar `A` can be read off the numerator. -/
theorem min_div_div (a b c : ℝ≥0∞) : min (a / c) (b / c) = min a b / c := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, min_eq_left (by gcongr)]
  · rw [min_eq_right hab, min_eq_right (by gcongr)]

/-- **The `ℝ≥0∞` integral against `uniformOn volume K`, in terms of the Bochner integral over
`K`.**  `uniformOn volume K = (volume K)⁻¹ • volume.restrict K` by `Arlib.uniformOn_def`, so the
normalisation is a single scalar; the ℝ↔ℝ≥0∞ passage is
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, which is where integrability and
nonnegativity are spent. -/
theorem lintegral_ofReal_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hInt : IntegrableOn h K volume)
    (hh0 : ∀ x, 0 ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K))
      = (volume K)⁻¹ * ENNReal.ofReal (∫ x in K, h x) := by
  rw [uniformOn_def, lintegral_smul_measure, smul_eq_mul,
    ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hh0)]

/-! ## The bridge, for measurable `h`

The hypothesis `hthm21` is the conclusion of `Arlib.thm21_of_localization`, universally
quantified over the data it must be applied to.  It carries a `Measurable g` binder, which
makes it *weaker* — and therefore easier to supply: `thm21_of_localization` needs no
measurability, so a caller holding the Localization Lemma discharges `hthm21` by

    fun g U₁ U₂ _ hU₁ hU₂ hdisj hg0 hg3 hchord A hA0 hA hmass =>
      thm21_of_localization hKb hU₁ hU₂ hdisj hg0 hg3 hchord hA0 hA hmass (hloc …)

with the measurability argument simply ignored. -/

/-- **The `hIso` conclusion for measurable `h`**, from Theorem 2.1's conclusion.

All three gaps are closed here.  Gap 1 is the `rcases le_total (volume T₁) (volume T₂)`: in the
second branch the roles of `T₁` and `T₂` are exchanged, which is legitimate by
`Arlib.chord_bound_comm` (the chord hypothesis), `Disjoint.symm`, and `sdiff_sdiff_comm` (the
conclusion's set).  Gap 2 is `Arlib.two_mul_min_measure_le`, applied *after* the branch has made
`A` the smaller relative mass.  Gap 3 is `Arlib.lintegral_ofReal_uniformOn`,
`Arlib.uniformOn_apply` and `Arlib.min_div_div`, plus the `(volume K)⁻¹` bookkeeping at the end —
where exactly **one** factor of `volume K` survives, absorbed into `A`. -/
theorem hIso_measurable_of_thm21 {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hthm21 : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
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
  -- finiteness bookkeeping
  have hQsub : (K \ T₁) \ T₂ ⊆ K := Set.sdiff_subset.trans Set.sdiff_subset
  have hQm : MeasurableSet ((K \ T₁) \ T₂) := (hKm.diff hT₁).diff hT₂
  have hT₁top : volume T₁ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₁K)
  have hT₂top : volume T₂ ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hT₂K)
  have hQtop : volume ((K \ T₁) \ T₂) ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hQsub)
  have hVR : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
  have hVR0 : (volume K).toReal ≠ 0 := hVR.ne'
  -- `h` is integrable on `K`: it is bounded by `1/3` there and `K` has finite volume
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKtop.lt_top⟩
  have hInt : IntegrableOn h K volume := by
    refine Integrable.mono' (integrable_const (1 / 3 : ℝ)) hhm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hKm]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
    exact hh3 x hx
  -- the ℝ → ℝ≥0∞ passage, shared by the two branches
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
  -- the key inequality, before normalisation: one factor of `volume K` survives
  have key : ENNReal.ofReal (∫ x in K, h x) * min (volume T₁) (volume T₂)
      ≤ volume ((K \ T₁) \ T₂) * volume K := by
    have hhalf := two_mul_min_measure_le hT₂ hT₁K hT₂K hdisj
    rcases le_total (volume T₁) (volume T₂) with hmin | hmin
    · -- `T₁` is the smaller piece: apply Theorem 2.1 as it stands
      have hminEq : min (volume T₁) (volume T₂) = volume T₁ := min_eq_left hmin
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
        (hthm21 h T₁ T₂ hhm hT₁ hT₂ hdisj hh0 hh3 hchord _ hA0 hAhalf hmass)
    · -- `T₂` is the smaller piece: swap the two, which `chord_bound_comm` licenses
      have hminEq : min (volume T₁) (volume T₂) = volume T₂ := min_eq_right hmin
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
      have hswap := hthm21 h T₂ T₁ hhm hT₂ hT₁ hdisj.symm hh0 hh3
        (chord_bound_comm hKb hT₁K hT₂K hdisj hchord) _ hA0 hAhalf hmass
      rw [show (K \ T₂) \ T₁ = (K \ T₁) \ T₂ from _root_.sdiff_sdiff_comm] at hswap
      exact conv T₂ hT₂top hswap
  -- normalisation: the `(volume K)⁻¹` bookkeeping
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

/-! ## The bridge, for arbitrary `h`: the `hIso` binder itself

`hIso` places no measurability clause on `h`, so `hIso_measurable_of_thm21` cannot be handed to
`conductance_hitAndRun_ge` by `exact`.  The clause is removed by approximation from below:
Mathlib defines `∫⁻` as the supremum of the integrals of its simple minorants
(`MeasureTheory.lintegral_eq_nnreal`), and each of `hIso`'s hypotheses on `h` — `0 ≤ h`,
`h ≤ 1/3` on `K`, and the chord bound — is an *upper* bound on `h`, hence is inherited by every
minorant.  So the measurable case applies to each minorant `x ↦ (φ x : ℝ)` and the general case
is the supremum. -/

/-- **The `hIso` binder of `Arlib.MarkovChains.conductance_hitAndRun_ge`, proved from
Theorem 2.1's conclusion.**  Stated verbatim in the binder's own hypothesis order, so that it
discharges the binder by `exact`.

The only mathematical input is `hthm21`; `hKb`, `hKm`, `hK0`, `hKtop` are the structural facts
about `K` that the source theorem and the `uniformOn` normalisation need, and all four are
available at the `conductance_hitAndRun_ge` call site (see
`Arlib.conductance_hitAndRun_ge_of_thm21`).

**This is not a proof that `hIso` is true.**  `Arlib.not_hIso_two` refutes `hIso` at `n = 2`,
`K = [0,4]²` *without* the clause `∀ x ∈ K, h x ≤ 1/3`; the clause is present here, in both
`hthm21` and the conclusion, exactly as in the corrected binder.  What is proved is one
implication: the ℝ≥0∞-valued, `uniformOn`-normalised, `min`-parameterised encoding **follows
from** the ℝ-valued, Lebesgue-normalised, `A`-parameterised one.  The converse is not proved
here, and is not immediate: `hmassK` pins `A` to `U₁`, and when `U₁` is the larger piece the
`min`-form is strictly the weaker statement. -/
theorem hIso_of_thm21 {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hthm21 : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
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
  -- the measurable case, applied to an arbitrary simple minorant of `ofReal ∘ h`
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
    have hcore := hIso_measurable_of_thm21 (h := fun x => ((φ x : ℝ≥0) : ℝ)) hKb hKm hK0 hKtop
      hthm21 (measurable_coe_nnreal_real.comp φ.measurable)
      (fun x => (φ x).coe_nonneg) (fun x hx => (hgh x).trans (hh3 x hx))
      hT₁ hT₂ hT₁K hT₂K hdisj
      (fun u hu v hv x hx hex => (hgh x).trans (hchord u hu v hv x hx hex))
    have heq : (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (uniformOn volume K)
        = ∫⁻ x, ENNReal.ofReal ((φ x : ℝ≥0) : ℝ) ∂(uniformOn volume K) := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      exact lintegral_congr fun x => by simp
    rw [heq]
    exact hcore
  -- and the supremum over minorants
  rcases eq_or_ne (min (uniformOn volume K T₁) (uniformOn volume K T₂)) 0 with hm0 | hm0
  · rw [hm0, mul_zero]
    exact zero_le
  · rw [← ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inr (measure_ne_top _ _)),
      lintegral_eq_nnreal]
    refine iSup₂_le fun φ hφ => ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inr (measure_ne_top _ _))]
    exact main φ hφ

/-! ## The payoff: Theorem 4.2 with `hIso` traded for Theorem 2.1

`Arlib.MarkovChains.conductance_hitAndRun_ge` carries two mathematical binders, `hLem41` (the
paper's Lemma 4.1) and `hIso`.  Below, `hIso` is replaced by `hthm21`; `hLem41` is carried
verbatim, since another agent owns it.  `volume K ≠ 0` and `volume K ≠ ⊤` are *derived* from the
inball `hball` and the boundedness `hKb`, so they are not extra hypotheses. -/

open MarkovChains in
/-- **Theorem 4.2 of Lovász–Vempala, with `hIso` replaced by Theorem 2.1's conclusion.**

Residual binders: `hLem41` and `hthm21`.  The second is the ℝ-valued, Lebesgue-normalised form
that `Arlib.thm21_of_localization` proves from the Localization Lemma, so the moment that
localization work lands this theorem is one `exact` away from carrying only `hLem41`.

The trade is exactly `Arlib.hIso_of_thm21` and nothing else. -/
theorem conductance_hitAndRun_ge_of_thm21 (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hthm21 : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
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
    (hIso_of_thm21 hKb hKm hK0 hKtop hthm21)

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration of this file, plus the two upstream results it rests on, must report exactly
`[propext, Classical.choice, Quot.sound]`.  The upstream two are listed deliberately: this
file's claim is about what they say, so it checks that both are clean rather than taking their
own files' word for it.

`#print axioms` cannot see `∀`-binders in a type.  In words: `hIso_of_thm21` assumes `hthm21`
and the four structural facts about `K`; `conductance_hitAndRun_ge_of_thm21` assumes `hthm21`
and `hLem41`.  Neither claims that Theorem 2.1 is true — `Arlib.not_hIso_two` shows the
uncorrected form is false — only that the `hIso` encoding follows from the `hthm21` encoding. -/

section AxiomCheck

#print axioms thm21_of_localization
#print axioms crossRatioDist_comm

#print axioms chord_bound_comm
#print axioms two_mul_min_measure_le
#print axioms min_div_div
#print axioms lintegral_ofReal_uniformOn
#print axioms hIso_measurable_of_thm21
#print axioms hIso_of_thm21
#print axioms conductance_hitAndRun_ge_of_thm21

end AxiomCheck

end Arlib
