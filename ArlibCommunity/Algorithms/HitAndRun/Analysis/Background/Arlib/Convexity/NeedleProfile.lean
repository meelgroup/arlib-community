/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLimit

/-!
# (G2) reduced: a concave profile already suffices, and the weak-convergence step, proved

`Arlib.Convexity.LocalizationLimit` recorded gap **(G2)** — the limit passage of the
Lovász–Simonovits localisation argument — as having two residual pieces:

> *(i)* the **weak-convergence statement**
> `lim (1/vol Cₖ) ∫_{Cₖ} f = ∫ G(t)^m f(a + t(b-a)) dt`; and
> *(ii)* a **concave-to-affine reduction**, made necessary (it said) by
> `Arlib.exists_convex_slice_profile_not_affine`, which shows sharp Brunn–Minkowski pins the
> limit profile down only to a *concave* `G`, not an affine one.

**This file closes (i) and shows that (ii) is not needed.**

## 1. Piece (ii) is not load-bearing

Every one-dimensional consumer of a needle in this repository takes as input *log-concavity of
the needle density* — that is the explicit contract of `Arlib.logConcaveOn_needleDensity`
("precisely the hypothesis that every one-dimensional lemma downstream consumes"), and of
`Arlib.IsLogConcave.comp_needleMap` in `Arlib.Convexity.Isoperimetry`.  Affineness of `ℓ` is
used only to *establish* that log-concavity, via `Arlib.logConcaveOn_needleWeight`.

But a nonnegative concave function is log-concave (`Arlib.logConcaveOn_of_concaveOn`), so a
nonnegative power of one is too:

* `Arlib.logConcaveOn_rpow_of_concaveOn`, `Arlib.logConcaveOn_pow_of_concaveOn`;
* `Arlib.logConcaveOn_concaveNeedleDensity` — the needle density `t ↦ G t ^ k · f(a + t·v)` is
  log-concave on `[0,1]` for **any** nonnegative concave `G`, not just an affine one;
* `Arlib.logConcaveOn_needleDensity_of_concaveNeedle` — and `Arlib.logConcaveOn_needleDensity`
  is the special case `G t = (1-t)p + tq`, so nothing is lost.

Consequence: the *concave* form of the Localization Lemma — the same statement with `ℓ(t)^{n-1}`
replaced by `G(t)^{n-1}` for a nonnegative concave `G` — feeds every downstream consumer exactly
as the affine form does.  `Arlib.exists_convex_slice_profile_not_affine` remains true, and
remains a correct refutation of "sharp Brunn identifies the profile as a power of an affine
function"; it simply refutes a step that nothing in this development needs.

## 2. Piece (i), proved

The weak-convergence statement is proved here, in coordinates in which the needle is the first
coordinate axis of `ℝ^(m+1)` (a general needle is carried to this position by an affine change of
variables; that reduction is *not* formalised here — see §3).

* `Arlib.setIntegral_eq_integral_slice` — Fubini along the first coordinate, transported from
  `MeasureTheory.volume_preserving_piFinSuccAbove` through the `Fin.cons` coordinates.
* `Arlib.measurable_volume_slice` — the slice-volume profile `t ↦ vol (slice K t)` is a
  measurable function of the height.
* `Arlib.integral_volume_slice` — it integrates to `vol K`, so the **normalised** profile is a
  probability density on the height axis.
* `Arlib.abs_setIntegral_sub_slice_profile_le` — **the thin-tube comparison.**  If `f` varies by
  at most `δ` between a point of `K` and the point of the axis at the same height, then
  `|∫_K f − ∫ vol(slice K t)·f(axis t) dt| ≤ δ · vol K`.  This is the *only* place transverse
  thinness — the corrected target of (G1), see `Arlib.Convexity.NeedleLimit` — is consumed.  No
  convexity is used.
* `Arlib.tendsto_average_setIntegral_of_profile` — **the limit passage.**  For measurable bodies
  `C k` of finite positive volume in the unit slab, a bounded measurable `f`, transverse
  thinness `δ k → 0`, and normalised slice profiles converging pointwise to `W` and uniformly
  bounded by `B`, the normalised integrals `(∫_{C k} f)/vol(C k)` converge to the needle integral
  `∫ W(t)·f(axis t) dt`.
* `Arlib.tendsto_average_setIntegral_of_profile_unitCube` — a non-vacuity witness: every
  hypothesis of the previous theorem holds simultaneously, with nonzero volumes and a nonzero
  limit.

`Arlib.concaveOn_limit_slice_profile` (in `Arlib.Convexity.LocalizationLimit`) is the companion
fact that `W ^ (1/m)` is concave when the `C k` are convex; combined with §1, the limit measure
that comes out is *exactly* of the form a downstream one-dimensional lemma accepts.

## 3. What (G2) still needs, stated exactly

**(G2a) and (G2b) are now proved**, in `Arlib.Convexity.ConcaveSelection`.  Only (G2c) is
left of (G2).  The two paragraphs below are kept because their *content* is still accurate —
what changed is that each is now a theorem rather than a hypothesis.

**(G2a) Pointwise convergence of the normalised profiles (a Helly selection).**  Given convex
bodies `C k` in the unit slab, extract a subsequence along which
`t ↦ vol (slice (C k) t)/vol (C k)` converges pointwise.  By `Arlib.brunn_slice_concaveOn` the
`1/m`-th powers of these profiles are concave, so this is Helly selection for a uniformly
bounded sequence of concave functions on `[0,1]` — a diagonal argument on `ℚ ∩ [0,1]` plus the
local Lipschitz bound of a concave function.  **Mathlib `v4.32` has no Helly selection theorem
— that remains true**, and every `helly` in Mathlib is the *convex-geometry* Helly theorem
(`Analysis/Convex/Radon.lean`); its Arzelà–Ascoli is compactness-of-closure only, never a
sequence statement (`Topology/UniformSpace/Ascoli.lean`, whose own TODO says so).  So it is
proved by hand in `Arlib.exists_subseq_tendsto_normalised_slice_profile`, as Arzelà–Ascoli on
the *profiles* rather than Blaschke selection on the *bodies*.  That theorem needs two
hypotheses beyond the list here — `hsfin` (each slice has finite volume, required by
`brunn_slice_concaveOn`) and `hspan` (the bodies span the slab) — both recorded there.

**(G2b) A uniform bound `B` on the normalised profiles.**  This is elementary and is the one
place convexity would enter the limit passage: if `u ≥ 0` is concave on `[0,1]` with maximum at
`t₀`, then `u ≥ u(t₀)/2` on a subinterval of length `≥ 1/4`, so `∫₀¹ u^m ≥ u(t₀)^m/(4·2^m)`;
with `∫₀¹ u^m = 1` (`Arlib.integral_volume_slice`) this gives a bound.  **Proved** as
`Arlib.normalised_volume_slice_le`, at the better constant **`2^(m+1)`** — and the prediction
in this paragraph was right about the obstruction: `ConcaveOn` alone does not give
measurability of `u`, so it is threaded through the measurable slice profile.  The anticipated
case split on which side of `1/2` the maximum falls turned out to be unnecessary.

**(G2c) The affine change of coordinates.**  Everything above is stated with the needle along
the first coordinate axis and the slab `{x | x 0 ∈ [0,1]}`.  Transporting a general segment
`[a,b] ⊆ ℝⁿ` to that position is **not** the routine change of variables this paragraph once
claimed.  It needs `Measure.addHaar_preimage_linearMap` for `volume` on `Fin n → ℝ` *and* a
compatible statement for the `(n−1)`-dimensional **slice** volumes — a factorisation of the
determinant into first-coordinate scaling times transverse determinant, so that Fubini in the
rotated frame lines up with `Arlib.setIntegral_eq_integral_slice`.  The transverse factor
cancels in the *normalised* profile, but that cancellation still has to be proved.  A separate
development, not a small finish.

Note also that the thin-tube comparison consumes a **modulus-of-continuity** hypothesis on `f`
(the inline `hδ`), not lower semicontinuity.  For a continuous `f` on a compact tube it is
supplied by uniform continuity; the Lovász–Simonovits statement for merely lower semicontinuous
integrable `f` needs an extra approximation step that is **not** carried out here.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` at all — only theorems
proved outright.  Nothing below asserts the Localization Lemma, Blaschke selection, Helly
selection, or a profile-convergence property; the one undischarged ingredient (G2c)
appears only as inline `∀`-hypotheses of
`Arlib.tendsto_average_setIntegral_of_profile`, and the non-vacuity witness
`Arlib.tendsto_average_setIntegral_of_profile_unitCube` shows they can be met.
-/

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Topology

namespace Arlib

/-! ### A concave profile already gives a log-concave needle density -/

section ConcaveProfile

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A nonnegative real power of a nonnegative concave function is log-concave. -/
theorem logConcaveOn_rpow_of_concaveOn {s : Set E} {G : E → ℝ} (hG : ConcaveOn ℝ s G)
    (hG₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ G x) {c : ℝ} (hc : 0 ≤ c) :
    LogConcaveOn s (fun x => G x ^ c) :=
  (logConcaveOn_of_concaveOn hG hG₀).rpow hG₀ hc

/-- A natural power of a nonnegative concave function is log-concave. -/
theorem logConcaveOn_pow_of_concaveOn {s : Set E} {G : E → ℝ} (hG : ConcaveOn ℝ s G)
    (hG₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ G x) (k : ℕ) :
    LogConcaveOn s (fun x => G x ^ k) := by
  have h := logConcaveOn_rpow_of_concaveOn hG hG₀ (c := (k : ℝ)) (Nat.cast_nonneg k)
  have he : (fun x => G x ^ (k : ℝ)) = fun x => G x ^ k := by
    funext x; rw [Real.rpow_natCast]
  rwa [he] at h

end ConcaveProfile

section ConcaveNeedle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **A needle carrying a `k`-th power of a *concave* profile still has a log-concave density.**

This is `Arlib.logConcaveOn_needleDensity` with the affine weight `((1-t)p + tq)^k` replaced by
`G t ^ k` for an arbitrary nonnegative concave `G`. -/
theorem logConcaveOn_concaveNeedleDensity {f : E → ℝ} (hf : IsLogConcave f) (hf₀ : ∀ x, 0 ≤ f x)
    {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Icc (0:ℝ) 1) G) (hG₀ : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ G t) (k : ℕ)
    (a v : E) :
    LogConcaveOn (Icc (0:ℝ) 1) (fun t => G t ^ k * f (needleMap a v t)) :=
  LogConcaveOn.mul (logConcaveOn_pow_of_concaveOn hG (fun _ ht => hG₀ _ ht) k)
    ((hf.comp_needleMap a v).logConcaveOn (convex_Icc 0 1))
    (fun t ht => pow_nonneg (hG₀ t ht) k) (fun _ _ => hf₀ _)

/-- The affine needle weight is the special case `G t = (1-t)p + tq`, so
`Arlib.logConcaveOn_needleDensity` is recovered from
`Arlib.logConcaveOn_concaveNeedleDensity`. -/
theorem logConcaveOn_needleDensity_of_concaveNeedle {f : E → ℝ} (hf : IsLogConcave f)
    (hf₀ : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) (a v : E) :
    LogConcaveOn (Icc (0:ℝ) 1) (fun t => needleWeight p q k t * f (needleMap a v t)) :=
  logConcaveOn_concaveNeedleDensity hf hf₀ (concaveOn_affine_interp p q)
    (fun _ ht => affine_interp_nonneg hp hq ht) k a v

end ConcaveNeedle

/-! ### Fubini along the needle axis -/

section Fubini

variable {m : ℕ}

/-- Fubini for a set integral, cutting off the first coordinate: the integral of `f` over
`K ⊆ ℝ^(m+1)` is the integral over heights `t` of the integrals of `f` over the slices. -/
theorem setIntegral_eq_integral_slice {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K)
    {f : (Fin (m + 1) → ℝ) → ℝ} (hf : IntegrableOn f K) :
    ∫ x in K, f x = ∫ t : ℝ, ∫ y in slice K t, f (Fin.cons t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e.symm (volume : Measure (ℝ × (Fin m → ℝ))) volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hsymm : ∀ p : ℝ × (Fin m → ℝ), e.symm p = (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ) := by
    intro p
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    rfl
  have hindic : Integrable (K.indicator f) := (integrable_indicator_iff hK).mpr hf
  have hint : Integrable (fun p : ℝ × (Fin m → ℝ) => K.indicator f (e.symm p)) volume :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr hindic
  have hcons : ∀ (t : ℝ) (y : Fin m → ℝ),
      K.indicator f (Fin.cons t y : Fin (m + 1) → ℝ)
        = (slice K t).indicator (fun y => f (Fin.cons t y)) y := by
    intro t y
    by_cases hy : (Fin.cons t y : Fin (m + 1) → ℝ) ∈ K
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ slice K t from hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ slice K t from hy)]
  calc ∫ x in K, f x = ∫ x, K.indicator f x := (integral_indicator hK).symm
    _ = ∫ p : ℝ × (Fin m → ℝ), K.indicator f (e.symm p) := (hmp.integral_comp' _).symm
    _ = ∫ t : ℝ, ∫ y : Fin m → ℝ, K.indicator f (e.symm (t, y)) := by
        rw [Measure.volume_eq_prod]
        exact integral_prod _ (by rwa [← Measure.volume_eq_prod])
    _ = ∫ t : ℝ, ∫ y in slice K t, f (Fin.cons t y) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        have hpt : ∀ y : Fin m → ℝ, K.indicator f (e.symm (t, y))
            = (slice K t).indicator (fun y => f (Fin.cons t y)) y := by
          intro y; rw [hsymm]; exact hcons t y
        simp only [hpt]
        exact integral_indicator (measurableSet_slice hK t)

/-- The axis value of `f` at height `t`, i.e. `f` evaluated at the point of the first coordinate
axis with first coordinate `t`. -/
private theorem measurable_axis {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Measurable f) :
    Measurable fun x : Fin (m + 1) → ℝ => f (Fin.cons (x 0) (0 : Fin m → ℝ)) := by
  have h1 : Measurable fun t : ℝ => (Fin.cons t (0 : Fin m → ℝ) : Fin (m + 1) → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]; exact measurable_id'
    · intro j; simp only [Fin.cons_succ]; exact measurable_const
  exact hf.comp (h1.comp (measurable_pi_apply 0))

/-- The integral of the *axis* profile: `∫_K f(axis(x 0)) dx = ∫ vol(slice K t) · f(axis t) dt`. -/
theorem setIntegral_axis_eq_integral_slice_volume {K : Set (Fin (m + 1) → ℝ)}
    (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤) {f : (Fin (m + 1) → ℝ) → ℝ}
    (hfm : Measurable f) {M : ℝ} (hM : ∀ x ∈ K, |f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ M) :
    ∫ x in K, f (Fin.cons (x 0) (0 : Fin m → ℝ))
      = ∫ t : ℝ, (volume (slice K t)).toReal * f (Fin.cons t (0 : Fin m → ℝ)) := by
  have hint : IntegrableOn (fun x : Fin (m + 1) → ℝ => f (Fin.cons (x 0) (0 : Fin m → ℝ))) K :=
    Measure.integrableOn_of_bounded hKfin (measurable_axis hfm).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem hK] with x hx
        simpa [Real.norm_eq_abs] using hM x hx)
  rw [setIntegral_eq_integral_slice hK hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hcongr : ∀ y : Fin m → ℝ,
      f (Fin.cons ((Fin.cons t y : Fin (m + 1) → ℝ) 0) (0 : Fin m → ℝ))
        = f (Fin.cons t (0 : Fin m → ℝ)) := by
    intro y; simp
  simp only [hcongr]
  rw [setIntegral_const, smul_eq_mul, Measure.real]

/-- **The thin-tube comparison — the analytic core of the weak-convergence step of (G2).**

If `f` varies by at most `δ` between a point of `K` and the point of the first-coordinate axis
at the same height, then the integral of `f` over `K` differs from the *needle integral*
`∫ vol(slice K t) · f(axis t) dt` by at most `δ · vol K`.

Dividing by `vol K`, this says: for bodies that are transversally thin to within `δ`-variation
of `f`, the normalised integral over the body agrees with the integral against the slice-volume
profile along the axis.  **This is the step at which transverse thinness — the output of (G1),
`Arlib.Convexity.NeedleLimit`'s corrected target — is consumed, and it is the only place it is
consumed.**  No convexity is used. -/
theorem abs_setIntegral_sub_slice_profile_le {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K)
    (hKfin : volume K ≠ ⊤) {f : (Fin (m + 1) → ℝ) → ℝ} (hfm : Measurable f) {M δ : ℝ}
    (hM : ∀ x ∈ K, |f x| ≤ M)
    (hδ : ∀ x ∈ K, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ) :
    |(∫ x in K, f x) - ∫ t : ℝ, (volume (slice K t)).toReal * f (Fin.cons t (0 : Fin m → ℝ))|
      ≤ δ * (volume K).toReal := by
  have hMax : ∀ x ∈ K, |f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ M + δ := by
    intro x hx
    have h1 := hM x hx
    have h2 := hδ x hx
    have := abs_sub_abs_le_abs_sub (f x) (f (Fin.cons (x 0) (0 : Fin m → ℝ)))
    cases abs_cases (f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))) with
    | inl h => cases abs_cases (f x) with
      | inl h' => rw [abs_le]; constructor <;> linarith [abs_nonneg (f x)]
      | inr h' => rw [abs_le]; constructor <;> linarith [abs_nonneg (f x)]
    | inr h => cases abs_cases (f x) with
      | inl h' => rw [abs_le]; constructor <;> linarith [abs_nonneg (f x)]
      | inr h' => rw [abs_le]; constructor <;> linarith [abs_nonneg (f x)]
  have hf : IntegrableOn f K :=
    Measure.integrableOn_of_bounded hKfin hfm.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem hK] with x hx
        simpa [Real.norm_eq_abs] using hM x hx)
  have hF : IntegrableOn (fun x : Fin (m + 1) → ℝ => f (Fin.cons (x 0) (0 : Fin m → ℝ))) K :=
    Measure.integrableOn_of_bounded hKfin (measurable_axis hfm).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem hK] with x hx
        simpa [Real.norm_eq_abs] using hMax x hx)
  rw [← setIntegral_axis_eq_integral_slice_volume hK hKfin hfm hMax, ← integral_sub hf hF]
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin (m + 1) → ℝ)))
    (s := K) (f := fun x => f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))) (C := δ)
    (lt_top_iff_ne_top.mpr hKfin) (by simpa [Real.norm_eq_abs] using hδ)
  simpa [Real.norm_eq_abs, Measure.real, mul_comm] using this

/-- The map `t ↦ (t, 0, …, 0)` onto the first coordinate axis is measurable. -/
theorem measurable_consAxis (m : ℕ) :
    Measurable fun t : ℝ => (Fin.cons t (0 : Fin m → ℝ) : Fin (m + 1) → ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]; exact measurable_id'
  · intro j; simp only [Fin.cons_succ]; exact measurable_const

/-- **The slice-volume profile of a measurable set is a measurable function of the height.**
Transported from `MeasureTheory.measurable_measure_prodMk_left` through the `Fin.cons`
coordinates. -/
theorem measurable_volume_slice {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K) :
    Measurable fun t : ℝ => volume (slice K t) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hsymm : ∀ p : ℝ × (Fin m → ℝ), e.symm p = (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ) := by
    intro p
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    rfl
  have hs : MeasurableSet ((fun p : ℝ × (Fin m → ℝ) => e.symm p) ⁻¹' K) :=
    e.symm.measurable hK
  have h : Measurable fun t : ℝ => (volume : Measure (Fin m → ℝ))
      (Prod.mk t ⁻¹' ((fun p : ℝ × (Fin m → ℝ) => e.symm p) ⁻¹' K)) :=
    measurable_measure_prodMk_left hs
  have hset : ∀ t : ℝ, (Prod.mk t ⁻¹' ((fun p : ℝ × (Fin m → ℝ) => e.symm p) ⁻¹' K))
      = slice K t := by
    intro t
    ext y
    simp only [Set.mem_preimage, hsymm]
    rfl
  simpa only [hset] using h

/-- The real-valued slice-volume profile is measurable. -/
theorem measurable_volume_slice_toReal {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K) :
    Measurable fun t : ℝ => (volume (slice K t)).toReal :=
  ENNReal.measurable_toReal.comp (measurable_volume_slice hK)

/-- **The slice-volume profile integrates to the volume.**  Hence the *normalised* profile
`t ↦ vol (slice K t) / vol K` is a probability density on the height axis. -/
theorem integral_volume_slice {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K)
    (hKfin : volume K ≠ ⊤) :
    ∫ t : ℝ, (volume (slice K t)).toReal = (volume K).toReal := by
  have h := setIntegral_axis_eq_integral_slice_volume (K := K) hK hKfin
    (f := fun _ => (1:ℝ)) measurable_const (M := 1) (fun _ _ => by norm_num)
  simp only [mul_one] at h
  rw [← h, setIntegral_const, smul_eq_mul, mul_one, Measure.real]

end Fubini

/-! ### The limit passage -/

section Limit

variable {m : ℕ}

/-- **The weak-convergence step of (G2), proved.**

Let `C k` be measurable bodies of finite positive volume, all contained in the unit slab
`{x | x 0 ∈ [0,1]}`, and let `f` be a bounded measurable function.  Suppose

* (*transverse thinness, the interface with (G1)*) `f` varies by at most `δ k` between a point
  of `C k` and the point of the first-coordinate axis at the same height, with `δ k → 0`;
* (*profile convergence*) the **normalised** slice-volume profiles
  `t ↦ vol (slice (C k) t) / vol (C k)` converge pointwise to `W`, and are uniformly bounded
  by `B`.

Then the normalised integrals of `f` over `C k` converge to the needle integral
`∫ W t · f(axis t) dt`.

`Arlib.concaveOn_limit_slice_profile` supplies the extra information that `W ^ (1/m)` is
concave whenever it is a limit of *convex* bodies' profiles; nothing here needs convexity.

Both hypotheses on the profiles are inline `∀`-hypotheses, not a named `Prop` — and both are
now **discharged**: see `Arlib.exists_subseq_tendsto_average_setIntegral'`, which is this
theorem with the profile hypotheses removed.

Worth noting why the endpoints cause no trouble, since they are the classical difficulty for
concave functions: this theorem consumes `hlim` **only** through
`tendsto_integral_of_dominated_convergence`, so it needs pointwise convergence plus a uniform
bound and never continuity or uniform convergence of the limit `W`.  The limit may well be
discontinuous at `0` and `1`; nothing here cares.  (And `0`, `1` are rational, so the
diagonal extraction over `ℚ` pins them for free.) -/
theorem tendsto_average_setIntegral_of_profile
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hCm : ∀ k, MeasurableSet (C k))
    (hCfin : ∀ k, volume (C k) ≠ ⊤) (hCpos : ∀ k, 0 < volume (C k))
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0:ℝ) 1)
    {f : (Fin (m + 1) → ℝ) → ℝ} (hfm : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {δ : ℕ → ℝ} (hδ : ∀ k, ∀ x ∈ C k, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0)) {W : ℝ → ℝ} {B : ℝ}
    (hB : ∀ k, ∀ t : ℝ, (volume (slice (C k) t)).toReal / (volume (C k)).toReal ≤ B)
    (hlim : ∀ t : ℝ, Tendsto
      (fun k => (volume (slice (C k) t)).toReal / (volume (C k)).toReal) atTop (𝓝 (W t))) :
    Tendsto (fun k => (∫ x in C k, f x) / (volume (C k)).toReal) atTop
      (𝓝 (∫ t : ℝ, W t * f (Fin.cons t (0 : Fin m → ℝ)))) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hVpos : ∀ k, 0 < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  -- the profile vanishes off the slab
  have hoff : ∀ k, ∀ t : ℝ, t ∉ Icc (0:ℝ) 1 → volume (slice (C k) t) = 0 := by
    intro k t ht
    have : slice (C k) t = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y hy => ht ?_
      simpa using hslab k _ hy
    rw [this, measure_empty]
  have hB0 : (0 : ℝ) ≤ B := by
    have h := hB 0 2
    have hz : (volume (slice (C 0) 2)).toReal / (volume (C 0)).toReal = 0 := by
      rw [hoff 0 2 (by norm_num)]; simp
    rwa [hz] at h
  set g : ℕ → ℝ → ℝ := fun k t =>
    (volume (slice (C k) t)).toReal / (volume (C k)).toReal
      * f (Fin.cons t (0 : Fin m → ℝ)) with hg
  -- Step 1: the thin-tube comparison, normalised
  have hstep1 : ∀ k, |(∫ x in C k, f x) / (volume (C k)).toReal - ∫ t : ℝ, g k t| ≤ δ k := by
    intro k
    have hA := abs_setIntegral_sub_slice_profile_le (hCm k) (hCfin k) hfm
      (M := M) (fun x _ => hM x) (hδ k)
    have hgint : (∫ t : ℝ, g k t)
        = (∫ t : ℝ, (volume (slice (C k) t)).toReal * f (Fin.cons t (0 : Fin m → ℝ)))
          / (volume (C k)).toReal := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun t => by rw [hg]; ring)
    rw [hgint, div_sub_div_same, abs_div, abs_of_pos (hVpos k), div_le_iff₀ (hVpos k)]
    calc |(∫ x in C k, f x)
            - ∫ t : ℝ, (volume (slice (C k) t)).toReal * f (Fin.cons t (0 : Fin m → ℝ))|
        ≤ δ k * (volume (C k)).toReal := hA
      _ = δ k * (volume (C k)).toReal := rfl
  -- Step 2: dominated convergence for the profile integrals
  have hmeas : ∀ k, AEStronglyMeasurable (g k) (volume : Measure ℝ) := by
    intro k
    exact (((measurable_volume_slice_toReal (hCm k)).div_const _).mul
      (hfm.comp (measurable_consAxis m))).aestronglyMeasurable
  have hbound : Integrable ((Icc (0:ℝ) 1).indicator fun _ => B * M) (volume : Measure ℝ) := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hdom : ∀ k, ∀ᵐ t : ℝ, ‖g k t‖ ≤ (Icc (0:ℝ) 1).indicator (fun _ => B * M) t := by
    intro k
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem ht, hg]
      have hw0 : 0 ≤ (volume (slice (C k) t)).toReal / (volume (C k)).toReal :=
        div_nonneg ENNReal.toReal_nonneg (hVpos k).le
      calc ‖(volume (slice (C k) t)).toReal / (volume (C k)).toReal
              * f (Fin.cons t (0 : Fin m → ℝ))‖
          = ((volume (slice (C k) t)).toReal / (volume (C k)).toReal)
              * |f (Fin.cons t (0 : Fin m → ℝ))| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
        _ ≤ B * M := mul_le_mul (hB k t) (hM _) (abs_nonneg _) hB0
    · rw [Set.indicator_of_notMem ht, hg]
      have : (volume (slice (C k) t)).toReal = 0 := by rw [hoff k t ht]; simp
      simp [this]
  have hptlim : ∀ᵐ t : ℝ, Tendsto (fun k => g k t) atTop
      (𝓝 (W t * f (Fin.cons t (0 : Fin m → ℝ)))) :=
    Eventually.of_forall fun t => (hlim t).mul_const _
  have hstep2 : Tendsto (fun k => ∫ t : ℝ, g k t) atTop
      (𝓝 (∫ t : ℝ, W t * f (Fin.cons t (0 : Fin m → ℝ)))) :=
    tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hptlim
  -- Step 3: combine
  have hstep3 : Tendsto
      (fun k => (∫ x in C k, f x) / (volume (C k)).toReal - ∫ t : ℝ, g k t) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa [Real.norm_eq_abs] using hstep1 k) hδ0
  have := hstep3.add hstep2
  simpa using this

/-! ### Non-vacuity

`Arlib.tendsto_average_setIntegral_of_profile` bundles seven hypotheses; the following witness
checks that they can hold **simultaneously**, with nonzero volumes and a nonzero limit, so the
theorem is not a statement about an empty configuration. -/

/-- **Non-vacuity of `Arlib.tendsto_average_setIntegral_of_profile`.**

The constant sequence `C k = [0,1]^(m+1)` with `f = 1` meets every hypothesis (`δ = 0`,
`B = 1`, `W = 1_{[0,1]}`), and the conclusion it yields is the true statement that the
normalised integral, which is `1` for every `k`, converges to `∫ 1_{[0,1]} = 1`. -/
theorem tendsto_average_setIntegral_of_profile_unitCube (m : ℕ) :
    Tendsto (fun _ : ℕ => (∫ _x in (Set.univ.pi fun _ : Fin (m + 1) => Icc (0:ℝ) 1), (1:ℝ))
        / (volume (Set.univ.pi fun _ : Fin (m + 1) => Icc (0:ℝ) 1)).toReal) atTop
      (𝓝 (∫ t : ℝ, (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) t * (1:ℝ))) := by
  set Q : Set (Fin (m + 1) → ℝ) := Set.univ.pi fun _ => Icc (0:ℝ) 1 with hQ
  have hQm : MeasurableSet Q := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hQvol : volume Q = 1 := by rw [hQ, volume_pi_pi]; simp [Real.volume_Icc]
  have hslice_mem : ∀ t ∈ Icc (0:ℝ) 1,
      slice Q t = Set.univ.pi fun _ : Fin m => Icc (0:ℝ) 1 := by
    intro t ht
    ext y
    simp only [mem_slice, hQ, Set.mem_univ_pi]
    constructor
    · intro h j; simpa using h j.succ
    · intro h i
      refine Fin.cases ?_ ?_ i
      · simpa using ht
      · intro j; simpa using h j
  have hslice_not : ∀ t : ℝ, t ∉ Icc (0:ℝ) 1 → slice Q t = ∅ := by
    intro t ht
    refine Set.eq_empty_of_forall_notMem fun y hy => ht ?_
    have h := (Set.mem_univ_pi.mp (show (Fin.cons t y : Fin (m + 1) → ℝ) ∈ Q from hy)) 0
    simpa using h
  have hprofile : ∀ t : ℝ, (volume (slice Q t)).toReal / (volume Q).toReal
      = (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ Icc (0:ℝ) 1
    · rw [hslice_mem t ht, Set.indicator_of_mem ht, hQvol, volume_pi_pi]
      simp [Real.volume_Icc]
    · rw [hslice_not t ht, Set.indicator_of_notMem ht, hQvol]
      simp
  refine tendsto_average_setIntegral_of_profile (C := fun _ => Q) (fun _ => hQm)
    (fun _ => by rw [hQvol]; exact ENNReal.one_ne_top) (fun _ => by rw [hQvol]; exact zero_lt_one)
    (fun _ x hx => Set.mem_univ_pi.mp hx 0) (f := fun _ => (1:ℝ)) measurable_const
    (M := 1) (fun _ => by norm_num) (δ := fun _ => 0) (fun _ x _ => by norm_num)
    tendsto_const_nhds (B := 1) (fun _ t => ?_) (fun t => ?_)
  · rw [hprofile t]
    by_cases ht : t ∈ Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]; norm_num
  · simpa only [hprofile] using tendsto_const_nhds

end Limit

end Arlib

/-! ### Axiom check -/

#print axioms Arlib.logConcaveOn_rpow_of_concaveOn
#print axioms Arlib.logConcaveOn_pow_of_concaveOn
#print axioms Arlib.logConcaveOn_concaveNeedleDensity
#print axioms Arlib.logConcaveOn_needleDensity_of_concaveNeedle
#print axioms Arlib.setIntegral_eq_integral_slice
#print axioms Arlib.setIntegral_axis_eq_integral_slice_volume
#print axioms Arlib.abs_setIntegral_sub_slice_profile_le
#print axioms Arlib.measurable_consAxis
#print axioms Arlib.measurable_volume_slice
#print axioms Arlib.measurable_volume_slice_toReal
#print axioms Arlib.integral_volume_slice
#print axioms Arlib.tendsto_average_setIntegral_of_profile
#print axioms Arlib.tendsto_average_setIntegral_of_profile_unitCube
