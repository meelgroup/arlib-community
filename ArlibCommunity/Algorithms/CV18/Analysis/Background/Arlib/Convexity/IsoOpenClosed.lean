/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationMeasurable
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLSC
import ArlibCommunity.External.Kr25.Arlib.Convexity.GaussianCooling.IndicatorVariance

/-!
# `thm:iso` with **no** localization binder, for `S₁, S₂` open and `S₃` closed

`Arlib.gaussianRestricted_isoperimetry_of_localization`
(`Arlib/Convexity/HlocFromLocalization.lean:882`) proves Cousins–Vempala's `thm:iso` from a single
residual binder `hLoc`, the Localization Lemma applied to `g₁ = 1_{S₁}h − A·h` and
`g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h` for **merely measurable** `S₁, S₂, S₃`.  That binder cannot be
discharged by any almost-everywhere argument: `Arlib.exists_null_measurableSet_needleIntegral_eq_one`
(`Arlib/Convexity/LocalizationMeasurable.lean:442`) exhibits a *null* measurable `S` with an
admissible profile whose needle mass is `1`, so `L¹` density, Lusin, Vitali–Carathéodory and every
in-measure regularisation are dead, and `Arlib.exists_transverse_oscillation_eq_one` kills the
"weaken `Continuous` to `Measurable`" route.

This file takes the remaining route: **restrict the topology and discharge the binder outright.**

## Main results

* `Arlib.exists_compact_body_continuous_pair` — the crux.  For `S₁, S₂` open, `S₃` closed and `h`
  continuous, bounded, integrable, it builds a compact convex body `K` and a **continuous** pair
  `g₁, g₂` with `∫_K g₁ = 0` *exactly*, `ε·vol K < ∫_K g₂`, the nondegeneracy `g₁ x = 0 → g₂ x < ε`,
  and `g₁ ≤ 1_{S₁}h − A·h`, `g₂ ≤ (d/σ)A·1_{S₂}h − 1_{S₃}h` pointwise.
* `Arlib.exists_needle_openClosed` — **the localization binder, proved.**  The needle comes from
  `Arlib.exists_needle_of_compact_convex`; the two conclusions transport back to the indicator
  integrands by `Arlib.needleIntegral_mono`.
* `Arlib.hloc_gt_of_localization_ge`, `Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim`
  — `Arlib.hloc_ge_of_localization_ge` and
  `Arlib.gaussianRestricted_isoperimetry_concave_of_oneDim` copied with the binder's first
  antecedent **strict**; proofs unchanged apart from the closing contradiction, which becomes
  `Arlib.needle_masses_contradiction_ge'`.
* `Arlib.gaussianRestricted_isoperimetry_openClosed` — **the capstone.**  `thm:iso` at the sharp
  constant `d/σ` and the same threshold `2√3·d`, with **no residual binder of any kind**, for
  `S₁, S₂` open, `S₃` closed and `h` continuous and bounded.
* `Arlib.gaussianRestricted_isoperimetry_openClosed_witness` — non-vacuity: the standard Gaussian
  and a slab partition satisfy every hypothesis with a strictly positive left-hand side.
* `Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement` — the reduction of the
  measurable case, *given* disjoint open enlargements that keep the separation hypothesis.
* `Arlib.exists_separated_no_disjoint_open_enlargement` — **the obstruction**: data satisfying
  every hypothesis of the measurable `thm:iso`, with a strictly positive left-hand side, for which
  **no** disjoint open enlargement of `S₁, S₂` exists at all.

## How the `η`-slack is avoided

`Arlib.Convexity.LocalizationLSC` reaches lower semicontinuous integrands but pays, in the
*equality* slot, an additive re-centring constant `κ ∈ [0, η]` chosen **before** the needle
(`Arlib.exists_needle_of_lowerSemicontinuous_pair`), and that slack cannot be sent to `0` at a
fixed needle.  Here it is not paid at all.  The minorant `φ` of `1_{S₁}h` is nonnegative, so it can
be **scaled** rather than shifted: `g₁ := s·φ − A·h` with the *scalar*
`s = A·∫_K h / ∫_K φ ∈ (0,1)` has `∫_K g₁ = 0` exactly and is still `≤ 1_{S₁}h − A·h` pointwise.

The price is that the binder's antecedent must be **strict**, `A·∫h < ∫_{S₁}h`, since `∫_K φ`
must exceed `A·∫_K h` on a compact `K`.  That price is zero at the point of use: the consumer
chooses `A` itself, and applies the binder at `A = A₀ − ρ` with `A₀ = ∫_{S₁}h/∫h`, `ρ` small
enough that the second antecedent — strict already — survives.  The closing contradiction
(`Arlib.needle_masses_contradiction_ge'`) is insensitive to which constant is used, provided the
same one appears in both needle facts.  This is where the `≥`-form finding of
`Arlib/Convexity/HlocFromLocalization.lean` is spent: the equality slot is never needed.

## What is assumed

**Nothing.**  No `def`, `structure`, `class` or named `Prop` below asserts the Localization Lemma,
`thm:iso`, or any part of either, and no theorem below takes any of them as a hypothesis.  The
capstone's hypotheses are geometry, analysis and topology of the data.  The two copied theorems are
copies of results already proved in this repository, with a strictly weaker hypothesis; the
copying is forced only by the one-agent-per-file discipline.

## What remains for the general measurable case

The reduction "replace `S₁, S₂` by open `εd`-neighbourhoods, `S₃` by the complementary closed set"
does **not** work in general, and `Arlib.exists_separated_no_disjoint_open_enlargement` is the
machine-checked reason: the separation hypothesis is a *disjunction*, and its density branch
`4(d/σ)√n ≤ d_h(u,v)` is satisfied at **distance zero** wherever `h` vanishes — `d_h(u,v) = 1`
whenever exactly one of `h u, h v` is `0`.  So `S₁` and `S₂` may touch, and then no open supersets
of them are disjoint, let alone `εd`-close ones.  Only the metric branch degrades gracefully from
`d` to `d(1−2ε)`.

Two further gaps, recorded honestly: the capstone also needs `h` **continuous and bounded**, which
the measurable statement does not assume, and the touching set lies in `{h = 0}`, which has
`h`-measure zero but positive Lebesgue measure — so it cannot be discarded by a measure-theoretic
argument either (needle integrals see Lebesgue-null sets:
`Arlib.exists_null_measurableSet_needleIntegral_eq_one`).
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

namespace Arlib

/-! ### Exhausting the space by balls -/

section Exhaustion

variable {n : ℕ}

/-- **A large ball eventually carries more than any strictly smaller amount than the total.**

The exhaustion `⋃ k, closedBall 0 k = univ` together with
`MeasureTheory.tendsto_setIntegral_of_monotone`.  Stated as an `Eventually` so that finitely many
such requirements can be met by one radius; the integrand is *not* assumed nonnegative, so a
plain `∃` would not be intersectable. -/
theorem eventually_setIntegral_closedBall_gt {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Integrable g) {c : ℝ} (hc : c < ∫ x, g x) :
    ∀ᶠ R : ℕ in atTop, c < ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), g x := by
  have hmono : Monotone fun k : ℕ => closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ) :=
    fun i j hij => closedBall_subset_closedBall (by exact_mod_cast hij)
  have hunion : (⋃ k : ℕ, closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ)) = Set.univ :=
    iUnion_closedBall_nat 0
  have hlim := tendsto_setIntegral_of_monotone (μ := volume)
    (fun _ : ℕ => measurableSet_closedBall) hmono (by rw [hunion]; exact hg.integrableOn)
  rw [hunion, Measure.restrict_univ] at hlim
  exact (tendsto_order.mp hlim).1 c hc

end Exhaustion

/-! ### The compact body and the continuous pair -/

section ContinuousPair

variable {n : ℕ}

/-- **The data `Arlib.exists_needle_of_compact_convex` consumes, built from an open/closed
partition.**

Given `S₁, S₂` open, `S₃` closed, `h` continuous nonnegative bounded integrable, and a constant
`A > 0` with

* `A · ∫h < ∫_{S₁}h`  (**strictly** — this is what buys the exact equality below), and
* `∫_{S₃}h < (d/σ)·A·∫_{S₂}h`,

this produces a compact convex body `K` and a **continuous** bounded integrable pair `g₁, g₂`
with `∫_K g₁ = 0` *exactly*, `ε·vol K < ∫_K g₂`, the nondegeneracy `g₁ x = 0 → g₂ x < ε`, and —
the two clauses that carry the conclusion back — the pointwise dominations

  `g₁ ≤ 1_{S₁}h − A·h`,  `g₂ ≤ (d/σ)A·1_{S₂}h − 1_{S₃}h`.

Both dominations are in the direction the needle conclusions need: the equality slot's conclusion
`∫W·g₁∘γ = 0` becomes `A·∫W·h∘γ ≤ ∫W·1_{S₁}h∘γ`, and the positivity slot's conclusion is
monotone increasing in the integrand.

**How the exact equality is obtained without an `η`-slack.**  `g₁ := s·φ − A·h` where `φ` is a
Lipschitz minorant of `1_{S₁}h` (nonnegative, `≤ 1_{S₁}h`) and `s ∈ (0,1)` is the *scalar*
`A·∫_K h / ∫_K φ`.  Scaling a nonnegative minorant down keeps it a minorant, so no additive
re-centring — and hence no `η`-slack of the kind
`Arlib.exists_needle_of_lowerSemicontinuous_pair` must carry — is needed.  This is exactly where
the strict hypothesis `A·∫h < ∫_{S₁}h` is spent: it is what makes `∫_K φ > A·∫_K h` achievable,
i.e. `s < 1`. -/
theorem exists_compact_body_continuous_pair {σ d A B : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh0 : ∀ x, 0 ≤ h x) (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₃ : IsClosed S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃)
    (hA : 0 < A) (hdσ : 0 ≤ d / σ)
    (hone : A * (∫ x, h x) < ∫ x in S₁, h x)
    (htwo : (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ) (M ε : ℝ),
      IsCompact K ∧ Convex ℝ K ∧ Continuous g₁ ∧ Continuous g₂ ∧
      Integrable g₁ ∧ Integrable g₂ ∧ (∀ x, |g₁ x| ≤ M) ∧ (∀ x, |g₂ x| ≤ M) ∧
      (∫ x in K, g₁ x) = 0 ∧ 0 < ε ∧ ε * (volume K).toReal < ∫ x in K, g₂ x ∧
      (∀ x, g₁ x = 0 → g₂ x < ε) ∧
      (∀ x, g₁ x ≤ S₁.indicator h x - A * h x) ∧
      (∀ x, g₂ x ≤ d / σ * A * S₂.indicator h x - S₃.indicator h x) ∧
      (∀ x, |S₁.indicator h x - A * h x| ≤ M) ∧
      (∀ x, |d / σ * A * S₂.indicator h x - S₃.indicator h x| ≤ M) := by
  classical
  set c : ℝ := d / σ * A with hcdef
  have hc0 : 0 ≤ c := mul_nonneg hdσ hA.le
  have hB0 : (0 : ℝ) ≤ B := le_trans (hh0 0) (hhB 0)
  -- elementary facts about the three indicators
  have hind0 : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (x), 0 ≤ S.indicator h x :=
    fun S x => Set.indicator_nonneg (fun a _ => hh0 a) x
  have hindle : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (x), S.indicator h x ≤ h x := by
    intro S x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; exact hh0 x
  have hindi : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      Integrable (S.indicator h) := fun S hS => hhi.indicator hS
  -- the two lower semicontinuous integrands
  set F₁ : EuclideanSpace ℝ (Fin n) → ℝ := S₁.indicator h with hF₁def
  set G₂ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => c * S₂.indicator h x - S₃.indicator h x with hG₂def
  have hF₁lsc : LowerSemicontinuous F₁ := lowerSemicontinuous_indicator_of_isOpen hS₁ hhc hh0
  have hG₂lsc : LowerSemicontinuous G₂ :=
    lowerSemicontinuous_smul_indicator_sub_indicator hS₂ hS₃ hhc hh0 hc0
  have hF₁abs : ∀ x, |F₁ x| ≤ B := fun x =>
    abs_le.mpr ⟨by linarith [hind0 S₁ x, hB0], le_trans (hindle S₁ x) (hhB x)⟩
  have hG₂abs : ∀ x, |G₂ x| ≤ (c + 1) * B := by
    intro x
    have h1 : G₂ x ≤ c * h x := by
      have := hind0 S₃ x
      have := mul_le_mul_of_nonneg_left (hindle S₂ x) hc0
      simp only [hG₂def]; linarith
    have h2 : -h x ≤ G₂ x := by
      have := mul_nonneg hc0 (hind0 S₂ x)
      have := hindle S₃ x
      simp only [hG₂def]; linarith
    have hexp : (c + 1) * B = c * B + B := by ring
    have hcB : 0 ≤ c * B := mul_nonneg hc0 hB0
    have hch : c * h x ≤ c * B := mul_le_mul_of_nonneg_left (hhB x) hc0
    have h3 : c * h x ≤ (c + 1) * B := by linarith [hhB x]
    have h4 : h x ≤ (c + 1) * B := by linarith [hhB x]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hF₁i : Integrable F₁ := hindi S₁ hS₁.measurableSet
  have hG₂i : Integrable G₂ :=
    ((hindi S₂ hS₂.measurableSet).const_mul c).sub (hindi S₃ hS₃.measurableSet)
  -- their total masses
  have hF₁tot : (∫ x, F₁ x) = ∫ x in S₁, h x := integral_indicator hS₁.measurableSet
  have hG₂tot : (∫ x, G₂ x) = c * (∫ x in S₂, h x) - ∫ x in S₃, h x := by
    rw [hG₂def, integral_sub ((hindi S₂ hS₂.measurableSet).const_mul c)
      (hindi S₃ hS₃.measurableSet), integral_const_mul, integral_indicator hS₂.measurableSet,
      integral_indicator hS₃.measurableSet]
  -- a radius meeting both requirements at once
  have hev₁ : ∀ᶠ R : ℕ in atTop,
      A * (∫ x, h x) < ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), F₁ x :=
    eventually_setIntegral_closedBall_gt hF₁i (by rw [hF₁tot]; exact hone)
  have hev₂ : ∀ᶠ R : ℕ in atTop,
      (0 : ℝ) < ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), G₂ x :=
    eventually_setIntegral_closedBall_gt hG₂i (by rw [hG₂tot]; linarith)
  obtain ⟨R, ⟨hR₁, hR₂⟩, hR⟩ := ((hev₁.and hev₂).and (eventually_ge_atTop 1)).exists
  set K : Set (EuclideanSpace ℝ (Fin n)) := closedBall (0 : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    with hKdef
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hR
  have hKcomp : IsCompact K := isCompact_closedBall _ _
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKfin : volume K ≠ ⊤ := hKcomp.measure_lt_top.ne
  have hKvol : 0 < volume K :=
    lt_of_lt_of_le (measure_ball_pos volume 0 hRpos) (measure_mono ball_subset_closedBall)
  have hKreal : (0 : ℝ) < (volume K).toReal := ENNReal.toReal_pos hKvol.ne' hKfin
  -- everything bounded is integrable on `K`
  have hIK : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), AEStronglyMeasurable f volume →
      ∀ {C : ℝ}, (∀ x, |f x| ≤ C) → IntegrableOn f K volume := by
    intro f hf C hC
    exact Measure.integrableOn_of_bounded hKfin hf
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hhK : IntegrableOn h K volume := hhi.integrableOn
  have hF₁K : IntegrableOn F₁ K volume := hF₁i.integrableOn
  -- `∫_K h > 0`, and the strict inequality that makes the scaling work
  have hAK : A * (∫ x in K, h x) < ∫ x in K, F₁ x := by
    refine lt_of_le_of_lt ?_ hR₁
    have : (∫ x in K, h x) ≤ ∫ x, h x :=
      setIntegral_le_integral hhi (Eventually.of_forall hh0)
    exact mul_le_mul_of_nonneg_left this hA.le
  have hKh0 : 0 < ∫ x in K, h x := by
    have h1 : (∫ x in K, F₁ x) ≤ ∫ x in K, h x :=
      integral_mono hF₁K hhK fun x => hindle S₁ x
    have h2 : (0 : ℝ) ≤ ∫ x in K, h x := setIntegral_nonneg measurableSet_closedBall fun x _ => hh0 x
    nlinarith
  -- the Lipschitz minorant of `1_{S₁}h`, scaled so that its `K`-mass is exactly `A · ∫_K h`
  have hlim₁ := tendsto_setIntegral_lipschitzMinorant (μ := volume) (K := K) hKfin hF₁lsc hF₁abs
  obtain ⟨N, hN⟩ := ((tendsto_order.mp hlim₁).1 (A * ∫ x in K, h x) hAK).exists
  set φ : EuclideanSpace ℝ (Fin n) → ℝ := lipschitzMinorant F₁ N with hφdef
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => le_lipschitzMinorant (fun y => hind0 S₁ y) N x
  have hφle : ∀ x, φ x ≤ F₁ x := fun x => lipschitzMinorant_le (fun y => hind0 S₁ y) N x
  have hφc : Continuous φ := continuous_lipschitzMinorant (fun y => hind0 S₁ y) N
  have hφh : ∀ x, φ x ≤ h x := fun x => le_trans (hφle x) (hindle S₁ x)
  have hφabs : ∀ x, |φ x| ≤ B := fun x =>
    abs_le.mpr ⟨by linarith [hφ0 x, hB0], le_trans (hφh x) (hhB x)⟩
  have hφK : IntegrableOn φ K volume := hIK φ hφc.aestronglyMeasurable hφabs
  have hφpos : 0 < ∫ x in K, φ x := lt_of_le_of_lt (mul_nonneg hA.le hKh0.le) hN
  set s : ℝ := A * (∫ x in K, h x) / ∫ x in K, φ x with hsdef
  have hs0 : 0 < s := div_pos (mul_pos hA hKh0) hφpos
  have hs1 : s < 1 := (div_lt_one hφpos).mpr hN
  set g₁ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => s * φ x - A * h x with hg₁def
  have hg₁c : Continuous g₁ := (continuous_const.mul hφc).sub (continuous_const.mul hhc)
  have hsφ : ∀ x, s * φ x ≤ φ x := fun x => mul_le_of_le_one_left (hφ0 x) hs1.le
  have hsφ0 : ∀ x, 0 ≤ s * φ x := fun x => mul_nonneg hs0.le (hφ0 x)
  have hg₁dom : ∀ x, g₁ x ≤ S₁.indicator h x - A * h x := by
    intro x
    have h2 : φ x ≤ S₁.indicator h x := hφle x
    have h1 := hsφ x
    simp only [hg₁def]; linarith
  have hg₁abs : ∀ x, |g₁ x| ≤ (1 + A) * B := by
    intro x
    have h1 := hsφ0 x
    have h2 : s * φ x ≤ h x := le_trans (hsφ x) (hφh x)
    have h3 : 0 ≤ A * h x := mul_nonneg hA.le (hh0 x)
    have h5 : A * h x ≤ A * B := mul_le_mul_of_nonneg_left (hhB x) hA.le
    have hAB : 0 ≤ A * B := mul_nonneg hA.le hB0
    have hexp : (1 + A) * B = B + A * B := by ring
    have h4 : h x ≤ B := hhB x
    simp only [hg₁def]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hg₁i : Integrable g₁ := by
    refine Integrable.mono' (hhi.const_mul (1 + A)) hg₁c.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := hsφ0 x
    have h2 : s * φ x ≤ h x := le_trans (hsφ x) (hφh x)
    have h3 : 0 ≤ A * h x := mul_nonneg hA.le (hh0 x)
    have hexp : (1 + A) * h x = h x + A * h x := by ring
    simp only [hg₁def, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hg₁zero : (∫ x in K, g₁ x) = 0 := by
    rw [hg₁def, integral_sub (hφK.const_mul s) (hhK.const_mul A), integral_const_mul,
      integral_const_mul, hsdef]
    field_simp
    ring
  -- the Lipschitz minorant of `g₂`, clamped below by `−h` so that it stays integrable
  obtain ⟨f₂, hf₂c, hf₂le, hf₂abs, hf₂pos⟩ :=
    exists_continuous_le_setIntegral_pos (μ := volume) hKfin hG₂lsc hG₂abs hR₂
  set g₂ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => max (f₂ x) (-h x) with hg₂def
  have hg₂c : Continuous g₂ := hf₂c.max hhc.neg
  have hg₂dom : ∀ x, g₂ x ≤ G₂ x := by
    intro x
    refine max_le (hf₂le x) ?_
    have := mul_nonneg hc0 (hind0 S₂ x)
    have := hindle S₃ x
    simp only [hG₂def]; linarith
  have hg₂ge : ∀ x, -h x ≤ g₂ x := fun x => le_max_right _ _
  have hg₂abs : ∀ x, |g₂ x| ≤ (c + 1) * B := by
    intro x
    have h1 : g₂ x ≤ (c + 1) * B := le_trans (hg₂dom x) (abs_le.mp (hG₂abs x)).2
    have h2 : -((c + 1) * B) ≤ g₂ x := by
      have := hg₂ge x
      have hexp : (c + 1) * B = c * B + B := by ring
      have hcB : 0 ≤ c * B := mul_nonneg hc0 hB0
      have h3 : h x ≤ (c + 1) * B := by linarith [hhB x]
      linarith
    exact abs_le.mpr ⟨h2, h1⟩
  have hg₂i : Integrable g₂ := by
    refine Integrable.mono' (hhi.const_mul (c + 1)) hg₂c.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 : g₂ x ≤ c * h x := le_trans (hg₂dom x) (by
      have := mul_le_mul_of_nonneg_left (hindle S₂ x) hc0
      have := hind0 S₃ x
      simp only [hG₂def]; linarith)
    have h2 : -h x ≤ g₂ x := hg₂ge x
    have hexp : (c + 1) * h x = c * h x + h x := by ring
    have hch : 0 ≤ c * h x := mul_nonneg hc0 (hh0 x)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hh0 x], by linarith [hh0 x]⟩
  have hg₂K : IntegrableOn g₂ K volume := hIK g₂ hg₂c.aestronglyMeasurable hg₂abs
  have hf₂K : IntegrableOn f₂ K volume := hIK f₂ hf₂c.aestronglyMeasurable hf₂abs
  have hg₂pos : 0 < ∫ x in K, g₂ x :=
    lt_of_lt_of_le hf₂pos (integral_mono hf₂K hg₂K fun x => le_max_left _ _)
  -- the nondegeneracy constant
  set ε : ℝ := (∫ x in K, g₂ x) / (2 * (volume K).toReal) with hεdef
  have hεpos : 0 < ε := div_pos hg₂pos (by linarith)
  have hεK : ε * (volume K).toReal < ∫ x in K, g₂ x := by
    rw [hεdef, div_mul_eq_mul_div, mul_comm (2 : ℝ) ((volume K).toReal), ← div_div,
      mul_div_assoc, div_self hKreal.ne', mul_one]
    linarith
  -- `g₁ x = 0` forces `g₂ x ≤ 0`: either `h x = 0`, or `x ∈ S₁` and both other indicators vanish
  have hsep : ∀ x, g₁ x = 0 → g₂ x < ε := by
    intro x hx
    refine lt_of_le_of_lt ?_ hεpos
    refine le_trans (hg₂dom x) ?_
    rcases eq_or_lt_of_le (hh0 x) with hzero | hpos
    · have hφx : φ x = 0 := le_antisymm (le_trans (hφh x) (le_of_eq hzero.symm)) (hφ0 x)
      have h2 : S₂.indicator h x ≤ 0 := le_trans (hindle S₂ x) (le_of_eq hzero.symm)
      have h3 : 0 ≤ S₃.indicator h x := hind0 S₃ x
      have := mul_le_mul_of_nonneg_left h2 hc0
      simp only [hG₂def]; linarith
    · have hφx : 0 < φ x := by
        simp only [hg₁def] at hx
        have heq : s * φ x = A * h x := by linarith
        have hAh : 0 < A * h x := mul_pos hA hpos
        by_contra hle
        push Not at hle
        have hnp : s * φ x ≤ s * 0 := mul_le_mul_of_nonneg_left hle hs0.le
        rw [mul_zero] at hnp
        linarith
      have hmem : x ∈ S₁ := by
        by_contra hnot
        have : F₁ x = 0 := Set.indicator_of_notMem hnot h
        linarith [hφle x]
      have h2 : S₂.indicator h x = 0 :=
        Set.indicator_of_notMem (Set.disjoint_left.mp h12 hmem) h
      have h3 : S₃.indicator h x = 0 :=
        Set.indicator_of_notMem (Set.disjoint_left.mp h13 hmem) h
      simp only [hG₂def, h2, h3]; simp
  -- the two model integrands are bounded by the same constant
  have hG₁abs : ∀ x, |S₁.indicator h x - A * h x| ≤ (1 + A) * B := by
    intro x
    have h1 := hind0 S₁ x
    have h2 := hindle S₁ x
    have h3 : 0 ≤ A * h x := mul_nonneg hA.le (hh0 x)
    have h5 : A * h x ≤ A * B := mul_le_mul_of_nonneg_left (hhB x) hA.le
    have hAB : 0 ≤ A * B := mul_nonneg hA.le hB0
    have hexp : (1 + A) * B = B + A * B := by ring
    have h4 : h x ≤ B := hhB x
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨K, g₁, g₂, max ((1 + A) * B) ((c + 1) * B), ε, hKcomp, hKconv, hg₁c, hg₂c, hg₁i, hg₂i,
    fun x => le_trans (hg₁abs x) (le_max_left _ _),
    fun x => le_trans (hg₂abs x) (le_max_right _ _), hg₁zero, hεpos, hεK, hsep, hg₁dom, hg₂dom,
    fun x => le_trans (hG₁abs x) (le_max_left _ _),
    fun x => le_trans (hG₂abs x) (le_max_right _ _)⟩

end ContinuousPair

/-! ### The Localization Lemma, discharged for an open/closed partition -/

section Needle

variable {n : ℕ}

/-- **The localization binder of `thm:iso`, proved outright for `S₁, S₂` open and `S₃` closed.**

This is the raw shape `Arlib.hloc_ge_of_localization_ge` consumes — un-normalised direction
`v ≠ 0`, profile concave only after the `(n−1)`-st root and only on `Ioo 0 1`, full-line
integrals — with the *equality* slot weakened to `≥`, which is all
`Arlib.needle_masses_contradiction_ge` needs.

It is a **theorem, not a hypothesis**: the needle comes from
`Arlib.exists_needle_of_compact_convex`, applied to the continuous pair of
`Arlib.exists_compact_body_continuous_pair`, and the two conclusions are transported back to the
indicator integrands by `Arlib.needleIntegral_mono` — both dominations point the right way.

The price of dropping the localization binder is exactly three hypotheses: `S₁, S₂` **open**,
`S₃` **closed**, and `h` **continuous and bounded**.  The first three are what make the two
integrands lower semicontinuous, hence approximable from below by continuous ones
(`Arlib.Convexity.LocalizationLSC`); the last is what makes those approximants exist at all and
keeps the needle mass of `h` integrable.  `Arlib.exists_null_measurableSet_needleIntegral_eq_one`
shows the topological hypotheses cannot be removed by any almost-everywhere argument.

The antecedent on `S₁` is **strict** (`A·∫h < ∫_{S₁}h`).  That strictness is what pays for the
exact equality `∫_K g₁ = 0` on a *compact* body — see
`Arlib.exists_compact_body_continuous_pair` — and it costs the consumer nothing, because the
consumer applies the binder at a constant `A` of its own choosing. -/
theorem exists_needle_openClosed (hn : 2 ≤ n) {σ d A B : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh0 : ∀ x, 0 ≤ h x) (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₃ : IsClosed S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃)
    (hA : 0 < A) (hdσ : 0 ≤ d / σ)
    (hone : A * (∫ x, h x) < ∫ x in S₁, h x)
    (htwo : (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x) :
    ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
      v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
      Integrable (fun t => W t * h (needleMap b v t)) ∧
      A * (∫ t : ℝ, W t * h (needleMap b v t))
        ≤ ∫ t : ℝ, W t * S₁.indicator h (needleMap b v t) ∧
      0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
            - S₃.indicator h (needleMap b v t)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have hhabs : ∀ x, |h x| ≤ B := fun x => abs_le.mpr ⟨by linarith [hh0 x, hhB x, hh0 0, hhB 0],
    hhB x⟩
  obtain ⟨K, g₁, g₂, M, ε, hKcomp, hKconv, hg₁c, hg₂c, hg₁i, hg₂i, hM₁, hM₂, hzero, hεpos, hεK,
      hsep, hg₁dom, hg₂dom, hG₁abs, hG₂abs⟩ :=
    exists_compact_body_continuous_pair hh0 hhc hhB hhi hS₁ hS₂ hS₃ h12 h13 hA hdσ hone htwo
  obtain ⟨b, v, W, hv0, hW0, hWsupp, hWi, hWconc, hW₁, hW₂⟩ :=
    exists_needle_of_compact_convex hm hKcomp hKconv hg₁c hg₂c hg₁i hg₂i hM₁ hM₂ hzero hεpos hεK
      hsep
  set γ : ℝ → EuclideanSpace ℝ (Fin (m + 1)) := needleMap b v with hγdef
  have hγ : Measurable γ := (continuous_needleMap b v).measurable
  have hWint : Integrable fun t => W t * h (γ t) :=
    integrable_profile_mul hγ hWi hhc.measurable hhabs
  -- the two model integrands
  set G₁ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x => S₁.indicator h x - A * h x with hG₁def
  set G₂ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ :=
    fun x => d / σ * A * S₂.indicator h x - S₃.indicator h x with hG₂def
  have hG₁meas : Measurable G₁ :=
    (hhc.measurable.indicator hS₁.measurableSet).sub (measurable_const.mul hhc.measurable)
  have hG₂meas : Measurable G₂ :=
    (measurable_const.mul (hhc.measurable.indicator hS₂.measurableSet)).sub
      (hhc.measurable.indicator hS₃.measurableSet)
  -- transport the two needle conclusions along the pointwise dominations
  have hmono₁ : (∫ t : ℝ, W t * g₁ (γ t)) ≤ ∫ t : ℝ, W t * G₁ (γ t) :=
    needleIntegral_mono hγ hWi hW0 hg₁c.measurable hG₁meas hM₁ hG₁abs hg₁dom
  have hmono₂ : (∫ t : ℝ, W t * g₂ (γ t)) ≤ ∫ t : ℝ, W t * G₂ (γ t) :=
    needleIntegral_mono hγ hWi hW0 hg₂c.measurable hG₂meas hM₂ hG₂abs hg₂dom
  have hsplit : (∫ t : ℝ, W t * G₁ (γ t))
      = (∫ t : ℝ, W t * S₁.indicator h (γ t)) - A * ∫ t : ℝ, W t * h (γ t) := by
    have heq : (fun t => W t * G₁ (γ t))
        = fun t => W t * S₁.indicator h (γ t) - A * (W t * h (γ t)) := by
      funext t; simp only [hG₁def]; ring
    rw [heq, integral_sub (integrable_profile_mul_indicator_needle hWint hS₁.measurableSet)
      (hWint.const_mul A), integral_const_mul]
  have hexp : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) - 1) = 1 / (m : ℝ) := by push_cast; ring_nf
  refine ⟨b, v, W, hv0, hW0, hWsupp, ?_, hWint, ?_, ?_⟩
  · rw [hexp]; exact hWconc
  · have h0 : (0 : ℝ) ≤ ∫ t : ℝ, W t * G₁ (γ t) := by rw [← hW₁]; exact hmono₁
    rw [hsplit] at h0
    linarith
  · exact lt_of_lt_of_le hW₂ hmono₂

end Needle

/-! ### The same two reshapings, at a strict antecedent -/

section StrictShape

variable {n : ℕ}

/-- **`Arlib.hloc_ge_of_localization_ge` with the first antecedent strict.**

Identical to that theorem — same proof, line for line — except that the binder's first antecedent
and the corresponding antecedent of the conclusion read `A·∫h < ∫_{S₁}h` instead of `≤`.  The
proof passes that antecedent to `hLoc` opaquely, so nothing else changes.

The strict form is the one that can be **discharged**: `Arlib.exists_needle_openClosed` needs the
strict inequality to place an exact-mass compact body, and the consumer
(`Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim`) supplies it by applying the binder
at a constant slightly below `∫_{S₁}h / ∫h`.  The copy lives here because
`Arlib/Convexity/HlocFromLocalization.lean` is not edited by this file. -/
theorem hloc_gt_of_localization_ge (hn : 2 ≤ n) {σ d : ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hLoc : ∀ A : ℝ, 0 < A →
      A * (∫ x, h x) < ∫ x in S₁, h x →
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
      A * (∫ x, h x) < ∫ x in S₁, h x →
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

end StrictShape

/-! ### The consumer, at a strict antecedent and a `≥` equality slot -/

section StrictConsumer

variable {n : ℕ}

/-- **`Arlib.gaussianRestricted_isoperimetry_concave_of_oneDim` with `hloc` weakened twice over.**

Same theorem, same proof, with the localization binder changed in exactly two places:

* its first antecedent is `A·∫h < ∫_{S₁}h` (strict) instead of the equality `∫_{S₁}h = A·∫h`;
* its first conclusion is `A·I ≤ I₁` instead of the equality `I₁ = A·I`.

Both weakenings are free at the point of use.  `Arlib.needle_masses_contradiction_ge'`
(`Arlib/Convexity/HlocFromLocalization.lean:558`) closes the contradiction from `A·I ≤ I₁`, given
`0 ≤ I₂` and `0 ≤ I₃` — both immediate, the needle density being nonnegative — so the equality was
never needed.  And the antecedent may be strengthened to a strict inequality because the constant
`A` is chosen *by this proof*: it is applied at `A = A₀ − ρ` with `A₀ = ∫_{S₁}h / ∫h`, where `ρ`
is small enough that the second antecedent `∫_{S₃}h < (d/σ)A·∫_{S₂}h` — which is strict to begin
with — survives.  The closing contradiction is insensitive to which constant is used, provided the
same one appears in both needle facts, which it does.

Weakening the binder is what makes it **provable** rather than assumed: see
`Arlib.exists_needle_openClosed`. -/
theorem gaussianRestricted_isoperimetry_concave_gt_of_oneDim (hn : 0 < n) {σ d c₂ : ℝ} (hσ : 0 < σ)
    (hc₂ : 0 < c₂)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / c₂ ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v)
    -- **(L)** The Localization Lemma, with a **concave** profile; see the module docstring.
    (hloc : ∀ A : ℝ, 0 < A →
      A * (∫ x, h x) < ∫ x in S₁, h x →
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
              l t ^ (n - 1) * h (needleMap p e t))
    -- **(1d-2)** `vol3_journal.tex:501`, at coefficient `c₂/σ`.
    (h1d2 : ∀ (F : ℝ → ℝ) (t₀ α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ F t) → LogConcaveOn (Set.Icc α β) F →
      IntervalIntegrable (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β →
      c₂ / σ * (v - u) *
            ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
              (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
        ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hgauss : IsLogConcave
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :=
    isLogConcave_gaussian σ
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hhc : IsLogConcave h := by
    have he : h = fun x => f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := funext hh
    rw [he]
    exact IsLogConcave.mul hfc hgauss hf₀ fun _ => (Real.exp_pos _).le
  by_contra hcon
  push Not at hcon
  set M := ∫ x, h x with hM
  set m₁ := ∫ x in S₁, h x with hm₁def
  set m₂ := ∫ x in S₂, h x with hm₂def
  set m₃ := ∫ x in S₃, h x with hm₃def
  have hm₁ : 0 ≤ m₁ := integral_nonneg fun x => h0 x
  have hm₂ : 0 ≤ m₂ := integral_nonneg fun x => h0 x
  have hm₃ : 0 ≤ m₃ := integral_nonneg fun x => h0 x
  have hpos : 0 < d / σ * (m₁ * m₂) := lt_of_le_of_lt (mul_nonneg hmass.le hm₃) hcon
  have hdσ : 0 < d / σ := by
    rcases le_or_gt (d / σ) 0 with hle | hgt
    · exact absurd hpos (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hle (mul_nonneg hm₁ hm₂)))
    · exact hgt
  have hm₁pos : 0 < m₁ := by
    rcases eq_or_lt_of_le hm₁ with he | hlt
    · exfalso; rw [← he] at hpos; simp at hpos
    · exact hlt
  have hm₂pos : 0 < m₂ := by
    rcases eq_or_lt_of_le hm₂ with he | hlt
    · exfalso; rw [← he] at hpos; simp at hpos
    · exact hlt
  set A₀ := m₁ / M with hA₀
  have hA₀pos : 0 < A₀ := div_pos hm₁pos hmass
  have rel1 : m₁ = A₀ * M := (div_mul_cancel₀ m₁ hmass.ne').symm
  have rel2 : m₃ < d / σ * A₀ * m₂ := by
    have h' : M * m₃ < M * (d / σ * A₀ * m₂) := by
      have hrw : M * (d / σ * A₀ * m₂) = d / σ * (m₁ * m₂) := by
        rw [hA₀]; field_simp
      rw [hrw]; exact hcon
    exact lt_of_mul_lt_mul_left h' hmass.le
  -- The binder is applied at a constant `A` strictly below `A₀ = m₁/M`.  The second antecedent is
  -- strict, so a small enough decrease preserves it; the first antecedent then becomes strict,
  -- which is what a needle can be produced from.  The closing contradiction is insensitive to
  -- which constant is used, as long as the *same* one appears in both needle facts.
  have hq : 0 < d / σ * m₂ := mul_pos hdσ hm₂pos
  set ρ : ℝ := min (A₀ / 2) ((d / σ * A₀ * m₂ - m₃) / (2 * (d / σ * m₂))) with hρdef
  have hρhalf : ρ ≤ A₀ / 2 := by rw [hρdef]; exact min_le_left _ _
  have hρsmall : ρ ≤ (d / σ * A₀ * m₂ - m₃) / (2 * (d / σ * m₂)) := by
    rw [hρdef]; exact min_le_right _ _
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith) (div_pos (by linarith) (by linarith))
  set A := A₀ - ρ with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  have rel1' : A * M < m₁ := by
    have hexp : A * M = A₀ * M - ρ * M := by rw [hAdef]; ring
    have hρM : 0 < ρ * M := mul_pos hρpos hmass
    rw [hexp, ← rel1]
    linarith
  have rel2' : m₃ < d / σ * A * m₂ := by
    have hcancel : ∀ q X : ℝ, q ≠ 0 → q * (X / (2 * q)) = X / 2 := by
      intro q X hqq; field_simp
    have hstep : d / σ * m₂ * ρ ≤ (d / σ * A₀ * m₂ - m₃) / 2 := by
      have h2 := mul_le_mul_of_nonneg_left hρsmall hq.le
      calc d / σ * m₂ * ρ
          ≤ d / σ * m₂ * ((d / σ * A₀ * m₂ - m₃) / (2 * (d / σ * m₂))) := h2
        _ = (d / σ * A₀ * m₂ - m₃) / 2 := hcancel _ _ hq.ne'
    have hexp : d / σ * A * m₂ = d / σ * A₀ * m₂ - d / σ * m₂ * ρ := by rw [hAdef]; ring
    rw [hexp]; linarith
  -- localisation, with a concave profile
  obtain ⟨p, e, l, α, β, he1, hαβ, hlnn, hlc, hint, hZ1, hZ3⟩ := hloc A hApos rel1' rel2'
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := needleMap p e with hγ
  set D : ℝ → ℝ := fun t => l t ^ (n - 1) * h (γ t) with hD
  have hγc : Continuous γ := by
    rw [hγ]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t := fun t ht =>
    mul_nonneg (pow_nonneg (hlnn t ht) _) (h0 _)
  have hmZ1 : MeasurableSet (γ ⁻¹' S₁ ∩ Set.Icc α β) :=
    (hγc.measurable hS₁).inter measurableSet_Icc
  have hmZ2 : MeasurableSet (γ ⁻¹' S₂ ∩ Set.Icc α β) :=
    (hγc.measurable hS₂).inter measurableSet_Icc
  have hmZ3 : MeasurableSet (γ ⁻¹' S₃ ∩ Set.Icc α β) :=
    (hγc.measurable hS₃).inter measurableSet_Icc
  -- the induced three-way partition of the parameter interval
  have hpart' : IsPartition3 (Set.Icc α β) (γ ⁻¹' S₁ ∩ Set.Icc α β)
      (γ ⁻¹' S₂ ∩ Set.Icc α β) (γ ⁻¹' S₃ ∩ Set.Icc α β) := by
    have h1 := isPartition3_inter (T := Set.Icc α β) (hpart.preimage γ)
    rwa [Set.preimage_univ, Set.univ_inter] at h1
  -- the needle carries positive mass
  have hIccint : IntegrableOn D (Set.Icc α β) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hint
  have hZ3nn : 0 ≤ ∫ t in γ ⁻¹' S₃ ∩ Set.Icc α β, D t :=
    setIntegral_nonneg hmZ3 fun x hx => hD0 x hx.2
  have hZ2pos : 0 < ∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t := by
    rcases le_or_gt (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) 0 with hle | hgt
    · exact absurd hZ3 (not_lt.mpr (le_trans
        (mul_nonpos_of_nonneg_of_nonpos (mul_pos hdσ hApos).le hle) hZ3nn))
    · exact hgt
  have hIccle : (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) ≤ ∫ t in α..β, D t := by
    have h1 : (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) ≤ ∫ t in Set.Icc α β, D t :=
      setIntegral_mono_set hIccint
        (ae_restrict_of_forall_mem measurableSet_Icc hD0)
        (Set.inter_subset_right).eventuallyLE
    rwa [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc]
  have hIpos : 0 < ∫ t in α..β, D t := lt_of_lt_of_le hZ2pos hIccle
  -- the Gaussian factor along the needle, and the log-concave cofactor `F`
  set t₀ : ℝ := -(inner ℝ p e) with ht₀
  set K : ℝ := Real.exp (-(‖p‖ ^ 2 - (inner ℝ p e) ^ 2) / (2 * σ ^ 2)) with hK
  set F : ℝ → ℝ := fun t => K * (l t ^ (n - 1) * f (γ t)) with hF
  have hFD : ∀ t, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) = D t := by
    intro t
    have hg := gaussian_needleMap p e he1 hσ t
    rw [← hγ, ← hK, ← ht₀] at hg
    simp only [hF, hD, hh (γ t), hg]
    ring
  have hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t := fun t ht =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg (hlnn t ht) _) (hf₀ _))
  have hFc : LogConcaveOn (Set.Icc α β) F := by
    refine LogConcaveOn.const_mul ?_ ?_ (Real.exp_pos _).le
    · exact LogConcaveOn.mul
        (logConcaveOn_pow_of_concaveOn hlc (fun _ ht => hlnn _ ht) (n - 1))
        ((hfc.comp_needleMap p e).logConcaveOn (convex_Icc α β))
        (fun t ht => pow_nonneg (hlnn t ht) _) (fun _ _ => hf₀ _)
    · exact fun t ht => mul_nonneg (pow_nonneg (hlnn t ht) _) (hf₀ _)
  have hintF : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β := by
    simpa only [hFD] using hint
  have hg0 : ∀ t ∈ Set.Icc α β, 0 ≤ h (γ t) := fun t _ => h0 _
  have hgc : LogConcaveOn (Set.Icc α β) (fun t => h (γ t)) :=
    (hhc.comp_needleMap p e).logConcaveOn (convex_Icc α β)
  -- the coefficient function the needle carries, and its two properties
  set κ : ℝ → ℝ → ℝ := fun x y =>
    max (densDist (fun t => h (γ t)) x y / (4 * Real.sqrt n))
      (c₂ / σ * (y - x)) with hκ
  have hκ1 : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t := by
    intro x y hx hxy hy
    have hone := kls38_concave hn hx hxy hy hg0 hgc hlnn hlc hint
    have htwo := h1d2 F t₀ α β x y hx hxy hy hF0 hFc hintF
    simp only [hFD] at htwo
    exact oneDimCoeff_mul_le' hn hone htwo
  have hdd : ∀ s t : ℝ, densDist (fun u => h (γ u)) (min s t) (max s t)
      = densDist h (γ s) (γ t) := by
    intro s t
    rcases le_total s t with hst | hst
    · rw [min_eq_left hst, max_eq_right hst]; rfl
    · rw [min_eq_right hst, max_eq_left hst]
      exact densDist_comm _ _ _
  have hκ2 : ∀ s ∈ γ ⁻¹' S₁ ∩ Set.Icc α β, ∀ t ∈ γ ⁻¹' S₂ ∩ Set.Icc α β,
      d / σ ≤ κ (min s t) (max s t) := by
    intro s hs t ht
    have hnorm : ‖γ s - γ t‖ = max s t - min s t := by
      have hdst := dist_needleMap p e s t
      rw [dist_eq_norm, Real.dist_eq, he1, mul_one] at hdst
      rw [hγ, hdst, ← max_sub_min_eq_abs, max_comm t s, min_comm t s]
    have hsep' := hsep (γ s) hs.1 (γ t) ht.1
    rw [hnorm] at hsep'
    rw [hκ]
    simp only
    rw [hdd s t]
    exact le_oneDimCoeff_of_sep' hn hσ hc₂ hsep'
  -- the one-dimensional isoperimetric inequality for the induced partition
  have hiso := oneDim_partition D _ _ _ κ α β (d / σ) hαβ hD0 hint hpart' hmZ1 hmZ2 hmZ3 hκ1 hκ2
  exact needle_masses_contradiction_ge' hIpos hApos hZ2pos.le hZ3nn hZ1 hZ3 hiso

end StrictConsumer

/-! ### The capstone: `thm:iso` for an open/closed partition, with no residual binder -/

section Capstone

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` with the Localization Lemma discharged, for `S₁, S₂` open,
`S₃` closed and `h` continuous and bounded.**

Same statement as `Arlib.gaussianRestricted_isoperimetry_concave`
(`Arlib/Convexity/SharpIsoperimetryConcave.lean:435`) — same conclusion at the same sharp constant
`d/σ`, same separation hypothesis at the same threshold `2√3·d` — **with the `hloc` binder
removed**.  In exchange it asks that

* `S₁` and `S₂` be **open** and `S₃` **closed** (they still partition `ℝⁿ`), and
* `h` be **continuous** and **bounded** (and integrable, which `hmass` alone does not give).

Nothing else changes, and no hypothesis of localization type remains: the needle is produced by
`Arlib.exists_needle_openClosed`, which is a theorem.

**Why those hypotheses, and why they are not removable by approximation.**  The needle is a
Lebesgue-null subset of `ℝⁿ`, so a needle integral is not a function of the almost-everywhere
class of its integrand: `Arlib.exists_null_measurableSet_needleIntegral_eq_one` exhibits a null
`S` whose needle mass is `1`.  Every `L¹`/Lusin/Vitali–Carathéodory route is therefore closed, and
what survives is *pointwise* approximation from below — which is exactly lower semicontinuity,
i.e. `S₁, S₂` open, `S₃` closed, `h` continuous.  Boundedness is what the localization stack's
entry point `Arlib.exists_needle_of_compact_convex` asks of its integrands.

The reduction of the general **measurable** case to this one is not a theorem of this file; see
`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement` for the reduction that does
work, and `Arlib.exists_separated_no_disjoint_open_enlargement` for why the uniform
neighbourhood mechanism does not. -/
theorem gaussianRestricted_isoperimetry_openClosed (hn : 2 ≤ n) {σ d B : ℝ} (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₃ : IsClosed S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  rcases le_or_gt 0 (d / σ) with hdσ | hneg
  · have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    refine gaussianRestricted_isoperimetry_concave_gt_of_oneDim (by omega) hσ (by positivity)
      hf₀ hfc hh hpart hS₁.measurableSet hS₂.measurableSet hS₃.measurableSet hmass ?_
      (hloc_gt_of_localization_ge hn hS₁.measurableSet hS₂.measurableSet hS₃.measurableSet
        (fun A hA hone htwo => exists_needle_openClosed hn h0 hhc hhB hhi hS₁ hS₂ hS₃
          hpart.disjoint₁₂ hpart.disjoint₁₃ hA hdσ hone htwo))
      (fun F t₀ α β u v hau huv hvβ hF0 hFc hint =>
        oneDim_isoperimetry_gaussianFactor_unconditional hσ F t₀ α β u v hau huv hvβ hF0 hFc hint)
    intro u hu v hv
    rcases hsep u hu v hv with hmetric | hdens
    · left
      have hrw : d / (1 / (2 * Real.sqrt 3)) = 2 * Real.sqrt 3 * d := by
        rw [div_div_eq_mul_div, div_one]; ring
      rw [hrw]
      exact hmetric
    · exact Or.inr hdens
  · -- `d < 0`: the left-hand side is nonpositive and the right-hand side nonnegative
    have hm₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
    have hm₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
    have hm₃ : 0 ≤ ∫ x in S₃, h x := integral_nonneg fun x => h0 x
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (mul_nonneg hm₁ hm₂))
      (mul_nonneg hmass.le hm₃)

end Capstone

/-! ### Non-vacuity -/

section Witness

variable {n : ℕ}

/-- **Non-vacuity witness for `Arlib.gaussianRestricted_isoperimetry_openClosed`.**

Every hypothesis is satisfiable simultaneously, at parameters where the conclusion is a *strictly
positive* lower bound (so the statement is not the trivial `0 ≤ something`).  The instance is
`σ = 1`, `f ≡ 1` — so `h` is the **standard Gaussian**, which is continuous, bounded by `1` and
integrable — and the slab partition orthogonal to the first coordinate axis,

  `S₁ = {⟪e,x⟫ < −1/4}`,  `S₂ = {1/4 < ⟪e,x⟫}`,  `S₃ = {−1/4 ≤ ⟪e,x⟫ ≤ 1/4}`,

whose first two parts are open and whose third is closed, with `d = 1/8`.  The separation
hypothesis fires on the metric branch: `2√3·d ≤ 4d = 1/2 ≤ ‖u − v‖`, using `√3 ≤ 2`.

Unlike `Arlib.gaussianRestricted_isoperimetry_concave_witness`, this witness has **no `hloc`
clause to discharge** — the capstone has no such binder — so the vacuity that
`Arlib.hloc_antecedent_false_of_isoperimetry` forces on every witness of the conditional form
does not arise here.  Every clause below is satisfied outright. -/
theorem gaussianRestricted_isoperimetry_openClosed_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d B : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      IsOpen S₁ ∧ IsOpen S₂ ∧ IsClosed S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
  have h0 : ∀ x, 0 ≤ h x := fun x => (Real.exp_pos _).le
  have hhc : Continuous h := by rw [hhdef]; fun_prop
  have hhB : ∀ x, h x ≤ 1 := by
    intro x
    rw [hhdef]
    simp only
    refine Real.exp_le_one_iff.mpr ?_
    have : (0:ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (2:ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hhi : Integrable h := by
    have heq : h = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; rw [hhdef]; norm_num
    rw [heq]
    exact Arlib.GaussianCooling.integrable_gaussian_eucl one_pos
  -- balls of radius `1/8` about `r·e`, for `|r| ≤ 1/2`, sit in the unit ball
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      ‖x‖ ≤ 1 ∧ |(inner ℝ e x : ℝ) - r| < 1/8 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      Real.exp (-(1:ℝ)/2) ≤ h x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    rw [hhdef]
    simp only
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2:ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hme : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | inner ℝ e x < -(1/4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1/4 : ℝ) < inner ℝ e x} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | -(1/4 : ℝ) ≤ inner ℝ e x ∧ (inner ℝ e x : ℝ) ≤ 1/4} with hS₃def
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1/2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  have hp1 : 0 < ∫ x in S₁, h x := by
    refine setIntegral_pos_of_ball_le (z := (-(1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1/2)) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1/2)) (by norm_num) x hx
    rw [hS₁def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.2]
  have hp2 : 0 < ∫ x in S₂, h x := by
    refine setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1/2) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (1/2) (by norm_num) x hx
    rw [hS₂def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.1]
  refine ⟨fun _ => (1 : ℝ), h, S₁, S₂, S₃, 1, 1/8, 1, one_pos, by norm_num,
    fun _ => zero_le_one, isLogConcave_const zero_le_one, fun x => by rw [hhdef]; ring,
    hhc, hhB, hhi, isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1/4), ?_, ?_, ?_, hM, ?_, ?_⟩
  · exact isOpen_lt hme continuous_const
  · exact isOpen_lt continuous_const hme
  · exact (isClosed_le continuous_const hme).inter (isClosed_le hme continuous_const)
  · -- separation: the metric branch, `2√3·(1/8) ≤ 1/2 ≤ ‖u − v‖`
    intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1/4 : ℝ)) hu hv
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    linarith
  · have h1 : (0:ℝ) < (1/8 : ℝ) / 1 := by norm_num
    exact mul_pos h1 (mul_pos hp1 hp2)

/-- **Non-vacuity of `Arlib.exists_needle_openClosed`.**

Every hypothesis of that theorem is met simultaneously, by data on which the needle machinery
genuinely fires — so the discharged binder is not vacuously true for want of a satisfiable
antecedent.  The data is the standard Gaussian and the slab partition of
`Arlib.gaussianRestricted_isoperimetry_openClosed_witness`, with `S₃` replaced by `∅` (closed, and
disjoint from `S₁`) and the constant taken to be `A = ∫_{S₁}h / (2∫h)`, which makes the strict
antecedent `A·∫h = (∫_{S₁}h)/2 < ∫_{S₁}h` hold with room to spare and the second antecedent read
`0 < (d/σ)A·∫_{S₂}h`.

This is the analogue of `Arlib.exists_needle_of_compact_convex_witness` one level up, and it is
*not* vacuous in the way every witness for the conditional form must be
(`Arlib.hloc_antecedent_false_of_isoperimetry`): there the antecedent contradicts the theorem's own
conclusion, here it is satisfied outright. -/
theorem exists_needle_openClosed_witness (hn : 2 ≤ n) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d A B : ℝ),
      (∀ x, 0 ≤ h x) ∧ Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsOpen S₁ ∧ IsOpen S₂ ∧ IsClosed S₃ ∧ Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧
      0 < A ∧ 0 ≤ d / σ ∧
      A * (∫ x, h x) < ∫ x in S₁, h x ∧
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x ∧
      ∃ (b v : EuclideanSpace ℝ (Fin n)) (W : ℝ → ℝ),
        v ≠ 0 ∧ (∀ t, 0 ≤ W t) ∧ (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧
        ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / ((n : ℝ) - 1))) ∧
        Integrable (fun t => W t * h (needleMap b v t)) ∧
        A * (∫ t : ℝ, W t * h (needleMap b v t))
          ≤ ∫ t : ℝ, W t * S₁.indicator h (needleMap b v t) ∧
        0 < ∫ t : ℝ, W t * (d / σ * A * S₂.indicator h (needleMap b v t)
              - S₃.indicator h (needleMap b v t)) := by
  obtain ⟨f, h, S₁, S₂, S₃, σ, d, B, hσ, hd, hf₀, hfc, hh, hhc, hhB, hhi, hpart, hS₁, hS₂, hS₃,
    hM, hsep, hLHS⟩ := gaussianRestricted_isoperimetry_openClosed_witness (n := n) hn
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hdσ : 0 < d / σ := div_pos hd hσ
  have hm₁nn : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
  have hm₂nn : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
  have hprod : 0 < (∫ x in S₁, h x) * ∫ x in S₂, h x := by
    by_contra hle
    rw [not_lt] at hle
    exact absurd hLHS (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hdσ.le hle))
  have hm₁ : 0 < ∫ x in S₁, h x := by
    rcases eq_or_lt_of_le hm₁nn with he | hlt
    · exfalso; rw [← he, zero_mul] at hprod; exact lt_irrefl 0 hprod
    · exact hlt
  have hm₂ : 0 < ∫ x in S₂, h x := by
    rcases eq_or_lt_of_le hm₂nn with he | hlt
    · exfalso; rw [← he, mul_zero] at hprod; exact lt_irrefl 0 hprod
    · exact hlt
  set A : ℝ := (∫ x in S₁, h x) / (2 * ∫ x, h x) with hAdef
  have hA : 0 < A := div_pos hm₁ (by linarith)
  have hone : A * (∫ x, h x) < ∫ x in S₁, h x := by
    rw [hAdef, div_mul_eq_mul_div, mul_comm (2 : ℝ) (∫ x, h x), ← div_div, mul_div_assoc,
      div_self hM.ne', mul_one]
    linarith
  have hempty : (∫ x in (∅ : Set (EuclideanSpace ℝ (Fin n))), h x) = 0 := setIntegral_empty
  have htwo : (∫ x in (∅ : Set (EuclideanSpace ℝ (Fin n))), h x)
      < d / σ * A * ∫ x in S₂, h x := by
    rw [hempty]
    exact mul_pos (mul_pos hdσ hA) hm₂
  exact ⟨h, S₁, S₂, ∅, σ, d, A, B, h0, hhc, hhB, hhi, hS₁, hS₂, isClosed_empty,
    hpart.disjoint₁₂, disjoint_empty _, hA, hdσ.le, hone, htwo,
    exists_needle_openClosed hn h0 hhc hhB hhi hS₁ hS₂ isClosed_empty hpart.disjoint₁₂
      (disjoint_empty _) hA hdσ.le hone htwo⟩

end Witness

/-! ### The reduction of the measurable case, and its obstruction -/

section Reduction

variable {n : ℕ}

/-- **The measurable case follows from the open/closed case whenever the two parts admit disjoint
open enlargements that keep the separation hypothesis.**

Given `S₁, S₂, S₃` merely *measurable* — indeed, arbitrary — and **disjoint open** `U₁ ⊇ S₁`,
`U₂ ⊇ S₂` for which the separation hypothesis still holds at the same `d`, the conclusion of
`thm:iso` for `S₁, S₂, S₃` follows from `Arlib.gaussianRestricted_isoperimetry_openClosed` applied
to `U₁, U₂, (U₁ ∪ U₂)ᶜ`.

All three monotonicities point the right way: enlarging `S₁, S₂` only **increases** the left-hand
side `π(S₁)·π(S₂)`, and the residual part `(U₁ ∪ U₂)ᶜ` is **contained** in `S₃`, so the right-hand
side only decreases.  No limit is taken and no regularity of the measure is used — the reduction
is pure monotonicity once the enlargement exists.

**What is not proved here is that the enlargement exists.**  Outer regularity supplies open
supersets of prescribed excess mass, but not *disjoint* ones, and not ones preserving the
separation hypothesis.  `Arlib.exists_separated_no_disjoint_open_enlargement` shows that both
failures are real: there is data satisfying every hypothesis of `thm:iso` for which **no** pair of
disjoint open supersets exists at all.  So this lemma is a per-instance reduction, not a general
one. -/
theorem gaussianRestricted_isoperimetry_of_openClosed_enlargement (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hUdisj : Disjoint U₁ U₂)
    (hsub₁ : S₁ ⊆ U₁) (hsub₂ : S₂ ⊆ U₂)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ U₁, ∀ v ∈ U₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  rcases le_or_gt 0 (d / σ) with hdσ | hneg
  · have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
      { union := Set.union_compl_self (U₁ ∪ U₂)
        disjoint₁₂ := hUdisj
        disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
        disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
    have hmain := gaussianRestricted_isoperimetry_openClosed hn hσ hf₀ hfc hh hhc hhB hhi hpart'
      hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hmass hsep
    -- the residual part is inside `S₃`
    have hsub₃ : (U₁ ∪ U₂)ᶜ ⊆ S₃ := by
      intro x hx
      have hmem : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; trivial
      rcases hmem with (h1 | h2) | h3
      · exact absurd (Or.inl (hsub₁ h1)) hx
      · exact absurd (Or.inr (hsub₂ h2)) hx
      · exact h3
    have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
        (∫ x in S, h x) ≤ ∫ x in T, h x := by
      intro S T hST
      exact setIntegral_mono_set hhi.integrableOn
        (Filter.Eventually.of_forall h0) hST.eventuallyLE
    have hm₁ : (∫ x in S₁, h x) ≤ ∫ x in U₁, h x := hmono hsub₁
    have hm₂ : (∫ x in S₂, h x) ≤ ∫ x in U₂, h x := hmono hsub₂
    have hm₃ : (∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ ∫ x in S₃, h x := hmono hsub₃
    have hp₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
    have hp₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
    calc d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ d / σ * ((∫ x in U₁, h x) * ∫ x in U₂, h x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hm₁ hm₂ hp₂ (le_trans hp₁ hm₁)) hdσ
      _ ≤ (∫ x, h x) * ∫ x in (U₁ ∪ U₂)ᶜ, h x := hmain
      _ ≤ (∫ x, h x) * ∫ x in S₃, h x := mul_le_mul_of_nonneg_left hm₃ hmass.le
  · have hp₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
    have hp₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
    have hp₃ : 0 ≤ ∫ x in S₃, h x := integral_nonneg fun x => h0 x
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (mul_nonneg hp₁ hp₂))
      (mul_nonneg hmass.le hp₃)

end Reduction

section Obstruction

variable {n : ℕ}

/-- **The enlargement the reduction needs need not exist: `S₁` and `S₂` can touch.**

Data satisfying **every** hypothesis of Cousins–Vempala's `thm:iso` in its measurable form
(`Arlib.gaussianRestricted_isoperimetry_concave`), with a *strictly positive* left-hand side —
and for which **no** open `U₁ ⊇ S₁` and `U₂ ⊇ S₂` are disjoint.  A fortiori no `εd`-neighbourhood
enlargement is disjoint, so the reduction of the measurable case to the open/closed case cannot be
performed by enlarging `S₁, S₂` to open supersets, however small the enlargement.

The instance is `σ = 1`, `f = 1_{B(0,1)}` the indicator of the **open** unit ball (log-concave),
so `h` is the Gaussian restricted to that ball, and

  `S₁ = {‖x‖ ≥ 1} ∪ {⟪e,x⟫ < −1/4}`,  `S₂ = {‖x‖ < 1} ∩ {⟪e,x⟫ > 1/4}`,  `S₃ = (S₁ ∪ S₂)ᶜ`.

The separation hypothesis holds for **both** reasons at once, each on its own half of `S₁`:

* if `‖u‖ ≥ 1` then `h u = 0` while `h v > 0`, so `d_h(u,v) = 1` — the *density* branch, and it is
  satisfied at every distance, including distance `0`;
* if `‖u‖ < 1` then `⟪e,u⟫ < −1/4 < 1/4 < ⟪e,v⟫`, so `‖u − v‖ ≥ 1/2` — the *metric* branch.

The touching happens on the sphere: `e ∈ S₁` (its norm is `1`) is a limit of points `(1−t)e ∈ S₂`,
so every open set containing `S₁` meets every open set containing `S₂`.

**What this does and does not show.**  It refutes the *mechanism* — open enlargement — not the
statement being reduced: `thm:iso` holds for this data, and the theorem is not vacuous here
(`0 < (d/σ)·π(S₁)π(S₂)`).  The failure is entirely due to the density branch, which is satisfied
at arbitrarily small distances wherever `h` vanishes; the metric branch alone would degrade
gracefully from `d` to `d(1−2ε)`.  Note also that any repair must move `S₁ ∩ {h = 0}`, a set of
`h`-measure zero but of *positive Lebesgue measure* — and needle integrals are not invariant under
changes on Lebesgue-null sets either
(`Arlib.exists_null_measurableSet_needleIntegral_eq_one`), so the repair cannot be purely
measure-theoretic. -/
theorem exists_separated_no_disjoint_open_enlargement (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      Integrable h ∧ (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ∧
      ∀ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)), IsOpen U₁ → IsOpen U₂ →
        S₁ ⊆ U₁ → S₂ ⊆ U₂ → ¬ Disjoint U₁ U₂ := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  set f : EuclideanSpace ℝ (Fin n) → ℝ := Set.indicator (Metric.ball 0 1) 1 with hfdef
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => f x * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hfc : IsLogConcave f := isLogConcave_indicator_iff.mpr (convex_ball 0 1)
  have h0 : ∀ x, 0 ≤ h x := fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le
  have hin : ∀ x, ‖x‖ < 1 → h x = Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
    intro x hx
    have hmem : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    rw [hhdef]
    simp [hfdef, Set.indicator_of_mem hmem]
  have hout : ∀ x, ¬ ‖x‖ < 1 → h x = 0 := by
    intro x hx
    have hmem : x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    rw [hhdef]
    simp [hfdef, Set.indicator_of_notMem hmem]
  have hheq : h = Set.indicator (Metric.ball 0 1)
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2))) := by
    funext x
    by_cases hx : ‖x‖ < 1
    · have hmem : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx
      rw [hin x hx, Set.indicator_of_mem hmem]
    · have hmem : x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx
      rw [hout x hx, Set.indicator_of_notMem hmem]
  have hgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2))) := by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)))
        = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; norm_num
    rw [heq]
    exact Arlib.GaussianCooling.integrable_gaussian_eucl one_pos
  have hhi : Integrable h := by rw [hheq]; exact hgi.indicator measurableSet_ball
  -- balls of radius `1/8` about `r·e`, `|r| ≤ 1/2`, sit well inside the unit ball
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      ‖x‖ < 1 ∧ |(inner ℝ e x : ℝ) - r| < 1/8 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      Real.exp (-(1:ℝ)/2) ≤ h x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    rw [hin x hx1]
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2:ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hme : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ¬ ‖x‖ < 1} ∪ {x | inner ℝ e x < -(1/4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ‖x‖ < 1} ∩ {x | (1/4 : ℝ) < inner ℝ e x} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) := (S₁ ∪ S₂)ᶜ with hS₃def
  have hS₁meas : MeasurableSet S₁ := by
    refine MeasurableSet.union ?_ (measurableSet_lt hme.measurable measurable_const)
    exact (measurableSet_lt continuous_norm.measurable measurable_const).compl
  have hS₂meas : MeasurableSet S₂ :=
    (measurableSet_lt continuous_norm.measurable measurable_const).inter
      (measurableSet_lt measurable_const hme.measurable)
  have hdisj12 : Disjoint S₁ S₂ := by
    refine Set.disjoint_left.mpr fun a ha hb => ?_
    obtain ⟨hb1, hb2⟩ := hb
    rcases ha with ha | ha
    · exact ha hb1
    · simp only [Set.mem_setOf_eq] at ha hb2; linarith
  have hpart : IsPartition3 Set.univ S₁ S₂ S₃ :=
    { union := Set.union_compl_self (S₁ ∪ S₂)
      disjoint₁₂ := hdisj12
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  -- the two masses are positive
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1/2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  have hp1 : 0 < ∫ x in S₁, h x := by
    refine setIntegral_pos_of_ball_le (z := (-(1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1/2)) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1/2)) (by norm_num) x hx
    rw [abs_lt] at hx2
    exact Or.inr (by simp only [Set.mem_setOf_eq]; linarith [hx2.2])
  have hp2 : 0 < ∫ x in S₂, h x := by
    refine setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1/2) (by norm_num))
    intro x hx
    obtain ⟨hx1, hx2⟩ := hballs (1/2) (by norm_num) x hx
    rw [abs_lt] at hx2
    exact ⟨hx1, by simp only [Set.mem_setOf_eq]; linarith [hx2.1]⟩
  -- the separation parameter: small enough for both branches
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  set d : ℝ := min (1/8) (1 / (4 * Real.sqrt n)) with hddef
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hd8 : d ≤ 1/8 := min_le_left _ _
  have hdn : 4 * (d / 1) * Real.sqrt n ≤ 1 := by
    have h1 : d ≤ 1 / (4 * Real.sqrt n) := min_le_right _ _
    have h2 : d * (4 * Real.sqrt n) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    rw [div_one]
    linarith
  refine ⟨f, h, S₁, S₂, S₃, 1, d, one_pos, hd0, hf0, hfc, fun x => by rw [hhdef], hpart,
    hS₁meas, hS₂meas, (hS₁meas.union hS₂meas).compl, hhi, hM, ?_, ?_, ?_⟩
  · -- separation, by cases on which half of `S₁` the point lies in
    intro u hu v hv
    obtain ⟨hv1, hv2⟩ := hv
    simp only [Set.mem_setOf_eq] at hv1 hv2
    by_cases huin : ‖u‖ < 1
    · -- the metric branch
      left
      have hu2 : (inner ℝ e u : ℝ) < -(1/4 : ℝ) := by
        rcases hu with hu | hu
        · exact absurd huin hu
        · exact hu
      have hgeo : (1/2 : ℝ) ≤ ‖u - v‖ := by
        have hip := abs_real_inner_le_norm e (u - v)
        rw [he, one_mul, inner_sub_right] at hip
        have : (1/2 : ℝ) ≤ |(inner ℝ e u : ℝ) - inner ℝ e v| := by
          rw [abs_sub_comm, le_abs]
          left; linarith
        linarith
      have hs3 : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      nlinarith
    · -- the density branch, at `d_h(u,v) = 1`, valid at *every* distance
      right
      have hu0 : h u = 0 := hout u huin
      have hvpos : 0 < h v := by rw [hin v hv1]; exact Real.exp_pos _
      have hdd : densDist h u v = 1 := by
        rw [densDist, hu0, max_eq_right hvpos.le, zero_sub, abs_neg,
          abs_of_nonneg hvpos.le, div_self hvpos.ne']
      rw [hdd]
      exact hdn
  · have h1 : (0:ℝ) < d / 1 := by rw [div_one]; exact hd0
    exact mul_pos h1 (mul_pos hp1 hp2)
  · -- no disjoint open enlargement: `e ∈ S₁` is a limit of points of `S₂`
    intro U₁ U₂ hU₁ hU₂ hs₁ hs₂ hdisj
    have heS₁ : e ∈ S₁ := Or.inl (by simp only [Set.mem_setOf_eq, he]; norm_num)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU₁ e (hs₁ heS₁)
    set t : ℝ := min (δ / 2) (1/2) with htdef
    have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht2 : t ≤ 1/2 := min_le_right _ _
    set x : EuclideanSpace ℝ (Fin n) := (1 - t) • e with hxdef
    have hxnorm : ‖x‖ = 1 - t := by
      rw [hxdef, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith)]
    have hxin : ‖x‖ < 1 := by rw [hxnorm]; linarith
    have hxip : (inner ℝ e x : ℝ) = 1 - t := by
      rw [hxdef, real_inner_smul_right, hee, mul_one]
    have hxS₂ : x ∈ S₂ := ⟨by simpa using hxin, by simp only [Set.mem_setOf_eq, hxip]; linarith⟩
    have hxU₁ : x ∈ U₁ := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm, hxdef]
      have : (1 - t) • e - e = (-t) • e := by module
      rw [this, norm_smul, Real.norm_eq_abs, he, mul_one, abs_neg, abs_of_nonneg ht0.le]
      exact htδ
    exact absurd hxU₁ (Set.disjoint_right.mp hdisj (hs₂ hxS₂))

end Obstruction

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`,
Mathlib's three standard foundational axioms — and nothing else. -/

#print axioms Arlib.eventually_setIntegral_closedBall_gt
#print axioms Arlib.exists_compact_body_continuous_pair
#print axioms Arlib.exists_needle_openClosed
#print axioms Arlib.hloc_gt_of_localization_ge
#print axioms Arlib.gaussianRestricted_isoperimetry_concave_gt_of_oneDim
#print axioms Arlib.gaussianRestricted_isoperimetry_openClosed
#print axioms Arlib.gaussianRestricted_isoperimetry_openClosed_witness
#print axioms Arlib.exists_needle_openClosed_witness
#print axioms Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement
#print axioms Arlib.exists_separated_no_disjoint_open_enlargement
