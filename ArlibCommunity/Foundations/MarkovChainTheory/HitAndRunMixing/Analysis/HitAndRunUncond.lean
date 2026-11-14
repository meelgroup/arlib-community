/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductance
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.ConductanceToTV
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.SphereCap
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductanceRoutes
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.ChordContinuity
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationNeedleInBody
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Prelude

section
/-!
# The hit-and-run conductance bound with the Lemma 4.1 overlap constant as a parameter

`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge`
(`ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunConductance.lean`) states Theorem 4.2 of
Lovász–Vempala with the paper's **Lemma 4.1 constant hardcoded**: its binder demands

    ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500))

and **nothing this repository proves can feed that hypothesis**.  The module docstring of
`ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunOverlap.lean` (§ "Constants: the printed `1/6` is
wrong, and `1 − 1/500` does not survive", lines 123–170) shows that two of the three bounds
in the paper's proof of Lemma 4.1 are wrong in the same direction: the cap bound `1/6` is
never attainable (the true quantity decreases to `2(1 − Φ(1)) = 0.31731…`), and the printed
`A₃`, of mass `1/3`, is too small to support the chord comparison — the `A₃` that does
support it has sharp mass `1/2`.  The overlap constant the corrected proof delivers is
`1 − 1/1892.8…` in the limit and `1 − 1/34386` at `n = 5`; nothing near `1 − 1/500`.

This file therefore restates and re-proves the conductance bound with that constant **free**,
so that whatever Lemma 4.1 eventually lands can be composed with Theorem 4.2 immediately.

## The `c`-dependence, traced

`1/500` enters the argument at exactly one place and propagates linearly.  Tracing it in
`HitAndRunConductance.lean`:

* `conductance_hitAndRun_ge` (line 999) is a wrapper: it calls
  `conductance_hitAndRun_ge_of_tv` (line 618) at `lam = 1/500` and rounds
  `500 · 245760 = 122880000` up to `2²⁷ = 134217728`.
* `conductance_hitAndRun_ge_of_tv` is **already parametric**: it carries `{lam : ℝ}`
  with `0 < lam`, `lam ≤ 1`, consumes the overlap hypothesis at `1 − lam`, and concludes
  `ofReal (lam / (245760 · n · D))`.
* Inside that proof `lam` is used only through `eps = ofReal (lam / 2)`: the failure of
  Lemma 4.1 at a deep pair (line 752) forces `P u S < ofReal (lam/2 + (1 − lam))` and hence
  `P u S + P u Sᶜ < 1`, a contradiction; and the two comparisons `hcmp1`, `hcmp3` (lines 893,
  900) push `4 · lam/(245760 n D)` below `eps` and below `eps · 1/(30720 n D)`.  Both are
  linear in `lam`, so the conclusion is.

So the true dependence is **linear, with no other loss**:

    Φ(hit-and-run on K)  ≥  c / (245760 · n · D)      for any achievable overlap constant `c`.

Nothing in this file re-derives the geometry; the whole content is the observation that the
`1/500` was hardcoded only in the wrapper, plus the faithfulness check
`conductance_hitAndRun_ge_of_param` and the instantiations at the constants the corrected
Lemma 4.1 route actually reaches.

## What is here

* `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_param` — the parametric statement, at a free
  overlap constant `c` with `0 < c ≤ 1`, concluding `ofReal (c / (245760 · n · D))`.
* `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_param` — **the faithfulness check**: the
  original statement of `conductance_hitAndRun_ge`, verbatim, re-derived from the parametric
  one at `c = 1/500`.  It does not call `conductance_hitAndRun_ge`; it repeats that theorem's
  own final comparison, so a successful build certifies that the parametrisation loses
  nothing.
* `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_2048` and
  `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_34386` — the instantiations at `c = 1/2048`
  and `c = 1/34386`, in exact form, with `..._pow` variants rounded to a power of two.
* `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_param_of_le` — graceful degradation: an
  overlap hypothesis at a *better* constant `c'` feeds the bound at any `c ≤ c'`.

## The numbers, plainly

| overlap constant `c` | conductance bound (exact) | rounded up to a power of two |
|---|---|---|
| `1/500` (paper, **not reached by the corrected route**) | `1/(122880000 · n · D)` | `1/(2²⁷ · n · D)` |
| `1/2048` | `1/(503316480 · n · D)` | `1/(2²⁹ · n · D)` |
| `1/34386` (the corrected route at `n = 5`) | `1/(8450703360 · n · D)` | `1/(2³³ · n · D)` |

`2048` is a convenient round value bracketing the limiting `1892.8…` of `HitAndRunOverlap`
from above; `34386` is that file's `n = 5` entry.  The powers of two are the least ones that
work: `2²⁸ = 268435456 < 503316480` and `2³² = 4294967296 < 8450703360`.

`hIso` — the paper's Theorem 2.1 in its corrected form, still the open gap — and the inputs
of `hLem41` are carried through **verbatim** as binders; nothing about them is touched here.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The parametric conductance bound -/

/-- **Theorem 4.2 of Lovász–Vempala with the Lemma 4.1 overlap constant as a parameter.**

If the one-step laws of two points that are close in cross-ratio distance and close relative
to their median steps are at total variation distance at most `1 − c`, for *any* `c ∈ (0,1]`,
then

    Φ(hit-and-run on K)  ≥  c / (245760 · n · D).

The dependence on `c` is linear; see the module docstring for the trace.  This is the form to
compose with whatever Lemma 4.1 actually delivers — `ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunOverlap.lean` shows the
paper's `c = 1/500` is not reached by the corrected proof, which gives `c = 1/1892.8…` in
the limit and `c = 1/34386` at `n = 5`.

`hIso` is the paper's Theorem 2.1 in the corrected form of `conductance_hitAndRun_ge`, and is
carried verbatim; it remains the open gap. -/
theorem conductance_hitAndRun_ge_param (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
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
    ENNReal.ofReal (c / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_tv hn hKc hKcl hKm hKb hball hD hc0 hc1 hLem41 hIso

/-! ## 2. The faithfulness check: the original statement, recovered at `c = 1/500` -/

/-- **The original `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge`, recovered from the
parametric form at `c = 1/500`.**

The statement is that of `conductance_hitAndRun_ge`
(`HitAndRunConductance.lean`) verbatim, down to the binder names and the `2²⁷`.  The
proof does **not** invoke `conductance_hitAndRun_ge`; it goes through
`conductance_hitAndRun_ge_param` and repeats the original wrapper's own final comparison
`500 · 245760 = 122880000 ≤ 2²⁷ = 134217728`.  A successful build is therefore evidence that
the parametrisation is faithful — that nothing was lost or strengthened in freeing the
constant.

The hypothesis is still one no proof in this repository can supply (see the module
docstring); this theorem exists to certify the generalisation, not to be used. -/
theorem conductance_hitAndRun_ge_of_param (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
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
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD (c := 1 / 500)
      (by norm_num) (by norm_num) hLem41 hIso)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## 3. The constants the corrected Lemma 4.1 route reaches -/

/-- **The conductance bound at the overlap constant `c = 1/2048`:**

    Φ(hit-and-run on K)  ≥  1/(503316480 · n · D),

since `2048 · 245760 = 503316480`.  `2048` brackets from above the limiting `1892.8…` that
`ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunOverlap.lean` reports for the corrected Lemma 4.1
(`1 − 1/1892.8…` as `n → ∞`); it is a round value, not a proved one — the overlap hypothesis
is still a binder here. -/
theorem conductance_hitAndRun_ge_2048 (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 2048)))
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
    ENNReal.ofReal (1 / (503316480 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    (conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD (c := 1 / 2048)
      (by norm_num) (by norm_num) hLem41 hIso)
  rw [div_div]
  congr 1
  ring

/-- **The conductance bound at the overlap constant `c = 1/34386`:**

    Φ(hit-and-run on K)  ≥  1/(8450703360 · n · D),

since `34386 · 245760 = 8450703360`.  `1 − 1/34386` is the constant that
`ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunOverlap.lean` reports at `n = 5`, the
smallest dimension at which the corrected Lemma 4.1 says anything at all (for `2 ≤ n ≤ 4` its
budget `q = 1/8 + q₂(n) + 1/2` exceeds `1`).  As everywhere in this file, the overlap
hypothesis is a binder, not a discharged fact. -/
theorem conductance_hitAndRun_ge_34386 (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 34386)))
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
    ENNReal.ofReal (1 / (8450703360 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    (conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD (c := 1 / 34386)
      (by norm_num) (by norm_num) hLem41 hIso)
  rw [div_div]
  congr 1
  ring

/-! ## 4. The same two constants, rounded to a power of two

Purely for legibility, in the style of `conductance_hitAndRun_ge`'s `2²⁷`.  Both are the
least power of two that works: `2²⁸ = 268435456 < 503316480` and
`2³² = 4294967296 < 8450703360`.  The exact forms of §3 are strictly stronger. -/

/-- `Φ(hit-and-run on K) ≥ 1/(2²⁹ · n · D)` at overlap constant `c = 1/2048`.  The rounding
of `conductance_hitAndRun_ge_2048`: `503316480 ≤ 2²⁹ = 536870912`. -/
theorem conductance_hitAndRun_ge_2048_pow (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 2048)))
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
    ENNReal.ofReal (1 / (2 ^ 29 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_2048 hn hKc hKcl hKm hKb hball hD hLem41 hIso)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `Φ(hit-and-run on K) ≥ 1/(2³³ · n · D)` at overlap constant `c = 1/34386`.  The rounding
of `conductance_hitAndRun_ge_34386`: `8450703360 ≤ 2³³ = 8589934592`. -/
theorem conductance_hitAndRun_ge_34386_pow (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 34386)))
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
    ENNReal.ofReal (1 / (2 ^ 33 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_34386 hn hKc hKcl hKm hKb hball hD hLem41 hIso)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## 5. Graceful degradation -/

/-- **A better overlap constant feeds a weaker conductance bound.**  If Lemma 4.1 is
available at `c'` — total variation at most `1 − c'` — then for every `c ≤ c'` with
`0 < c ≤ 1` the conductance bound at `c` holds.  Immediate from `ArlibCommunity.Foundations.Convex.TVLe.mono`, since
`1 − c' ≤ 1 − c`.

This is the composition-facing form: a caller who proves *some* overlap constant need not
match the one a downstream lemma was stated at. -/
theorem conductance_hitAndRun_ge_param_of_le (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {c c' : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hcc : c ≤ c')
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c')))
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
    ENNReal.ofReal (c / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD hc0 hc1
    (fun u hu v hv h8 hstep =>
      (hLem41 u hu v hv h8 hstep).mono (ENNReal.ofReal_le_ofReal (by linarith)))
    hIso

/-! ## Axiom profile -/

section AxiomCheck

#print axioms conductance_hitAndRun_ge_param
#print axioms conductance_hitAndRun_ge_of_param
#print axioms conductance_hitAndRun_ge_2048
#print axioms conductance_hitAndRun_ge_34386
#print axioms conductance_hitAndRun_ge_2048_pow
#print axioms conductance_hitAndRun_ge_34386_pow
#print axioms conductance_hitAndRun_ge_param_of_le

end AxiomCheck

end ArlibCommunity.Foundations.MarkovChainTheory

end

section
/-!
# The hit-and-run mixing bound with the Lemma 4.1 overlap constant as a parameter

`ArlibCommunity/Foundations/MarkovChainTheory/HitAndRunMixing/Analysis/HitAndRunUncond.lean` freed the Lemma 4.1 overlap
constant in the **conductance** theorem (Theorem 4.2).  This file does the same for the
**mixing** theorem (Theorem 1.1), which is where the constants actually failed to compose:

* What is proved: `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_uncond` (`SphereCap.lean`)
  is Lemma 4.1 with no unproved hypothesis, at overlap constant `1 − 1/8000`, for `n ≥ 1100`.
* What the consumers demanded: `hLem41` binders hardcoded at `1 − 1/500`, a constant
  `HitAndRunOverlap.lean`'s module docstring shows the corrected proof cannot reach (two of
  the three bounds in the paper's proof are wrong in the same direction).
* And the mixing theorem hardcoded not just the constant but the *conductance value*:
  `tvLe_iterate_lazy_hitAndRun` (`ConductanceToTV.lean`) demands
  `Φ ≥ r/(2²⁸·n·R)` and a deadline `4·lvThreshold n r R M ε`, both of which are what the
  `1/500` route delivers and neither of which the `1/8000` route can meet.

## What is here

| name | content |
|---|---|
| `lsThreshold_anti` | the deadline `log(8M/ε²)/φ²` is antitone in `φ` |
| `tvLe_iterate_lazy_hitAndRun_param` | Theorem 1.1, lazy hit-and-run, at a **free** `phi`, deadline `4·lsThreshold M phi ε` |
| `tvLe_iterate_lazy_hitAndRun_of_param` | the original recovered at `phi = r/(2²⁸·n·R)` |
| `tvLe_iterate_lazy_hitAndRun_of_param_eq` | `rfl`-check: the recovered statement **is** the original |
| `ofReal_le_conductance_hitAndRun_of_unitBall_param` | `Φ ≥ c/(491520·n·R)` from Lemma 4.1 at `1 − c` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_param` | the unit-inball Theorem 1.1 at a free `c` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_of_param` | the original recovered at `c = 1/500` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq` | `rfl`-check for that one |
| `tvLe_hitAndRun_of_close_uncond_max` | the proved Lemma 4.1, restated in the `max(F u, F v)` shape the `hLem41` binder uses |
| `tvLe_iterate_lazy_hitAndRun_unitBall_8000` | the instantiation at `c = 1/8000`, deadline `4·2⁶⁴·n²R²·log(8M/ε²)` |

## The constant dependence, exactly

Lemma 4.1 at `1 − c` gives `Φ ≥ c/(245760·n·D) = c/(491520·n·R)` (`D ≤ 2R`), and the deadline
is quadratic in `1/Φ`:

    steps  =  4 · lsThreshold M (c/(491520·n·R)) ε  =  4 · 491520² · n²R²/c² · log(8M/ε²).

At `c = 1/500` this is `4·245760000²·n²R²·log(8M/ε²)`, *shorter* than the original's
`4·lvThreshold n 1 R M ε = 4·2⁵⁶·n²R²·log(8M/ε²)` by the factor `(2²⁸/245760000)² ≈ 1.19`
that the original threw away when it rounded `245760000` up to `2²⁸`.  At `c = 1/8000`, after
rounding `8000·491520 = 3932160000` up to `2³²`, it is `4·2⁶⁴·n²R²·log(8M/ε²)` — exactly
`256 = (8000/500)²` times the original.  The shape `O(n²R²·log(M/ε))` is unchanged.

## What remains

1. **`hIso`** — the paper's Theorem 2.1 (the weighted isoperimetric inequality) in its
   corrected form, carrying the clause `∀ x ∈ K, h x ≤ 1/3` without which it is false
   (`not_hIso_two` (not in this repository; see `REFERENCES.md`)).  It is a binder in `conductance_hitAndRun_ge`, is carried
   verbatim through `conductance_hitAndRun_ge_param`, and is carried verbatim through every
   theorem here.  It is being attacked separately as `htrans` + `hloc`.
2. **`n ≥ 1100`** — the threshold of `tvLe_hitAndRun_of_close_uncond`, an artifact of the
   union bound in the spherical-cap estimate (`SphereCap.lean`), not of the statement, which
   is true from `n = 5` on.  It appears in no *mixing* theorem of this file, because
   `hLem41` is still a binder; only the §4 bridge lemma carries it.
3. **`hLem41` itself, and why it is still a binder.**  Besides the binder's own hypotheses,
   `tvLe_hitAndRun_of_close_uncond` needs `u ≠ v`, the two `hmove`s
   (`hitAndRunProposal K u Set.univ = 1`), and `ha`/`hb` (`chordLow K u v < 0`,
   `1 < chordHigh K u v`).  Two of these are cheap: the `max`-versus-`F(u)` mismatch is
   closed by §4 below, and `u = v` by `ArlibCommunity.Foundations.Convex.TVLe.refl` and `ArlibCommunity.Foundations.Convex.TVLe.mono`.

   **`ha` and `hb` are not, and they fail at boundary points of every body.**  Let `K` be
   compact convex with nonempty interior, `u ∈ ∂K` and `v ∈ interior K`.  If
   `chordLow K u v < 0`, i.e. `u + t(v − u) ∈ K` for some `t < 0`, then `u` lies on the open
   segment between that point of `K` and the interior point `v`, hence `u ∈ interior K` —
   contradiction.  So `chordLow K u v = 0` and `ha` fails, for every such pair, in every
   dimension, smooth boundary or not.  Since the `hLem41` binder quantifies over *all*
   `u, v ∈ K`, no route through `tvLe_hitAndRun_of_close_uncond` can discharge it, and a
   theorem carrying `∀ u ∈ K, ∀ v ∈ K, u ≠ v → chordLow K u v < 0` would be vacuous.  None
   is stated here.

   `hmove` fails at boundary points too, though less uniformly: it is the *positive-measure*
   degeneracy of the chord that breaks it, not a single tangent direction.  At a vertex of a
   cube the directions with a nondegenerate chord are the inward cone and its reflection, of
   normalised measure `2^{1−n} < 1`, so the proposal is defective there; at a boundary point
   of a Euclidean ball the tangent directions have measure zero and `hmove` still holds.

   The mathematics is not the obstruction: `HitAndRunConductance.lean`'s module docstring
   (§ *Two places where the formalisation is more careful than the paper*, item 1, lines
   210–217) records that the conductance proof cuts `S₁'`, `S₂'` down to `interior K` and so
   only ever *uses* `hLem41` at interior points, where `hmove` is available from
   `ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_univ_eq_one_of_mem_interior`.  The obstruction is that the binder
   is *stated* over all of `K`.  Weakening it to `interior K` is a one-line change inside
   `conductance_hitAndRun_ge_of_tv`'s statement — in a file this module may not edit — and it
   is what would make `tvLe_iterate_lazy_hitAndRun_unitBall_8000` unconditional in `hLem41`.

So `tvLe_iterate_lazy_hitAndRun_unitBall_8000` is stated with `hLem41` intact, at the
constant `1 − 1/8000` the repository proves, in the style of
`conductance_hitAndRun_ge_2048`/`_34386`: the overlap hypothesis is a binder, not a
discharged fact.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

/-! ## 0. The deadline is antitone in the conductance -/

/-- **A better conductance bound is a shorter deadline.**  `lsThreshold M phi eps =
log(8M/ε²)/phi²` is antitone in `phi` on `phi > 0`, because `log(8M/ε²) ≥ 0` whenever
`M ≥ 1` and `0 < ε ≤ 1` (then `8M/ε² ≥ 8 ≥ 1`).

Both positivity hypotheses are needed: for `M < 1/8` and `ε = 1` the logarithm is negative
and the inequality reverses. -/
theorem lsThreshold_anti {M phi phi' eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hphi0 : 0 < phi) (hphi : phi ≤ phi') :
    lsThreshold M phi' eps ≤ lsThreshold M phi eps := by
  have hlog : 0 ≤ Real.log (8 * M / eps ^ 2) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [lsThreshold, lsThreshold]
  gcongr

/-! ## 1. Theorem 1.1 for the lazy hit-and-run walk, at a free conductance -/

/-- **`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun` with the conductance value a
parameter.**

The original (`ConductanceToTV.lean`) hardcodes `phi = r/(2²⁸·n·R)` — the value Theorem
4.2 delivers *at the paper's Lemma 4.1 constant* `1 − 1/500` — and states the deadline as
`4 · lvThreshold n r R M eps = 4 · 2⁵⁶ · n²R²/r² · log(8M/ε²)`.  Nothing in the proof needs
that particular number: the layer beneath (`tvLe_iterate_lazy_of_exceptional`,
`ConductanceToTV.lean`) already carries a free `phi`.  Here it is exposed, with the
deadline in its native form `4 · lsThreshold M phi eps = 4 · log(8M/ε²)/phi²`.

The factor `4` is `conductance_lazy`: laziness halves the conductance exactly, and the
deadline is quadratic in `1/phi`.

Everything mathematical is inherited: reversibility from `isReversible_hitAndRun`, the
spectral hypothesis from `hasNonnegSpectrum_lazy`, non-degeneracy from
`exists_smallSet_uniformOn`.  `hphi` is the only hypothesis with content, and it is now
whatever conductance bound the caller actually holds. -/
theorem tvLe_iterate_lazy_hitAndRun_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {phi : ℝ} (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    (hphi : ENNReal.ofReal phi ≤ conductance (hitAndRun K) (uniformOn volume K))
    {m : ℕ} (hm : 4 * lsThreshold M phi eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume hK0 hKtop
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ := exists_smallSet_uniformOn hn hKm hK0 hKtop
  exact tvLe_iterate_lazy_of_exceptional (isReversible_hitAndRun hKm)
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hphi0 hphi1 heps0 heps1 hSm hS hdom hphi hm

/-! ## 2. The faithfulness check: the original, recovered at `phi = r/(2²⁸·n·R)` -/

/-- **The original `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun`, recovered from the
parametric form.**

The statement is that of `ConductanceToTV.lean` verbatim, down to the binder names.  The
proof does **not** invoke the original; it goes through `tvLe_iterate_lazy_hitAndRun_param`
at `phi = r/(2²⁸·n·R)` and re-runs the original's own two arithmetic steps (`0 < phi`,
`phi ≤ 1` from `r ≤ R`, and `lsThreshold_eq_lvThreshold`).

That the two statements are *the same statement* is certified mechanically by
`tvLe_iterate_lazy_hitAndRun_of_param_eq` below, which would not typecheck if any binder
had drifted. -/
theorem tvLe_iterate_lazy_hitAndRun_of_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * ArlibCommunity.Foundations.Convex.uniformOn volume K A)
    (hphi : ENNReal.ofReal (r / (2 ^ 28 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (ArlibCommunity.Foundations.Convex.uniformOn volume K))
    {m : ℕ} (hm : 4 * lvThreshold n r R M eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (ArlibCommunity.Foundations.Convex.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hphi0 : 0 < r / (2 ^ 28 * (n : ℝ) * R) := by positivity
  have hphi1 : r / (2 ^ 28 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  refine tvLe_iterate_lazy_hitAndRun_param hn hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom hphi ?_
  rw [lsThreshold_eq_lvThreshold hn hr hR]
  exact hm

/-- **The two statements are literally the same statement.**  `rfl` here compares the *types*
of `tvLe_iterate_lazy_hitAndRun_of_param` and the original
`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun`: the equation does not even elaborate
unless every binder — implicit/explicit/instance, name, type — agrees, and definitional
proof irrelevance then closes it.

This is the check the brief calls for.  A parametrisation that silently dropped or weakened a
clause would fail here even though both files build. -/
theorem tvLe_iterate_lazy_hitAndRun_of_param_eq :
    @tvLe_iterate_lazy_hitAndRun_of_param = @tvLe_iterate_lazy_hitAndRun := rfl

/-! ## 3. The unit-inball version, at a free overlap constant

`conductance_hitAndRun_ge_param` (`HitAndRunConductanceParam.lean`) gives
`Φ ≥ c/(245760·n·D)` from Lemma 4.1 at `1 − c`.  A body inside a ball of radius `R` has
`D ≤ 2R`, so this reads

    Φ  ≥  c / (491520 · n · R),

and the deadline of §1 at that `phi` is `4·491520²·n²R²/c² · log(8M/ε²)` — the paper's shape
`O(n²R²·log(M/ε))`, with a `1/c²`. -/

/-- **The conductance bound in `R`-form, at a free overlap constant.**  This is
`ArlibCommunity.Foundations.MarkovChainTheory.ofReal_inv_le_conductance_hitAndRun_of_unitBall`
(`HitAndRunMixing.lean`) with `1/500` freed to `c`, and with the exact denominator
`491520 = 2·245760` in place of the original's rounding to `2²⁸`.

At `c = 1/500` it says `Φ ≥ 1/(245760000·n·R)`, which is *stronger* than the original's
`Φ ≥ 1/(2²⁸·n·R) = 1/(268435456·n·R)`; the original rounded the denominator up to a power of
two. -/
theorem ofReal_le_conductance_hitAndRun_of_unitBall_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR : 0 < R) (hout : K ⊆ Metric.closedBall zout R)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(ArlibCommunity.Foundations.Convex.uniformOn volume K)) *
          min (ArlibCommunity.Foundations.Convex.uniformOn volume K T₁) (ArlibCommunity.Foundations.Convex.uniformOn volume K T₂)
        ≤ ArlibCommunity.Foundations.Convex.uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (c / (491520 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (ArlibCommunity.Foundations.Convex.uniformOn volume K) := by
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hout
  have hD : Metric.diam K ≤ 2 * R := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.1 (hout hx)
    have hy' := Metric.mem_closedBall.1 (hout hy)
    calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
      _ = dist x zout + dist y zout := by rw [dist_comm zout y]
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  have h := conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD hc0 hc1 hLem41 hIso
  rwa [show (245760 : ℝ) * (n : ℝ) * (2 * R) = 491520 * (n : ℝ) * R from by ring] at h

/-- **`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun_unitBall` with the Lemma 4.1 overlap
constant a parameter.**

The original (`ConductanceToTV.lean`) hardcodes `hLem41` at `1 − 1/500`, a constant
`HitAndRunOverlap.lean` shows the corrected proof of Lemma 4.1 does not reach.  Here the
constant is free: `hLem41` is consumed at `1 − c` for any `c ∈ (0,1]`, `hIso` is carried
verbatim, and the deadline is the honest function of `c`,

    4 · lsThreshold M (c/(491520·n·R)) ε  =  4 · 491520² · n²R²/c² · log(8M/ε²),

quadratic in `1/c`.  At `c = 1/500` this is *shorter* than the original's
`4·lvThreshold n 1 R M ε`, which is what makes the recovery below go through.

`hLem41` is a binder, not a discharged fact — see the module docstring for exactly what
blocks discharging it from `tvLe_hitAndRun_of_close_uncond`. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * ArlibCommunity.Foundations.Convex.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(ArlibCommunity.Foundations.Convex.uniformOn volume K)) *
          min (ArlibCommunity.Foundations.Convex.uniformOn volume K T₁) (ArlibCommunity.Foundations.Convex.uniformOn volume K T₂)
        ≤ ArlibCommunity.Foundations.Convex.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ} (hm : 4 * lsThreshold M (c / (491520 * (n : ℝ) * R)) eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (ArlibCommunity.Foundations.Convex.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hout)
  have hphi0 : 0 < c / (491520 * (n : ℝ) * R) := by positivity
  have hphi1 : c / (491520 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  exact tvLe_iterate_lazy_hitAndRun_param hn hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom (ofReal_le_conductance_hitAndRun_of_unitBall_param hn hKc hKcl hKm hball hR hout hc0
      hc1 hLem41 hIso) hm

/-- **The original `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun_unitBall`, recovered from
the parametric form at `c = 1/500`.**

The statement is that of `ConductanceToTV.lean` verbatim; the certificate that no binder
drifted is `tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq` below.

The proof is `le_trans` on the deadline, as the brief allows: at `c = 1/500` the parametric
deadline is `4·lsThreshold M (1/(245760000·n·R)) ε`, and the original's
`4·lvThreshold n 1 R M ε = 4·lsThreshold M (1/(2²⁸·n·R)) ε` is *longer*, because
`245760000 ≤ 2²⁸ = 268435456` — the exact rounding the original performed.  So the
parametrisation loses nothing and in fact gains a factor `(268435456/245760000)² ≈ 1.19` in
the step count. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_of_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * ArlibCommunity.Foundations.Convex.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(ArlibCommunity.Foundations.Convex.uniformOn volume K)) *
          min (ArlibCommunity.Foundations.Convex.uniformOn volume K T₁) (ArlibCommunity.Foundations.Convex.uniformOn volume K T₂)
        ≤ ArlibCommunity.Foundations.Convex.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ} (hm : 4 * lvThreshold n 1 R M eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (ArlibCommunity.Foundations.Convex.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine tvLe_iterate_lazy_hitAndRun_unitBall_param hn hKc hKcl hKm hball hR1 hout
    (c := 1 / 500) (by norm_num) (by norm_num) hM heps0 heps1 hSm hS hdom hLem41 hIso ?_
  refine le_trans ?_ hm
  have hle : lsThreshold M ((1 : ℝ) / 500 / (491520 * (n : ℝ) * R)) eps
      ≤ lvThreshold n 1 R M eps := by
    rw [← lsThreshold_eq_lvThreshold hn one_pos hR]
    refine lsThreshold_anti hM heps0 heps1 (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hn1) hR]
  linarith

/-- **The two unit-ball statements are literally the same statement.**  As for
`tvLe_iterate_lazy_hitAndRun_of_param_eq`: the equation does not elaborate unless every
binder of `tvLe_iterate_lazy_hitAndRun_unitBall_of_param` matches the original's, including
the `hIso` bundle and the corrected clause `∀ x ∈ K, h x ≤ 1/3` inside it. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq :
    @tvLe_iterate_lazy_hitAndRun_unitBall_of_param = @tvLe_iterate_lazy_hitAndRun_unitBall :=
  rfl

/-! ## 4. Towards the `hLem41` binder: the proved Lemma 4.1 in the consumer's `max` shape

`tvLe_hitAndRun_of_close_uncond` (`SphereCap.lean`) asks for
`‖u − v‖ < 2/√n · F(u)` — the median step of the **first** point.  The `hLem41` binder asks
for `dist u v < 2/√n · max(F(u), F(v))`.  The gap is closed by symmetry, at no cost: in the
branch where the max is `F(v)`, apply the lemma with the roles exchanged and flip the
conclusion with `ArlibCommunity.Foundations.Convex.TVLe.symm`.  The chord hypotheses survive the exchange because
`chordLow K v u = 1 − chordHigh K u v` and `chordHigh K v u = 1 − chordLow K u v`
(`ArlibCommunity.Foundations.Convex.chordLow_swap`, `ArlibCommunity.Foundations.Convex.chordHigh_swap`), so `ha` and `hb` simply trade places, and
`crossRatioDist` is symmetric (`ArlibCommunity.Foundations.Convex.crossRatioDist_comm`). -/

/-- **Lemma 4.1 at `1 − 1/8000`, in the `max` shape the `hLem41` binder uses.**

Every hypothesis of `tvLe_hitAndRun_of_close_uncond` is retained: `huv`, the two `hmove`s and
the two chord conditions `ha`, `hb`.  Only the step-length hypothesis is relaxed, from
`F(u)` to `max(F(u), F(v))`.

Non-vacuity: at two distinct **interior** points of a bounded convex body with nonempty
interior, `hmoveu`/`hmovev` hold by `ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_univ_eq_one_of_mem_interior`
and `ha`/`hb` hold because the chord through `u` and `v` extends strictly beyond both.  What
they exclude is boundary points, where `ha` is *always* false — which is exactly why this
lemma does not close the `hLem41` binder; see the module docstring, `What remains`, item 3. -/
theorem tvLe_hitAndRun_of_close_uncond_max {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hF : dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v)) :
    ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  rw [dist_eq_norm] at hF
  rcases max_cases (medianStep K u) (medianStep K v) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at hF
    exact tvLe_hitAndRun_of_close_uncond hn hKc hKcl hKm hKb hu hv huv hmoveu hmovev ha hb
      hdK hF
  · rw [heq, norm_sub_rev u v] at hF
    refine (tvLe_hitAndRun_of_close_uncond hn hKc hKcl hKm hKb hv hu huv.symm hmovev hmoveu
      ?_ ?_ ?_ hF).symm
    · rw [chordLow_swap hKb huv hu]; linarith
    · rw [chordHigh_swap hKb huv hu]; linarith
    · rwa [← crossRatioDist_comm hKb huv hu hv]

/-! ## 5. The instantiation at the proved overlap constant `1 − 1/8000` -/

/-- **Theorem 1.1 for the lazy hit-and-run walk on a body with a unit inball, at the overlap
constant `1 − 1/8000` that `tvLe_hitAndRun_of_close_uncond` proves.**

    Φ  ≥  1/(3932160000·n·R)  ≥  1/(2³²·n·R),   deadline  4 · 2⁶⁴ · n²R² · log(8M/ε²).

Exactly `256 = (8000/500)²` times the original's `4 · 2⁵⁶ · n²R² · log(8M/ε²)`, and the same
`O(n²R²·log(M/ε))` shape.  (`8000 · 491520 = 3932160000 ≤ 2³² = 4294967296`; the deadline is
quadratic in `1/c`, and the rounding of `3932160000` up to `2³²` is what makes the ratio
exactly `256` rather than `214.6…`.)

`hLem41` is **still a binder** here, now at the constant the repository actually proves.
`tvLe_hitAndRun_of_close_uncond_max` above supplies it pointwise for two distinct interior
points; the module docstring says precisely why that does not close the binder, which ranges
over all of `K`.  `hIso` is likewise a binder, as everywhere in this chain. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_8000 {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * ArlibCommunity.Foundations.Convex.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(ArlibCommunity.Foundations.Convex.uniformOn volume K)) *
          min (ArlibCommunity.Foundations.Convex.uniformOn volume K T₁) (ArlibCommunity.Foundations.Convex.uniformOn volume K T₂)
        ≤ ArlibCommunity.Foundations.Convex.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ}
    (hm : 4 * (2 ^ 64 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2)) ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (ArlibCommunity.Foundations.Convex.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine tvLe_iterate_lazy_hitAndRun_unitBall_param hn hKc hKcl hKm hball hR1 hout
    (c := 1 / 8000) (by norm_num) (by norm_num) hM heps0 heps1 hSm hS hdom hLem41 hIso ?_
  refine le_trans ?_ hm
  have hstep : lsThreshold M ((1 : ℝ) / 8000 / (491520 * (n : ℝ) * R)) eps
      ≤ lsThreshold M (1 / (2 ^ 32 * (n : ℝ) * R)) eps := by
    refine lsThreshold_anti hM heps0 heps1 (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hn1) hR]
  have hval : lsThreshold M (1 / (2 ^ 32 * (n : ℝ) * R)) eps
      = 2 ^ 64 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [lsThreshold, div_pow, one_pow]
    field_simp
  rw [← hval]
  linarith

/-! ## Axiom profile -/

section AxiomCheck

#print axioms lsThreshold_anti
#print axioms tvLe_iterate_lazy_hitAndRun_param
#print axioms tvLe_iterate_lazy_hitAndRun_of_param
#print axioms tvLe_iterate_lazy_hitAndRun_of_param_eq
#print axioms ofReal_le_conductance_hitAndRun_of_unitBall_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_of_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq
#print axioms tvLe_hitAndRun_of_close_uncond_max
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_8000

end AxiomCheck

end ArlibCommunity.Foundations.MarkovChainTheory

end

section
/-!
# Lemma 4.1 discharged, and Theorem 4.2 with `hLem41` gone

`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_uncond` (`SphereCap.lean`) proves Lovász–Vempala's
Lemma 4.1 with no unproved hypothesis, at overlap constant `1 − 1/8000`, for `n ≥ 1100`.  It
was nevertheless unusable as a discharge of the `hLem41` binder of Theorem 4.2, because it
carries three side conditions that the binder does not:

* `hmoveu`, `hmovev` — `hitAndRunProposal K u Set.univ = 1`;
* `ha` — `chordLow K u v < 0`;
* `hb` — `1 < chordHigh K u v`.

**`ha` is not merely inconvenient at the boundary; it is false there.**  For `u ∈ K` outside
`interior K` and `v ∈ interior K`, a point `u + t(v − u) ∈ K` with `t < 0` would put `u` on an
open segment between a point of `K` and an interior `K`, hence in `interior K`. So
`chordLow K u v = 0` for every such pair, in every body, in every dimension — proved below as
`ArlibCommunity.Foundations.MarkovChainTheory.chordLow_eq_zero_of_notMem_interior`.  As long as the `hLem41` binder is
stated over all of `K`, no route through `tvLe_hitAndRun_of_close_uncond` can close it, and a
theorem asserting `∀ u ∈ K, ∀ v ∈ K, u ≠ v → chordLow K u v < 0` would be vacuous.

The resolution is that Theorem 4.2's proof never needed the binder over all of `K`: it cuts
`S₁'` and `S₂'` down to `interior K` (`HitAndRunConductance.lean`, module docstring, § *Two
places where the formalisation is more careful than the paper*, item 1) and applies `hLem41`
only at interior points.  `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_tv_interior` is that
theorem with the binder weakened accordingly — a strictly weaker hypothesis, as the derivation
of the unchanged `conductance_hitAndRun_ge_of_tv` from it witnesses.  On `interior K` all three
side conditions are available:

| side condition | source |
|---|---|
| `hmove` | `ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_univ_eq_one_of_mem_interior` |
| `ha` | `ArlibCommunity.Foundations.Convex.chordLow_neg_of_mem_interior` |
| `hb` | `ArlibCommunity.Foundations.Convex.one_lt_chordHigh_of_mem_interior` |
| `max (medianStep K u) (medianStep K v)` versus `medianStep K u` | `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_uncond_max` |
| `u ≠ v` | case split; `ArlibCommunity.Foundations.Convex.TVLe.refl` and `ArlibCommunity.Foundations.Convex.TVLe.mono` on the diagonal |

## What is here

| name | content |
|---|---|
| `tvLe_hitAndRun_of_close_interior` | **Lemma 4.1 as the interior binder, proved**: `∀ u ∈ interior K, ∀ v ∈ interior K, …` at `1 − 1/8000`, `n ≥ 1100`, no unproved hypothesis |
| `conductance_hitAndRun_ge_uncond_overlap` | Theorem 4.2 with `hLem41` **gone**: `Φ ≥ (1/8000)/(245760·n·D)`, only the isoperimetry binder left |
| `conductance_hitAndRun_ge_uncond_overlap_pow` | the same, rounded to `Φ ≥ 1/(2³¹·n·D)` |
| `chordLow_eq_zero_of_notMem_interior` | the boundary obstruction, proved: `chordLow K u v = 0` for `u ∈ K \ interior K`, `v ∈ interior K` |

## Constants

`1966080000 = 8000 · 245760`, and `1966080000 ≤ 2³¹ = 2147483648`.  The paper's Theorem 4.2
reads `Φ ≥ 1/(2²⁴·n·D)`; the `2³¹` here is `2²⁴` times `8000/500 = 16` (Lemma 4.1's corrected
constant, `HitAndRunOverlap.lean`) times a further `8` from the factor `10` in the proved
Lemma 3.3 and the rounding to a power of two.  The order `1/(n·D)` is the paper's.

## What remains in Theorem 4.2

Only `hIso`, the paper's Theorem 2.1 (weighted isoperimetry) in the corrected form carrying
`∀ x ∈ K, h x ≤ 1/3`, without which it is false (`not_hIso_two`).  Nothing here touches
it, and nothing here assumes it: it is passed through verbatim.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. Lemma 4.1 on the interior, with no unproved hypothesis -/

/-- **Lovász–Vempala's Lemma 4.1, in exactly the shape the (interior-ised) `hLem41` binder of
Theorem 4.2 asks for, proved.**

For `n ≥ 1100` and a convex, closed, measurable, bounded `K`: any two points of `interior K`
at cross-ratio distance `< 1/8` whose separation is `< (2/√n)·max(F u, F v)` have one-step
hit-and-run laws within total variation `1 − 1/8000`.

Every hypothesis of `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_uncond_max` beyond the two the
binder supplies is discharged here, and each of them is exactly what needs the interior:
`hitAndRunProposal K u univ = 1` from `ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_univ_eq_one_of_mem_interior`,
`chordLow K u v < 0` from `ArlibCommunity.Foundations.Convex.chordLow_neg_of_mem_interior`, and `1 < chordHigh K u v` from
`ArlibCommunity.Foundations.Convex.one_lt_chordHigh_of_mem_interior`.  The diagonal `u = v` is not excluded by the binder
and is handled separately, by reflexivity.

This is a *statement about all interior pairs*, not a binder: it has no hypothesis that the
caller must supply beyond the geometry of `K` and `1100 ≤ n`. -/
theorem tvLe_hitAndRun_of_close_interior (hn : 21 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) :
    ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  -- the walk leaves every interior point with probability one
  have hmove : ∀ x ∈ interior K, hitAndRunProposal K x Set.univ = 1 := by
    intro x hx
    obtain ⟨ε, hε, hbx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    exact hitAndRunProposal_univ_eq_one_of_mem_interior hKm hε (hbx.trans interior_subset) hR
  intro u hu v hv hdK hF
  rcases eq_or_ne u v with rfl | huv
  · exact (ArlibCommunity.Foundations.Convex.TVLe.refl _).mono bot_le
  exact tvLe_hitAndRun_of_close_uncond_max hn hKc hKcl hKm hKb (interior_subset hu)
    (interior_subset hv) huv (hmove u hu) (hmove v hv)
    (chordLow_neg_of_mem_interior hKb huv hu) (one_lt_chordHigh_of_mem_interior hKb huv hv)
    hdK hF

/-! ## 2. Theorem 4.2 with `hLem41` gone -/

/-- **Theorem 4.2 of Lovász–Vempala with the Lemma 4.1 binder discharged.**

    Φ(hit-and-run on K)  ≥  (1/8000) / (245760 · n · D).

`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_tv_interior` at `lam = 1/8000`, with its
`hLem41` supplied by `tvLe_hitAndRun_of_close_interior` rather than assumed.  The only mathematical
hypothesis left is `hIso`, the corrected Theorem 2.1, carried through verbatim.

Not routed through `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_param`: that theorem states
its `hLem41` over all of `K`, which is the form the boundary refutes
(`chordLow_eq_zero_of_notMem_interior` below).  The conclusion is the one `_param` would give
at `c = 1/8000`. -/
theorem conductance_hitAndRun_ge_uncond_overlap (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
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
    ENNReal.ofReal (1 / 8000 / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_tv_interior (by omega) hKc hKcl hKm hKb hball hD
    (by norm_num) (by norm_num) (tvLe_hitAndRun_of_close_interior hn hKc hKcl hKm hKb) hIso

/-- **The same bound, rounded to a power of two**: `Φ ≥ 1/(2³¹·n·D)`.

`8000 · 245760 = 1966080000 ≤ 2³¹ = 2147483648`.  Purely for legibility, in the style of
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge`'s `2²⁷`; the exact form
`conductance_hitAndRun_ge_uncond_overlap` is strictly stronger. -/
theorem conductance_hitAndRun_ge_uncond_overlap_pow (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
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
    ENNReal.ofReal (1 / (2 ^ 31 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn1 hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_uncond_overlap hn hKc hKcl hKm hKb hball hD hIso)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## 3. Why the `∀ u ∈ K` form is not available -/

/-- **The chord does not extend past a boundary point.**

For `K` convex, closed and bounded, `u ∈ K \ interior K` and `v ∈ interior K` with `u ≠ v`,

    chordLow K u v = 0,

so the hypothesis `ha : chordLow K u v < 0` of
`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_uncond` fails at every such pair.  This is why the
`∀ u ∈ K, ∀ v ∈ K` form of the `hLem41` binder cannot be discharged through that route, and
why `tvLe_hitAndRun_of_close_interior` is stated on `interior K`.

The argument: `chordLow ≤ 0` always (`ArlibCommunity.Foundations.Convex.chordLow_nonpos`).  Were it `< 0`, the chord
parameter set — an interval, by `ArlibCommunity.Foundations.Convex.chordParam_eq_Icc` — would contain that negative value
`s`, i.e. `w = u + s(v − u) ∈ K`.  Then `u` is the combination
`(−s/(1−s))·v + (1/(1−s))·w` with a strictly positive weight on the interior point `v`, so
`Convex.combo_interior_closure_mem_interior` puts `u` in `interior K`. -/
theorem chordLow_eq_zero_of_notMem_interior {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) (hu : u ∈ K) (hu' : u ∉ interior K)
    (hv : v ∈ interior K) : chordLow K u v = 0 := by
  refine le_antisymm (chordLow_nonpos hKb huv hu) (not_lt.mp fun hlt => hu' ?_)
  set s : ℝ := chordLow K u v with hsdef
  -- the chord parameter set is `Icc (chordLow) (chordHigh)`, so `s` itself is a parameter
  have hsmem : s ∈ chordParam K u v := by
    rw [chordParam_eq_Icc hKc hKcl hKb huv hu]
    exact ⟨le_rfl, chordLow_le_chordHigh hKb huv hu (interior_subset hv)⟩
  set w : EuclideanSpace ℝ (Fin n) := (AffineMap.lineMap u v : ℝ → _) s with hwdef
  have hwK : w ∈ K := hsmem
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hs1' : (1 : ℝ) - s ≠ 0 := hs1.ne'
  set a : ℝ := -s / (1 - s) with hadef
  set b : ℝ := 1 / (1 - s) with hbdef
  have ha0 : 0 < a := by rw [hadef]; exact div_pos (by linarith) hs1
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hab : a + b = 1 := by rw [hadef, hbdef]; field_simp; ring
  have hcombo : a • v + b • w = u := by
    rw [hwdef, ArlibCommunity.Foundations.Convex.lineMap_apply']
    rw [hadef, hbdef]
    match_scalars <;> field_simp <;> ring
  have := hKc.combo_interior_closure_mem_interior hv (subset_closure hwK) ha0 hb0 hab
  rwa [hcombo] at this

/-! ## Axiom profile -/

section AxiomCheck

#print axioms tvLe_hitAndRun_of_close_interior
#print axioms conductance_hitAndRun_ge_uncond_overlap
#print axioms conductance_hitAndRun_ge_uncond_overlap_pow
#print axioms chordLow_eq_zero_of_notMem_interior

end AxiomCheck

end ArlibCommunity.Foundations.MarkovChainTheory

end

section
/-!
# Theorem 4.2 of Lovász–Vempala, with no mathematical hypothesis

    Φ(hit-and-run on K)  ≥  (1/8000) / (245760 · n · D)   ≥   1 / (2³¹ · n · D)

for every convex, closed, measurable, bounded `K ⊆ ℝⁿ` containing a unit ball, with
`diam K ≤ D` and `n ≥ 1100`.

**Every binder is gone.**  The statement of `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond` below carries
only hypotheses about `n` and about the geometry of `K` — no `hIso`, no `hLem41`, no `htrans`, no
`hloc`.  Nothing here is assumed; this file is a composition of four theorems that are each
already proved and axiom-clean elsewhere in this repository.

## The four inputs

| binder of Theorem 4.2 | discharged by | file |
|---|---|---|
| `hLem41` (Lemma 4.1, on `interior K`, at `1 − 1/8000`) | `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_interior` | `MarkovChains/Continuous/HitAndRunLem41Discharge.lean` |
| `hIso` (Theorem 2.1, corrected, at lower semicontinuous weights) | `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` | `Convexity/IsoConcaveWeight.lean` |
| `htrans` (the chord transfer) | `ArlibCommunity.Foundations.Convex.htrans_of_compact` | `Convexity/ChordContinuity.lean` |
| `hloc` (Localization with the needle inside the body) | `ArlibCommunity.Foundations.Convex.hloc_needle_in_body` | `Convexity/LocalizationNeedleInBody.lean` |

`hIso` is fed to the *lower semicontinuous* replay of Theorem 4.2,
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_tv_lsc_interior`, because that is the only shape in which the
weight `x ↦ s_{63/64}(x)/(48·D·√n)` — concave on `K`, hence continuous only on `interior K` — can
be handed to an isoperimetric inequality proved for continuous integrands.

## Why `hLem41` is demanded on `interior K` and not on `K`

Because on `K` it is *unsatisfiable*.  The paper's Lemma 4.1 needs `chordLow K u v < 0`, and for
`u ∈ K \ interior K`, `v ∈ interior K`, `u ≠ v` one has `chordLow K u v = 0` in every body and
every dimension (`ArlibCommunity.Foundations.MarkovChainTheory.chordLow_eq_zero_of_notMem_interior`).  So a `∀ u ∈ K,
∀ v ∈ K` binder of that shape can never be discharged, and any theorem carrying it is vacuous.

The interior form is what Theorem 4.2's proof actually uses — it cuts `S₁`, `S₂` down to
`interior K` — and it is a *weaker* hypothesis, as the one-line derivations of the unchanged
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_tv_lsc`, `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_lsc` and
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_transfer_of_localization` from their `_interior` forms
witness.

## The side conditions on the volume

`ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` asks for `volume K ≠ 0` and `volume K ≠ ⊤`.  Neither is a
hypothesis here: the first follows from `closedBall z 1 ⊆ K` by `Metric.measure_closedBall_pos`,
the second from `Bornology.IsBounded K` by `measure_closedBall_lt_top`.

## The constant

`1/8000 / 245760 = 1/1966080000`, and `1966080000 ≤ 2³¹ = 2147483648`, whence the rounded form.
The paper states `1/(2²⁴·n·D)`.  The extra `2⁷` is `16` from Lemma 4.1's corrected overlap
constant (`8000` in place of the paper's `500`) times `8` from the factor `10` in the proved
Lemma 3.3 and the rounding to a power of two.  The order `1/(n·D)` is the paper's.

## What is here

| name | content |
|---|---|
| `conductance_hitAndRun_ge_uncond` | **Theorem 4.2 with no mathematical hypothesis**: `Φ ≥ (1/8000)/(245760·n·D)` |
| `conductance_hitAndRun_ge_uncond_pow` | the same, rounded: `Φ ≥ 1/(2³¹·n·D)` |
-/

open ArlibCommunity.Foundations.MarkovChainTheory ArlibCommunity.Foundations.Convex

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-- **Theorem 4.2 of Lovász–Vempala, unconditionally.**

    Φ(hit-and-run on K)  ≥  (1/8000) / (245760 · n · D).

For `n ≥ 1100` and a convex, closed, measurable, bounded body `K ⊆ ℝⁿ` containing a unit ball
`closedBall z 1` and of diameter at most `D`, the conductance of the hit-and-run walk on `K` with
respect to the uniform measure on `K` is at least `(1/8000)/(245760·n·D)`.

**There is no mathematical hypothesis.**  Every hypothesis above is about `n` or about the
geometry of `K`; the four binders that Theorem 4.2 used to carry — `hIso` (the paper's Theorem
2.1, in its corrected form), `hLem41` (Lemma 4.1, on the interior — the only satisfiable form),
`htrans` (the chord transfer) and `hloc` (the Localization Lemma with the needle inside the body)
— are supplied here by proved theorems, not assumed:

* `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_hitAndRun_of_close_interior` for `hLem41` at `1 − 1/8000`;
* `ArlibCommunity.Foundations.Convex.htrans_of_compact` for `htrans`;
* `ArlibCommunity.Foundations.Convex.hloc_needle_in_body` for `hloc`;
* `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` for `hIso`, built from the previous two.

`volume K ≠ 0` and `volume K ≠ ⊤`, which `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` asks for, are derived
from `hball` and `hKb` rather than assumed. -/
theorem conductance_hitAndRun_ge_uncond (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) :
    ENNReal.ofReal (1 / 8000 / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  exact conductance_hitAndRun_ge_of_tv_lsc_interior (by omega) hKc hKcl hKm hKb hball hD
    (by norm_num) (by norm_num) (tvLe_hitAndRun_of_close_interior hn hKc hKcl hKm hKb)
    (hIso_lowerSemicontinuous hKc hKcl hKm hKb hK0 hKtop (htrans_of_compact hKc hKcl hKb)
      (hloc_needle_in_body (by omega) hKc hKcl hKb))

/-- **The same bound, rounded to a power of two**: `Φ ≥ 1/(2³¹·n·D)`.

`8000 · 245760 = 1966080000 ≤ 2³¹ = 2147483648`.  Purely for legibility; the exact form
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond` is strictly stronger.  Like it, this statement has no
mathematical hypothesis. -/
theorem conductance_hitAndRun_ge_uncond_pow (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) :
    ENNReal.ofReal (1 / (2 ^ 31 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn1 hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_uncond hn hKc hKcl hKm hKb hball hD)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end ArlibCommunity.Foundations.MarkovChainTheory

/-! ### Axiom profile -/

section AxiomCheck

#print axioms ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond
#print axioms ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond_pow

end AxiomCheck

end

section
/-!
# Theorem 1.1 of Lovász–Vempala for the lazy hit-and-run walk, with no mathematical hypothesis

`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond` (`Convexity/HitAndRunConductanceUncond.lean`) made
Theorem 4.2 unconditional:

    Φ(hit-and-run on K)  ≥  (1/8000)/(245760·n·D)  ≥  1/(2³¹·n·D)

for `n ≥ 1100` and a convex, closed, measurable, bounded `K ⊆ ℝⁿ` with a unit inball and
`diam K ≤ D`.  This file pushes that through the mixing theorem.

`ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun_param` (`HitAndRunUncond.lean`) is Theorem
1.1 with the conductance value a free parameter `phi` and deadline `4·lsThreshold M phi ε`.
Instantiating it at `phi = 1/(2³¹·n·D)` and feeding `conductance_hitAndRun_ge_uncond_pow` for
`hphi` gives

    `ArlibCommunity.Foundations.MarkovChainTheory.tvLe_iterate_lazy_hitAndRun_uncond`,

in which **no conductance, isoperimetry or overlap hypothesis remains**.

## The deadline

`lsThreshold M phi ε = log(8M/ε²)/phi²`, and `1/phi² = 2⁶²·n²·D²`, so `4·lsThreshold` is

    `hrDeadlineUncond n D M ε  =  2⁶⁴ · n² · D² · log(8M/ε²)`,

recorded as a definition and identified with `4 · lsThreshold M (1/(2³¹·n·D)) ε` by
`hrDeadlineUncond_eq`.  This is the paper's `O(n²D²·log(M/ε))` shape.

## Contents

| name | content |
|---|---|
| `hrDeadlineUncond` | `2⁶⁴·n²D²·log(8M/ε²)`, the deadline in closed form |
| `hrDeadlineUncond_eq` | it **is** `4 · lsThreshold M (1/(2³¹·n·D)) ε` |
| `tvLe_iterate_lazy_hitAndRun_uncond` | Theorem 1.1, no conductance/isoperimetry/overlap binder |
| `tvLe_iterate_lazy_hitAndRun_uncond_ball` | the same for `K ⊆ closedBall zout R`, deadline `2⁶⁶·n²R²·log(8M/ε²)` |
| `tvLe_iterate_lazy_hitAndRun_uncond_witness` | a concrete instance of every hypothesis at once |

## What remains, and why

The **warm-start data** `M`, `S`, `hM`, `hS`, `hdom` stays.  It is Lovász–Vempala Theorem 1.1's
own `(M, S)` clause — "the density `dσ/dπ_K` is bounded by `M` except on a set `S` with
`σ(S) ≤ ε/2`" — not a lemma this repository failed to prove; a mixing theorem without *some*
hypothesis on the start distribution is false (a point mass never mixes in a bounded number of
steps under a fixed bound).  Beyond that only `0 < ε ≤ 1`, `1100 ≤ n` and the geometry of `K`
remain, exactly as in Theorem 4.2.

`hM : 1 ≤ M` is not a restriction: `M = 1` with `S = ∅` is the stationary start, and the witness
below uses it.

## The exact form is stronger

The composition is done at the power-of-two conductance bound `1/(2³¹·n·D)` because it makes the
deadline a clean `2⁶⁴·n²D²·log(8M/ε²)`.  `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond`'s exact value
`(1/8000)/(245760·n·D) = 1/(1966080000·n·D)` is strictly larger, hence gives a strictly shorter
deadline (by a factor `(2³¹/1966080000)² ≈ 1.19`); `lsThreshold_anti` would carry it across.  No
second theorem is stated for it.

## Non-vacuity

`tvLe_iterate_lazy_hitAndRun_uncond_witness` discharges **every** hypothesis simultaneously:
`K = closedBall 0 1` in `ℝ¹¹⁰⁰`, `D = 2`, `σ = uniformOn volume K`, `M = 1`, `S = ∅`, `ε = 1/2`,
and an explicit step count past the deadline.  The conclusion is a genuine `1/2`-total-variation
bound, not the trivial `ε = 1` one.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

/-! ## 1. The deadline in closed form -/

/-- **`hrDeadlineUncond` is `4 · lsThreshold M (1/(2³¹·n·D)) ε`.**  Pure arithmetic:
`(1/(2³¹nD))² = 1/(2⁶²n²D²)`, and `4 · 2⁶² = 2⁶⁴`.  Stated as an equation so that a caller
holding either form of the deadline hypothesis holds the other. -/
theorem hrDeadlineUncond_eq {n : ℕ} {D M eps : ℝ} (hn : (n : ℝ) ≠ 0) (hD : D ≠ 0) :
    hrDeadlineUncond n D M eps = 4 * lsThreshold M (1 / (2 ^ 31 * (n : ℝ) * D)) eps := by
  rw [hrDeadlineUncond, lsThreshold, div_pow, one_pow]
  field_simp
  ring

/-! ## 2. Theorem 1.1, unconditional -/

/-- **Theorem 1.1 of Lovász–Vempala for the lazy hit-and-run walk, with no conductance,
isoperimetry or overlap hypothesis.**

For `n ≥ 1100` and a convex, closed, measurable, bounded `K ⊆ ℝⁿ` containing a unit ball, of
diameter at most `D`, the lazy hit-and-run walk started at any `(M, S)`-warm `σ` is within `ε`
in total variation of the uniform measure on `K` after

    `hrDeadlineUncond n D M ε  =  2⁶⁴ · n² · D² · log(8M/ε²)`

steps.

Every binder that used to carry mathematics is discharged: `hphi` is
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond_pow`, which in turn absorbed `hIso`, `hLem41`, `htrans`
and `hloc`.  What is left is the geometry of `K`, `0 < ε ≤ 1`, and the warm-start data
`M`, `S`, `hM`, `hS`, `hdom` — Theorem 1.1's own hypothesis on the starting distribution, which
no mixing theorem can drop.  See the module docstring.

`volume K ≠ 0` and `volume K ≠ ⊤`, which the parametric form asks for, are derived here from
`hball` and `hKb` rather than assumed, exactly as in
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond`. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    {m : ℕ} (hm : hrDeadlineUncond n D M eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn1 hKb hball) hD
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  have hphi0 : 0 < 1 / (2 ^ 31 * (n : ℝ) * D) := by positivity
  have hphi1 : 1 / (2 ^ 31 * (n : ℝ) * D) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  refine tvLe_iterate_lazy_hitAndRun_param hn1 hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom (ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_uncond_pow hn hKc hKcl hKm hKb hball hD) ?_
  rwa [hrDeadlineUncond_eq (by positivity) (by positivity)] at hm

/-! ## 3. The circumradius form -/

/-- **Theorem 1.1, unconditional, for a body inside a ball of radius `R`.**

`K ⊆ closedBall zout R` gives `diam K ≤ 2R` by the triangle inequality, so §2 applies at
`D = 2R`, where the conductance bound reads `Φ ≥ 1/(2³²·n·R)` and the deadline is

    `hrDeadlineUncond n (2R) M ε  =  2⁶⁶ · n² · R² · log(8M/ε²)`

— a factor `4` worse than the diameter form, which is the price of measuring a body by its
circumradius.  This is the shape of the original `tvLe_iterate_lazy_hitAndRun_unitBall`, whose
deadline `4 · lvThreshold n 1 R M ε = 2⁵⁸·n²R²·log(8M/ε²)` this exceeds by exactly
`(8000/500)² = 256`, the square of the corrected Lemma 4.1 constant.  The rounding of the
conductance denominator to a power of two costs the same factor `16` on both routes
(`245760000 → 2²⁸` and `3932160000 → 2³²`), so it cancels from the comparison.

No hypothesis on `R` is needed: `0 ≤ R` follows from `hball` and `hout` (the body is
nonempty), and `1 ≤ 2R` from `one_le_diam_of_unitBall` inside §2.  Like §2, this statement has
no conductance, isoperimetry or overlap binder. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond_ball {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    {m : ℕ}
    (hm : 2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2) ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hout
  have hzK : z ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
  have hRnn : (0 : ℝ) ≤ R := le_trans dist_nonneg (Metric.mem_closedBall.1 (hout hzK))
  have hD : Metric.diam K ≤ 2 * R := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.1 (hout hx)
    have hy' := Metric.mem_closedBall.1 (hout hy)
    calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
      _ = dist x zout + dist y zout := by rw [dist_comm zout y]
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  refine tvLe_iterate_lazy_hitAndRun_uncond hn hKc hKcl hKm hKb hball hD hM heps0 heps1 hSm hS
    hdom ?_
  rwa [hrDeadlineUncond, show (2 : ℝ) ^ 64 * (n : ℝ) ^ 2 * (2 * R) ^ 2 = 2 ^ 66 * (n : ℝ) ^ 2 * R ^ 2
    from by ring]

/-! ## 4. Non-vacuity

Every hypothesis of §2 at once, on a body that satisfies them all: the unit ball of `ℝ¹¹⁰⁰`,
started at its own uniform measure.  `M = 1` with `S = ∅` is the stationary start — the
smallest legal warm-start datum — and `ε = 1/2` keeps the conclusion a real bound (at `ε = 1`
`TVLe` holds between any two probability measures for trivial reasons).

The step count `2⁶⁴ · 150040000` is past the deadline because
`hrDeadlineUncond 1100 2 1 (1/2) = 2⁶⁴ · 1100² · 2² · log 32` and `log 32 ≤ 31`. -/

/-- **A concrete instance discharging every hypothesis of
`tvLe_iterate_lazy_hitAndRun_uncond` simultaneously.**

`K = closedBall 0 1 ⊆ ℝ¹¹⁰⁰`, `n = 1100`, `D = 2`, `σ = uniformOn volume K`, `M = 1`,
`S = ∅`, `ε = 1/2`, `m = 2⁶⁴·150040000`.

The geometry is immediate (`convex_closedBall`, `Metric.isClosed_closedBall`,
`measurableSet_closedBall`, `Metric.isBounded_closedBall`, `hball` is `subset_rfl`, and
`Metric.diam_closedBall` gives `diam K ≤ 2`).  The warm start is the stationary one:
`σ(∅) = 0 ≤ ε/2` and `σ(A \ ∅) = σ A = 1 · π_K(A)`, so `hS` and `hdom` hold with `M = 1`.

Without this the theorem above could be vacuous. -/
theorem tvLe_iterate_lazy_hitAndRun_uncond_witness :
    ArlibCommunity.Foundations.Convex.TVLe
      (iterate (lazy (hitAndRun (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1)))
        (uniformOn volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
        (2 ^ 64 * 150040000))
      (uniformOn volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1100)) 1))
      (ENNReal.ofReal (1 / 2)) := by
  set K : Set (EuclideanSpace ℝ (Fin 1100)) := Metric.closedBall 0 1 with hK
  have hK0 : volume K ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hD : Metric.diam K ≤ 2 := by
    simpa using Metric.diam_closedBall (x := (0 : EuclideanSpace ℝ (Fin 1100)))
      (zero_le_one' ℝ)
  have hlog : Real.log (8 * 1 / ((1 : ℝ) / 2) ^ 2) ≤ 31 := by
    have h32 : (8 : ℝ) * 1 / ((1 : ℝ) / 2) ^ 2 = 32 := by norm_num
    have := Real.log_le_sub_one_of_pos (x := (32 : ℝ)) (by norm_num)
    rw [h32]
    linarith
  refine tvLe_iterate_lazy_hitAndRun_uncond (n := 1100) (by norm_num) (convex_closedBall 0 1)
    Metric.isClosed_closedBall measurableSet_closedBall Metric.isBounded_closedBall
    (z := 0) subset_rfl hD (M := 1) (eps := 1 / 2) le_rfl (by norm_num) (by norm_num)
    (S := ∅) MeasurableSet.empty (by simp)
    (fun A _ => by rw [Set.sdiff_empty, ENNReal.ofReal_one, one_mul]) ?_
  rw [hrDeadlineUncond]
  push_cast
  nlinarith [hlog, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8 * 1 / ((1 : ℝ) / 2) ^ 2)]

/-! ## Axiom profile -/

section AxiomCheck

#print axioms hrDeadlineUncond_eq
#print axioms tvLe_iterate_lazy_hitAndRun_uncond
#print axioms tvLe_iterate_lazy_hitAndRun_uncond_ball
#print axioms tvLe_iterate_lazy_hitAndRun_uncond_witness

end AxiomCheck

end ArlibCommunity.Foundations.MarkovChainTheory

end
