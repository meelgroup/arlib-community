/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunConductance

/-!
# The hit-and-run conductance bound with the Lemma 4.1 overlap constant as a parameter

`Arlib.MarkovChains.conductance_hitAndRun_ge`
(`Arlib/MarkovChains/Continuous/HitAndRunConductance.lean:999`) states Theorem 4.2 of
Lovász–Vempala with the paper's **Lemma 4.1 constant hardcoded**: its binder demands

    Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500))

and **nothing this repository proves can feed that hypothesis**.  The module docstring of
`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean` (§ "Constants: the printed `1/6` is
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

* `Arlib.MarkovChains.conductance_hitAndRun_ge_param` — the parametric statement, at a free
  overlap constant `c` with `0 < c ≤ 1`, concluding `ofReal (c / (245760 · n · D))`.
* `Arlib.MarkovChains.conductance_hitAndRun_ge_of_param` — **the faithfulness check**: the
  original statement of `conductance_hitAndRun_ge`, verbatim, re-derived from the parametric
  one at `c = 1/500`.  It does not call `conductance_hitAndRun_ge`; it repeats that theorem's
  own final comparison, so a successful build certifies that the parametrisation loses
  nothing.
* `Arlib.MarkovChains.conductance_hitAndRun_ge_2048` and
  `Arlib.MarkovChains.conductance_hitAndRun_ge_34386` — the instantiations at `c = 1/2048`
  and `c = 1/34386`, in exact form, with `..._pow` variants rounded to a power of two.
* `Arlib.MarkovChains.conductance_hitAndRun_ge_param_of_le` — graceful degradation: an
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

namespace Arlib.MarkovChains

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
compose with whatever Lemma 4.1 actually delivers — `Arlib/…/HitAndRunOverlap.lean` shows the
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
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

/-- **The original `Arlib.MarkovChains.conductance_hitAndRun_ge`, recovered from the
parametric form at `c = 1/500`.**

The statement is that of `conductance_hitAndRun_ge`
(`HitAndRunConductance.lean:999`) verbatim, down to the binder names and the `2²⁷`.  The
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
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
`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean` reports for the corrected Lemma 4.1
(`1 − 1/1892.8…` as `n → ∞`); it is a round value, not a proved one — the overlap hypothesis
is still a binder here. -/
theorem conductance_hitAndRun_ge_2048 (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 2048)))
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
`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean` reports at `n = 5`, the
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 34386)))
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 2048)))
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 34386)))
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
`0 < c ≤ 1` the conductance bound at `c` holds.  Immediate from `Arlib.TVLe.mono`, since
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
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c')))
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

end Arlib.MarkovChains
