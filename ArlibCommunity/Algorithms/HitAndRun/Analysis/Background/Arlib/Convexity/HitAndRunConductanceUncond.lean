/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.ChordContinuity
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationNeedleInBody
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunLem41Discharge

/-!
# Theorem 4.2 of Lovász–Vempala, with no mathematical hypothesis

    Φ(hit-and-run on K)  ≥  (1/8000) / (245760 · n · D)   ≥   1 / (2³¹ · n · D)

for every convex, closed, measurable, bounded `K ⊆ ℝⁿ` containing a unit ball, with
`diam K ≤ D` and `n ≥ 1100`.

**Every binder is gone.**  The statement of `Arlib.conductance_hitAndRun_ge_uncond` below carries
only hypotheses about `n` and about the geometry of `K` — no `hIso`, no `hLem41`, no `htrans`, no
`hloc`.  Nothing here is assumed; this file is a composition of four theorems that are each
already proved and axiom-clean elsewhere in this repository.

## The four inputs

| binder of Theorem 4.2 | discharged by | file |
|---|---|---|
| `hLem41` (Lemma 4.1, on `interior K`, at `1 − 1/8000`) | `Arlib.MarkovChains.hLem41_interior_uncond` | `MarkovChains/Continuous/HitAndRunLem41Discharge.lean` |
| `hIso` (Theorem 2.1, corrected, at lower semicontinuous weights) | `Arlib.hIso_lowerSemicontinuous` | `Convexity/IsoConcaveWeight.lean` |
| `htrans` (the chord transfer) | `Arlib.htrans_of_compact` | `Convexity/ChordContinuity.lean` |
| `hloc` (Localization with the needle inside the body) | `Arlib.hloc_needle_in_body` | `Convexity/LocalizationNeedleInBody.lean` |

`hIso` is fed to the *lower semicontinuous* replay of Theorem 4.2,
`Arlib.conductance_hitAndRun_ge_of_tv_lsc_interior`, because that is the only shape in which the
weight `x ↦ s_{63/64}(x)/(48·D·√n)` — concave on `K`, hence continuous only on `interior K` — can
be handed to an isoperimetric inequality proved for continuous integrands.

## Why `hLem41` is demanded on `interior K` and not on `K`

Because on `K` it is *unsatisfiable*.  The paper's Lemma 4.1 needs `chordLow K u v < 0`, and for
`u ∈ K \ interior K`, `v ∈ interior K`, `u ≠ v` one has `chordLow K u v = 0` in every body and
every dimension (`Arlib.MarkovChains.chordLow_eq_zero_of_notMem_interior`).  So a `∀ u ∈ K,
∀ v ∈ K` binder of that shape can never be discharged, and any theorem carrying it is vacuous.

The interior form is what Theorem 4.2's proof actually uses — it cuts `S₁`, `S₂` down to
`interior K` — and it is a *weaker* hypothesis, as the one-line derivations of the unchanged
`Arlib.conductance_hitAndRun_ge_of_tv_lsc`, `Arlib.conductance_hitAndRun_ge_lsc` and
`Arlib.conductance_hitAndRun_ge_of_transfer_of_localization` from their `_interior` forms
witness.

## The side conditions on the volume

`Arlib.hIso_lowerSemicontinuous` asks for `volume K ≠ 0` and `volume K ≠ ⊤`.  Neither is a
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

namespace Arlib

open MeasureTheory ProbabilityTheory Metric MarkovChains
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

* `Arlib.MarkovChains.hLem41_interior_uncond` for `hLem41` at `1 − 1/8000`;
* `Arlib.htrans_of_compact` for `htrans`;
* `Arlib.hloc_needle_in_body` for `hloc`;
* `Arlib.hIso_lowerSemicontinuous` for `hIso`, built from the previous two.

`volume K ≠ 0` and `volume K ≠ ⊤`, which `Arlib.hIso_lowerSemicontinuous` asks for, are derived
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
    (by norm_num) (by norm_num) (hLem41_interior_uncond hn hKc hKcl hKm hKb)
    (hIso_lowerSemicontinuous hKc hKcl hKm hKb hK0 hKtop (htrans_of_compact hKc hKcl hKb)
      (hloc_needle_in_body (by omega) hKc hKcl hKb))

/-- **The same bound, rounded to a power of two**: `Φ ≥ 1/(2³¹·n·D)`.

`8000 · 245760 = 1966080000 ≤ 2³¹ = 2147483648`.  Purely for legibility; the exact form
`Arlib.conductance_hitAndRun_ge_uncond` is strictly stronger.  Like it, this statement has no
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

end Arlib

/-! ### Axiom profile -/

section AxiomCheck

#print axioms Arlib.conductance_hitAndRun_ge_uncond
#print axioms Arlib.conductance_hitAndRun_ge_uncond_pow

end AxiomCheck
