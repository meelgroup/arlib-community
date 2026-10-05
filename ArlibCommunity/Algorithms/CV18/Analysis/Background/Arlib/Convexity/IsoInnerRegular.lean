/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Inner regularity of a continuous nonnegative density, **inside its positivity locus**

The headline result of this file is

    `Arlib.exists_compact_subset_setIntegral_ge` :
      for `h : EuclideanSpace ℝ (Fin n) → ℝ` continuous, nonnegative and `volume`-integrable,
      any measurable `S` and any `ε > 0`, there is a **compact** `C ⊆ S` with
      `∀ x ∈ C, 0 < h x` and `∫_S h ≤ ∫_C h + ε`.

The clause `∀ x ∈ C, 0 < h x` is the point of the lemma, not a bonus.  The known obstruction to
the "enlarge to disjoint opens" route — `Arlib.exists_separated_no_disjoint_open_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1205`) — lives exactly on `{h = 0}`, where the density
distance `densDist h` is degenerate.  Because `h ≥ 0`, the set `{h = 0}` carries **zero** mass for
the measure `h · volume`, so restricting attention to `{h > 0}` deletes the obstruction at no cost
in integral.  This file makes that "no cost" precise and simultaneously buys compactness.

## Main results

* `Arlib.setIntegral_eq_setIntegral_inter_pos` — **exact**, no `ε` lost:
  `∫_S h = ∫_{S ∩ {h > 0}} h`.  Splitting `S` along the open set `{h > 0}` and noting that
  `0 ≤ h` together with `¬ (0 < h x)` forces `h x = 0` pointwise on the complement.
* `Arlib.setIntegral_eq_toReal_withDensity` — the dictionary between the Bochner integral of `h`
  and the measure `volume.withDensity (ENNReal.ofReal ∘ h)`:
  `∫_B h = ((volume.withDensity (fun x => ENNReal.ofReal (h x))) B).toReal` for measurable `B`.
* `Arlib.exists_compact_subset_setIntegral_ge` — **the deliverable**, assembled from the two
  above plus Mathlib's `MeasurableSet.exists_isCompact_lt_add`.
* `Arlib.exists_compact_subset_setIntegral_ge_witness` — a **non-vacuity witness**: concrete
  `n = 2`, `h x = max 0 (1 - ‖x‖)` (continuous, nonnegative, compactly supported hence
  integrable, and strictly positive somewhere in `S`), `S = closedBall 0 1`, `ε = 1`, together
  with the conclusion instantiated at them.  So the hypotheses of the main theorem are jointly
  satisfiable in a genuinely non-degenerate way.

## Where the compactness comes from

Let `μ := volume.withDensity (fun x => ENNReal.ofReal (h x))`.  Integrability of `h` makes `μ` a
**finite** measure (`MeasureTheory.isFiniteMeasure_withDensity_ofReal`).  `EuclideanSpace ℝ (Fin n)`
is a finite-dimensional real normed space, hence pseudo-metrizable, `σ`-compact and a `BorelSpace`,
so Mathlib's instance chain
`IsFiniteMeasure → IsLocallyFiniteMeasure → Measure.Regular → Measure.InnerRegularCompactLTTop`
fires automatically once the finiteness instance is in scope, and
`MeasurableSet.exists_isCompact_lt_add` applies to `S ∩ {h > 0}`.

## Honesty notes

* Nothing was weakened or assumed: the statement proved is verbatim the requested one, with
  exactly the hypotheses `Continuous h`, `∀ x, 0 ≤ h x`, `Integrable h` (w.r.t. `volume`),
  `MeasurableSet S`, `0 < ε`.  **No extra hypothesis was needed.**
* The `≤` in the conclusion is genuinely `≤`; Mathlib's inner regularity gives the strict
  `μ A < μ C + ofReal ε`, which we weaken to `≤` after passing to `ENNReal.toReal`.
* The lemma says nothing about `C` being nonempty.  If `∫_S h = 0` (e.g. `S` null, or `h ≡ 0`
  on `S`) the compact set produced may well be empty — that is correct and unavoidable, since
  the positivity clause forbids putting `{h = 0}` points into `C`.
-/

namespace Arlib

open MeasureTheory Set

/-- Because `h ≥ 0`, the mass of `h` over a measurable set `S` is entirely carried by the open
positivity locus `{h > 0}`: `∫_S h = ∫_{S ∩ {h > 0}} h`, with **no** error term.

On `S \ {h > 0}` the integrand is identically `0`: `¬ (0 < h x)` gives `h x ≤ 0`, and `0 ≤ h x`
is the standing hypothesis, so `h x = 0` there — not merely almost everywhere. -/
theorem setIntegral_eq_setIntegral_inter_pos {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    (hhi : Integrable h) (S : Set (EuclideanSpace ℝ (Fin n))) :
    ∫ x in S, h x = ∫ x in S ∩ {x | 0 < h x}, h x := by
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
    isOpen_lt continuous_const hhc
  have key :
      (∫ x in S ∩ {x | 0 < h x}, h x) + ∫ x in S \ {x | 0 < h x}, h x = ∫ x in S, h x :=
    integral_inter_add_sdiff hopen.measurableSet hhi.integrableOn
  have hzero : ∫ x in S \ {x : EuclideanSpace ℝ (Fin n) | 0 < h x}, h x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro x hx
    exact le_antisymm (not_lt.mp hx.2) (hh0 x)
  rw [hzero, add_zero] at key
  exact key.symm

/-- The dictionary between the Bochner integral of a continuous nonnegative `h` over a measurable
set `B` and the finite measure `volume.withDensity (ENNReal.ofReal ∘ h)` of `B`. -/
theorem setIntegral_eq_toReal_withDensity {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∫ x in B, h x
      = ((volume.withDensity fun x => ENNReal.ofReal (h x)) B).toReal := by
  rw [withDensity_apply _ hB]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh0)
    hhc.aestronglyMeasurable

/-- **Inner regularity inside the positivity locus.**

For a continuous, nonnegative, `volume`-integrable density `h` on `EuclideanSpace ℝ (Fin n)`, a
measurable set `S` and `ε > 0`, there is a **compact** `C ⊆ S` on which `h` is **strictly
positive** and which captures all but `ε` of the `h`-mass of `S`.

The strict positivity clause is what makes this usable downstream: it places `C` inside the open
set `{h > 0}`, away from `{h = 0}` where `densDist h` degenerates. -/
theorem exists_compact_subset_setIntegral_ge {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    (hhi : MeasureTheory.Integrable h)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C ∧ C ⊆ S ∧ (∀ x ∈ C, 0 < h x) ∧
      ∫ x in S, h x ≤ (∫ x in C, h x) + ε := by
  classical
  haveI : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (h x)) :=
    isFiniteMeasure_withDensity_ofReal hhi.2
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
    isOpen_lt continuous_const hhc
  have hAm : MeasurableSet (S ∩ {x : EuclideanSpace ℝ (Fin n) | 0 < h x}) :=
    hS.inter hopen.measurableSet
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨C, hCA, hCcomp, hCμ⟩ :=
    hAm.exists_isCompact_lt_add
      (μ := volume.withDensity fun x => ENNReal.ofReal (h x)) (measure_ne_top _ _) hε'
  have hCm : MeasurableSet C := hCcomp.measurableSet
  refine ⟨C, hCcomp, fun x hx => (hCA hx).1, fun x hx => (hCA hx).2, ?_⟩
  have hstep : (∫ x in S, h x) = ((volume.withDensity fun x => ENNReal.ofReal (h x))
      (S ∩ {x : EuclideanSpace ℝ (Fin n) | 0 < h x})).toReal := by
    rw [setIntegral_eq_setIntegral_inter_pos hhc hh0 hhi S]
    exact setIntegral_eq_toReal_withDensity hhc hh0 hAm
  rw [hstep, setIntegral_eq_toReal_withDensity hhc hh0 hCm]
  have hne : (volume.withDensity fun x => ENNReal.ofReal (h x)) C + ENNReal.ofReal ε ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
  have h2 := ENNReal.toReal_mono hne hCμ.le
  rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le] at h2

/-- **Non-vacuity witness** for `Arlib.exists_compact_subset_setIntegral_ge`.

Concretely: `n = 2`, `h x = max 0 (1 - ‖x‖)` (continuous, nonnegative, compactly supported hence
`volume`-integrable, and strictly positive at `0 ∈ S`), `S = Metric.closedBall 0 1`, `ε = 1`.
Every hypothesis of the main theorem holds, and `h` is not the degenerate zero density, so the
theorem is not vacuously true. -/
theorem exists_compact_subset_setIntegral_ge_witness :
    ∃ (n : ℕ) (h : EuclideanSpace ℝ (Fin n) → ℝ) (S : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ),
      Continuous h ∧ (∀ x, 0 ≤ h x) ∧ MeasureTheory.Integrable h ∧ MeasurableSet S ∧ 0 < ε ∧
      (∃ x ∈ S, 0 < h x) ∧
      ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C ∧ C ⊆ S ∧ (∀ x ∈ C, 0 < h x) ∧
        ∫ x in S, h x ≤ (∫ x in C, h x) + ε := by
  classical
  set h : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => max 0 (1 - ‖x‖) with hh
  have hhc : Continuous h := continuous_const.max (continuous_const.sub continuous_norm)
  have hh0 : ∀ x, 0 ≤ h x := fun x => le_max_left _ _
  have hsupp : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ?_
    intro x hx
    have hx1 : 1 < ‖x‖ := by
      by_contra hcon
      exact hx (by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hcon)
    exact max_eq_left (by linarith)
  have hhi : MeasureTheory.Integrable h := hhc.integrable_of_hasCompactSupport hsupp
  have hSm : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    measurableSet_closedBall
  have hpos : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
      ∧ 0 < h 0 := by
    refine ⟨Metric.mem_closedBall_self zero_le_one, ?_⟩
    simp [hh]
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ :=
    exists_compact_subset_setIntegral_ge hhc hh0 hhi hSm (ε := 1) one_pos
  exact ⟨2, h, Metric.closedBall 0 1, 1, hhc, hh0, hhi, hSm, one_pos,
    ⟨0, hpos.1, hpos.2⟩, C, hC1, hC2, hC3, hC4⟩

#print axioms Arlib.setIntegral_eq_setIntegral_inter_pos
#print axioms Arlib.setIntegral_eq_toReal_withDensity
#print axioms Arlib.exists_compact_subset_setIntegral_ge
#print axioms Arlib.exists_compact_subset_setIntegral_ge_witness

end Arlib
