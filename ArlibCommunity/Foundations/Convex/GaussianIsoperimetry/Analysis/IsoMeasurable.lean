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
import ArlibCommunity.Foundations.Convex.Basic.Isoperimetry
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.OneDimSharp

section
/-!
# Inner regularity of a continuous nonnegative density, **inside its positivity locus**

The headline result of this file is

    `ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge` :
      for `h : EuclideanSpace ℝ (Fin n) → ℝ` continuous, nonnegative and `volume`-integrable,
      any measurable `S` and any `ε > 0`, there is a **compact** `C ⊆ S` with
      `∀ x ∈ C, 0 < h x` and `∫_S h ≤ ∫_C h + ε`.

The clause `∀ x ∈ C, 0 < h x` is the point of the lemma, not a bonus.  The known obstruction to
the "enlarge to disjoint opens" route — `ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) — lives exactly on `{h = 0}`, where the density
distance `densDist h` is degenerate.  Because `h ≥ 0`, the set `{h = 0}` carries **zero** mass for
the measure `h · volume`, so restricting attention to `{h > 0}` deletes the obstruction at no cost
in integral.  This file makes that "no cost" precise and simultaneously buys compactness.

## Main results

* `ArlibCommunity.Foundations.Convex.setIntegral_eq_setIntegral_inter_pos` — **exact**, no `ε` lost:
  `∫_S h = ∫_{S ∩ {h > 0}} h`.  Splitting `S` along the open set `{h > 0}` and noting that
  `0 ≤ h` together with `¬ (0 < h x)` forces `h x = 0` pointwise on the complement.
* `ArlibCommunity.Foundations.Convex.setIntegral_eq_toReal_withDensity` — the dictionary between the Bochner integral of `h`
  and the measure `volume.withDensity (ENNReal.ofReal ∘ h)`:
  `∫_B h = ((volume.withDensity (fun x => ENNReal.ofReal (h x))) B).toReal` for measurable `B`.
* `ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge` — **the deliverable**, assembled from the two
  above plus Mathlib's `MeasurableSet.exists_isCompact_lt_add`.
* `ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge_witness` — a **non-vacuity witness**: concrete
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



namespace ArlibCommunity.Foundations.Convex

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

/-- **Non-vacuity witness** for `ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge`.

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

#print axioms ArlibCommunity.Foundations.Convex.setIntegral_eq_setIntegral_inter_pos
#print axioms ArlibCommunity.Foundations.Convex.setIntegral_eq_toReal_withDensity
#print axioms ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge
#print axioms ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge_witness

end ArlibCommunity.Foundations.Convex

end

section
/-!
# Disjoint open enlargements for a *continuous* density, with no Lipschitz constant

`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) reduces the measurable case of Cousins–Vempala's
`thm:iso` to the open/closed case, **given** disjoint open `U₁ ⊇ S₁`, `U₂ ⊇ S₂` on which the
separation hypothesis still holds.  Everything turns on producing that enlargement.

The route taken so far — `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_gaussianIndicator`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoIndicator.lean`) — produces it by pushing **every** pair into the
*metric* branch of the disjunction, which needs a global log-Lipschitz bound
`d_h(u,v) ≤ L·‖u − v‖`.  For the indicator density `1_K·γ` that is free (`1_K` is constant on
`K`, `γ` has `L = R/σ²`).  For the `ℓ`-weighted density it is the binder `hellLip`, which
has, by an informal argument, no witness with non-constant `ℓ` at the operative step, because
`hLσ` caps `L` far below the true rate `≈ √n·log 2/δ` forced by a corner
(`two_pow_mul_ell_cube_corner_le_one` (not in this repository; see `REFERENCES.md`)).

**This file takes the other route: never convert the density branch.**  Each pair stays in
whichever branch it was already in, and both branches are allowed to degrade slightly.  The
only thing then needed is that `densDist h` does not move much under a small perturbation of
its two arguments — and that is free from *uniform continuity on a compact set*, provided the
thickening radius is chosen **after** the sets are fixed.  A global constant has to satisfy an
inequality against `σ`, `R` and `n`; a radius chosen second has nothing to satisfy.

Two facts make it work, and both are already in the tree for the density that matters:

* `h = ℓ·γ` is globally **continuous** (`ArlibCommunity.Foundations.MarkovChainTheory.continuous_ell_toReal`) and log-concave
  (`ArlibCommunity.Foundations.MarkovChainTheory.isLogConcave_ell_toReal`), and `ArlibCommunity.Foundations.MarkovChainTheory.ellGaussian_isoperimetry_openClosed_logTwo` is
  stated for exactly that `h`, with no indicator — so the open/closed side needs no change.
* `{h = 0}` carries no `h`-mass, and that is precisely where the known obstruction lives: in
  `ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement`
  (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) the touching is on the sphere, *inside* `{h = 0}`.
  Restricting to compact subsets of `{h > 0}` deletes it, at no cost in mass.

## What is proved here

* `ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb` — the arithmetic core: if `a, b, a', b'` all lie in
  `[m, ∞)` with `m > 0` and `|a − a'|, |b − b'| ≤ η`, then

      |a − b| / max a b  −  3η/m  ≤  |a' − b'| / max a' b'.

  The constant `3` is not optimised; it comes from `|a − b| ≤ max a b`.
* `ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb_fun` — the same for `densDist h` at perturbed points.
* **`ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous`** — the enlargement itself.  From
  disjoint compacts `C₁, C₂` inside `{h > 0}` carrying the disjunction at `(c₁, c₂)`, it
  produces disjoint **open** `U₁ ⊇ C₁`, `U₂ ⊇ C₂` carrying it at any strictly smaller
  `(c₁', c₂')`.  The only hypotheses on `h` are continuity and positivity on the compacts;
  there is no Lipschitz constant, no `σ`, no `R`, no dimension threshold.
* `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous_witness` — non-vacuity, on an
  instance where the **metric branch is false** at the only pair, so the density branch
  carries the disjunction alone.  That instance is out of reach of the Lipschitz route.

## Scope — what this file is not

This is a statement about enlarging sets, not an isoperimetric inequality.  Two further
pieces are needed before `thm:iso` holds for measurable `S₁, S₂, S₃`, and they are in
separate files: inner regularity, to replace measurable `S₁, S₂` by compact subsets of
`{h > 0}` at negligible cost in mass, and a slack-tolerant form of
`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_openClosed_enlargement`, which currently demands
*exact* supersets `S₁ ⊆ U₁`.  Nothing here may be quoted as a conductance, mixing-time or
runtime statement.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

variable {E : Type*}

/-! ## 1. `|a − b| ≤ max a b` for nonnegative reals -/

/-- For nonnegative reals the gap never exceeds the larger value.  This is what makes the
constant in `ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb` a `3` rather than something involving `X/M`. -/
theorem abs_sub_le_max_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ max a b := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith)]
    calc -(a - b) = b - a := by ring
      _ ≤ b := by linarith
      _ ≤ max a b := le_max_right a b
  · rw [abs_of_nonneg (by linarith)]
    calc a - b ≤ a := by linarith
      _ ≤ max a b := le_max_left a b

/-! ## 2. The arithmetic core -/

/-- **The perturbation bound for `densDist`, as arithmetic on reals.**

If `a, b, a', b'` are all at least `m > 0` and the primed values are within `η` of the
unprimed ones, then the density distance drops by at most `3η/m`:

    |a − b| / max a b  −  3η/m  ≤  |a' − b'| / max a' b'.

Note what does **not** appear: no Lipschitz constant, no bound relating `η` to the ambient
geometry.  In the consumer, `m` is the minimum of a continuous positive `h` on a compact set
and `η` is supplied by uniform continuity *after* `m` is known, so the two are chosen in the
order that makes the estimate free. -/
theorem densDist_ge_sub_of_perturb {a b a' b' m η : ℝ} (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (ha' : m ≤ a') (hb' : m ≤ b')
    (hη : 0 ≤ η) (hda : |a - a'| ≤ η) (hdb : |b - b'| ≤ η) :
    |a - b| / max a b - 3 * η / m ≤ |a' - b'| / max a' b' := by
  set M : ℝ := max a b with hMdef
  set M' : ℝ := max a' b' with hM'def
  have hMa : a ≤ M := le_max_left a b
  have hMb : b ≤ M := le_max_right a b
  have hmM : m ≤ M := le_trans ha hMa
  have hM0 : 0 < M := lt_of_lt_of_le hm hmM
  have hmM' : m ≤ M' := le_trans ha' (le_max_left a' b')
  have hM'0 : 0 < M' := lt_of_lt_of_le hm hmM'
  have hX : |a - b| ≤ M :=
    abs_sub_le_max_of_nonneg (le_trans hm.le ha) (le_trans hm.le hb)
  -- the numerator can drop by at most `2η`
  have hnum : |a - b| - 2 * η ≤ |a' - b'| := by
    have e : a - b = (a - a') + ((a' - b') + (b' - b)) := by ring
    have h1 : |a - b| ≤ |a - a'| + |(a' - b') + (b' - b)| := by
      rw [e]; exact abs_add_le _ _
    have h2 : |(a' - b') + (b' - b)| ≤ |a' - b'| + |b' - b| := abs_add_le _ _
    have h3 : |b' - b| ≤ η := by rwa [abs_sub_comm]
    linarith
  -- the denominator can grow by at most `η`
  have hden : M' ≤ M + η := by
    have h1 : a' ≤ M + η := by
      have := (abs_le.mp hda).1
      linarith
    have h2 : b' ≤ M + η := by
      have := (abs_le.mp hdb).1
      linarith
    exact max_le h1 h2
  rcases le_or_gt (|a - b|) (2 * η) with hsmall | hbig
  · -- the unperturbed distance was already within the slack
    have h1 : |a - b| / M ≤ 3 * η / m := by
      have hle : |a - b| / M ≤ 2 * η / m := by
        calc |a - b| / M ≤ (2 * η) / M := by gcongr
          _ ≤ (2 * η) / m := by gcongr
      have : 2 * η / m ≤ 3 * η / m := by gcongr <;> linarith
      linarith
    have h2 : 0 ≤ |a' - b'| / M' := div_nonneg (abs_nonneg _) hM'0.le
    linarith
  · -- the main case: the numerator stays positive
    have hpos : 0 < |a - b| - 2 * η := by linarith
    have hMη : 0 < M + η := by linarith
    have hstep1 : (|a - b| - 2 * η) / (M + η) ≤ |a' - b'| / M' := by
      rw [div_le_div_iff₀ hMη hM'0]
      nlinarith [mul_le_mul_of_nonneg_right hnum hM'0.le,
        mul_le_mul_of_nonneg_left hden (abs_nonneg (a' - b'))]
    have hstep2 : |a - b| / M - 3 * η / m ≤ (|a - b| - 2 * η) / (M + η) := by
      have hkey : |a - b| / M - (|a - b| - 2 * η) / (M + η)
          = η * (|a - b| + 2 * M) / (M * (M + η)) := by
        field_simp
        ring
      have hb1 : η * (|a - b| + 2 * M) / (M * (M + η)) ≤ 3 * η / (M + η) := by
        rw [div_le_div_iff₀ (by positivity) hMη]
        have hfac : (|a - b| + 2 * M) * (M + η) ≤ (3 * M) * (M + η) :=
          mul_le_mul_of_nonneg_right (by linarith) hMη.le
        nlinarith [mul_le_mul_of_nonneg_left hfac hη]
      have hb2 : 3 * η / (M + η) ≤ 3 * η / m := by
        gcongr
        linarith
      linarith
    linarith

/-! ## 3. The same, at perturbed points of a function -/

/-- **`ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb` in the shape the enlargement lemma consumes.**

`m` is a positive lower bound for `h` at the four points, `η` a common bound on the movement
of `h`.  No hypothesis relates `η` to any distance: the consumer picks the thickening radius
*after* both `m` and `η`. -/
theorem densDist_ge_sub_of_perturb_fun {h : E → ℝ} {u v u' v' : E} {m η : ℝ} (hm : 0 < m)
    (hu : m ≤ h u) (hv : m ≤ h v) (hu' : m ≤ h u') (hv' : m ≤ h v')
    (hη : 0 ≤ η) (hdu : |h u - h u'| ≤ η) (hdv : |h v - h v'| ≤ η) :
    densDist h u v - 3 * η / m ≤ densDist h u' v' :=
  densDist_ge_sub_of_perturb hm hu hv hu' hv' hη hdu hdv

/-! ## 4. The enlargement, with the radius chosen last -/

open Metric in
/-- **Disjoint open enlargements of two compact sets inside `{h > 0}`, at any strictly
weakened pair of thresholds — with no Lipschitz hypothesis.**

Let `C₁, C₂` be disjoint compact sets on which the continuous `h` is strictly positive, and
suppose every pair `(u,v) ∈ C₁ × C₂` satisfies the Cousins–Vempala disjunction at `(c₁, c₂)`:
either `c₁ ≤ ‖u − v‖` or `c₂ ≤ d_h(u,v)`.  Then for **any** strictly smaller pair
`(c₁', c₂')` there are disjoint open `U₁ ⊇ C₁`, `U₂ ⊇ C₂` on which every pair satisfies the
disjunction at `(c₁', c₂')`.

This is the replacement for `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_gaussianIndicator`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoIndicator.lean`).  That one converts the density branch into the
metric branch and therefore needs a global log-Lipschitz constant for `h`; this one leaves
each pair in its own branch, so it needs nothing but continuity.

**The order of choice is the whole trick.**  The thickening radius `ρ` is picked *after*

* `ρ₀`, a radius whose closed thickening of `C₁ ∪ C₂` still lies in the open set `{h > 0}`;
* `m > 0`, the minimum of `h` on that (compact) closed thickening `N`;
* `η := (c₂ − c₂')·m/3`, so that `3η/m` is exactly the density slack `c₂ − c₂'`;
* `ρ₁`, from **uniform** continuity of `h` on the compact `N` at tolerance `η`;
* `ρ₂`, a radius separating the disjoint compacts `C₁, C₂` (`Disjoint.exists_thickenings`);
* `(c₁ − c₁')/2`, the metric slack.

A global Lipschitz constant would have to be compared against `σ`, `R` and `n` — that is
`hLσ`, and it fails.  Here nothing is compared against anything: `ρ` is the minimum of five
positive numbers already in hand.

`ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) is not contradicted: there the two sets touch
*inside* `{h = 0}`, and the hypotheses `hC₁h`, `hC₂h` exclude exactly that.  In the consumer,
`C₁, C₂` come from inner regularity applied inside `{h > 0}`, which costs no mass because
`h` vanishes on the discarded part. -/
theorem exists_disjoint_open_enlargement_of_continuous {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h)
    {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂)
    (hC₁h : ∀ x ∈ C₁, 0 < h x) (hC₂h : ∀ x ∈ C₂, 0 < h x)
    (hdisj : Disjoint C₁ C₂)
    {c₁ c₂ c₁' c₂' : ℝ} (hlt₁ : c₁' < c₁) (hlt₂ : c₂' < c₂)
    (hsep : ∀ u ∈ C₁, ∀ v ∈ C₂, c₁ ≤ ‖u - v‖ ∨ c₂ ≤ densDist h u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ C₁ ⊆ U₁ ∧ C₂ ⊆ U₂ ∧
      ∀ u ∈ U₁, ∀ v ∈ U₂, c₁' ≤ ‖u - v‖ ∨ c₂' ≤ densDist h u v := by
  classical
  -- the degenerate cases, where one side of the disjunction is vacuous
  rcases Set.eq_empty_or_nonempty C₁ with rfl | hne₁
  · exact ⟨∅, Set.univ, isOpen_empty, isOpen_univ, by simp, by simp, by simp, by simp⟩
  rcases Set.eq_empty_or_nonempty C₂ with rfl | hne₂
  · exact ⟨Set.univ, ∅, isOpen_univ, isOpen_empty, by simp, by simp, by simp, by simp⟩
  set K : Set (EuclideanSpace ℝ (Fin n)) := C₁ ∪ C₂ with hKdef
  have hKc : IsCompact K := hC₁.union hC₂
  have hKpos : ∀ x ∈ K, 0 < h x := by
    intro x hx
    rcases hx with hx | hx
    · exact hC₁h x hx
    · exact hC₂h x hx
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
    isOpen_lt continuous_const hhc
  -- `ρ₀`: a closed thickening of `K` still inside `{h > 0}`
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := hKc.exists_cthickening_subset_open hopen hKpos
  set N : Set (EuclideanSpace ℝ (Fin n)) := cthickening ρ₀ K with hNdef
  have hNc : IsCompact N := hKc.cthickening
  have hKN : K ⊆ N := self_subset_cthickening K
  have hNne : N.Nonempty := Set.Nonempty.mono (Set.subset_union_left.trans hKN) hne₁
  -- `m`: the minimum of `h` on `N`, positive because `N ⊆ {h > 0}`
  obtain ⟨x₀, hx₀N, hx₀min⟩ := hNc.exists_isMinOn hNne hhc.continuousOn
  set m : ℝ := h x₀ with hmdef
  have hm : 0 < m := hρ₀sub hx₀N
  have hmle : ∀ y ∈ N, m ≤ h y := fun y hy => isMinOn_iff.mp hx₀min y hy
  -- `η`: the movement of `h` that the density slack can absorb
  set η : ℝ := (c₂ - c₂') * m / 3 with hηdef
  have hηpos : 0 < η := by
    have hc : 0 < c₂ - c₂' := by linarith
    rw [hηdef]
    positivity
  have h3η : 3 * η / m = c₂ - c₂' := by
    rw [hηdef]
    field_simp
  -- `ρ₁`: uniform continuity of `h` on the compact `N`, at tolerance `η`
  obtain ⟨ρ₁, hρ₁, hρ₁unif⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hNc.uniformContinuousOn_of_continuous hhc.continuousOn) η hηpos
  -- `ρ₂`: the disjoint compacts are a positive distance apart
  obtain ⟨ρ₂, hρ₂, hρ₂disj⟩ := hdisj.exists_thickenings hC₁ hC₂.isClosed
  set ρ : ℝ := min (min ρ₀ ρ₁) (min ρ₂ ((c₁ - c₁') / 2)) with hρdef
  have hρρ₀ : ρ ≤ ρ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρmet : ρ ≤ (c₁ - c₁') / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρpos : 0 < ρ := by
    have hc : 0 < (c₁ - c₁') / 2 := by linarith
    rw [hρdef, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hρ₀, hρ₁⟩, hρ₂, hc⟩
  -- every thickening of a subset of `K` stays inside `N`
  have hUN : ∀ C : Set (EuclideanSpace ℝ (Fin n)), C ⊆ K → thickening ρ C ⊆ N := by
    intro C hC
    calc thickening ρ C ⊆ thickening ρ K := thickening_subset_of_subset ρ hC
      _ ⊆ thickening ρ₀ K := thickening_mono hρρ₀ K
      _ ⊆ N := thickening_subset_cthickening ρ₀ K
  refine ⟨thickening ρ C₁, thickening ρ C₂, isOpen_thickening, isOpen_thickening,
    hρ₂disj.mono (thickening_mono hρρ₂ C₁) (thickening_mono hρρ₂ C₂),
    self_subset_thickening hρpos C₁, self_subset_thickening hρpos C₂, ?_⟩
  intro u' hu' v' hv'
  obtain ⟨u, huC, hdu⟩ := mem_thickening_iff.mp hu'
  obtain ⟨v, hvC, hdv⟩ := mem_thickening_iff.mp hv'
  -- the four points all live in `N`
  have huN : u ∈ N := hKN (Set.mem_union_left _ huC)
  have hvN : v ∈ N := hKN (Set.mem_union_right _ hvC)
  have hu'N : u' ∈ N := hUN C₁ Set.subset_union_left hu'
  have hv'N : v' ∈ N := hUN C₂ Set.subset_union_right hv'
  -- the movement of `h` between them is at most `η`
  have hmoveu : |h u - h u'| ≤ η := by
    have hd : dist u u' < ρ₁ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hdu hρρ₁
    have := hρ₁unif u huN u' hu'N hd
    rw [Real.dist_eq] at this
    exact this.le
  have hmovev : |h v - h v'| ≤ η := by
    have hd : dist v v' < ρ₁ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hdv hρρ₁
    have := hρ₁unif v hvN v' hv'N hd
    rw [Real.dist_eq] at this
    exact this.le
  rcases hsep u huC v hvC with hmetric | hdens
  · -- the metric branch degrades from `c₁` to `c₁'`
    left
    have hnu : ‖u - u'‖ < ρ := by rw [← dist_eq_norm, dist_comm]; exact hdu
    have hnv : ‖v' - v‖ < ρ := by rw [← dist_eq_norm]; exact hdv
    have htri : ‖u - v‖ ≤ ‖u - u'‖ + ‖u' - v'‖ + ‖v' - v‖ := by
      calc ‖u - v‖ = ‖(u - u') + ((u' - v') + (v' - v))‖ := by congr 1; abel
        _ ≤ ‖u - u'‖ + ‖(u' - v') + (v' - v)‖ := norm_add_le _ _
        _ ≤ ‖u - u'‖ + (‖u' - v'‖ + ‖v' - v‖) := by gcongr; exact norm_add_le _ _
        _ = ‖u - u'‖ + ‖u' - v'‖ + ‖v' - v‖ := by ring
    linarith
  · -- the density branch degrades from `c₂` to `c₂'`, by exactly `3η/m`
    right
    have hkey := densDist_ge_sub_of_perturb_fun (h := h) hm (hmle u huN) (hmle v hvN)
      (hmle u' hu'N) (hmle v' hv'N) hηpos.le hmoveu hmovev
    rw [h3η] at hkey
    linarith

/-! ## 5. Non-vacuity -/

open Metric in
/-- **The hypothesis bundle of `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous` is
satisfiable — on an instance where the *metric* branch fails.**

`n = 1`, `h x = 1/(1 + ‖x‖)`, `C₁ = {0}`, `C₂ = {e₀}`, `c₁ = 2`, `c₂ = 1/2`, weakened to
`c₁' = 1`, `c₂' = 1/4`.  At the only pair, `‖0 − e₀‖ = 1 < 2 = c₁`, so the metric branch is
**false**, and the disjunction holds only because `d_h(0,e₀) = 1/2 = c₂`.

That is the point of the witness, and the reason the last conjunct is stated: this instance
is out of reach of `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_gaussianIndicator`, whose whole
method is to discharge the metric branch.  It also shows the theorem is not vacuously about
its two degenerate branches — both compacts are nonempty. -/
theorem exists_disjoint_open_enlargement_of_continuous_witness :
    ∃ (k : ℕ) (h : EuclideanSpace ℝ (Fin k) → ℝ)
      (C₁ C₂ : Set (EuclideanSpace ℝ (Fin k))) (c₁ c₂ c₁' c₂' : ℝ),
      Continuous h ∧ IsCompact C₁ ∧ IsCompact C₂ ∧
      (∀ x ∈ C₁, 0 < h x) ∧ (∀ x ∈ C₂, 0 < h x) ∧ Disjoint C₁ C₂ ∧
      C₁.Nonempty ∧ C₂.Nonempty ∧ c₁' < c₁ ∧ c₂' < c₂ ∧
      (∀ u ∈ C₁, ∀ v ∈ C₂, c₁ ≤ ‖u - v‖ ∨ c₂ ≤ densDist h u v) ∧
      (∃ u ∈ C₁, ∃ v ∈ C₂, ¬ c₁ ≤ ‖u - v‖) ∧
      ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin k)),
        IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ C₁ ⊆ U₁ ∧ C₂ ⊆ U₂ ∧
        ∀ u ∈ U₁, ∀ v ∈ U₂, c₁' ≤ ‖u - v‖ ∨ c₂' ≤ densDist h u v := by
  classical
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have hen : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set h : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => 1 / (1 + ‖x‖) with hhdef
  have hcont : Continuous h := by
    rw [hhdef]
    exact Continuous.div continuous_const (by fun_prop) (fun x => by positivity)
  have hpos : ∀ x : EuclideanSpace ℝ (Fin 1), 0 < h x := by
    intro x; rw [hhdef]; positivity
  have hh0 : h 0 = 1 := by rw [hhdef]; simp
  have hhe : h e = 1 / 2 := by rw [hhdef]; simp only [hen]; norm_num
  have hne : (0 : EuclideanSpace ℝ (Fin 1)) ≠ e := by
    intro hc
    rw [← hc, norm_zero] at hen
    norm_num at hen
  have hdist : ‖(0 : EuclideanSpace ℝ (Fin 1)) - e‖ = 1 := by
    rw [zero_sub, norm_neg, hen]
  have hdens : densDist h 0 e = 1 / 2 := by
    rw [densDist, hh0, hhe]
    rw [max_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 1)]
    norm_num
  have hsep : ∀ u ∈ ({0} : Set (EuclideanSpace ℝ (Fin 1))), ∀ v ∈ ({e} : Set _),
      (2 : ℝ) ≤ ‖u - v‖ ∨ (1 / 2 : ℝ) ≤ densDist h u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact Or.inr (by rw [hdens])
  obtain ⟨U₁, U₂, hU₁, hU₂, hUd, hs₁, hs₂, hUsep⟩ :=
    exists_disjoint_open_enlargement_of_continuous (n := 1) (h := h) hcont
      isCompact_singleton isCompact_singleton
      (fun x _ => hpos x) (fun x _ => hpos x)
      (Set.disjoint_singleton.mpr hne)
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hsep
  refine ⟨1, h, {0}, {e}, 2, 1 / 2, 1, 1 / 4, hcont, isCompact_singleton, isCompact_singleton,
    fun x _ => hpos x, fun x _ => hpos x, Set.disjoint_singleton.mpr hne,
    Set.singleton_nonempty _, Set.singleton_nonempty _, by norm_num, by norm_num, hsep,
    ⟨0, rfl, e, rfl, ?_⟩, U₁, U₂, hU₁, hU₂, hUd, hs₁, hs₂, hUsep⟩
  rw [hdist]
  norm_num

section AxiomCheck

#print axioms ArlibCommunity.Foundations.Convex.abs_sub_le_max_of_nonneg
#print axioms ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb
#print axioms ArlibCommunity.Foundations.Convex.densDist_ge_sub_of_perturb_fun
#print axioms ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous
#print axioms ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous_witness

end AxiomCheck

end ArlibCommunity.Foundations.Convex

end

section
/-!
# From *measurable* `S₁, S₂, S₃` to disjoint open enlargements, for a continuous density

This is the join of the two halves that precede it:

* `ArlibCommunity.Foundations.Convex.exists_compact_subset_setIntegral_ge` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`) —
  inner regularity: a measurable `S` contains a **compact** `C ⊆ S ∩ {h > 0}` carrying all
  but `ε` of `∫_S h`;
* `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous`
  (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`) — disjoint **open** enlargements of two
  disjoint compacts inside `{h > 0}`, at any strictly weakened thresholds, needing nothing of
  `h` but continuity.

Composing them gives exactly the hypothesis a slack-tolerant form of
`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) consumes, in Cousins–Vempala's own threshold
shape `d/log 2` and `4(d/σ)√n`.

## Why this evades the known obstruction

`ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean`) exhibits
data satisfying every hypothesis of `thm:iso` for which **no** disjoint open supersets of
`S₁, S₂` exist at all — the two sets touch, and they touch *inside* `{h = 0}`, where the
density branch of the disjunction is satisfied at distance `0`.

The composition here never asks for supersets of `S₁, S₂`. It asks for supersets of compact
subsets of `S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}`, which are disjoint **compact** sets and hence a
positive distance apart. The mass discarded is `≤ ε` on each side, because `h` vanishes on
`{h = 0}`; and the residual set `(U₁ ∪ U₂)ᶜ` therefore exceeds `S₃` by at most `2ε`. That is
the `2ε` in the statement below, and it is why the conclusion is stated with slack rather
than exactly.

## What is proved here

* `ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable` — the composition, in the `∃ U₁ U₂, …` shape.
* `ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable_witness` — non-vacuity.

## Scope

Still not an isoperimetric inequality: the remaining step is to feed this to the open/closed
capstone and pass to the limit `ε ↓ 0`, `d' ↑ d`. Nothing here may be quoted as a
conductance, mixing-time or runtime statement.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

open MeasureTheory Metric

variable {n : ℕ}

/-! ## 1. Monotonicity of the set integral of a nonnegative integrable function -/

/-- Set-monotonicity of `∫_A h` for `h ≥ 0` integrable.  Used four times below. -/
theorem setIntegral_mono_set_of_nonneg {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh0 : ∀ x, 0 ≤ h x) (hhi : Integrable h)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hAB : A ⊆ B) :
    ∫ x in A, h x ≤ ∫ x in B, h x :=
  setIntegral_mono_set hhi.integrableOn (Filter.Eventually.of_forall fun x => hh0 x)
    (LE.le.eventuallyLE hAB)

/-- The mass of `S` outside a compact `C ⊆ S` that already carries all but `ε`. -/
theorem setIntegral_sdiff_le_of_compact_ge {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hhi : Integrable h) {S C : Set (EuclideanSpace ℝ (Fin n))} (hC : MeasurableSet C)
    (hCS : C ⊆ S) {ε : ℝ} (hint : ∫ x in S, h x ≤ (∫ x in C, h x) + ε) :
    ∫ x in S \ C, h x ≤ ε := by
  have hsplit : (∫ x in S ∩ C, h x) + ∫ x in S \ C, h x = ∫ x in S, h x :=
    integral_inter_add_sdiff hC hhi.integrableOn
  rw [Set.inter_eq_self_of_subset_right hCS] at hsplit
  linarith

/-! ## 2. The composition -/

/-- **Measurable `S₁, S₂, S₃` admit disjoint open enlargements with `ε`-slack, at any
strictly smaller separation parameter — for any continuous nonnegative integrable `h`.**

No hypothesis on `h` beyond continuity, nonnegativity and integrability: no Lipschitz
constant, no bound relating `σ`, `R` and `n`, no dimension threshold.  `n ≠ 0` is used only
to know `√n > 0`, so that the density threshold `4(d/σ)√n` is strictly monotone in `d`.

The three mass clauses are exactly what a slack-tolerant reduction needs:

* `U₁` carries all but `ε` of `S₁`'s mass, and likewise `U₂` for `S₂`;
* the residual `(U₁ ∪ U₂)ᶜ` carries at most `S₃`'s mass plus `2ε` — one `ε` for each of the
  two pieces of `S₁, S₂` that the compacts failed to capture. -/
theorem exists_enlargement_of_measurable (hn : n ≠ 0) {σ d d' ε : ℝ}
    (hσ : 0 < σ) (hd'd : d' < d) (hε : 0 < ε)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
      ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
      ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
      (∀ u ∈ U₁, ∀ v ∈ U₂,
        d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v) := by
  classical
  -- inner regularity on each side, inside `{h > 0}`
  obtain ⟨C₁, hC₁c, hC₁S, hC₁pos, hC₁int⟩ :=
    exists_compact_subset_setIntegral_ge hhc hh0 hhi hS₁ hε
  obtain ⟨C₂, hC₂c, hC₂S, hC₂pos, hC₂int⟩ :=
    exists_compact_subset_setIntegral_ge hhc hh0 hhi hS₂ hε
  have hCdisj : Disjoint C₁ C₂ := hpart.disjoint₁₂.mono hC₁S hC₂S
  -- both thresholds are strictly monotone in `d`
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hlt₁ : d' / Real.log 2 < d / Real.log 2 := by gcongr
  have hlt₂ : 4 * (d' / σ) * Real.sqrt n < 4 * (d / σ) * Real.sqrt n := by
    have hdiv : d' / σ < d / σ := by gcongr
    nlinarith [hsqrt, hdiv]
  -- the enlargement
  obtain ⟨U₁, U₂, hU₁o, hU₂o, hUd, hCU₁, hCU₂, hUsep⟩ :=
    exists_disjoint_open_enlargement_of_continuous hhc hC₁c hC₂c hC₁pos hC₂pos hCdisj hlt₁ hlt₂
      (fun u hu v hv => hsep u (hC₁S hu) v (hC₂S hv))
  refine ⟨U₁, U₂, hU₁o, hU₂o, hUd, ?_, ?_, ?_, hUsep⟩
  · have := setIntegral_mono_set_of_nonneg hh0 hhi hCU₁
    linarith
  · have := setIntegral_mono_set_of_nonneg hh0 hhi hCU₂
    linarith
  · -- the residual, cut along the partition
    have hUm : MeasurableSet (U₁ ∪ U₂) := (hU₁o.union hU₂o).measurableSet
    have hUcm : MeasurableSet (U₁ ∪ U₂)ᶜ := hUm.compl
    set T₁ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₁ with hT₁def
    set T₂ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₂ with hT₂def
    set T₃ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₃ with hT₃def
    have hT₁m : MeasurableSet T₁ := hUcm.inter hS₁
    have hT₂m : MeasurableSet T₂ := hUcm.inter hS₂
    have hT₃m : MeasurableSet T₃ := hUcm.inter hS₃
    -- the three pieces cover the residual, because `S₁, S₂, S₃` cover everything
    have hcover : (U₁ ∪ U₂)ᶜ = (T₁ ∪ T₂) ∪ T₃ := by
      rw [hT₁def, hT₂def, hT₃def, ← Set.inter_union_distrib_left,
        ← Set.inter_union_distrib_left, hpart.union, Set.inter_univ]
    -- and they are pairwise disjoint, because `S₁, S₂, S₃` are
    have hd₁₂ : Disjoint T₁ T₂ :=
      hpart.disjoint₁₂.mono Set.inter_subset_right Set.inter_subset_right
    have hd₁₃ : Disjoint T₁ T₃ :=
      hpart.disjoint₁₃.mono Set.inter_subset_right Set.inter_subset_right
    have hd₂₃ : Disjoint T₂ T₃ :=
      hpart.disjoint₂₃.mono Set.inter_subset_right Set.inter_subset_right
    have hsplit : ∫ x in (U₁ ∪ U₂)ᶜ, h x
        = ((∫ x in T₁, h x) + ∫ x in T₂, h x) + ∫ x in T₃, h x := by
      rw [hcover, setIntegral_union (Set.disjoint_union_left.mpr ⟨hd₁₃, hd₂₃⟩) hT₃m
        hhi.integrableOn hhi.integrableOn,
        setIntegral_union hd₁₂ hT₂m hhi.integrableOn hhi.integrableOn]
    -- `T₁` misses `C₁` entirely, so it lies in the `ε`-small part of `S₁`
    have hT₁sub : T₁ ⊆ S₁ \ C₁ := by
      intro x hx
      refine ⟨hx.2, fun hc => hx.1 (Set.mem_union_left _ (hCU₁ hc))⟩
    have hT₂sub : T₂ ⊆ S₂ \ C₂ := by
      intro x hx
      refine ⟨hx.2, fun hc => hx.1 (Set.mem_union_right _ (hCU₂ hc))⟩
    have hb₁ : ∫ x in T₁, h x ≤ ε :=
      le_trans (setIntegral_mono_set_of_nonneg hh0 hhi hT₁sub)
        (setIntegral_sdiff_le_of_compact_ge hhi hC₁c.measurableSet hC₁S hC₁int)
    have hb₂ : ∫ x in T₂, h x ≤ ε :=
      le_trans (setIntegral_mono_set_of_nonneg hh0 hhi hT₂sub)
        (setIntegral_sdiff_le_of_compact_ge hhi hC₂c.measurableSet hC₂S hC₂int)
    have hb₃ : ∫ x in T₃, h x ≤ ∫ x in S₃, h x :=
      setIntegral_mono_set_of_nonneg hh0 hhi Set.inter_subset_right
    rw [hsplit]
    linarith

/-! ## 3. Non-vacuity -/

/-- **The hypothesis bundle of `ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable` is satisfiable, with
`S₁` and `S₂` both of positive `h`-mass.**

`n = 1`, `h x = max 0 (5 − ‖x‖)` (continuous, nonnegative, compactly supported hence
integrable), `S₁ = closedBall 0 (1/2)`, `S₂ = {x | 3 ≤ ‖x‖}`, `S₃` the rest, `σ = 1`, `d = 1`,
`d' = 1/2`, `ε = 1`.  The separation holds on the metric branch, `‖u − v‖ ≥ 5/2 > 1/log 2`.

Both `S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}` are nonempty here — `h = 5` at the centre and `h = 2`
on `{‖x‖ = 3}` — so inner regularity returns nonempty compacts and the theorem does not
reduce to the degenerate branches of
`ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous`.

For an instance where the **density** branch carries the disjunction on its own, see
`ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous_witness`. -/
theorem exists_enlargement_of_measurable_witness :
    ∃ (k : ℕ) (h : EuclideanSpace ℝ (Fin k) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin k))) (σ d d' ε : ℝ),
      k ≠ 0 ∧ 0 < σ ∧ d' < d ∧ 0 < ε ∧
      Continuous h ∧ (∀ x, 0 ≤ h x) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∃ x ∈ S₁, 0 < h x) ∧ (∃ x ∈ S₂, 0 < h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt k ≤ densDist h u v) := by
  classical
  set h : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => max 0 (5 - ‖x‖) with hhdef
  have hcont : Continuous h := by rw [hhdef]; fun_prop
  have hh0 : ∀ x, 0 ≤ h x := fun x => le_max_left _ _
  have hsupp : ∀ x : EuclideanSpace ℝ (Fin 1), x ∉ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 5 →
      h x = 0 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    rw [hhdef]
    exact max_eq_left (by linarith)
  have hint : Integrable h :=
    hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 5) hsupp)
  set S₁ : Set (EuclideanSpace ℝ (Fin 1)) := closedBall 0 (1 / 2) with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin 1)) := {x | 3 ≤ ‖x‖} with hS₂def
  have hmem₁ : ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ S₁ ↔ ‖x‖ ≤ 1 / 2 := by
    intro x; rw [hS₁def, mem_closedBall, dist_zero_right]
  have hS₁m : MeasurableSet S₁ := measurableSet_closedBall
  have hS₂m : MeasurableSet S₂ :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hdisj₁₂ : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h1 := (hmem₁ x).1 hx₁
    have h2 : (3 : ℝ) ≤ ‖x‖ := hx₂
    linarith
  refine ⟨1, h, S₁, S₂, (S₁ ∪ S₂)ᶜ, 1, 1, 1 / 2, 1, one_ne_zero, one_pos, by norm_num,
    one_pos, hcont, hh0, hint,
    { union := Set.union_compl_self _
      disjoint₁₂ := hdisj₁₂
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) },
    hS₁m, hS₂m, (hS₁m.union hS₂m).compl, ?_, ?_, ?_⟩
  · refine ⟨0, (hmem₁ 0).2 (by simp), ?_⟩
    rw [hhdef]
    simp
  · refine ⟨EuclideanSpace.single ⟨0, by omega⟩ (3 : ℝ), ?_, ?_⟩
    · show (3 : ℝ) ≤ ‖_‖
      rw [PiLp.norm_single]
      norm_num
    · rw [hhdef]
      simp only [PiLp.norm_single]
      norm_num
  · intro u hu v hv
    left
    have h1 : ‖u‖ ≤ 1 / 2 := (hmem₁ u).1 hu
    have h2 : (3 : ℝ) ≤ ‖v‖ := hv
    -- `log 2 ≥ 1/2`, from `log x ≤ x − 1` at `x = 1/2`
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hx := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
      rw [Real.log_inv] at hx
      norm_num at hx
      linarith
    have hlogpos : 0 < Real.log 2 := by linarith
    have huv : (5 : ℝ) / 2 ≤ ‖u - v‖ := by
      have := norm_sub_norm_le v u
      rw [norm_sub_rev v u] at this
      linarith
    have hdiv : (1 : ℝ) / Real.log 2 ≤ 5 / 2 := by
      rw [div_le_div_iff₀ hlogpos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith

section AxiomCheck

#print axioms ArlibCommunity.Foundations.Convex.setIntegral_mono_set_of_nonneg
#print axioms ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable_witness
#print axioms ArlibCommunity.Foundations.Convex.setIntegral_sdiff_le_of_compact_ge
#print axioms ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable

end AxiomCheck

end ArlibCommunity.Foundations.Convex

end

section
/-!
# `thm:iso` from *approximate* open enlargements

`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`) reduces the measurable case of Cousins–Vempala's
`thm:iso` to the open/closed case, but it demands **exact** open supersets `S₁ ⊆ U₁`, `S₂ ⊆ U₂`
holding the separation at the *same* `d` — and
`ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`)
shows such supersets need not exist.

This file supplies the reduction that consumes the enlargements one can actually build: open sets
that cover `S₁, S₂` only up to `ε` of `h`-mass, leave a residual `(U₁ ∪ U₂)ᶜ` no larger than `S₃`
up to `2ε`, and hold the separation only at a strictly smaller parameter `d' < d`.

## Main results

* `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_enlargement_slack` — the slack-tolerant reduction.
  From disjoint open `U₁, U₂` with `∫_{S₁}h − ε ≤ ∫_{U₁}h`, `∫_{S₂}h − ε ≤ ∫_{U₂}h`,
  `∫_{(U₁∪U₂)ᶜ}h ≤ ∫_{S₃}h + 2ε` and the separation at `d`, it gives
  `(d/σ)·max 0 (∫_{S₁}h − ε)·max 0 (∫_{S₂}h − ε) ≤ (∫h)·(∫_{S₃}h + 2ε)`.
  Pure monotonicity on top of `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo`, applied to
  the open/closed partition `U₁, U₂, (U₁ ∪ U₂)ᶜ`.  The `max 0 (·)` truncations make the statement
  unconditionally true — no positivity of `∫_{Sᵢ}h − ε` is assumed — and the consumer discharges
  them by `max_eq_right` once `ε ↓ 0`.
* `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_of_enlargements` — the limit.  If enlargements
  of the above kind exist for **every** `ε > 0` and **every** `d' ∈ (0, d)`, then `thm:iso` holds
  for the (arbitrary — not even measurable) sets `S₁, S₂, S₃` at the full parameter `d`.  Both
  limits are elementary: `ε ↓ 0` along `𝓝[>] 0` and `d' ↑ d` along `𝓝[<] d`, each by
  `le_of_tendsto_of_tendsto'` against a continuous function of the parameter.
* `ArlibCommunity.Foundations.Convex.exists_enlargements_witness` — non-vacuity.  The standard Gaussian (`σ = 1`, `f ≡ 1`) and
  the **closed** slab partition `S₁ = {⟪e,x⟫ ≤ −1/4}`, `S₂ = {1/4 ≤ ⟪e,x⟫}`, `S₃` the open middle,
  at `d = log 2 / 4`, satisfy the whole hypothesis bundle of the previous theorem — `henl`
  included, discharged by the fixed open slabs `U₁ = {⟪e,x⟫ < −1/8}`, `U₂ = {1/8 < ⟪e,x⟫}` — with
  a strictly positive left-hand side.  Note `S₁, S₂` are *not* open there, so the open/closed
  capstone does not apply to this data directly; the enlargement route is doing real work.

## What is assumed

**Nothing beyond the imported results.**  No `def`, `structure` or named `Prop` below asserts any
part of `thm:iso` or of the Localization Lemma.  Both reductions are monotonicity and limits over
`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo`, whose own hypotheses (`h = f·γ_σ` with
`f` log-concave and nonnegative, `h` continuous, bounded, integrable, `0 < ∫h`) are threaded
through unchanged.  In particular `h ≥ 0` is *derived* from `hh` and `hf₀`, which is what makes
every set integral below nonnegative and the monotonicity go through.

The existence of the enlargements is **not** proved here: it is the hypothesis `henl` of the
second theorem, and the third theorem only shows that hypothesis is inhabited.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal _root_.Topology



open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

section Slack

variable {n : ℕ}

set_option linter.unusedVariables false in
/-- **The measurable case from *approximate* disjoint open enlargements, at the same `d`.**

The slack-tolerant form of `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_openClosed_enlargement`:
`U₁, U₂` need not contain `S₁, S₂`, only capture their `h`-mass up to `ε`, and the residual
`(U₁ ∪ U₂)ᶜ` need not sit inside `S₃`, only carry no more than `2ε` extra mass.  No partition
hypothesis on `S₁, S₂, S₃` is needed — the three sets enter only through their integrals.

The proof is `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo` on the honest open/closed
partition `U₁, U₂, (U₁ ∪ U₂)ᶜ`, then three monotonicities:
`max 0 (∫_{S₁}h − ε) ≤ ∫_{U₁}h` (by `hsl₁` and nonnegativity of the right side), likewise for
`S₂`, and `∫_{(U₁∪U₂)ᶜ}h ≤ ∫_{S₃}h + 2ε` (`hres`) against the nonnegative factor `∫h`.

`hε : 0 ≤ ε` is accepted and **not used**: the `max 0 (·)` truncations already make the statement
true for every real `ε`, `hres` being the only place `ε` enters on the right.  It is kept in the
signature because every consumer has it and its absence would be a surprise. -/
theorem gaussianRestricted_isoperimetry_of_enlargement_slack (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hUdisj : Disjoint U₁ U₂)
    (hmass : 0 < ∫ x, h x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsl₁ : (∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x)
    (hsl₂ : (∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x)
    (hres : (∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε)
    (hsep : ∀ u ∈ U₁, ∀ v ∈ U₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
      ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hdσ : 0 ≤ d / σ := (div_pos hd hσ).le
  have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
    { union := Set.union_compl_self (U₁ ∪ U₂)
      disjoint₁₂ := hUdisj
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  have hmain := gaussianRestricted_isoperimetry_openClosed_logTwo hn hσ hf₀ hfc hh hhc hhB hhi
    hpart' hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hmass hsep
  have hq₁ : 0 ≤ ∫ x in U₁, h x := integral_nonneg fun x => h0 x
  have hq₂ : 0 ≤ ∫ x in U₂, h x := integral_nonneg fun x => h0 x
  have hle₁ : max 0 ((∫ x in S₁, h x) - ε) ≤ ∫ x in U₁, h x := max_le hq₁ hsl₁
  have hle₂ : max 0 ((∫ x in S₂, h x) - ε) ≤ ∫ x in U₂, h x := max_le hq₂ hsl₂
  calc d / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
      ≤ d / σ * ((∫ x in U₁, h x) * ∫ x in U₂, h x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hle₁ hle₂ (le_max_left _ _) hq₁) hdσ
    _ ≤ (∫ x, h x) * ∫ x in (U₁ ∪ U₂)ᶜ, h x := hmain
    _ ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) :=
        mul_le_mul_of_nonneg_left hres hmass.le

/-- **`thm:iso` for arbitrary `S₁, S₂, S₃`, from a family of approximate open enlargements.**

`henl` asks, for every mass slack `ε > 0` and every separation parameter `d' ∈ (0, d)`, for a pair
of disjoint open sets capturing `∫_{S₁}h, ∫_{S₂}h` up to `ε`, leaving a residual of mass at most
`∫_{S₃}h + 2ε`, and separated at `d'`.  Given that family, the conclusion holds at the full `d`
with no slack at all.

The proof is `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_enlargement_slack` at each `(ε, d')`
followed by two elementary limits:

* `ε ↓ 0` along `𝓝[>] 0` at fixed `d'`, where the left side tends to
  `(d'/σ)·(∫_{S₁}h)(∫_{S₂}h)` — this is where `max 0 (∫_{Sᵢ}h − ε) → ∫_{Sᵢ}h` uses `h ≥ 0` — and
  the right side to `(∫h)·∫_{S₃}h`;
* `d' ↑ d` along `𝓝[<] d`, where the left side is linear in `d'` and the right side constant.

No measurability, and no partition hypothesis, is required of `S₁, S₂, S₃`: they enter only
through their integrals and through `henl`. -/
theorem gaussianRestricted_isoperimetry_measurable_of_enlargements (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hmass : 0 < ∫ x, h x)
    (henl : ∀ ε > (0 : ℝ), ∀ d' : ℝ, 0 < d' → d' < d →
      ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
        ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
        ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
        ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
        (∀ u ∈ U₁, ∀ v ∈ U₂,
          d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v)) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hP₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
  have hP₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
  -- the conclusion at every `d' < d`, obtained by letting `ε ↓ 0`
  have step : ∀ d' : ℝ, 0 < d' → d' < d →
      d' / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
    intro d' hd'0 hd'd
    have hslack : ∀ ε : ℝ, 0 < ε →
        d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
          ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by
      intro ε hε
      obtain ⟨U₁, U₂, hU₁, hU₂, hUdisj, hsl₁, hsl₂, hres, hsep⟩ := henl ε hε d' hd'0 hd'd
      exact gaussianRestricted_isoperimetry_of_enlargement_slack hn hσ hd'0 hf₀ hfc hh hhc hhB hhi
        hU₁ hU₂ hUdisj hmass hε.le hsl₁ hsl₂ hres hsep
    have hL : Tendsto (fun ε : ℝ =>
        d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (d' / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x))) := by
      have hc : Continuous fun ε : ℝ =>
          d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε)) :=
        continuous_const.mul
          ((continuous_const.max (continuous_const.sub continuous_id)).mul
            (continuous_const.max (continuous_const.sub continuous_id)))
      have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [max_eq_right hP₁, max_eq_right hP₂] using ht
    have hR : Tendsto (fun ε : ℝ => (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε))
        (𝓝[>] (0 : ℝ)) (𝓝 ((∫ x, h x) * ∫ x in S₃, h x)) := by
      have hc : Continuous fun ε : ℝ => (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by fun_prop
      have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using ht
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hslack ε hε
  -- now `d' ↑ d`
  have hL2 : Tendsto (fun t : ℝ => t / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)) (𝓝[<] d)
      (𝓝 (d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x))) := by
    have hc : Continuous fun t : ℝ => t / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by fun_prop
    exact (hc.tendsto d).mono_left (nhdsWithin_le_nhds (s := Set.Iio d))
  refine le_of_tendsto hL2 ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hd)]
    with t ht1 ht2 using step t ht2 ht1

end Slack

/-! ### Non-vacuity: the enlargement hypothesis is inhabited -/

section Witness

variable {n : ℕ}

/-- **The closed-slab partition.**  For a vector `e` and `c > 0`, the two *closed* half-spaces
`⟪e,x⟫ ≤ −c` and `c ≤ ⟪e,x⟫` together with the open slab between them partition `ℝⁿ`.

The mirror image of `ArlibCommunity.Foundations.Convex.isPartition3_slab`, which puts the two half-spaces open and the slab
closed.  This is the shape for which the open/closed capstone
`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo` does **not** apply directly. -/
theorem isPartition3_closedSlab (e : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc0 : 0 < c) :
    IsPartition3 Set.univ {x | (inner ℝ e x : ℝ) ≤ -c} {x | c ≤ (inner ℝ e x : ℝ)}
      {x | -c < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < c} where
  union := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases le_or_gt (inner ℝ e x : ℝ) (-c) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt c (inner ℝ e x : ℝ) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨h, h'⟩
  disjoint₁₂ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith
  disjoint₁₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.1]
  disjoint₂₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.2]

/-- A closed half-space bounded by a unit normal is **not** open: its boundary point `c·e` is a
limit of points just outside. -/
theorem not_isOpen_inner_le {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (c : ℝ) :
    ¬ IsOpen {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) ≤ c} := by
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  intro hopen
  have hmem : (c • e : EuclideanSpace ℝ (Fin n)) ∈ {x : EuclideanSpace ℝ (Fin n) |
      (inner ℝ e x : ℝ) ≤ c} := by
    simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]
    exact le_rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  have hy : (c • e + (r / 2) • e : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (c • e) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (c • e + (r / 2) • e : EuclideanSpace ℝ (Fin n)) - c • e = (r / 2) • e := by abel
    rw [this, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith)]
    linarith
  have := hball hy
  simp only [Set.mem_setOf_eq, inner_add_right, real_inner_smul_right, hee, mul_one] at this
  linarith

/-- The mirror of `ArlibCommunity.Foundations.Convex.not_isOpen_inner_le` for the opposite half-space. -/
theorem not_isOpen_le_inner {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (c : ℝ) :
    ¬ IsOpen {x : EuclideanSpace ℝ (Fin n) | c ≤ (inner ℝ e x : ℝ)} := by
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  intro hopen
  have hmem : (c • e : EuclideanSpace ℝ (Fin n)) ∈ {x : EuclideanSpace ℝ (Fin n) |
      c ≤ (inner ℝ e x : ℝ)} := by
    simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]
    exact le_rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  have hy : (c • e - (r / 2) • e : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (c • e) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (c • e - (r / 2) • e : EuclideanSpace ℝ (Fin n)) - c • e = (-(r / 2)) • e := by
      rw [neg_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonpos (by linarith)]
    linarith
  have := hball hy
  simp only [Set.mem_setOf_eq, inner_sub_right, real_inner_smul_right, hee, mul_one] at this
  linarith

/-- **Non-vacuity of `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_of_enlargements`** — in
particular of its enlargement hypothesis `henl`, which is the only strong one.

The data is `σ = 1`, `f ≡ 1` — so `h` is the standard Gaussian, continuous, bounded by `1`,
integrable, of positive total mass — the **closed** slab partition orthogonal to the first
coordinate axis,

  `S₁ = {⟪e,x⟫ ≤ −1/4}`,  `S₂ = {1/4 ≤ ⟪e,x⟫}`,  `S₃ = {−1/4 < ⟪e,x⟫ < 1/4}`,

and `d = log 2 / 4`.  `henl` is discharged, for **every** `ε > 0` and every `d' ∈ (0, d)`, by the
single pair of open half-spaces

  `U₁ = {⟪e,x⟫ < −1/8}`,  `U₂ = {1/8 < ⟪e,x⟫}`,

which are disjoint, contain `S₁, S₂` (so the two mass clauses hold with slack to spare, for every
`ε > 0`), leave the residual `(U₁ ∪ U₂)ᶜ = {|⟪e,x⟫| ≤ 1/8} ⊆ S₃`, and are separated by
`1/4 = 2·(1/8) ≤ ‖u − v‖ ≥ d'/log 2`, the last inequality because `d' < log 2/4`.

Two clauses are recorded beyond the theorem's hypotheses: `S₁` and `S₂` are **not open**
(`ArlibCommunity.Foundations.Convex.not_isOpen_inner_le`, `ArlibCommunity.Foundations.Convex.not_isOpen_le_inner`), so
`ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo` does not apply to this data directly and
the enlargement really is what carries it; and the conclusion is a **strictly positive** lower
bound, so the instance is not the trivial `0 ≤ 0`. -/
theorem exists_enlargements_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d B : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ ε > (0 : ℝ), ∀ d' : ℝ, 0 < d' → d' < d →
        ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
          ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
          ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
          ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
          (∀ u ∈ U₁, ∀ v ∈ U₂,
            d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v)) ∧
      ¬ IsOpen S₁ ∧ ¬ IsOpen S₂ ∧
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
    have hx : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (2 : ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hhi : Integrable h := by
    have heq : h = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; rw [hhdef]; norm_num
    rw [heq]
    exact ArlibCommunity.Foundations.Convex.integrable_gaussian_eucl one_pos
  -- balls of radius `1/8` about `r·e`, for `|r| ≤ 1/2`, sit in the unit ball
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1 / 8),
      ‖x‖ ≤ 1 ∧ |(inner ℝ e x : ℝ) - r| < 1 / 8 := by
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
  have hlow : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1 / 8),
      Real.exp (-(1 : ℝ) / 2) ≤ h x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    rw [hhdef]
    simp only
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2 : ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) ≤ -(1 / 4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 4 : ℝ) ≤ (inner ℝ e x : ℝ)} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | -(1 / 4 : ℝ) < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < 1 / 4} with hS₃def
  set U₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)} with hU₁def
  set U₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)} with hU₂def
  have hme : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
      (∫ x in S, h x) ≤ ∫ x in T, h x := by
    intro S T hST
    exact setIntegral_mono_set hhi.integrableOn (Filter.Eventually.of_forall h0) hST.eventuallyLE
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := ((1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1 / 2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  have hp1 : 0 < ∫ x in S₁, h x := by
    refine setIntegral_pos_of_ball_le (z := (-(1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1 / 2)) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1 / 2)) (by norm_num) x hx
    rw [hS₁def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.2]
  have hp2 : 0 < ∫ x in S₂, h x := by
    refine setIntegral_pos_of_ball_le (z := ((1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1 / 2) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (1 / 2) (by norm_num) x hx
    rw [hS₂def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.1]
  refine ⟨fun _ => (1 : ℝ), h, S₁, S₂, S₃, 1, Real.log 2 / 4, 1, one_pos, by linarith,
    fun _ => zero_le_one, isLogConcave_const zero_le_one, fun x => by rw [hhdef]; ring,
    hhc, hhB, hhi, isPartition3_closedSlab e (by norm_num : (0 : ℝ) < 1 / 4), hM, ?_, ?_, ?_, ?_⟩
  · -- the enlargement family: the fixed pair of open half-spaces at `±1/8`
    intro ε hε d' hd'0 hd'd
    refine ⟨U₁, U₂, isOpen_lt hme continuous_const, isOpen_lt continuous_const hme, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro x hx hx'
      rw [hU₁def] at hx
      rw [hU₂def] at hx'
      simp only [Set.mem_setOf_eq] at hx hx'
      linarith
    · have hsub : S₁ ⊆ U₁ := by
        intro x hx
        rw [hS₁def] at hx
        rw [hU₁def]
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      linarith [hmono hsub]
    · have hsub : S₂ ⊆ U₂ := by
        intro x hx
        rw [hS₂def] at hx
        rw [hU₂def]
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      linarith [hmono hsub]
    · have hsub : (U₁ ∪ U₂)ᶜ ⊆ S₃ := by
        intro x hx
        have hx1 : x ∉ U₁ := fun hc => hx (Or.inl hc)
        have hx2 : x ∉ U₂ := fun hc => hx (Or.inr hc)
        rw [hU₁def] at hx1
        rw [hU₂def] at hx2
        simp only [Set.mem_setOf_eq, not_lt] at hx1 hx2
        rw [hS₃def]
        simp only [Set.mem_setOf_eq]
        constructor <;> linarith
      linarith [hmono hsub]
    · intro u hu v hv
      left
      rw [hU₁def] at hu
      rw [hU₂def] at hv
      simp only [Set.mem_setOf_eq] at hu hv
      have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1 / 8 : ℝ)) hu hv
      have hd'l : d' / Real.log 2 ≤ 1 / 4 := by
        rw [div_le_iff₀ hlog2]
        linarith
      linarith
  · rw [hS₁def]; exact not_isOpen_inner_le he _
  · rw [hS₂def]; exact not_isOpen_le_inner he _
  · have h1 : (0 : ℝ) < Real.log 2 / 4 / 1 := by
      rw [div_one]; linarith
    exact mul_pos h1 (mul_pos hp1 hp2)

end Witness

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_of_enlargement_slack
#print axioms ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_of_enlargements
#print axioms ArlibCommunity.Foundations.Convex.isPartition3_closedSlab
#print axioms ArlibCommunity.Foundations.Convex.not_isOpen_inner_le
#print axioms ArlibCommunity.Foundations.Convex.not_isOpen_le_inner
#print axioms ArlibCommunity.Foundations.Convex.exists_enlargements_witness

end ArlibCommunity.Foundations.Convex

end

section
/-!
# Cousins–Vempala's `thm:iso` for **measurable** sets, with no Lipschitz hypothesis

[CV18] states `thm:iso` for an *arbitrary* partition `S₁, S₂, S₃`
of `ℝⁿ`.  Its proof reduces to the one-dimensional inequalities `(1d-1)`, `(1d-2)` by the
Localization Lemma, via the step at [CV18]:

> "By a standard combinatorial argument, we can assume that `Zᵢ = {t : (1−t)a+tb ∈ Sᵢ}` are
> intervals that partition `[a,b]`."

That step is not proved in the paper.  This repository proved the theorem for `S₁, S₂` **open**
and `S₃` **closed** — `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/OneDimSharp.lean`), where the reduction *is* available — and the
measurable case has been the open blocker since.

**This file closes it.**  The composition is:

1. `ArlibCommunity.Foundations.Convex.exists_enlargement_of_measurable` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`) —
   inner regularity inside `{h > 0}` followed by
   `ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_of_continuous`
   (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`), giving disjoint **open** `U₁, U₂` that carry
   all but `ε` of the mass of `S₁, S₂` and satisfy the separation at any `d' < d`;
2. `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_of_enlargements`
   (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`) — the open/closed capstone applied to
   `U₁, U₂, (U₁ ∪ U₂)ᶜ`, then `ε ↓ 0` and `d' ↑ d`.

## The two things that make it work

**Nothing is asked of `h` beyond continuity.**  The previous route to the measurable case —
`ArlibCommunity.Foundations.Convex.exists_disjoint_open_enlargement_gaussianIndicator`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoIndicator.lean`) — discharges the *density* branch of the
disjunction by converting it into the *metric* branch, which needs a global log-Lipschitz
bound on `h`.  That is free for the indicator density `1_K·γ` and is the binder `hellLip` for
the `ℓ`-weighted one, where, by the same informal argument, it has no witness with non-constant `ℓ`.
Here each pair stays in its own branch and only the *thresholds* move, so the estimate needed
is a perturbation bound for `densDist`, which uniform continuity on a compact set supplies —
**with the radius chosen after the sets**, hence with no inequality to satisfy against `σ`,
`R` or `n`.

**The known obstruction is evaded, not contradicted.**
`ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoOpenClosed.lean`)
exhibits data satisfying every hypothesis of `thm:iso` for which no disjoint open supersets of
`S₁, S₂` exist at all.  There the two sets touch, and they touch *inside* `{h = 0}`.  The route
above never asks for supersets of `S₁, S₂`: it asks for supersets of compact subsets of
`S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}`, which are disjoint compacts and hence a positive distance
apart, and the discarded part carries no mass precisely because `h` vanishes on it.

## What is proved here

* `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_logTwo` — `thm:iso` at the separation
  threshold `d/log 2`, for **measurable** `S₁, S₂, S₃`, for `h = f·γ` with `f` an arbitrary
  nonnegative log-concave function and `h` continuous, bounded and integrable.

Every binder is one the open/closed capstone already had, except that `hS₁ : IsOpen S₁`,
`hS₂ : IsOpen S₂`, `hS₃ : IsClosed S₃` are replaced by `MeasurableSet`, and `hd : 0 < d` is
added (the `d ≤ 0` case is trivial but is not routed here).

## Scope

This is an isoperimetric inequality.  It is **not** a conductance bound, a mixing time or a
running time, and may not be quoted as one.  What it does supply is the `hiso` binder shape of
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_speedyGaussian_ge`, once instantiated at a density; that
instantiation is a separate step and is not performed here.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/



open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

open MeasureTheory

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` ([CV18]) for measurable
`S₁, S₂, S₃`, at the separation threshold `d/log 2`.**

This is `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/OneDimSharp.lean`) with its three regularity binders

    hS₁ : IsOpen S₁,  hS₂ : IsOpen S₂,  hS₃ : IsClosed S₃

replaced by `MeasurableSet S₁`, `MeasurableSet S₂`, `MeasurableSet S₃`.  Everything else —
`hf₀`, `hfc`, `hh`, `hhc`, `hhB`, `hhi`, `hpart`, `hmass`, `hsep` and the conclusion — is
verbatim, save the added `hd : 0 < d`.

The proof carries **no** Lipschitz hypothesis on `h`, and no relation between `σ`, `R` and
`n`; see the module docstring for why the route avoids one and why
`ArlibCommunity.Foundations.Convex.exists_separated_no_disjoint_open_enlargement` does not apply to it. -/
theorem gaussianRestricted_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  refine gaussianRestricted_isoperimetry_measurable_of_enlargements hn hσ hd hf₀ hfc hh hhc
    hhB hhi hmass ?_
  intro ε hε d' _ hd'd
  exact exists_enlargement_of_measurable (by omega) hσ hd'd hε hhc hh0 hhi hpart hS₁ hS₂ hS₃ hsep

/-! ## The `ℓ`-weighted instantiation -/

/-! ## Non-vacuity of the capstone -/

/-- **The hypothesis bundle of `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_logTwo` is
satisfiable at data that the open/closed capstone cannot reach.**

`f ≡ 1`, so `h` is the standard Gaussian; `σ = 1`, `d = log 2 / 4`, and the **closed slab**
partition of `ArlibCommunity.Foundations.Convex.isPartition3_closedSlab` at `c = 1/4`:

    S₁ = {⟪e,x⟫ ≤ −1/4},   S₂ = {1/4 ≤ ⟪e,x⟫},   S₃ = {−1/4 < ⟪e,x⟫ < 1/4}.

The separation holds on the metric branch: `⟪e, v − u⟫ ≥ 1/2` and `‖e‖ = 1`, so
`‖u − v‖ ≥ 1/2 ≥ 1/4 = d/log 2`.

The last two conjuncts are the point: `S₁` and `S₂` are **not open**
(`ArlibCommunity.Foundations.Convex.not_isOpen_inner_le`, `ArlibCommunity.Foundations.Convex.not_isOpen_le_inner`), so this data is *outside* the
reach of `ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_openClosed_logTwo` — the theorem proved here
is being applied where its predecessor cannot be.

`ArlibCommunity.Foundations.Convex.exists_enlargements_witness` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoMeasurable.lean`) certifies,
for this same slab data, that the left-hand side `d/σ·(∫_{S₁}h)(∫_{S₂}h)` is **strictly
positive**, so the conclusion here is not the trivial `0 ≤ ·`. -/
theorem gaussianRestricted_isoperimetry_measurable_logTwo_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d B : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      ¬ IsOpen S₁ ∧ ¬ IsOpen S₂ ∧
      d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
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
    refine Real.exp_le_one_iff.mpr ?_
    have hx : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < 2 * (1 : ℝ) ^ 2 := by norm_num
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
  have hhi : Integrable h := by
    have heq : h = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; rw [hhdef]; norm_num
    rw [heq]
    exact ArlibCommunity.Foundations.Convex.integrable_gaussian_eucl one_pos
  -- positive total mass, from a floor on the unit ball
  have hlow : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, Real.exp (-(1 : ℝ) / 2) ≤ h x := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [hhdef]
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2 * (1:ℝ) ^ 2)]
    nlinarith
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _)
      (Set.subset_univ _) hlow
    rwa [setIntegral_univ] at hpos
  -- the slabs
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) ≤ -(1 / 4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 4 : ℝ) ≤ (inner ℝ e x : ℝ)} with hS₂def
  have hipc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) := by fun_prop
  have hS₁m : MeasurableSet S₁ := measurableSet_le hipc.measurable measurable_const
  have hS₂m : MeasurableSet S₂ := measurableSet_le measurable_const hipc.measurable
  have hdlog : Real.log 2 / 4 / Real.log 2 = 1 / 4 := by
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  refine ⟨fun _ => 1, h, S₁, S₂, {x | -(1/4 : ℝ) < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < 1/4},
    1, Real.log 2 / 4, 1, one_pos, by positivity, fun _ => zero_le_one,
    isLogConcave_const zero_le_one, (fun x => by rw [hhdef]; ring), hhc, hhB, hhi,
    isPartition3_closedSlab e (by norm_num), hS₁m, hS₂m,
    (measurableSet_lt measurable_const hipc.measurable).inter
      (measurableSet_lt hipc.measurable measurable_const),
    hM, ?_, not_isOpen_inner_le he _, not_isOpen_le_inner he _, ?_⟩
  · -- the metric branch, at `d/log 2 = 1/4 ≤ 1/2 ≤ ‖u − v‖`
    intro u hu v hv
    left
    rw [hdlog]
    have h1 : (inner ℝ e u : ℝ) ≤ -(1 / 4 : ℝ) := hu
    have h2 : (1 / 4 : ℝ) ≤ (inner ℝ e v : ℝ) := hv
    have hip := abs_real_inner_le_norm e (v - u)
    rw [he, one_mul, inner_sub_right] at hip
    have hle : (inner ℝ e v : ℝ) - (inner ℝ e u : ℝ) ≤ ‖v - u‖ :=
      le_trans (le_abs_self _) hip
    rw [norm_sub_rev] at hle
    linarith
  · -- the conclusion, from the capstone itself
    refine gaussianRestricted_isoperimetry_measurable_logTwo hn one_pos (by positivity)
      (fun _ => zero_le_one) (isLogConcave_const zero_le_one) (fun x => by rw [hhdef]; ring)
      hhc hhB hhi (isPartition3_closedSlab e (by norm_num)) hS₁m hS₂m
      ((measurableSet_lt measurable_const hipc.measurable).inter
        (measurableSet_lt hipc.measurable measurable_const)) hM ?_
    intro u hu v hv
    left
    rw [hdlog]
    have h1 : (inner ℝ e u : ℝ) ≤ -(1 / 4 : ℝ) := hu
    have h2 : (1 / 4 : ℝ) ≤ (inner ℝ e v : ℝ) := hv
    have hip := abs_real_inner_le_norm e (v - u)
    rw [he, one_mul, inner_sub_right] at hip
    have hle : (inner ℝ e v : ℝ) - (inner ℝ e u : ℝ) ≤ ‖v - u‖ :=
      le_trans (le_abs_self _) hip
    rw [norm_sub_rev] at hle
    linarith

section AxiomCheck

#print axioms ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_logTwo
#print axioms ArlibCommunity.Foundations.Convex.gaussianRestricted_isoperimetry_measurable_logTwo_witness

end AxiomCheck

end ArlibCommunity.Foundations.Convex

end
