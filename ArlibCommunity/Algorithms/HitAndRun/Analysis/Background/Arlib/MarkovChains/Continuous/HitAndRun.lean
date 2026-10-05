/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalk
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Conductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.UniformOn
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The hit-and-run walk on a body, as a Markov kernel

Lovász–Vempala, *Hit-and-Run from a Corner* (SIAM J. Comput. 35 (2006) 985-1005;
`https://faculty.cc.gatech.edu/~vempala/papers/start.pdf`), §3, define the **hit-and-run
walk** on a body `K ⊆ ℝⁿ`: from the current point `u`, pick a direction `θ` uniformly at
random on the unit sphere, and move to a point chosen **uniformly from the chord**
`K ∩ (u + ℝθ)`.  This module builds that walk as a genuine `ProbabilityTheory.Kernel` on
`EuclideanSpace ℝ (Fin n)`, proves the closed form of its one-step density — equation (5)
of the paper — and deduces detailed balance for the uniform measure on `K`.

The walk is defined **operationally**, exactly as described above
(`hitAndRunProposal_apply_uniformOn` states the "uniform direction, then uniform point on
the chord" reading against `Arlib.uniformOn`); equation (5) is then a *theorem*
(`hitAndRunProposal_eq_density`), not a definition.

## Main definitions

* `Arlib.MarkovChains.chordSet K u v = {t : ℝ | u + t • v ∈ K}` — the **parameter set of
  the chord** of `K` through `u` in direction `v`.  For convex `K` this is an interval;
  nothing below assumes convexity, and for a general measurable `K` it is the parameter
  set of the whole one-dimensional slice.
* `Arlib.MarkovChains.chordLength K u x = ‖x - u‖ · vol₁(chordSet K u (x - u))` — the
  paper's `ℓ(u, x)`, the one-dimensional Lebesgue measure of the chord of `K` through `u`
  and `x`.  The factor `‖x - u‖` is the speed of the parameterisation `t ↦ u + t(x - u)`.
* `Arlib.MarkovChains.sphereArea n` and `Arlib.MarkovChains.unifSphere n` — the surface
  area `vol_{n-1}(∂B)` of the unit sphere (Mathlib's `MeasureTheory.Measure.toSphere` of
  the whole sphere) and the normalised measure on it.
* `Arlib.MarkovChains.hitAndRunProposal K u` — the law of one step from `u`: the image
  under `(θ, t) ↦ u + t • θ` of `unifSphere ⊗ volume` reweighted by
  `chordDensity K u (θ, t) = 1[u + t θ ∈ K] / vol₁(chordSet K u θ)`.
* `Arlib.MarkovChains.hitAndRunDensity K u x = 1 / (ℓ(u,x) · ‖x - u‖^{n-1})` — the
  integrand of equation (5).
* `Arlib.MarkovChains.hitAndRun K` — **the hit-and-run kernel**.  On a measurable `K` it
  is `hitAndRunProposal K u + (1 - hitAndRunProposal K u univ) • dirac u`; on a
  non-measurable `K` — where the proposal is not a kernel at all — it is the identity
  kernel, so that `hitAndRun` is a total function of `K`.  Every lemma below that says
  anything about its value carries `MeasurableSet K`.

## Main results

* `Arlib.MarkovChains.isMarkovKernel_hitAndRun` — **hit-and-run is a Markov kernel**, for
  every `K` and every `n`.  The lazy atom at `u` absorbs whatever mass the proposal
  loses, which is exactly the mass of the directions along which the chord through `u` is
  null or infinite; `hitAndRunProposal_univ_eq_one` says the atom is empty as soon as
  every chord through `u` has positive finite length, and
  `hitAndRunProposal_unitBall_univ` discharges that on the unit ball.
* `Arlib.MarkovChains.lintegral_polar`, `Arlib.MarkovChains.lintegral_polar_at` — **polar
  coordinates for `lintegral`**, at the origin and at an arbitrary centre `u`:
  `∫⁻ x, g x = ∫⁻_{∂B} ∫⁻_{r > 0} r^{n-1} g(u + rθ) dr dθ`.  Built from Mathlib's
  `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, which is exactly
  the right tool: it is the statement that the polar homeomorphism carries Haar measure
  to `μ.toSphere ⊗ volumeIoiPow (n-1)`.  Mathlib only exposes the *radial* consequences
  (`integral_fun_norm_addHaar`), so the general-integrand `ℝ≥0∞` version is built here.
* `Arlib.MarkovChains.hitAndRunProposal_eq_density` — **equation (5)**:

      P_u(A) = (2 / vol_{n-1}(∂B)) · ∫_{A ∩ K} dx / (ℓ(u,x) · ‖x - u‖^{n-1}).

  The factor `2` is the two half-rays of each chord: the direction `θ` and the direction
  `-θ` give the same chord, and here they are combined by reflecting the inward half-ray
  through `u` (`lintegral_ray_neg`) rather than by any symmetry of the sphere measure.
* `Arlib.MarkovChains.chordLength_comm`, `Arlib.MarkovChains.hitAndRunDensity_comm` — the
  crux: **`ℓ(u,x) = ℓ(x,u)`**, because `t ↦ 1 - t` carries the parameterisation of the
  chord from `u` to the parameterisation from `x`.  Hence the density of equation (5) is
  manifestly symmetric.
* `Arlib.MarkovChains.isReversible_hitAndRun`, `Arlib.MarkovChains.invariant_hitAndRun` —
  **detailed balance for the uniform measure on `K`**, and therefore its invariance.  No
  convexity and no boundedness of `K` is needed: given equation (5), reversibility is one
  application of Tonelli plus `hitAndRunDensity_comm`.
* `Arlib.MarkovChains.exists_hitAndRun_witness` — the non-vacuity witness (`CLAUDE.md`
  §11): on the unit ball the uniform measure is a genuine probability measure, the walk
  leaves its current point with probability one, and its kernel *is* the density of
  equation (5) with no stay-put mass at all.

## Degenerate cases

**`n = 0`.**  `EuclideanSpace ℝ (Fin 0)` has an empty unit sphere, so there is no
direction to pick and the proposal is the zero measure: the kernel degenerates to
`dirac u`.  The kernel, its Markov property and reversibility are all still correct
statements at `n = 0`; polar coordinates and equation (5) carry `[NeZero n]`.

**Chords of measure `0` or `∞`.**  `ℝ≥0∞` divides by zero to zero, so a direction along
which the chord is null contributes nothing, and one along which it is infinite (an
unbounded `K`) likewise.  That lost mass is returned to `u` by the lazy atom, which is
why the kernel is Markov with no hypothesis on `K` whatsoever.  Statements whose content
is about a walk that actually moves therefore carry an explicit
`hitAndRunProposal K u univ = 1` hypothesis, discharged on the unit ball by
`hitAndRunProposal_unitBall_univ`.

## Scope: what is deliberately absent

There is **no conductance bound and no mixing bound here, in any form** — not as a
theorem, not as an assumed predicate, not as a definition whose name asserts one.  The
paper's conductance bound (Theorem 4.2) rests on its Theorem 2.1, which is proved by
applying the Localization Lemma to *signed* integrands; that step is an open gap in this
repository (see `Arlib/Convexity/TransverseCut.lean`, and note that Borsuk–Ulam is absent
from Mathlib v4.32).  What this file supplies is the object such a bound would be
*about*, together with the reversibility that any conductance argument presupposes.  The
conductance machinery it feeds — `Arlib.MarkovChains.conductance`, `Cheeger.lean`,
`L2Mixing.lean`'s `mixesWithin_of_conductance` — is already in place and needs only the
missing isoperimetric input.

`Arlib.MarkovChains.Continuous.BallWalk` is imported for `IsReversible.smul` and for the
unit-ball guards `volume_unitBall_ne_zero` / `volume_unitBall_ne_top` /
`isProbabilityMeasure_uniformOn_unitBall`, which are walk-independent.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## The chord -/

/-- The parameter set of the chord. -/
def chordSet (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {t | u + t • v ∈ K}

theorem mem_chordSet_iff {K : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n)} {t : ℝ} : t ∈ chordSet K u v ↔ u + t • v ∈ K := Iff.rfl

theorem measurableSet_chordSet {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u v : EuclideanSpace ℝ (Fin n)) : MeasurableSet (chordSet K u v) :=
  hK.preimage (by fun_prop)

/-- The chord length. -/
noncomputable def chordLength (K : Set (EuclideanSpace ℝ (Fin n)))
    (u x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ‖x - u‖ * volume (chordSet K u (x - u))

/-- `chordSet` at a rescaled direction. -/
theorem chordSet_smul (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n))
    (r : ℝ) : chordSet K u (r • v) = (fun t => t * r) ⁻¹' chordSet K u v := by
  ext t
  simp only [chordSet, Set.mem_setOf_eq, Set.mem_preimage, smul_smul]

theorem volume_chordSet_smul (K : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : r ≠ 0) :
    volume (chordSet K u (r • v)) = ENNReal.ofReal |r⁻¹| * volume (chordSet K u v) := by
  rw [chordSet_smul K u v r, Real.volume_preimage_mul_right hr]

/-- **The chord through `u` and `x` does not depend on which endpoint parameterises it.** -/
theorem chordSet_comm (K : Set (EuclideanSpace ℝ (Fin n))) (u x : EuclideanSpace ℝ (Fin n)) :
    chordSet K x (u - x) = (fun t => 1 - t) ⁻¹' chordSet K u (x - u) := by
  ext t
  simp only [chordSet, Set.mem_setOf_eq, Set.mem_preimage]
  congr! 1
  module

theorem volume_chordSet_comm (K : Set (EuclideanSpace ℝ (Fin n))) (u x : EuclideanSpace ℝ (Fin n)) :
    volume (chordSet K x (u - x)) = volume (chordSet K u (x - u)) := by
  rw [chordSet_comm]
  exact (Measure.measurePreserving_sub_left volume 1).measure_preimage_emb
    (measurableEmbedding_subLeft 1) _

/-- **`ℓ(u, x) = ℓ(x, u)`** — the gift that makes reversibility easy. -/
theorem chordLength_comm (K : Set (EuclideanSpace ℝ (Fin n))) (u x : EuclideanSpace ℝ (Fin n)) :
    chordLength K u x = chordLength K x u := by
  rw [chordLength, chordLength, norm_sub_rev, volume_chordSet_comm]

/-! ## Measurability -/

theorem measurable_volume_chordSet {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      volume (chordSet K p.1 p.2) := by
  have hS : MeasurableSet
      {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ | q.1.1 + q.2 • q.1.2 ∈ K} :=
    hK.preimage (by fun_prop)
  have := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hS
  convert this using 2 with p
  rfl

theorem measurable_chordLength {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      chordLength K p.1 p.2 := by
  refine Measurable.mul ?_ ?_
  · exact (continuous_norm.comp (continuous_snd.sub continuous_fst)).measurable.ennreal_ofReal
  · exact (measurable_volume_chordSet hK).comp (measurable_fst.prodMk
      (measurable_snd.sub measurable_fst))

/-! ## The uniform measure on the sphere of directions -/

/-- The total mass of `Measure.toSphere`: the surface area `vol_{n-1}(∂B)` of the unit
sphere. -/
noncomputable def sphereArea (n : ℕ) : ℝ≥0∞ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ

theorem sphereArea_eq (n : ℕ) :
    sphereArea n = n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [sphereArea, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]

theorem sphereArea_ne_zero [NeZero n] : sphereArea n ≠ 0 := by
  rw [sphereArea]
  exact fun h => (Measure.toSphere_ne_zero (E := EuclideanSpace ℝ (Fin n)) volume)
    (Measure.measure_univ_eq_zero.1 h)

theorem sphereArea_ne_top (n : ℕ) : sphereArea n ≠ ⊤ :=
  (measure_lt_top _ _).ne

/-- The uniform (normalised surface) measure on the unit sphere of directions. -/
noncomputable def unifSphere (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (sphereArea n)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

instance isProbabilityMeasure_unifSphere [NeZero n] : IsProbabilityMeasure (unifSphere n) := by
  refine ⟨?_⟩
  rw [unifSphere, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel sphereArea_ne_zero (sphereArea_ne_top n)

instance isFiniteMeasure_unifSphere : IsFiniteMeasure (unifSphere n) := by
  refine ⟨lt_of_le_of_lt ?_ ENNReal.one_lt_top⟩
  rw [unifSphere, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

/-! ## The proposal measure -/

/-- The density of the hit-and-run step in direction/parameter coordinates. -/
noncomputable def chordDensity (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) : ℝ≥0∞ :=
  (volume (chordSet K u (p.1 : EuclideanSpace ℝ (Fin n))))⁻¹ *
    K.indicator 1 (u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)))

theorem indicator_eq_chordSet_indicator (K : Set (EuclideanSpace ℝ (Fin n)))
    (u v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (u + t • v)
      = (chordSet K u v).indicator 1 t := by
  by_cases h : u + t • v ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_chordSet_iff.2 h), Pi.one_apply,
      Pi.one_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (mem_chordSet_iff.1 hc))]

theorem measurable_chordDensity_prod {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) :
    Measurable fun q : EuclideanSpace ℝ (Fin n) ×
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) => chordDensity K q.1 q.2 := by
  refine Measurable.mul ?_ ?_
  · exact ((measurable_volume_chordSet hK).comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp (measurable_fst.comp
        measurable_snd)))).inv
  · exact (measurable_one.indicator hK).comp
      ((continuous_fst.add ((continuous_snd.comp continuous_snd).smul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).measurable)

theorem measurable_chordDensity {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) : Measurable (chordDensity K u) := by
  refine Measurable.mul ?_ ?_
  · exact ((measurable_volume_chordSet hK).comp
      (measurable_const.prodMk (measurable_subtype_coe.comp measurable_fst))).inv
  · exact (measurable_one.indicator hK).comp
      ((continuous_const.add (continuous_snd.smul
        (continuous_subtype_val.comp continuous_fst))).measurable)

/-- **The hit-and-run proposal from `u`.** -/
noncomputable def hitAndRunProposal (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (((unifSphere n).prod volume).withDensity (chordDensity K u)).map
    (fun p => u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)))

theorem measurable_polarMap (u : EuclideanSpace ℝ (Fin n)) :
    Measurable fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)) :=
  (continuous_const.add (continuous_snd.smul continuous_subtype_val.fst')).measurable

theorem hitAndRunProposal_apply (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRunProposal K u A
      = ∫⁻ p in (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
            u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n))) ⁻¹' A,
          chordDensity K u p ∂((unifSphere n).prod volume) := by
  rw [hitAndRunProposal, Measure.map_apply (measurable_polarMap u) hA,
    withDensity_apply _ (hA.preimage (measurable_polarMap u))]

theorem unifSphere_univ_le_one (n : ℕ) : unifSphere n Set.univ ≤ 1 := by
  rw [unifSphere, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

theorem hitAndRunProposal_apply' (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRunProposal K u A
      = ∫⁻ p, A.indicator 1 (u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n))) * chordDensity K u p
          ∂((unifSphere n).prod volume) := by
  rw [hitAndRunProposal_apply K u hA, ← lintegral_indicator (hA.preimage (measurable_polarMap u))]
  refine lintegral_congr fun p => ?_
  by_cases hp : u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n)) ∈ A
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by exact hp), Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by exact hp), zero_mul]

theorem lintegral_chordDensity {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ p, chordDensity K u p ∂((unifSphere n).prod volume)
      = ∫⁻ θ, (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ *
          volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) ∂(unifSphere n) := by
  rw [lintegral_prod _ (measurable_chordDensity hK u).aemeasurable]
  refine lintegral_congr fun θ => ?_
  simp only [chordDensity]
  simp_rw [indicator_eq_chordSet_indicator K u (θ : EuclideanSpace ℝ (Fin n))]
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_chordSet hK u _)),
    lintegral_indicator_one (measurableSet_chordSet hK _ _)]

theorem hitAndRunProposal_univ_le_one {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n)) :
    hitAndRunProposal K u Set.univ ≤ 1 := by
  rw [hitAndRunProposal_apply K u MeasurableSet.univ, Set.preimage_univ, Measure.restrict_univ,
    lintegral_chordDensity hK u]
  calc ∫⁻ θ, (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ *
        volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) ∂(unifSphere n)
      ≤ ∫⁻ _, 1 ∂(unifSphere n) := lintegral_mono fun θ => ENNReal.inv_mul_le_one _
    _ ≤ 1 := by rw [lintegral_const, one_mul]; exact unifSphere_univ_le_one n

theorem measurable_hitAndRunProposal {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    Measurable fun u => hitAndRunProposal K u A := by
  have hfun : Measurable fun q : EuclideanSpace ℝ (Fin n) ×
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) =>
      A.indicator 1 (q.1 + q.2.2 • (q.2.1 : EuclideanSpace ℝ (Fin n))) *
        chordDensity K q.1 q.2 := by
    refine Measurable.mul ?_ (measurable_chordDensity_prod hK)
    exact (measurable_one.indicator hA).comp
      ((continuous_fst.add ((continuous_snd.comp continuous_snd).smul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).measurable)
  simpa only [hitAndRunProposal_apply' K _ hA] using hfun.lintegral_prod_right'

theorem measurable_polarIntegrand {K A : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hA : MeasurableSet A) (u : EuclideanSpace ℝ (Fin n)) :
    Measurable fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      A.indicator 1 (u + p.2 • (p.1 : EuclideanSpace ℝ (Fin n))) * chordDensity K u p := by
  refine Measurable.mul ?_ (measurable_chordDensity hK u)
  exact (measurable_one.indicator hA).comp
    ((continuous_const.add (continuous_snd.smul
      (continuous_subtype_val.comp continuous_fst))).measurable)

/-- **The proposal really is "uniform direction, then uniform point on the chord".**
Conditionally on the direction `θ`, the parameter `t` is distributed uniformly on the
chord's parameter set `chordSet K u θ`, and the walk moves to `u + t • θ`. -/
theorem hitAndRunProposal_apply_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRunProposal K u A
      = ∫⁻ θ, Arlib.uniformOn (volume : Measure ℝ)
            (chordSet K u (θ : EuclideanSpace ℝ (Fin n)))
            {t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A} ∂(unifSphere n) := by
  rw [hitAndRunProposal_apply' K u hA,
    lintegral_prod _ (measurable_polarIntegrand hK hA u).aemeasurable]
  refine lintegral_congr fun θ => ?_
  have hpre : MeasurableSet {t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A} :=
    hA.preimage (by fun_prop)
  rw [Arlib.uniformOn_apply _ (measurableSet_chordSet hK u _) hpre, ENNReal.div_eq_inv_mul]
  simp only [chordDensity]
  have hset : ∀ t : ℝ,
      A.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
          (u + t • (θ : EuclideanSpace ℝ (Fin n))) *
        ((volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ *
          K.indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))))
      = (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ *
          ({t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A} ∩
            chordSet K u (θ : EuclideanSpace ℝ (Fin n))).indicator 1 t := by
    intro t
    by_cases h1 : u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A <;>
      by_cases h2 : u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ K <;>
      simp [h1, h2, chordSet, Set.mem_inter_iff]
  simp_rw [hset]
  rw [lintegral_const_mul _ (measurable_one.indicator (hpre.inter (measurableSet_chordSet hK u _))),
    lintegral_indicator_one (hpre.inter (measurableSet_chordSet hK u _))]

/-! ## The kernel -/

/-- The hit-and-run kernel on a measurable `K`. -/
noncomputable def hitAndRunAux (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun u := hitAndRunProposal K u + (1 - hitAndRunProposal K u Set.univ) • Measure.dirac u
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ ht]
    exact (measurable_hitAndRunProposal hK ht).add
      ((measurable_const.sub (measurable_hitAndRunProposal hK MeasurableSet.univ)).mul
        (measurable_one.indicator ht))

theorem hitAndRunAux_apply (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) :
    hitAndRunAux K hK u
      = hitAndRunProposal K u + (1 - hitAndRunProposal K u Set.univ) • Measure.dirac u := rfl

theorem hitAndRunAux_apply_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) :
    hitAndRunAux K hK u t
      = hitAndRunProposal K u t + (1 - hitAndRunProposal K u Set.univ) * t.indicator 1 u := by
  rw [hitAndRunAux_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ ht]

instance isMarkovKernel_hitAndRunAux (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) :
    IsMarkovKernel (hitAndRunAux K hK) := by
  refine ⟨fun u => ⟨?_⟩⟩
  rw [hitAndRunAux_apply_set hK u MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ u), Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (hitAndRunProposal_univ_le_one hK u)

open scoped Classical in
/-- **The hit-and-run walk on `K`.** -/
noncomputable def hitAndRun (K : Set (EuclideanSpace ℝ (Fin n))) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  if hK : MeasurableSet K then hitAndRunAux K hK else Kernel.deterministic id measurable_id

open scoped Classical in
theorem hitAndRun_eq {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    hitAndRun K = hitAndRunAux K hK := dif_pos hK

instance isMarkovKernel_hitAndRun (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsMarkovKernel (hitAndRun K) := by
  unfold hitAndRun
  split_ifs with hK
  · exact isMarkovKernel_hitAndRunAux K hK
  · infer_instance

theorem hitAndRun_apply_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) :
    hitAndRun K u t
      = hitAndRunProposal K u t + (1 - hitAndRunProposal K u Set.univ) * t.indicator 1 u := by
  rw [hitAndRun_eq hK, hitAndRunAux_apply_set hK u ht]

/-! ## Polar coordinates -/

section Polar

variable [NeZero n]

/-- **Polar coordinates for `lintegral`, centred at the origin.** -/
theorem lintegral_polar {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (n - 1)) * g (r • (θ : EuclideanSpace ℝ (Fin n)))
          ∂(volume : Measure ℝ) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1 = n - 1 := by
    rw [finrank_euclideanSpace_fin]
  -- Step 1: the measure-preserving polar homeomorphism.
  have MP := (volume :
    Measure (EuclideanSpace ℝ (Fin n))).measurePreserving_homeomorphUnitSphereProd
  have MP' := MP.symm
    (Homeomorph.toMeasurableEquiv (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))))
  have h := MP'.lintegral_comp
    (f := fun y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) => g y)
    (hg.comp measurable_subtype_coe)
  rw [lintegral_subtype_comap (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin n))).compl,
    restrict_compl_singleton] at h
  have h2 : ∫⁻ p, g ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)))
        ∂(((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).prod
          (Measure.volumeIoiPow (n - 1)))
      = ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← hdim, ← h]
    rfl
  rw [← h2]
  -- Step 2: Tonelli, then the `r ^ (n-1)` density.
  rw [lintegral_prod _ (by fun_prop : AEMeasurable
    (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ) =>
      g ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)))) _)]
  refine lintegral_congr fun θ => ?_
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ← lintegral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)) * g (r • (θ : EuclideanSpace ℝ (Fin n))))]
  rfl

/-- **Polar coordinates for `lintegral`, centred at `u`.** -/
theorem lintegral_polar_at (u : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (n - 1)) * g (u + r • (θ : EuclideanSpace ℝ (Fin n)))
          ∂(volume : Measure ℝ) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hgu : Measurable fun y : EuclideanSpace ℝ (Fin n) => g (u + y) :=
    hg.comp (measurable_const_add u)
  have ht : ∫⁻ y, g (u + y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin n))) u).lintegral_comp hg
  rw [← ht, lintegral_polar hgu]

end Polar

/-! ## The density -/

/-- `ℓ(u, x)` on the ray through `u` in direction `θ`. -/
theorem chordLength_polar (K : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) {r : ℝ} (hr : 0 < r) :
    chordLength K u (u + r • (θ : EuclideanSpace ℝ (Fin n)))
      = volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) := by
  have hθ : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
  rw [chordLength, add_sub_cancel_left, volume_chordSet_smul K u _ hr.ne', norm_smul, hθ,
    mul_one, Real.norm_eq_abs, abs_of_pos hr, ← mul_assoc, ← ENNReal.ofReal_mul hr.le,
    abs_of_pos (inv_pos.2 hr), mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul]

/-- Reflecting in `u` does not change the chord length at `u`. -/
theorem chordLength_reflect (K : Set (EuclideanSpace ℝ (Fin n)))
    (u y : EuclideanSpace ℝ (Fin n)) : chordLength K u (u + u - y) = chordLength K u y := by
  have h1 : u + u - y - u = (-1 : ℝ) • (y - u) := by module
  rw [chordLength, chordLength, h1, volume_chordSet_smul K u (y - u) (by norm_num : (-1:ℝ) ≠ 0),
    norm_smul]
  norm_num

/-- **The one-step density of equation (5)**, without its normalising constant:
`1 / (ℓ(u,x) · ‖x - u‖^{n-1})`. -/
noncomputable def hitAndRunDensity (K : Set (EuclideanSpace ℝ (Fin n)))
    (u x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (chordLength K u x * ENNReal.ofReal (‖x - u‖ ^ (n - 1)))⁻¹

/-- **The density is symmetric in its two arguments** — the reason hit-and-run is
reversible. -/
theorem hitAndRunDensity_comm (K : Set (EuclideanSpace ℝ (Fin n)))
    (u x : EuclideanSpace ℝ (Fin n)) : hitAndRunDensity K u x = hitAndRunDensity K x u := by
  rw [hitAndRunDensity, hitAndRunDensity, chordLength_comm, norm_sub_rev]

theorem measurable_hitAndRunDensity {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      hitAndRunDensity K p.1 p.2 := by
  refine (Measurable.mul (measurable_chordLength hK) ?_).inv
  exact (((continuous_snd.sub continuous_fst).norm.pow _).measurable).ennreal_ofReal

theorem measurable_hitAndRunDensity_right {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n)) :
    Measurable (hitAndRunDensity K u) := by
  have h1 : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      chordLength K ((u, x) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)).1 (u, x).2 :=
    (measurable_chordLength hK).comp (measurable_const.prodMk measurable_id)
  have h2 : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (‖x - u‖ ^ (n - 1)) :=
    ((continuous_id.sub continuous_const).norm.pow _).measurable.ennreal_ofReal
  exact (h1.mul h2).inv

/-- Reflecting in `u` does not change the density at `u`. -/
theorem hitAndRunDensity_reflect (K : Set (EuclideanSpace ℝ (Fin n)))
    (u y : EuclideanSpace ℝ (Fin n)) :
    hitAndRunDensity K u (u + u - y) = hitAndRunDensity K u y := by
  have h1 : ‖u + u - y - u‖ = ‖y - u‖ := by
    rw [show u + u - y - u = -(y - u) by module, norm_neg]
  rw [hitAndRunDensity, hitAndRunDensity, chordLength_reflect, h1]

/-! ## Equation (5) -/

section Five

variable [NeZero n]

omit [NeZero n] in
theorem measurable_rayLIntegral {K B : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hB : MeasurableSet B) (u : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    Measurable fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∫⁻ r in Set.Ioi (0 : ℝ),
        B.indicator 1 (u + (ε * r) • (θ : EuclideanSpace ℝ (Fin n))) *
          (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ := by
  have hf : Measurable fun q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      B.indicator 1 (u + (ε * q.2) • (q.1 : EuclideanSpace ℝ (Fin n))) *
        (volume (chordSet K u (q.1 : EuclideanSpace ℝ (Fin n))))⁻¹ := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_one.indicator hB).comp (by fun_prop)
    · exact ((measurable_volume_chordSet hK).comp
        (measurable_const.prodMk (measurable_subtype_coe.comp measurable_fst))).inv
  exact hf.lintegral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))

/-- The outgoing half-ray. -/
theorem lintegral_ray_pos {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
          B.indicator 1 (u + r • (θ : EuclideanSpace ℝ (Fin n))) *
            (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ ∂(volume : Measure ℝ)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      = ∫⁻ x in B, hitAndRunDensity K u x := by
  rw [← lintegral_indicator hB,
    lintegral_polar_at u ((measurable_hitAndRunDensity_right hK u).indicator hB)]
  refine lintegral_congr fun θ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  have hpow : ENNReal.ofReal (r ^ (n - 1)) ≠ 0 := by
    simpa using pow_pos hr0 (n - 1)
  have hlen : chordLength K u (u + r • (θ : EuclideanSpace ℝ (Fin n)))
      = volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) := chordLength_polar K u θ hr0
  have hnorm : ‖u + r • (θ : EuclideanSpace ℝ (Fin n)) - u‖ = r := by
    rw [add_sub_cancel_left, norm_smul, mem_sphere_zero_iff_norm.1 θ.2, mul_one,
      Real.norm_eq_abs, abs_of_pos hr0]
  by_cases hmem : u + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ B
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Pi.one_apply, one_mul,
      hitAndRunDensity, hlen, hnorm,
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr hpow), mul_left_comm,
      ENNReal.mul_inv_cancel hpow ENNReal.ofReal_ne_top, mul_one]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul, mul_zero]

/-- The incoming half-ray. -/
theorem lintegral_ray_neg {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
          B.indicator 1 (u + (-r) • (θ : EuclideanSpace ℝ (Fin n))) *
            (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ ∂(volume : Measure ℝ)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      = ∫⁻ x in B, hitAndRunDensity K u x := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => B.indicator (hitAndRunDensity K u) (u + u - x) with hg_def
  have hgmeas : Measurable g :=
    ((measurable_hitAndRunDensity_right hK u).indicator hB).comp
      (measurable_const.sub measurable_id)
  have hrefl : ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = ∫⁻ x in B, hitAndRunDensity K u x := by
    have := (Measure.measurePreserving_sub_left
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (u + u)).lintegral_comp hgmeas
    rw [← this, ← lintegral_indicator hB]
    refine lintegral_congr fun y => ?_
    rw [hg_def]
    simp only
    rw [sub_sub_cancel]
  rw [← hrefl, lintegral_polar_at u hgmeas]
  refine lintegral_congr fun θ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  have hpow : ENNReal.ofReal (r ^ (n - 1)) ≠ 0 := by
    simpa using pow_pos hr0 (n - 1)
  have hlen : chordLength K u (u + r • (θ : EuclideanSpace ℝ (Fin n)))
      = volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) := chordLength_polar K u θ hr0
  have hnorm : ‖u + r • (θ : EuclideanSpace ℝ (Fin n)) - u‖ = r := by
    rw [add_sub_cancel_left, norm_smul, mem_sphere_zero_iff_norm.1 θ.2, mul_one,
      Real.norm_eq_abs, abs_of_pos hr0]
  have hpt : u + u - (u + r • (θ : EuclideanSpace ℝ (Fin n)))
      = u + (-r) • (θ : EuclideanSpace ℝ (Fin n)) := by module
  rw [hg_def]
  simp only [hpt]
  by_cases hmem : u + (-r) • (θ : EuclideanSpace ℝ (Fin n)) ∈ B
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Pi.one_apply, one_mul,
      ← hpt, hitAndRunDensity_reflect, hitAndRunDensity, hlen, hnorm,
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr hpow), mul_left_comm,
      ENNReal.mul_inv_cancel hpow ENNReal.ofReal_ne_top, mul_one]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul, mul_zero]

omit [NeZero n] in
/-- The proposal, written against the unnormalised surface measure. -/
theorem hitAndRunProposal_eq_toSphere {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRunProposal K u A
      = (sphereArea n)⁻¹ * ∫⁻ θ, ∫⁻ t,
            (A ∩ K).indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) *
              (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [hitAndRunProposal_apply' K u hA,
    lintegral_prod _ (measurable_polarIntegrand hK hA u).aemeasurable, unifSphere,
    lintegral_smul_measure]
  congr 1
  refine lintegral_congr fun θ => lintegral_congr fun t => ?_
  simp only [chordDensity]
  by_cases h1 : u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ A
  · by_cases h2 : u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ K
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        Set.indicator_of_mem (Set.mem_inter h1 h2)]
      simp [mul_comm]
    · rw [Set.indicator_of_notMem h2,
        Set.indicator_of_notMem (fun hc => h2 (Set.mem_of_mem_inter_right hc))]
      simp
  · rw [Set.indicator_of_notMem h1,
      Set.indicator_of_notMem (fun hc => h1 (Set.mem_of_mem_inter_left hc))]
    simp

omit [NeZero n] in
/-- Splitting the line through `u` into its two half-rays. -/
theorem lintegral_ray_split {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (u : EuclideanSpace ℝ (Fin n)) (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (c : ℝ≥0∞) :
    ∫⁻ t, B.indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) * c ∂(volume : Measure ℝ)
      = (∫⁻ r in Set.Ioi (0 : ℝ),
            B.indicator 1 (u + r • (θ : EuclideanSpace ℝ (Fin n))) * c ∂(volume : Measure ℝ))
        + ∫⁻ r in Set.Ioi (0 : ℝ),
            B.indicator 1 (u + (-r) • (θ : EuclideanSpace ℝ (Fin n))) * c
              ∂(volume : Measure ℝ) := by
  have hFm : Measurable fun t : ℝ =>
      B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
        (u + t • (θ : EuclideanSpace ℝ (Fin n))) * c :=
    ((measurable_one.indicator hB).comp (by fun_prop)).mul measurable_const
  have hset : (Neg.neg ⁻¹' Set.Iio (0 : ℝ)) = Set.Ioi 0 := by
    ext x; simp
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (s := Set.Iio (0 : ℝ)) measurableSet_Iio hFm
  rw [hset] at hneg
  rw [← lintegral_add_compl _ (measurableSet_Ioi (a := (0 : ℝ))), Set.compl_Ioi,
    ← Measure.restrict_congr_set Iio_ae_eq_Iic, ← hneg]

/-- **Equation (5) of Lovász–Vempala.** -/
theorem hitAndRunProposal_eq_density {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRunProposal K u A
      = 2 / sphereArea n * ∫⁻ x in A ∩ K, hitAndRunDensity K u x := by
  have hAK : MeasurableSet (A ∩ K) := hA.inter hK
  have hP := measurable_rayLIntegral (B := A ∩ K) hK hAK u 1
  have hN := measurable_rayLIntegral (B := A ∩ K) hK hAK u (-1)
  simp only [one_mul] at hP
  simp only [neg_one_mul] at hN
  rw [hitAndRunProposal_eq_toSphere hK u hA]
  have hsplit : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫⁻ t, (A ∩ K).indicator 1 (u + t • (θ : EuclideanSpace ℝ (Fin n))) *
          (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ ∂(volume : Measure ℝ))
        = (∫⁻ r in Set.Ioi (0 : ℝ),
              (A ∩ K).indicator 1 (u + r • (θ : EuclideanSpace ℝ (Fin n))) *
                (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹ ∂(volume : Measure ℝ))
          + ∫⁻ r in Set.Ioi (0 : ℝ),
              (A ∩ K).indicator 1 (u + (-r) • (θ : EuclideanSpace ℝ (Fin n))) *
                (volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))))⁻¹
                ∂(volume : Measure ℝ) :=
    fun θ => lintegral_ray_split hAK u θ _
  simp_rw [hsplit]
  rw [lintegral_add_left hP, lintegral_ray_pos hK u hAK, lintegral_ray_neg hK u hAK,
    ENNReal.div_eq_inv_mul, mul_assoc]
  congr 1
  rw [two_mul]

/-! ## Reversibility -/

omit [NeZero n] in
theorem measurable_setLIntegral_density {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (B' : Set (EuclideanSpace ℝ (Fin n))) :
    Measurable fun u => ∫⁻ x in B', hitAndRunDensity K u x :=
  (measurable_hitAndRunDensity hK).lintegral_prod_right'
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict B')

/-- **The flow of the hit-and-run walk, split into its two parts.** -/
theorem flow_hitAndRun {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    flow (hitAndRun K) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) S T
      = 2 / sphereArea n * (∫⁻ u in S ∩ K, ∫⁻ x in T ∩ K, hitAndRunDensity K u x)
        + ∫⁻ u in T ∩ (S ∩ K), (1 - hitAndRunProposal K u Set.univ) := by
  have hpt : ∀ u : EuclideanSpace ℝ (Fin n), hitAndRun K u T
      = 2 / sphereArea n * (∫⁻ x in T ∩ K, hitAndRunDensity K u x)
        + T.indicator (fun v => 1 - hitAndRunProposal K v Set.univ) u := by
    intro u
    rw [hitAndRun_apply_set hK u hT, hitAndRunProposal_eq_density hK u hT]
    by_cases h : u ∈ T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [flow, Measure.restrict_restrict hS]
  simp_rw [hpt]
  rw [lintegral_add_left ((measurable_setLIntegral_density hK (T ∩ K)).const_mul _),
    lintegral_const_mul _ (measurable_setLIntegral_density hK (T ∩ K)),
    lintegral_indicator hT, Measure.restrict_restrict hT]

omit [NeZero n] in
/-- **The two-sided integral of the density is symmetric.** -/
theorem lintegral_density_comm {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (S T : Set (EuclideanSpace ℝ (Fin n))) :
    (∫⁻ u in S ∩ K, ∫⁻ x in T ∩ K, hitAndRunDensity K u x)
      = ∫⁻ u in T ∩ K, ∫⁻ x in S ∩ K, hitAndRunDensity K u x := by
  rw [lintegral_lintegral_swap (measurable_hitAndRunDensity hK).aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun u => ?_
  exact hitAndRunDensity_comm K u x

/-- **Detailed balance for Lebesgue measure restricted to `K`.** -/
theorem isReversible_hitAndRun_restrict {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) :
    IsReversible (hitAndRun K) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
  intro S T hS hT
  have h2 : T ∩ (S ∩ K) = S ∩ (T ∩ K) := by
    ext y; simp only [Set.mem_inter_iff]; tauto
  rw [flow_hitAndRun hK hS hT, flow_hitAndRun hK hT hS, lintegral_density_comm hK S T, h2]

/-- **The hit-and-run walk is reversible for the uniform measure on `K`.** -/
theorem isReversible_hitAndRun {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    IsReversible (hitAndRun K)
      (Arlib.uniformOn (volume : Measure (EuclideanSpace ℝ (Fin n))) K) :=
  (isReversible_hitAndRun_restrict hK).smul _

/-- **The uniform measure on `K` is invariant for hit-and-run.** -/
theorem invariant_hitAndRun {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) :
    Kernel.Invariant (hitAndRun K)
      (Arlib.uniformOn (volume : Measure (EuclideanSpace ℝ (Fin n))) K) :=
  (isReversible_hitAndRun hK).invariant

/-! ## Non-degeneracy and the witness -/

omit [NeZero n] in
/-- **The proposal never stays put**: the pushforward puts no mass on `{u}` itself. -/
theorem hitAndRunProposal_singleton (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : hitAndRunProposal K u {u} = 0 := by
  rw [hitAndRunProposal_apply K u (measurableSet_singleton u)]
  refine setLIntegral_measure_zero _ _ ?_
  refine measure_mono_null
    (t := (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) ×ˢ ({0} : Set ℝ)) ?_ ?_
  · rintro ⟨θ, t⟩ hp
    have hz : t • (θ : EuclideanSpace ℝ (Fin n)) = 0 := by
      have := (Set.mem_singleton_iff.1 hp)
      simpa using this
    have hθ : (θ : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      have := mem_sphere_zero_iff_norm.1 θ.2
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact ⟨Set.mem_univ _, by simpa [hθ] using (smul_eq_zero.1 hz).resolve_right hθ⟩
  · rw [Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **The proposal is a probability measure** as soon as every chord through `u` has
positive finite length. -/
theorem hitAndRunProposal_univ_eq_one {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n))
    (h0 : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) ≠ 0)
    (htop : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      volume (chordSet K u (θ : EuclideanSpace ℝ (Fin n))) ≠ ⊤) :
    hitAndRunProposal K u Set.univ = 1 := by
  rw [hitAndRunProposal_apply K u MeasurableSet.univ, Set.preimage_univ, Measure.restrict_univ,
    lintegral_chordDensity hK u,
    lintegral_congr (g := fun _ => (1 : ℝ≥0∞)) fun θ => ENNReal.inv_mul_cancel (h0 θ) (htop θ),
    lintegral_const, one_mul, measure_univ]

/-- Where the proposal has full mass, the kernel **is** the density of equation (5). -/
theorem hitAndRun_apply_eq_density {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u : EuclideanSpace ℝ (Fin n)) (h : hitAndRunProposal K u Set.univ = 1)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    hitAndRun K u A = 2 / sphereArea n * ∫⁻ x in A ∩ K, hitAndRunDensity K u x := by
  rw [hitAndRun_apply_set hK u hA, h, tsub_self, zero_mul, add_zero,
    hitAndRunProposal_eq_density hK u hA]

omit [NeZero n] in
/-- **The walk moves with probability one** where the proposal has full mass. -/
theorem hitAndRun_apply_compl_singleton {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : EuclideanSpace ℝ (Fin n))
    (h : hitAndRunProposal K u Set.univ = 1) : hitAndRun K u {u}ᶜ = 1 := by
  rw [hitAndRun_apply_set hK u (measurableSet_singleton u).compl,
    Set.indicator_of_notMem (by simp), mul_zero, add_zero,
    measure_compl (measurableSet_singleton u) (by rw [hitAndRunProposal_singleton]; simp),
    hitAndRunProposal_singleton, h, tsub_zero]

/-! ### The unit ball -/

omit [NeZero n] in
theorem chordSet_unitBall_subset {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 1)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    chordSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) u
        (θ : EuclideanSpace ℝ (Fin n)) ⊆ Set.Icc (-2) 2 := by
  intro t ht
  have h1 : ‖u + t • (θ : EuclideanSpace ℝ (Fin n))‖ < 1 :=
    mem_ball_zero_iff.1 (mem_chordSet_iff.1 ht)
  have h2 : ‖t • (θ : EuclideanSpace ℝ (Fin n))‖ = |t| := by
    rw [norm_smul, mem_sphere_zero_iff_norm.1 θ.2, mul_one, Real.norm_eq_abs]
  have h3 : |t| ≤ ‖u + t • (θ : EuclideanSpace ℝ (Fin n))‖ + ‖u‖ := by
    have hn := norm_sub_le (u + t • (θ : EuclideanSpace ℝ (Fin n))) u
    rwa [add_sub_cancel_left, h2] at hn
  have : |t| ≤ 2 := by linarith
  exact Set.mem_Icc.2 (abs_le.1 this)

omit [NeZero n] in
theorem Ioo_subset_chordSet_unitBall (u : EuclideanSpace ℝ (Fin n))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Set.Ioo (-(1 - ‖u‖)) (1 - ‖u‖)
      ⊆ chordSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) u
          (θ : EuclideanSpace ℝ (Fin n)) := by
  intro t ht
  have habs : |t| < 1 - ‖u‖ := abs_lt.2 ⟨ht.1, ht.2⟩
  have h2 : ‖t • (θ : EuclideanSpace ℝ (Fin n))‖ = |t| := by
    rw [norm_smul, mem_sphere_zero_iff_norm.1 θ.2, mul_one, Real.norm_eq_abs]
  refine mem_chordSet_iff.2 (mem_ball_zero_iff.2 ?_)
  calc ‖u + t • (θ : EuclideanSpace ℝ (Fin n))‖
      ≤ ‖u‖ + ‖t • (θ : EuclideanSpace ℝ (Fin n))‖ := norm_add_le _ _
    _ < 1 := by rw [h2]; linarith

omit [NeZero n] in
theorem volume_chordSet_unitBall_ne_zero {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 1)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (chordSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) u
      (θ : EuclideanSpace ℝ (Fin n))) ≠ 0 := by
  refine fun h => absurd (measure_mono_null (Ioo_subset_chordSet_unitBall u θ) h) ?_
  rw [Real.volume_Ioo]
  simp only [ENNReal.ofReal_eq_zero, not_le]
  linarith

omit [NeZero n] in
theorem volume_chordSet_unitBall_ne_top {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 1)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (chordSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) u
      (θ : EuclideanSpace ℝ (Fin n))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (chordSet_unitBall_subset hu θ))
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

theorem hitAndRunProposal_unitBall_univ {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 1) :
    hitAndRunProposal (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) u Set.univ = 1 :=
  hitAndRunProposal_univ_eq_one measurableSet_ball u
    (fun θ => volume_chordSet_unitBall_ne_zero hu θ)
    (fun θ => volume_chordSet_unitBall_ne_top hu θ)

/-- **The non-vacuity witness.** -/
theorem exists_hitAndRun_witness :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧
      IsProbabilityMeasure (Arlib.uniformOn (volume : Measure (EuclideanSpace ℝ (Fin n))) K) ∧
      IsMarkovKernel (hitAndRun K) ∧
      IsReversible (hitAndRun K)
        (Arlib.uniformOn (volume : Measure (EuclideanSpace ℝ (Fin n))) K) ∧
      Kernel.Invariant (hitAndRun K)
        (Arlib.uniformOn (volume : Measure (EuclideanSpace ℝ (Fin n))) K) ∧
      hitAndRun K 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ = 1 ∧
      (∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
        hitAndRun K 0 A = 2 / sphereArea n * ∫⁻ x in A ∩ K, hitAndRunDensity K 0 x) := by
  have hu : ‖(0 : EuclideanSpace ℝ (Fin n))‖ < 1 := by simp
  refine ⟨Metric.ball 0 1, measurableSet_ball, isProbabilityMeasure_uniformOn_unitBall,
    isMarkovKernel_hitAndRun _, isReversible_hitAndRun measurableSet_ball,
    invariant_hitAndRun measurableSet_ball,
    hitAndRun_apply_compl_singleton measurableSet_ball 0
      (hitAndRunProposal_unitBall_univ hu),
    fun A hA => hitAndRun_apply_eq_density measurableSet_ball 0
      (hitAndRunProposal_unitBall_univ hu) hA⟩

end Five

end Arlib.MarkovChains
