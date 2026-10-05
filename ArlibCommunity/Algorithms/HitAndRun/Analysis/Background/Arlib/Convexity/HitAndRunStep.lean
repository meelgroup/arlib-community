/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.StepLength
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRun
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.SphereCoord

/-!
# Lemma 3.2 of Lovász–Vempala: the median hit-and-run step is at least `s_α/32`

This file proves **Lemma 3.2** of

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SIAM J. Comput. 35
> (2006) 985–1005, `https://faculty.cc.gatech.edu/~vempala/papers/start.pdf`

which bounds the step-length function `F` of the hit-and-run walk from below by the concave
function `s_α` of `Arlib/Convexity/StepLength.lean`:

> **Lemma 3.2.** If `α ≥ 63/64`, then for all `x ∈ K`, `F(x) ≥ s_α(x)/32`.

## Main definitions

* `Arlib.medianStepSet K x` — `{c : P(|x − y| ≤ c) > 1/8}`, the radii already carrying more
  than `1/8` of the one-step law.
* `Arlib.medianStep K x` — **the paper's `F(x)`**, the infimum of that set.

## Main results

* `Arlib.toSphere_mul_le_volume_of_cone` — **the cone bound**, the geometric engine: a set
  `D` of directions and a radial window `(a,b]` sweep out a set of volume at least
  `|D|·(bⁿ − aⁿ)/n`, where `|D|` is `Measure.toSphere D`.
* `Arlib.toSphere_badDir_le`, `Arlib.toSphere_badDir_neg_le` — **the paper's `p ≤ 1/32`**,
  for the two antipodal senses of "bad direction".
* `Arlib.hitAndRunProposal_closedBall_le` — **the paper's `P(|y − x| ≤ s/32) ≤ 1/8`**.
* `Arlib.stepRadius_le_medianStep` — **Lemma 3.2**, as `s_α(x) ≤ 32·F(x)`;
  `Arlib.stepRadius_div_le_medianStep` restates it as `F(x) ≥ s_α(x)/32`.
* `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` — discharges the one inline
  hypothesis (see below) for a bounded body and an interior point.
* `Arlib.exists_stepRadius_le_medianStep_witness` — the non-vacuity witness.

## How `F` is defined, and against which kernel

`F` is defined against `Arlib.MarkovChains.hitAndRun`, *the* hit-and-run kernel of
`Arlib/MarkovChains/Continuous/HitAndRun.lean`; no second notion of step length is
introduced.  The paper's equation (4) reads `P(|x − y| ≤ F(x)) = 1/8` and presupposes that
the law of `|x − y|` attains the value `1/8`.  We take instead the lower `1/8`-quantile

`F(x) = inf {c : P(|x − y| ≤ c) > 1/8}`,

which always exists (`medianStepSet_nonempty`, from the fact that `hitAndRun K x` is a
probability measure), is bounded below by `0`, and satisfies both defining inequalities:
`hitAndRun_closedBall_le_of_lt_medianStep` and `le_hitAndRun_closedBall_of_medianStep_lt`.
Where the paper's equation has a solution the two agree.

## The one inline hypothesis: `hmove`

`stepRadius_le_medianStep` carries `hmove : hitAndRunProposal K x univ = 1` — the walk moves
away from `x` with probability one.  This is **not removable**: `hitAndRun` has a lazy atom
at `x` absorbing the mass of the directions along which the chord through `x` is null or
infinite, and that atom sits at distance `0`, so a walk staying put with probability more
than `1/8` has `F(x) = 0` and Lemma 3.2 fails.  The paper never mentions the issue because
it silently works with an interior point of a bounded body.  Following the convention of
`HitAndRun.lean`, the hypothesis is an inline `∀`-free equation, **not** a named `Prop`, and
`hitAndRunProposal_univ_eq_one_of_mem_interior` discharges it whenever `ball x ε ⊆ K ⊆ RB`.

## Two findings about the paper

### 1. The printed bound `p ≤ 1 − α + 2⁻ⁿ ≤ 1/32` is invalid for `n ≤ 5`

The paper's proof sets `p` = the fraction of the sphere `∂(x + (s/2)B)` outside `K` and
writes

> `vol((x + sB) \ K) ≥ p·vol(sB) − vol((s/2)B)`,  hence  `p ≤ 1 − α + 2⁻ⁿ ≤ 1/32`.

The final `≤ 1/32` at `α ≥ 63/64` needs `2⁻ⁿ ≤ 1/64`, i.e. **`n ≥ 6`**, which the paper
never states.  So the displayed chain is a genuine gap for `n ≤ 5`.

**But Lemma 3.2 itself is true for every `n ≥ 1`, and that is what is proved here.**  The
gap is an artefact of a needless weakening: the cone swept out by the bad directions between
radii `s/2` and `s` has volume exactly `p·(vol(sB) − vol((s/2)B))`, and the paper throws away
the factor by weakening `p·(V − V/2ⁿ)` to `p·V − V/2ⁿ`.  Keeping it and comparing with
`vol((x+sB) \ K) ≤ (1−α)·vol(sB)` gives

`p ≤ (1 − α)/(1 − 2⁻ⁿ) ≤ 2(1 − α) ≤ 1/32`  for all `n ≥ 1`,

which is `Arlib.toSphere_badDir_le`.  This is why the theorems below carry `n ≠ 0` and no
other dimension hypothesis: the corrected proof needs none, so neither `n ≥ 6` nor a worse
constant nor a stronger `α` threshold had to be adopted.

### 2. The direction of the §4 chain — resolved, no bug

An earlier reading of §4 suspected that

`s(x) ≥ (|x−p|/|u−p|)·s(u) ≥ 32(|q−p|/|u−p|)·F(u)`

used Lemma 3.2 backwards.  It does not: **every relation in that chain is `≤`, not `≥`.**
The source reads

`s(x) ≤ (|x−p|/|u−p|)·s(u) ≤ 32(|q−p|/|u−p|)·F(u) ≤ 16√n·|u−v|·(|q−p|/|u−p|)`
`   = 16·d_K(u,v)·√n·|q−v| ≤ 16·d_K(u,v)·D√n`,

feeding `h(x) = s(x)/(48D√n) ≤ d_K(u,v)/3`, which is an **upper** bound on `s(x)` — exactly
the direction `s(u) ≤ 32·F(u)` supplies.  The first step is concavity used the correct way:
`u` lies between `p` and `x` on the chord, so `s(u) ≥ (|u−p|/|x−p|)·s(x)`, which is
`Arlib.theta_mul_stepRadius_le` of `Arlib/Convexity/StepLength.lean` with `θ = |u−p|/|x−p|`.
The earlier suspicion came from a lossy text extraction that dropped the `cmsy` relation
glyphs; re-extracting with the TeX math encoding resolves it.  **There is no bug in §4.**

## What had to be built, and what Mathlib is missing

Contrary to expectation, **no spherical-cap API was needed**.  The paper's `p` is a fraction
of the *whole* sphere of directions, not of a cap, so the entire counting argument is the
polar-coordinate identity `Arlib.MarkovChains.lintegral_polar_at` plus the elementary radial
integral `Arlib.lintegral_pow_Ioc`.  That is `toSphere_mul_le_volume_of_cone`, and it is the
only geometry in this file.

The one piece of API the argument needs beyond that is the invariance of `Measure.toSphere`
under `θ ↦ −θ`.  The paper uses it implicitly, by reading `p` as a property of the sphere
`∂(x + (s/2)B)` (a symmetric object) and then union-bounding over the two endpoints of the
chord.  The cone bound only ever sweeps the outgoing half-ray, so it bounds
`{θ : x + (s/2)θ ∉ K}` and not `{θ : x − (s/2)θ ∉ K}`.

Mathlib v4.32 does not have that invariance, but **this repository now does**:
`Arlib.MarkovChains.toSphere_map_neg` (and its set form `toSphere_preimage_neg`) of
`Arlib/MarkovChains/Continuous/SphereCoord.lean` proves
`(volume.toSphere).map (Neg.neg) = volume.toSphere`, as the antipodal case of the rotation
invariance `toSphere_map_sphereMap`.  Earlier versions of this file recorded the invariance
as "the single missing API this development would have liked" and worked around it by
reflecting the *body* (`K* = {y : x + x − y ∈ K}`), a ~40-line detour; that detour is gone.
`toSphere_badDir_neg_le` is now three lines: rewrite the incoming bad set as the antipodal
preimage of the outgoing one (`setOf_sub_smul_notMem_eq_preimage_neg`), apply the
invariance, and quote `toSphere_badDir_le`.

## Constants

The paper's own bookkeeping at the last step is `P ≤ 1/16 + (15/16)·(1/16) = 31/256 < 1/8`.
We prove the non-strict `P ≤ 1/16 + 1/16 = 1/8`, which is all that the quantile definition of
`F` consumes (`le_medianStep` compares at radii strictly below `F`) and which avoids `ℝ≥0∞`
truncated subtraction.  The headline constant `32` is the paper's, unchanged.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace Arlib

open Arlib.MarkovChains

variable {n : ℕ}

/-! ### The radial integral -/

/-- `∫_a^b r^{n-1} dr = (bⁿ − aⁿ)/n`, as a lower Lebesgue integral. -/
theorem lintegral_pow_Ioc (hn : n ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ r in Set.Ioc a b, ENNReal.ofReal (r ^ (n - 1))
      = ENNReal.ofReal ((b ^ n - a ^ n) / n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_ne_zero hn).symm⟩
  simp only [Nat.add_sub_cancel]
  have hcont : Continuous fun r : ℝ => r ^ m := by continuity
  have hint : IntegrableOn (fun r : ℝ => r ^ m) (Set.Ioc a b) :=
    (hcont.integrableOn_Icc (a := a) (b := b)).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun r : ℝ => r ^ m := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact pow_nonneg (le_trans ha hr.1.le) m
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hab, integral_pow]
  push_cast
  ring

/-! ### The cone bound

The engine of Lemma 3.2: a set of directions `D` on the unit sphere, together with a radial
window `(a, b]`, sweeps out a cone of volume `|D| · (bⁿ − aⁿ)/n`, where `|D|` is the
*unnormalised* surface measure `Measure.toSphere`.  This is `lintegral_polar_at` of
`Arlib/MarkovChains/Continuous/HitAndRun.lean` and nothing else — no spherical caps are
needed, because the paper's `p` is a fraction of the whole sphere, not of a cap. -/

/-- **The cone bound.**  If every point `x + rθ` with `θ ∈ D` and `a < r ≤ b` lies in `S`,
then `S` has volume at least `toSphere(D) · (bⁿ − aⁿ)/n`. -/
theorem toSphere_mul_le_volume_of_cone [NeZero n]
    {D : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)} (hD : MeasurableSet D)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (x : EuclideanSpace ℝ (Fin n)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcone : ∀ θ ∈ D, ∀ r ∈ Set.Ioc a b, x + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ S) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere D
        * ENNReal.ofReal ((b ^ n - a ^ n) / n)
      ≤ volume S := by
  have hn : n ≠ 0 := NeZero.ne n
  have hind : Measurable (S.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have key : volume S = ∫⁻ θ, ∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (n - 1)) *
          S.indicator 1 (x + r • (θ : EuclideanSpace ℝ (Fin n))) ∂(volume : Measure ℝ)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
    rw [← lintegral_indicator_one hS, lintegral_polar_at x hind]
  rw [key, mul_comm]
  calc ENNReal.ofReal ((b ^ n - a ^ n) / n)
        * (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere D
      = ∫⁻ _θ in D, ENNReal.ofReal ((b ^ n - a ^ n) / n)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ θ in D, ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (n - 1)) *
              S.indicator 1 (x + r • (θ : EuclideanSpace ℝ (Fin n))) ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
        refine setLIntegral_mono' hD fun θ hθ => ?_
        calc ENNReal.ofReal ((b ^ n - a ^ n) / n)
            = ∫⁻ r in Set.Ioc a b, ENNReal.ofReal (r ^ (n - 1)) ∂(volume : Measure ℝ) :=
              (lintegral_pow_Ioc hn ha.le hab).symm
          _ ≤ ∫⁻ r in Set.Ioc a b, ENNReal.ofReal (r ^ (n - 1)) *
                S.indicator 1 (x + r • (θ : EuclideanSpace ℝ (Fin n))) ∂(volume : Measure ℝ) := by
              refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
              rw [Set.indicator_of_mem (hcone θ hθ r hr), Pi.one_apply, mul_one]
          _ ≤ _ := lintegral_mono_set fun r hr => lt_of_lt_of_le ha hr.1.le
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-! ### The fraction of bad directions -/

/-- The volume of the part of a ball around `x` that misses `K` is at most `(1−α)` times the
volume of the ball, whenever `t` is an admissible radius at `x`. -/
theorem volume_closedBall_diff_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmem : t ∈ stepRadiusSet K α x) :
    volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (1 - α) * volume (Metric.closedBall x t) := by
  set V : ℝ≥0∞ := volume (Metric.closedBall x t) with hV
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hsplit : volume (Metric.closedBall x t ∩ K) + volume (Metric.closedBall x t \ K) = V :=
    measure_inter_add_sdiff _ hKm
  have hinter : ENNReal.ofReal α * V ≤ volume (Metric.closedBall x t ∩ K) := by
    rw [Set.inter_comm]; exact hmem.2
  have hsum : ENNReal.ofReal (1 - α) * V + ENNReal.ofReal α * V = V := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hα0, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hkey : volume (Metric.closedBall x t \ K) + ENNReal.ofReal α * V
      ≤ ENNReal.ofReal (1 - α) * V + ENNReal.ofReal α * V := by
    rw [hsum]
    calc volume (Metric.closedBall x t \ K) + ENNReal.ofReal α * V
        ≤ volume (Metric.closedBall x t \ K) + volume (Metric.closedBall x t ∩ K) :=
          add_le_add le_rfl hinter
      _ = V := by rw [add_comm]; exact hsplit
  exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop)).1 hkey

/-- Along a ray from a point of `K`, missing `K` at radius `t/2` forces missing it at every
larger radius: this is the convexity input to the cone bound. -/
theorem notMem_of_notMem_half {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) {v : EuclideanSpace ℝ (Fin n)} {t r : ℝ}
    (ht : 0 < t) (hr : t / 2 < r) (hbad : x + (t / 2) • v ∉ K) : x + r • v ∉ K := by
  intro hmem
  refine hbad ?_
  set lam : ℝ := (t / 2) / r with hlam
  have hrpos : 0 < r := lt_trans (by positivity) hr
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hrpos]; linarith
  have hcomb := hKc hmem hx hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
  have heq : lam • (x + r • v) + (1 - lam) • x = x + (t / 2) • v := by
    have : lam * r = t / 2 := by rw [hlam]; field_simp
    rw [smul_add, smul_smul, this]
    module
  rwa [heq] at hcomb

/-- **The fraction of bad directions is at most `1/32`.**

`p` is the (normalised) surface measure of the set of directions `θ` for which the point
`x + (t/2)θ` — a point of the sphere of radius `t/2` about `x` — falls outside `K`.

This is the paper's `p ≤ 1 − α + 2⁻ⁿ ≤ 1/32`, with the intermediate bound **repaired**: see
the module docstring.  The cone swept out by the bad directions between radii `t/2` and `t`
has volume `p·(vol(tB) − vol((t/2)B))`, and it is disjoint from `K`; comparing with
`vol((x+tB) \ K) ≤ (1−α)vol(tB)` gives `p ≤ (1−α)/(1 − 2⁻ⁿ) ≤ 2(1−α) ≤ 1/32`.  The paper
instead weakens the cone volume to `p·vol(tB) − vol((t/2)B)`, which yields the *false for
`n ≤ 5`* bound `p ≤ 1 − α + 2⁻ⁿ`. -/
theorem toSphere_badDir_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {α t : ℝ} (ht : 0 < t) (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    (hmem : t ∈ stepRadiusSet K α x) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
        {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K}
      ≤ ENNReal.ofReal (1 / 32) * sphereArea n := by
  have hn : n ≠ 0 := NeZero.ne n
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  set Bad : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {θ | x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K} with hBad
  have hBadm : MeasurableSet Bad := by
    have : Continuous fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) := by fun_prop
    exact hKm.compl.preimage this.measurable
  set Vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hVb
  set P : ℝ≥0∞ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Bad with hP
  -- the cone bound
  have hcone : P * ENNReal.ofReal ((t ^ n - (t / 2) ^ n) / n)
      ≤ volume (Metric.closedBall x t \ K) := by
    refine toSphere_mul_le_volume_of_cone hBadm (measurableSet_closedBall.diff hKm) x
      (by positivity) (by linarith) ?_
    rintro θ hθ r ⟨hr1, hr2⟩
    have hθ1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
    have hrpos : 0 < r := lt_trans (by positivity) hr1
    refine ⟨?_, notMem_of_notMem_half hKc hx ht hr1 hθ⟩
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hθ1, mul_one,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact hr2
  -- the α bound
  have halpha := volume_closedBall_diff_le hKm (by linarith : (0:ℝ) ≤ α) hα1 hmem
  have hballV : volume (Metric.closedBall x t) = ENNReal.ofReal t ^ n * Vb :=
    volume_closedBall_euclidean ht.le x
  -- the radial slack
  have hslack : ENNReal.ofReal (t ^ n / (2 * n)) ≤ ENNReal.ofReal ((t ^ n - (t / 2) ^ n) / n) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (t / 2) ^ n ≤ t ^ n / 2 := by
      rw [div_pow, div_le_div_iff_of_pos_left (by positivity) (by positivity) (by norm_num)]
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.2 hn)
    have hA : t ^ n / (2 * (n : ℝ)) = (t ^ n / 2) / (n : ℝ) := by ring
    rw [hA]
    gcongr
    linarith
  -- put it together
  set d : ℝ≥0∞ := ENNReal.ofReal (t ^ n / (2 * n)) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain : P * d ≤ ENNReal.ofReal (1 / 64) * (ENNReal.ofReal t ^ n * Vb) := by
    calc P * d ≤ P * ENNReal.ofReal ((t ^ n - (t / 2) ^ n) / n) := mul_le_mul' le_rfl hslack
      _ ≤ volume (Metric.closedBall x t \ K) := hcone
      _ ≤ ENNReal.ofReal (1 - α) * volume (Metric.closedBall x t) := halpha
      _ ≤ ENNReal.ofReal (1 / 64) * (ENNReal.ofReal t ^ n * Vb) := by
          rw [hballV]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  refine (ENNReal.mul_le_mul_iff_left hd0 hdtop).1 (hmain.trans (le_of_eq ?_))
  have hnum : (1 / 32 : ℝ) * n * (t ^ n / (2 * n)) = 1 / 64 * t ^ n := by
    field_simp; ring
  calc ENNReal.ofReal (1 / 64) * (ENNReal.ofReal t ^ n * Vb)
      = ENNReal.ofReal ((1 / 64 : ℝ) * t ^ n) * Vb := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (1:ℝ) / 64), ENNReal.ofReal_pow ht.le]
        ring
    _ = ENNReal.ofReal ((1 / 32 : ℝ) * n * (t ^ n / (2 * n))) * Vb := by rw [hnum]
    _ = ENNReal.ofReal (1 / 32) * sphereArea n * d := by
        rw [sphereArea_eq, hd, ← ENNReal.ofReal_natCast n,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / 32 * (n : ℝ)),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (1:ℝ) / 32)]
        ring

/-- **The same bound for the antipodal direction.**

The cone argument only ever sweeps the *outgoing* half-ray `{x + rθ : r > 0}`, so it bounds
the measure of `{θ : x + (t/2)θ ∉ K}` and not that of `{θ : x − (t/2)θ ∉ K}`.  The paper
gets the second bound for free by reading `p` as "the fraction of the sphere `∂(x+(s/2)B)`
outside `K`", which is a symmetric notion; formally that needs the invariance of
`Measure.toSphere` under `θ ↦ −θ`.

That invariance is `Arlib.MarkovChains.toSphere_map_neg` of
`Arlib/MarkovChains/Continuous/SphereCoord.lean` (set form: `toSphere_preimage_neg`), so the
proof is now the paper's own: the incoming bad directions are the antipodes of the outgoing
ones (`setOf_sub_smul_notMem_eq_preimage_neg`), and the antipodal map preserves the measure.
Earlier versions of this file avoided the invariance by reflecting the *body*
(`K* = {y : x + x − y ∈ K}`), which is no longer necessary. -/
theorem toSphere_badDir_neg_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {α t : ℝ} (ht : 0 < t) (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    (hmem : t ∈ stepRadiusSet K α x) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
        {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K}
      ≤ ENNReal.ofReal (1 / 32) * sphereArea n := by
  have hBadm : MeasurableSet {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K} := by
    have hc : Continuous fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) := by fun_prop
    exact hKm.compl.preimage hc.measurable
  rw [setOf_sub_smul_notMem_eq_preimage_neg, toSphere_preimage_neg hBadm]
  exact toSphere_badDir_le hKc hKm hx ht hα hα1 hmem

/-! ### The chord through a good direction -/

/-- If both antipodal points `x ± (t/2)θ` lie in `K`, then the chord of `K` through `x` in
direction `θ` has length at least `t`. -/
theorem ofReal_le_volume_chordSet {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    {x : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : 0 < t)
    {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hp : x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∈ K)
    (hm : x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∈ K) :
    ENNReal.ofReal t ≤ volume (chordSet K x (θ : EuclideanSpace ℝ (Fin n))) := by
  have hsub : Set.Icc (-(t / 2)) (t / 2)
      ⊆ chordSet K x (θ : EuclideanSpace ℝ (Fin n)) := by
    rintro r ⟨hr1, hr2⟩
    set lam : ℝ := (r + t / 2) / t with hlam
    have hlam0 : 0 ≤ lam := by rw [hlam]; apply div_nonneg _ ht.le; linarith
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one ht]; linarith
    have hcomb := hKc hp hm hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
    have heq : lam • (x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)))
          + (1 - lam) • (x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)))
        = x + (lam * (t / 2) - (1 - lam) * (t / 2)) • (θ : EuclideanSpace ℝ (Fin n)) := by
      module
    have hc : lam * (t / 2) - (1 - lam) * (t / 2) = r := by
      rw [hlam]; field_simp; ring
    rw [heq, hc] at hcomb
    exact hcomb
  calc ENNReal.ofReal t = volume (Set.Icc (-(t / 2)) (t / 2)) := by
        rw [Real.volume_Icc]; congr 1; ring
    _ ≤ _ := measure_mono hsub

/-! ### The one-step law of the walk near `x` -/

/-- Normalising a `toSphere` bound to a `unifSphere` (probability) bound. -/
theorem unifSphere_le_of_toSphere_le [NeZero n]
    {D : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)} {c : ℝ≥0∞}
    (h : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere D ≤ c * sphereArea n) :
    unifSphere n D ≤ c := by
  rw [unifSphere, Measure.smul_apply, smul_eq_mul]
  calc (sphereArea n)⁻¹ * (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere D
      ≤ (sphereArea n)⁻¹ * (c * sphereArea n) := mul_le_mul' le_rfl h
    _ = c := by
        rw [mul_comm c, ← mul_assoc,
          ENNReal.inv_mul_cancel sphereArea_ne_zero (sphereArea_ne_top n), one_mul]

/-- **The paper's `P(|y − x| ≤ s/32) ≤ 1/8`,** for the hit-and-run *proposal* from `x`.

The three ingredients are: at most a `1/32` fraction of directions is bad in each of the two
senses (`toSphere_badDir_le`, `toSphere_badDir_neg_le`), so at most `1/16` of directions
fails the two-sided test; along a direction that passes, the chord of `K` through `x` has
length at least `t`, while the target window `[-t/32, t/32]` has length `t/16`, so the
conditional probability is at most `1/16`.

The paper's own bookkeeping is sharper (`≤ 1/16 + (15/16)(1/16) = 31/256 < 1/8`); the
non-strict `≤ 1/8` proved here is all that `medianStep` consumes, and avoids `ℝ≥0∞`
subtraction. -/
theorem hitAndRunProposal_closedBall_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {α t : ℝ} (ht : 0 < t) (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    (hmem : t ∈ stepRadiusSet K α x) :
    hitAndRunProposal K x (Metric.closedBall x (t / 32)) ≤ 1 / 8 := by
  classical
  set Bp : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {θ | x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K} with hBp
  set Bm : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {θ | x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∉ K} with hBm
  have hBpm : MeasurableSet Bp := by
    have hc : Continuous fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) := by fun_prop
    exact hKm.compl.preimage hc.measurable
  have hBmm : MeasurableSet Bm := by
    have hc : Continuous fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) := by fun_prop
    exact hKm.compl.preimage hc.measurable
  set Bad : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := Bp ∪ Bm with hBad
  have hBadm : MeasurableSet Bad := hBpm.union hBmm
  have hq : unifSphere n Bad ≤ ENNReal.ofReal (1 / 16) := by
    refine (measure_union_le _ _).trans ?_
    have hp1 : unifSphere n Bp ≤ ENNReal.ofReal (1 / 32) :=
      unifSphere_le_of_toSphere_le (toSphere_badDir_le hKc hKm hx ht hα hα1 hmem)
    have hp2 : unifSphere n Bm ≤ ENNReal.ofReal (1 / 32) :=
      unifSphere_le_of_toSphere_le (toSphere_badDir_neg_le hKc hKm hx ht hα hα1 hmem)
    calc unifSphere n Bp + unifSphere n Bm
        ≤ ENNReal.ofReal (1 / 32) + ENNReal.ofReal (1 / 32) := add_le_add hp1 hp2
      _ = ENNReal.ofReal (1 / 16) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hset : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      {r : ℝ | x + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall x (t / 32)}
        = Set.Icc (-(t / 32)) (t / 32) := by
    intro θ
    have hθ1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
    ext r
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_smul, hθ1, mul_one, Real.norm_eq_abs, Set.mem_Icc]
    exact abs_le
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      Arlib.uniformOn (volume : Measure ℝ) (chordSet K x (θ : EuclideanSpace ℝ (Fin n)))
          {r : ℝ | x + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall x (t / 32)}
        ≤ Bad.indicator (1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ≥0∞) θ
            + ENNReal.ofReal (1 / 16) := by
    intro θ
    have hTm : MeasurableSet
        {r : ℝ | x + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall x (t / 32)} := by
      rw [hset θ]; exact measurableSet_Icc
    rw [Arlib.uniformOn_apply _ (measurableSet_chordSet hKm x _) hTm, hset θ]
    by_cases hθ : θ ∈ Bad
    · rw [Set.indicator_of_mem hθ, Pi.one_apply]
      refine le_trans (ENNReal.div_le_of_le_mul ?_) le_self_add
      rw [one_mul]
      exact measure_mono Set.inter_subset_right
    · rw [Set.indicator_of_notMem hθ, zero_add]
      have hp : x + (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∈ K :=
        not_not.1 (fun h => hθ (Or.inl h))
      have hm : x - (t / 2) • (θ : EuclideanSpace ℝ (Fin n)) ∈ K :=
        not_not.1 (fun h => hθ (Or.inr h))
      refine ENNReal.div_le_of_le_mul ?_
      calc volume (Set.Icc (-(t / 32)) (t / 32)
              ∩ chordSet K x (θ : EuclideanSpace ℝ (Fin n)))
          ≤ volume (Set.Icc (-(t / 32)) (t / 32)) := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (1 / 16) * ENNReal.ofReal t := by
            rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (1 / 16) * volume (chordSet K x (θ : EuclideanSpace ℝ (Fin n))) :=
            mul_le_mul' le_rfl (ofReal_le_volume_chordSet hKc ht hp hm)
  rw [hitAndRunProposal_apply_uniformOn hKm x measurableSet_closedBall]
  calc ∫⁻ θ, Arlib.uniformOn (volume : Measure ℝ)
          (chordSet K x (θ : EuclideanSpace ℝ (Fin n)))
          {r : ℝ | x + r • (θ : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall x (t / 32)}
        ∂(unifSphere n)
      ≤ ∫⁻ θ, (Bad.indicator (1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ≥0∞) θ
          + ENNReal.ofReal (1 / 16)) ∂(unifSphere n) := lintegral_mono hpt
    _ = unifSphere n Bad + ENNReal.ofReal (1 / 16) := by
        rw [lintegral_add_left (measurable_one.indicator hBadm),
          lintegral_indicator_one hBadm, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 / 16) + ENNReal.ofReal (1 / 16) := add_le_add hq le_rfl
    _ = 1 / 8 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
          show (1 / 16 + 1 / 16 : ℝ) = 1 / 8 by norm_num,
          ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-! ### `F(x)`, the median step length -/

/-- The set of radii that already capture more than `1/8` of the one-step law. -/
def medianStepSet (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {c : ℝ | 1 / 8 < hitAndRun K x (Metric.closedBall x c)}

/-- **`F(x)`, the "median" hit-and-run step length** — equation (4) of Lovász–Vempala,
`P(|x − y| ≤ F(x)) = 1/8`.

The paper writes `F(x)` as the solution of an equation, which presupposes that the law of
`|x − y|` hits the value `1/8` exactly.  We take instead the lower `1/8`-quantile
`inf {c : P(|x − y| ≤ c) > 1/8}`, which always exists and agrees with the paper's `F`
whenever the paper's equation has a solution.  The two defining inequalities are proved:
`hitAndRun_closedBall_le_of_lt_medianStep` (below `F` the mass is at most `1/8`) and
`le_hitAndRun_closedBall_of_medianStep_lt` (above `F` it is at least `1/8`).  Nothing about
this definition asserts anything unproved. -/
noncomputable def medianStep (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf (medianStepSet K x)

theorem nonneg_of_mem_medianStepSet {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hc : c ∈ medianStepSet K x) : 0 ≤ c := by
  rcases le_or_gt 0 c with h | h
  · exact h
  · rw [medianStepSet, Set.mem_setOf_eq, Metric.closedBall_eq_empty.2 h, measure_empty] at hc
    simp at hc

theorem bddBelow_medianStepSet (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : BddBelow (medianStepSet K x) :=
  ⟨0, fun _ hc => nonneg_of_mem_medianStepSet hc⟩

/-- The one-step law is a probability measure, so some ball around `x` does carry more than
`1/8` of it: `medianStepSet` is never empty and `medianStep` is not a junk value. -/
theorem medianStepSet_nonempty (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : (medianStepSet K x).Nonempty := by
  have hmono : Monotone fun m : ℕ => Metric.closedBall x (m : ℝ) := by
    intro a b hab
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
  have hunion : (⋃ m : ℕ, Metric.closedBall x (m : ℝ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge (dist y x)
    exact Set.mem_iUnion.2 ⟨m, hm⟩
  have htend := tendsto_measure_iUnion_atTop (μ := hitAndRun K x) hmono
  rw [hunion, measure_univ] at htend
  have h8 : (1 : ℝ≥0∞) / 8 < 1 := by
    rw [one_div, ENNReal.inv_lt_one]
    norm_num
  obtain ⟨m, hm⟩ := (htend.eventually_const_lt h8).exists
  exact ⟨(m : ℝ), hm⟩

theorem medianStep_nonneg (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ medianStep K x :=
  le_csInf (medianStepSet_nonempty K x) fun _ hc => nonneg_of_mem_medianStepSet hc

/-- **The lower bound on `F`.**  A radius whose ball carries at most `1/8` of the one-step law
is at most `F(x)`.  This is the shape Lemma 3.2 consumes. -/
theorem le_medianStep {K : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (h : hitAndRun K x (Metric.closedBall x r) ≤ 1 / 8) : r ≤ medianStep K x := by
  refine le_csInf (medianStepSet_nonempty K x) fun c hc => ?_
  rcases le_or_gt r c with hrc | hrc
  · exact hrc
  · exact absurd (lt_of_lt_of_le hc
      ((measure_mono (Metric.closedBall_subset_closedBall hrc.le)).trans h)) (lt_irrefl _)

/-- Below `F(x)` the one-step law puts mass at most `1/8` — half of the paper's equation (4). -/
theorem hitAndRun_closedBall_le_of_lt_medianStep {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (h : c < medianStep K x) :
    hitAndRun K x (Metric.closedBall x c) ≤ 1 / 8 := by
  rcases le_or_gt (hitAndRun K x (Metric.closedBall x c)) (1 / 8) with hle | hlt
  · exact hle
  · exact absurd (csInf_le (bddBelow_medianStepSet K x) (show c ∈ medianStepSet K x from hlt))
      (not_le.2 h)

/-- Above `F(x)` the one-step law puts mass at least `1/8` — the other half of equation (4). -/
theorem le_hitAndRun_closedBall_of_medianStep_lt {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (h : medianStep K x < c) :
    1 / 8 ≤ hitAndRun K x (Metric.closedBall x c) := by
  obtain ⟨c', hc', hlt⟩ := exists_lt_of_csInf_lt (medianStepSet_nonempty K x) h
  exact le_trans hc'.le (measure_mono (Metric.closedBall_subset_closedBall hlt.le))

/-! ### Lemma 3.2 -/

/-- **Lemma 3.2 of Lovász–Vempala.**  For `α ≥ 63/64` and any `x` in a convex body `K`,
the median hit-and-run step length satisfies `F(x) ≥ s_α(x)/32`.

Stated as `s_α(x) ≤ 32·F(x)` — which is also the direction §4 of the paper uses it in.

`hmove` is the hypothesis that the walk actually moves from `x`: the hit-and-run *proposal*
carries full mass, i.e. every chord of `K` through `x` has positive finite length.  Without
it the statement is false — the lazy atom of `Arlib.MarkovChains.hitAndRun` sits at `x`
itself, so a walk that stays put with probability more than `1/8` has `F(x) = 0`.  This is
the same hypothesis `Arlib/MarkovChains/Continuous/HitAndRun.lean` attaches to every
statement about a walk that moves; `hitAndRunProposal_univ_eq_one_of_mem_interior` below
discharges it for a bounded `K` and an interior `x`.

Note that **no lower bound on `n` appears**, even though the paper's displayed chain
`p ≤ 1 − α + 2⁻ⁿ ≤ 1/32` needs `n ≥ 6`; see the module docstring. -/
theorem stepRadius_le_medianStep (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {α : ℝ} (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    (hmove : hitAndRunProposal K x Set.univ = 1) :
    stepRadius K α x ≤ 32 * medianStep K x := by
  haveI : NeZero n := ⟨hn⟩
  refine csSup_le (stepRadiusSet_nonempty hn K α x) fun t htmem => ?_
  rcases eq_or_lt_of_le htmem.1 with h0 | ht
  · have := medianStep_nonneg K x
    linarith [h0]
  · have hkey : hitAndRun K x (Metric.closedBall x (t / 32)) ≤ 1 / 8 := by
      rw [hitAndRun_apply_set hKm x measurableSet_closedBall, hmove, tsub_self, zero_mul,
        add_zero]
      exact hitAndRunProposal_closedBall_le hKc hKm hx ht hα hα1 htmem
    have := le_medianStep hkey
    linarith

/-- **Lemma 3.2, in the paper's own shape**: `F(x) ≥ s_α(x)/32`. -/
theorem stepRadius_div_le_medianStep (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {α : ℝ} (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    (hmove : hitAndRunProposal K x Set.univ = 1) :
    stepRadius K α x / 32 ≤ medianStep K x := by
  have := stepRadius_le_medianStep hn hKc hKm hx hα hα1 hmove
  linarith

/-! ### Discharging `hmove`, and a non-vacuity witness -/

/-- **The walk moves with probability one from an interior point of a bounded body.**

This discharges the `hmove` hypothesis of Lemma 3.2: a ball of radius `ε` about `x` inside
`K` makes every chord through `x` at least `2ε` long, and `K ⊆ RB` makes every chord
finite. -/
theorem hitAndRunProposal_univ_eq_one_of_mem_interior [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) {x : EuclideanSpace ℝ (Fin n)} {ε R : ℝ} (hε : 0 < ε)
    (hball : Metric.ball x ε ⊆ K)
    (hbdd : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :
    hitAndRunProposal K x Set.univ = 1 := by
  refine hitAndRunProposal_univ_eq_one hKm x (fun θ => ?_) (fun θ => ?_)
  · have hθ1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
    have hsub : Set.Ioo (-ε) ε ⊆ chordSet K x (θ : EuclideanSpace ℝ (Fin n)) := by
      intro r hr
      refine mem_chordSet_iff.2 (hball ?_)
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hθ1, mul_one,
        Real.norm_eq_abs]
      exact abs_lt.2 ⟨hr.1, hr.2⟩
    intro h
    have hz := measure_mono_null hsub h
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
    linarith
  · have hθ1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
    have hsub : chordSet K x (θ : EuclideanSpace ℝ (Fin n))
        ⊆ Set.Icc (-(R + ‖x‖)) (R + ‖x‖) := by
      intro r hr
      have h1 : ‖x + r • (θ : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
        have hm := hbdd (mem_chordSet_iff.1 hr)
        rwa [Metric.mem_closedBall, dist_zero_right] at hm
      have h2 : ‖r • (θ : EuclideanSpace ℝ (Fin n))‖ = |r| := by
        rw [norm_smul, hθ1, mul_one, Real.norm_eq_abs]
      have h3 : ‖r • (θ : EuclideanSpace ℝ (Fin n))‖
          ≤ ‖x + r • (θ : EuclideanSpace ℝ (Fin n))‖ + ‖x‖ := by
        have hn' := norm_sub_le (x + r • (θ : EuclideanSpace ℝ (Fin n))) x
        rwa [add_sub_cancel_left] at hn'
      refine Set.mem_Icc.2 (abs_le.1 ?_)
      rw [← h2]; linarith
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- **The non-vacuity witness** (`CLAUDE.md` §11).  On the unit ball, seen from its centre,
every hypothesis of Lemma 3.2 holds, the walk leaves its current point with probability one,
and the step radius is *strictly positive* — so the conclusion `s_α(x) ≤ 32·F(x)` is a
genuine lower bound on `F` and not the vacuous `0 ≤ 32·F`. -/
theorem exists_stepRadius_le_medianStep_witness (hn : n ≠ 0) {α : ℝ}
    (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      Convex ℝ K ∧ MeasurableSet K ∧ x ∈ K ∧
        hitAndRunProposal K x Set.univ = 1 ∧
        0 < stepRadius K α x ∧
        stepRadius K α x ≤ 32 * medianStep K x ∧ 0 < medianStep K x := by
  haveI : NeZero n := ⟨hn⟩
  have hα0 : (0 : ℝ) < α := by linarith
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1 with hK
  have hKm : MeasurableSet K := measurableSet_ball
  have hKc : Convex ℝ K := convex_ball _ _
  have hx : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := by simp [hK]
  have hKfin : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hmove : hitAndRunProposal K (0 : EuclideanSpace ℝ (Fin n)) Set.univ = 1 :=
    hitAndRunProposal_unitBall_univ (by simp)
  have hmem : (1 / 2 : ℝ) ∈ stepRadiusSet K α 0 := by
    refine ⟨by norm_num, ?_⟩
    have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ K :=
      Metric.closedBall_subset_ball (by norm_num)
    rw [Set.inter_eq_right.2 hsub]
    calc ENNReal.ofReal α * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
        ≤ 1 * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hα1
      _ = _ := one_mul _
  have hpos : 0 < stepRadius K α 0 :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1 / 2)
      (le_csSup (bddAbove_stepRadiusSet hn hKfin hα0 0) hmem)
  have hmain := stepRadius_le_medianStep hn hKc hKm hx hα hα1 hmove
  exact ⟨K, 0, hKc, hKm, hx, hmove, hpos, hmain, by linarith⟩

/-! ### Axiom profile -/

section AxiomCheck

#print axioms lintegral_pow_Ioc
#print axioms toSphere_mul_le_volume_of_cone
#print axioms volume_closedBall_diff_le
#print axioms notMem_of_notMem_half
#print axioms toSphere_badDir_le
#print axioms toSphere_badDir_neg_le
#print axioms ofReal_le_volume_chordSet
#print axioms unifSphere_le_of_toSphere_le
#print axioms hitAndRunProposal_closedBall_le
#print axioms nonneg_of_mem_medianStepSet
#print axioms bddBelow_medianStepSet
#print axioms medianStepSet_nonempty
#print axioms medianStep_nonneg
#print axioms le_medianStep
#print axioms hitAndRun_closedBall_le_of_lt_medianStep
#print axioms le_hitAndRun_closedBall_of_medianStep_lt
#print axioms stepRadius_le_medianStep
#print axioms stepRadius_div_le_medianStep
#print axioms hitAndRunProposal_univ_eq_one_of_mem_interior
#print axioms exists_stepRadius_le_medianStep_witness

end AxiomCheck

end Arlib
