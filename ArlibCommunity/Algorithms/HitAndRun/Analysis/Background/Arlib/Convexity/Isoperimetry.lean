/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogConcave
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Geometric scaffolding for isoperimetry of log-concave measures

This file builds the vocabulary in which the isoperimetric inequality for log-concave
densities is stated, and proves the parts of the surrounding theory that Mathlib `v4.32`
supports today.

## Main definitions

* `Arlib.LogConcaveDensity E` — a measurable, nonnegative, log-concave function on `E`,
  bundled with those three facts. `LogConcaveDensity.measure` turns it into a measure by
  `withDensity` against a base measure (Lebesgue, in the intended reading).
* `Arlib.setDist S T` — `inf {dist u v | u ∈ S, v ∈ T}`, the separation between two sets.
* `Arlib.IsPartition3 K S₁ S₂ S₃` — `S₁ ∪ S₂ ∪ S₃ = K` with the three parts pairwise
  disjoint. This is the shape the isoperimetric statement quantifies over.
* `Arlib.densDist f u v` — `|f u − f v| / max (f u) (f v)`, the "`d_f`" of the
  convex-geometry literature.
* `Arlib.needleMap a v` — the line `t ↦ a + t • v`, along which the localisation argument
  restricts everything.

## Main results

* `Arlib.LogConcaveDensity.uniform`, `Arlib.LogConcaveDensity.gaussian` — the two running
  examples, built from `Arlib.isLogConcave_indicator_iff` and
  `Arlib.isLogConcave_gaussian`.
* `Arlib.setDist_smul` — `setDist (r • S) (r • T) = r * setDist S T` for `0 < r`.
* `Arlib.volume_smul_euclidean` — `volume (r • S) = ENNReal.ofReal (r ^ n) * volume S` on
  `EuclideanSpace ℝ (Fin n)`, for `0 ≤ r`.
* `Arlib.volume_smul_cross_eq` — the *ratio* `volume S / volume K` is unchanged by a
  dilation, in the division-free form `volume S * volume (r • K) = volume (r • S) *
  volume K`.
* `Arlib.IsPartition3.smul` — a three-way partition dilates to a three-way partition.
* `Arlib.IsLogConcave.comp_needleMap` — the restriction of a log-concave function to a
  line is a one-dimensional log-concave function. This is the "needle" of the localisation
  argument.
* `Arlib.setDist_le_norm_smul_setDist_preimage` — separation transfers from the ambient
  space to a needle.

## The target statement — PROSE, NOT LEAN

The theorem this file is scaffolding for is Cousins–Vempala Theorem 3.4 (`thm:iso`,
`vol3_journal.tex:467`):

> Let `π` be the Gaussian distribution `N(0, σ²Iₙ)` with density `γ` restricted by a
> log-concave `f : ℝⁿ → ℝ₊`, i.e. `π` has density proportional to `h(x) = f(x)γ(x)`. Let
> `S₁, S₂, S₃` partition `ℝⁿ` so that for every `u ∈ S₁` and `v ∈ S₂`, either
> `‖u − v‖ ≥ d / ln 2` or `d_h(u,v) ≥ 4d√n`. Then `π(S₃) ≥ (d/σ) · π(S₁) · π(S₂)`.

**It is not stated as a Lean `theorem` anywhere below, and no predicate in this file
asserts it.** Its proof runs through the Localization Lemma of Lovász–Simonovits, which
reduces the `n`-dimensional integral inequality to the one-dimensional "needle"
inequality, and through the one-dimensional isoperimetric inequality of
Kannan–Lovász–Simonovits. The Localization Lemma rests on Prékopa–Leindler in `ℝⁿ`, which
Mathlib `v4.32` does not have; the one-dimensional inequality does not exist in Mathlib
either. So the theorem is out of reach today.

What this file therefore contains is (i) the vocabulary, fully defined, and (ii) the
reductions around the target that *are* provable — the invariance of both sides of the
inequality under dilation (which is why its constant is dimensionless), the passage from
a log-concave density on `ℝⁿ` to a log-concave density on a needle, the induced
three-way partition of the needle, and the transfer of the separation hypothesis. What
remains is exactly the two cited inputs above.

Deliberately **absent**: any `def IsoInput …` / `def OneDimIso …` predicate whose name
asserts the conclusion. Such a predicate is inhabited only by degenerate witnesses and
proves nothing about the case with content; see `CV-ROADMAP.md` §2a.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3 (`../gaussian-cooling-vempala/vol3_journal.tex:404–508`).
-/

namespace Arlib

open MeasureTheory Set

/-! ### Log-concave densities and the measures they define -/

section Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]

/-- **A log-concave density on `E`**: a measurable, nonnegative, log-concave function.

The three fields are exactly what is needed to integrate it (`measurable`), to call the
result a measure (`nonneg`), and to run the convex-geometry arguments
(`logConcave`). Normalisation is *not* required: the measures of interest are stated as
ratios, so the total mass cancels. -/
structure LogConcaveDensity (E : Type*) [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] where
  /-- The underlying function. -/
  toFun : E → ℝ
  /-- The density is measurable. -/
  measurable : Measurable toFun
  /-- The density is nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The density is log-concave. -/
  logConcave : IsLogConcave toFun

/-- A `LogConcaveDensity` may be applied like the function it is. -/
instance : CoeFun (LogConcaveDensity E) (fun _ => E → ℝ) :=
  ⟨LogConcaveDensity.toFun⟩

/-- **The measure defined by a log-concave density** against a base measure `ν`
(Lebesgue, in the intended reading): `μ(S) = ∫⁻ x in S, f x ∂ν`. -/
noncomputable def LogConcaveDensity.measure (f : LogConcaveDensity E) (ν : Measure E) :
    Measure E :=
  ν.withDensity (fun x => ENNReal.ofReal (f x))

/-- The measure of a measurable set under a log-concave density is the integral of the
density over it. -/
theorem LogConcaveDensity.measure_apply (f : LogConcaveDensity E) (ν : Measure E)
    {S : Set E} (hS : MeasurableSet S) :
    f.measure ν S = ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν := by
  rw [LogConcaveDensity.measure, withDensity_apply _ hS]

/-- **The uniform measure on a convex body** is a log-concave measure: its density is the
indicator of the body, which is log-concave by `Arlib.isLogConcave_indicator_iff`. -/
noncomputable def LogConcaveDensity.uniform {K : Set E} (hK : MeasurableSet K)
    (hconv : Convex ℝ K) : LogConcaveDensity E where
  toFun := Set.indicator K (1 : E → ℝ)
  measurable := measurable_one.indicator hK
  nonneg x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
  logConcave := isLogConcave_indicator_iff.mpr hconv

/-- The density of `LogConcaveDensity.uniform` is the indicator of the body. -/
@[simp] theorem LogConcaveDensity.uniform_toFun {K : Set E} (hK : MeasurableSet K)
    (hconv : Convex ℝ K) :
    (LogConcaveDensity.uniform hK hconv).toFun = Set.indicator K (1 : E → ℝ) := rfl

end Density

section GaussianDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- **The Gaussian is a log-concave density**: `γ(x) = e^{−‖x‖²/(2σ²)}` is measurable,
positive and log-concave (`Arlib.isLogConcave_gaussian`). -/
noncomputable def LogConcaveDensity.gaussian (σ : ℝ) : LogConcaveDensity E where
  toFun := fun x => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))
  measurable := by
    refine Continuous.measurable ?_
    fun_prop
  nonneg _ := (Real.exp_pos _).le
  logConcave := isLogConcave_gaussian σ

/-- The density of `LogConcaveDensity.gaussian` is the Gaussian weight. -/
@[simp] theorem LogConcaveDensity.gaussian_toFun (σ : ℝ) :
    (LogConcaveDensity.gaussian (E := E) σ).toFun
      = fun x => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := rfl

end GaussianDensity

/-! ### The `f`-distance between points

`d_f(u,v) = |f(u) − f(v)| / max {f(u), f(v)}` (`vol3_journal.tex:399`). It measures how
much the density changes between two points, and appears in the second branch of the
separation hypothesis of the target theorem. -/

section DensDist

variable {E : Type*}

/-- **The `f`-distance between two points**, `d_f(u,v) = |f u − f v| / max (f u) (f v)`. -/
noncomputable def densDist (f : E → ℝ) (u v : E) : ℝ := |f u - f v| / max (f u) (f v)

/-- `d_f` is nonnegative for a nonnegative `f`. -/
theorem densDist_nonneg {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (u v : E) : 0 ≤ densDist f u v :=
  div_nonneg (abs_nonneg _) (le_max_of_le_left (hf u))

/-- `d_f(u,u) = 0`. -/
@[simp] theorem densDist_self (f : E → ℝ) (u : E) : densDist f u u = 0 := by
  simp [densDist]

/-- `d_f` is symmetric. -/
theorem densDist_comm (f : E → ℝ) (u v : E) : densDist f u v = densDist f v u := by
  rw [densDist, densDist, abs_sub_comm, max_comm]

/-- **`d_f ≤ 1` always**, for a nonnegative `f`.

This is a genuine constraint on the target theorem: its hypothesis offers the branch
`d_h(u,v) ≥ 4d√n`, which is *unsatisfiable* unless `4d√n ≤ 1`. That is why the ball-walk
analysis must cap `d` at `1/(16√n)`. -/
theorem densDist_le_one {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (u v : E) : densDist f u v ≤ 1 := by
  rcases lt_or_ge 0 (max (f u) (f v)) with hpos | hle
  · rw [densDist, div_le_one hpos]
    rcases le_total (f u) (f v) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right h]; linarith [hf u]
    · rw [abs_of_nonneg (by linarith), max_eq_left h]; linarith [hf v]
  · have h0 : max (f u) (f v) = 0 := le_antisymm hle (le_max_of_le_left (hf u))
    rw [densDist, h0, div_zero]
    norm_num

/-- **`d_f` does not see the normalisation constant**: `d_{c·f} = d_f` for `c > 0`. This
is what licenses stating the target theorem for the unnormalised density `h = f·γ` while
its conclusion is about the probability measure `π`. -/
theorem densDist_const_mul {f : E → ℝ} {c : ℝ} (hc : 0 < c) (u v : E) :
    densDist (fun x => c * f x) u v = densDist f u v := by
  rw [densDist, densDist, ← mul_sub, abs_mul, abs_of_pos hc, ← mul_max_of_nonneg _ _ hc.le,
    mul_div_mul_left _ _ hc.ne']

end DensDist

/-! ### The distance between two sets -/

section SetDist

variable {E : Type*} [PseudoMetricSpace E]

/-- **The distance between two sets**, `d(S,T) = inf {dist u v : u ∈ S, v ∈ T}`.

By the `Real.sInf` convention this is `0` when either set is empty. Every lemma below
that could be trivialised by that convention carries an explicit nonemptiness
hypothesis. -/
noncomputable def setDist (S T : Set E) : ℝ :=
  sInf ((fun p : E × E => dist p.1 p.2) '' (S ×ˢ T))

/-- The set of cross distances is bounded below by `0`. -/
theorem setDist_bddBelow (S T : Set E) :
    BddBelow ((fun p : E × E => dist p.1 p.2) '' (S ×ˢ T)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, -, rfl⟩
  exact dist_nonneg

/-- `d(S,T) ≥ 0`. -/
theorem setDist_nonneg (S T : Set E) : 0 ≤ setDist S T :=
  Real.sInf_nonneg (by rintro r ⟨p, -, rfl⟩; exact dist_nonneg)

/-- **`d` is symmetric**: `d(S,T) = d(T,S)`. -/
theorem setDist_comm (S T : Set E) : setDist S T = setDist T S := by
  refine congrArg sInf (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩; exact ⟨(v, u), ⟨hv, hu⟩, dist_comm v u⟩
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩; exact ⟨(v, u), ⟨hv, hu⟩, dist_comm v u⟩

/-- `d(∅,T) = 0` — the degenerate value the `Real.sInf` convention produces. -/
@[simp] theorem setDist_empty_left (T : Set E) : setDist (∅ : Set E) T = 0 := by
  simp [setDist]

/-- `d(S,∅) = 0` — the degenerate value the `Real.sInf` convention produces. -/
@[simp] theorem setDist_empty_right (S : Set E) : setDist S (∅ : Set E) = 0 := by
  simp [setDist]

/-- `d(S,T) ≤ dist u v` whenever `u ∈ S` and `v ∈ T`. -/
theorem setDist_le_dist {S T : Set E} {u v : E} (hu : u ∈ S) (hv : v ∈ T) :
    setDist S T ≤ dist u v :=
  csInf_le (setDist_bddBelow S T) ⟨(u, v), ⟨hu, hv⟩, rfl⟩

/-- If every cross pair is at distance at least `r`, then `d(S,T) ≥ r`.

Nonemptiness of both sets is essential: `d(∅,T) = 0`, so without it the statement would
be false for `r > 0`. -/
theorem le_setDist {S T : Set E} {r : ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (h : ∀ u ∈ S, ∀ v ∈ T, r ≤ dist u v) : r ≤ setDist S T := by
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hT
  refine le_csInf ⟨dist u v, ⟨(u, v), ⟨hu, hv⟩, rfl⟩⟩ ?_
  rintro q ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact h a ha b hb

/-- **Positive separation forces disjointness**: `0 < d(S,T)` implies `S ∩ T = ∅`.

The converse fails, which is the whole point of the isoperimetric hypothesis: two
disjoint sets can be at distance `0`. -/
theorem inter_eq_empty_of_setDist_pos {S T : Set E} (h : 0 < setDist S T) : S ∩ T = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have := setDist_le_dist hx.1 hx.2
  rw [dist_self] at this
  exact absurd this (not_le.mpr h)

/-- **Positive separation forces disjointness**, in `Disjoint` form. -/
theorem disjoint_of_setDist_pos {S T : Set E} (h : 0 < setDist S T) : Disjoint S T :=
  Set.disjoint_iff_inter_eq_empty.mpr (inter_eq_empty_of_setDist_pos h)

/-- Two sets that meet are at distance `0`. -/
theorem setDist_eq_zero_of_mem {S T : Set E} {x : E} (hS : x ∈ S) (hT : x ∈ T) :
    setDist S T = 0 :=
  le_antisymm (by simpa using setDist_le_dist hS hT) (setDist_nonneg S T)

end SetDist

/-! ### Three-way partitions -/

section Partition

variable {E : Type*}

/-- **A three-way partition of `K`**: `S₁ ∪ S₂ ∪ S₃ = K` with the three parts pairwise
disjoint.

This is the shape the isoperimetric inequality is quantified over: `S₁` and `S₂` are the
two separated parts and `S₃` is the "boundary" whose measure is bounded below.
Measurability is *not* bundled — it is carried as a separate hypothesis by the lemmas
that integrate over the parts, so that the definition stays purely set-theoretic. -/
structure IsPartition3 (K S₁ S₂ S₃ : Set E) : Prop where
  /-- The three parts cover `K` exactly. -/
  union : S₁ ∪ S₂ ∪ S₃ = K
  /-- `S₁` and `S₂` are disjoint. -/
  disjoint₁₂ : Disjoint S₁ S₂
  /-- `S₁` and `S₃` are disjoint. -/
  disjoint₁₃ : Disjoint S₁ S₃
  /-- `S₂` and `S₃` are disjoint. -/
  disjoint₂₃ : Disjoint S₂ S₃

variable {K S₁ S₂ S₃ : Set E}

/-- The first part of a partition is contained in the whole. -/
theorem IsPartition3.subset₁ (h : IsPartition3 K S₁ S₂ S₃) : S₁ ⊆ K := by
  rw [← h.union]; exact fun x hx => Or.inl (Or.inl hx)

/-- The second part of a partition is contained in the whole. -/
theorem IsPartition3.subset₂ (h : IsPartition3 K S₁ S₂ S₃) : S₂ ⊆ K := by
  rw [← h.union]; exact fun x hx => Or.inl (Or.inr hx)

/-- The third part of a partition is contained in the whole. -/
theorem IsPartition3.subset₃ (h : IsPartition3 K S₁ S₂ S₃) : S₃ ⊆ K := by
  rw [← h.union]; exact fun x hx => Or.inr hx

/-- Swapping the first two parts of a partition gives a partition. -/
theorem IsPartition3.symm (h : IsPartition3 K S₁ S₂ S₃) : IsPartition3 K S₂ S₁ S₃ where
  union := by rw [← h.union]; ac_rfl
  disjoint₁₂ := h.disjoint₁₂.symm
  disjoint₁₃ := h.disjoint₂₃
  disjoint₂₃ := h.disjoint₁₃

/-- **`IsPartition3` is inhabited with content**: `(K, ∅, ∅)` partitions `K`. -/
theorem isPartition3_self (K : Set E) : IsPartition3 K K ∅ ∅ where
  union := by simp
  disjoint₁₂ := by simp
  disjoint₁₃ := by simp
  disjoint₂₃ := by simp

/-- **A partition splits into two nonempty pieces and their complement** whenever `S ⊆ K`:
`(S, K \ S, ∅)` is a three-way partition of `K`. A non-degenerate witness. -/
theorem isPartition3_diff (h : S₁ ⊆ K) : IsPartition3 K S₁ (K \ S₁) ∅ where
  union := by simp [Set.union_sdiff_cancel h]
  disjoint₁₂ := Set.disjoint_sdiff_right
  disjoint₁₃ := by simp
  disjoint₂₃ := by simp

/-- **Partitions pull back along any map.** This is the step that turns a partition of
`ℝⁿ` into a partition of the parameter interval of a needle. -/
theorem IsPartition3.preimage {F : Type*} (h : IsPartition3 K S₁ S₂ S₃) (g : F → E) :
    IsPartition3 (g ⁻¹' K) (g ⁻¹' S₁) (g ⁻¹' S₂) (g ⁻¹' S₃) where
  union := by rw [← Set.preimage_union, ← Set.preimage_union, h.union]
  disjoint₁₂ := h.disjoint₁₂.preimage g
  disjoint₁₃ := h.disjoint₁₃.preimage g
  disjoint₂₃ := h.disjoint₂₃.preimage g

end Partition

/-! ### Scale invariance

The isoperimetric inequality `π(S₃) ≥ (d/D) · min(π S₁, π S₂)` has a *dimensionless*
constant, and this section is why: under the dilation `x ↦ r • x` the separation `d` and
the scale `D` both pick up a factor `r`, while `π` — a ratio of volumes — is unchanged.
Both sides of the inequality therefore scale identically, so proving it at one scale
proves it at every scale. This is the step the paper performs in one sentence
(`vol3_journal.tex:475`, "we prove the theorem for the case `σ = 1`, then note that by
applying the scaling `x = y/σ` we get the general case"). -/

section ScaleInvariance

open Pointwise

variable {E : Type*}

/-- Dilating by `r` and then by `r⁻¹` is the identity on sets. -/
theorem inv_smul_smul_set [AddCommGroup E] [Module ℝ E] {r : ℝ} (hr : r ≠ 0) (A : Set E) :
    r⁻¹ • (r • A) = A := by
  rw [← Set.image_smul, ← Set.image_smul, Set.image_image]
  simp [smul_smul, inv_mul_cancel₀ hr]

/-- Dilation by a nonzero scalar is injective. -/
theorem smul_injective [AddCommGroup E] [Module ℝ E] {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (fun x : E => r • x) := fun a b h => by
  have h' := congrArg (fun z : E => r⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hr] using h'

/-- **A three-way partition dilates to a three-way partition.** Together with
`Arlib.setDist_smul` and `Arlib.volume_smul_euclidean` this is the whole content of the
paper's "by applying the scaling `x = y/σ` we get the general case". -/
theorem IsPartition3.smul [AddCommGroup E] [Module ℝ E] {K S₁ S₂ S₃ : Set E} {r : ℝ}
    (h : IsPartition3 K S₁ S₂ S₃) (hr : r ≠ 0) :
    IsPartition3 (r • K) (r • S₁) (r • S₂) (r • S₃) where
  union := by
    rw [← Set.smul_set_union, ← Set.smul_set_union, h.union]
  disjoint₁₂ := by
    rw [← Set.image_smul, ← Set.image_smul]
    exact Set.disjoint_image_of_injective (smul_injective hr) h.disjoint₁₂
  disjoint₁₃ := by
    rw [← Set.image_smul, ← Set.image_smul]
    exact Set.disjoint_image_of_injective (smul_injective hr) h.disjoint₁₃
  disjoint₂₃ := by
    rw [← Set.image_smul, ← Set.image_smul]
    exact Set.disjoint_image_of_injective (smul_injective hr) h.disjoint₂₃

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One half of `Arlib.setDist_smul`: dilating by `r > 0` multiplies the separation by at
least `r`. -/
theorem mul_setDist_le_setDist_smul {r : ℝ} (hr : 0 < r) (S T : Set E) :
    r * setDist S T ≤ setDist (r • S) (r • T) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  refine le_setDist (hS.smul_set) (hT.smul_set) ?_
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left (setDist_le_dist hx hy) hr.le

/-- **Set distance is homogeneous of degree one**: `d(rS, rT) = r · d(S,T)` for `r > 0`.

This is the numerator of the isoperimetric ratio, and it scales like a length. -/
theorem setDist_smul {r : ℝ} (hr : 0 < r) (S T : Set E) :
    setDist (r • S) (r • T) = r * setDist S T := by
  refine le_antisymm ?_ (mul_setDist_le_setDist_smul hr S T)
  have h := mul_setDist_le_setDist_smul (r := r⁻¹) (inv_pos.mpr hr) (r • S) (r • T)
  rw [inv_smul_smul_set hr.ne' S, inv_smul_smul_set hr.ne' T] at h
  calc setDist (r • S) (r • T)
      = r * (r⁻¹ * setDist (r • S) (r • T)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    _ ≤ r * setDist S T := mul_le_mul_of_nonneg_left h hr.le

/-- **The separation-to-scale ratio is dilation-invariant.** If a configuration is
measured against a scale `D` (a standard deviation, a diameter, an inradius), then
dilating everything by `r > 0` — which sends `D` to `r · D` — leaves the ratio
`d(S,T)/D` unchanged. -/
theorem setDist_smul_div {r : ℝ} (hr : 0 < r) (S T : Set E) (D : ℝ) :
    setDist (r • S) (r • T) / (r * D) = setDist S T / D := by
  rw [setDist_smul hr, mul_div_mul_left _ _ hr.ne']

end ScaleInvariance

section VolumeScaling

open Pointwise

/-- **Lebesgue measure is homogeneous of degree `n`** on `ℝⁿ`:
`volume (r • S) = r^n · volume S` for `r ≥ 0`.

This is the denominator of the isoperimetric ratio. It is `Measure.addHaar_smul_of_nonneg`
specialised to `EuclideanSpace ℝ (Fin n)`, whose `ℝ`-dimension is `n`. -/
theorem volume_smul_euclidean {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    volume (r • S) = ENNReal.ofReal (r ^ n) * volume S := by
  rw [Measure.addHaar_smul_of_nonneg volume hr S, finrank_euclideanSpace_fin]

/-- **The volume ratio is dilation-invariant.**

Stated division-free, so that it holds unconditionally in `ℝ≥0∞`: `volume S / volume K`
and `volume (r•S) / volume (r•K)` have equal cross products. Combined with
`Arlib.setDist_smul_div`, this says that both sides of the isoperimetric inequality
`π(S₃) ≥ (d/D) · π(S₁) · π(S₂)` scale identically under `x ↦ r • x`, which is why its
constant carries no dimension and why proving the inequality at `σ = 1` suffices. -/
theorem volume_smul_cross_eq {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (S K : Set (EuclideanSpace ℝ (Fin n))) :
    volume S * volume (r • K) = volume (r • S) * volume K := by
  rw [volume_smul_euclidean hr S, volume_smul_euclidean hr K]
  ring

end VolumeScaling

/-! ### Reduction to a needle

The Localization Lemma of Lovász–Simonovits reduces the `n`-dimensional isoperimetric
inequality to a one-dimensional inequality along a *needle*: a segment carrying the
restriction of the density, reweighted by a power of a linear function. The lemma itself
is out of reach (see the module docstring), but the three ingredients that the reduction
*consumes* are elementary, and are proved here:

* the restriction of a log-concave function to a line is a one-dimensional log-concave
  function (`Arlib.IsLogConcave.comp_needleMap`);
* a three-way partition of the ambient space induces a three-way partition of the needle's
  parameter line (`Arlib.IsPartition3.comp_needleMap`);
* the separation of the two parts survives the restriction, up to the length of the
  direction vector (`Arlib.setDist_le_norm_smul_setDist_preimage`).

What remains after these is the Localization Lemma itself and the one-dimensional
isoperimetric inequality of Kannan–Lovász–Simonovits. Neither is stated below, in Lean or
as a predicate. -/

section Needle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The line through `a` in direction `v`**, parameterised by `ℝ`: `t ↦ a + t • v`.

The paper's needle is the restriction of the density to the image of this map, over a
parameter interval. -/
def needleMap (a v : E) : ℝ → E := fun t => a + t • v

/-- `needleMap a v t = a + t • v`, by definition. -/
theorem needleMap_apply (a v : E) (t : ℝ) : needleMap a v t = a + t • v := rfl

/-- The line map sends convex combinations of parameters to convex combinations of
points. -/
theorem needleMap_convex_comb (a v : E) {α β : ℝ} (hαβ : α + β = 1) (x y : ℝ) :
    needleMap a v (α * x + β * y) = α • needleMap a v x + β • needleMap a v y := by
  have hβ : β = 1 - α := by linarith
  subst hβ
  simp only [needleMap]
  module

/-- **The restriction of a log-concave function to a line is log-concave.**

This is the step that produces the one-dimensional density the localisation argument
works with: the "needle" `t ↦ h(a + t·v)` inherits log-concavity from `h`. -/
theorem IsLogConcave.comp_needleMap {f : E → ℝ} (hf : IsLogConcave f) (a v : E) :
    IsLogConcave (fun t : ℝ => f (needleMap a v t)) := by
  refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
  show f (needleMap a v x) ^ α * f (needleMap a v y) ^ β
    ≤ f (needleMap a v (α • x + β • y))
  rw [smul_eq_mul, smul_eq_mul, needleMap_convex_comb a v hαβ x y]
  exact hf.geom_le _ _ hα hβ hαβ

/-- **A three-way partition induces a three-way partition of every needle's parameter
line.** -/
theorem IsPartition3.comp_needleMap {K S₁ S₂ S₃ : Set E} (h : IsPartition3 K S₁ S₂ S₃)
    (a v : E) :
    IsPartition3 (needleMap a v ⁻¹' K) (needleMap a v ⁻¹' S₁) (needleMap a v ⁻¹' S₂)
      (needleMap a v ⁻¹' S₃) :=
  h.preimage (needleMap a v)

end Needle

section NeedleMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Distance along a line is `‖v‖` times the distance between the parameters. -/
theorem dist_needleMap (a v : E) (u w : ℝ) :
    dist (needleMap a v u) (needleMap a v w) = dist u w * ‖v‖ := by
  rw [dist_eq_norm, Real.dist_eq]
  have hsub : needleMap a v u - needleMap a v w = (u - w) • v := by
    simp only [needleMap]
    module
  rw [hsub, norm_smul, Real.norm_eq_abs]

/-- **Separation transfers to a needle.** If `S` and `T` both meet the line
`t ↦ a + t • v`, then their separation in `E` is at most `‖v‖` times the separation of
their parameter preimages.

Equivalently: the parameter sets are at least `d(S,T)/‖v‖` apart. This is the form the
localisation argument needs, since it must feed the ambient separation hypothesis to the
one-dimensional lemma. Both nonemptiness hypotheses are needed — without them the
right-hand side is `0` by the `Real.sInf` convention. -/
theorem setDist_le_norm_smul_setDist_preimage {a v : E} {S T : Set E}
    (hS : (needleMap a v ⁻¹' S).Nonempty) (hT : (needleMap a v ⁻¹' T).Nonempty) :
    setDist S T ≤ ‖v‖ * setDist (needleMap a v ⁻¹' S) (needleMap a v ⁻¹' T) := by
  rcases eq_or_ne v 0 with rfl | hv
  · obtain ⟨s, hs⟩ := hS
    obtain ⟨t, ht⟩ := hT
    simp only [Set.mem_preimage, needleMap, smul_zero, add_zero] at hs ht
    rw [setDist_eq_zero_of_mem hs ht, norm_zero, zero_mul]
  · have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    rw [← div_le_iff₀' hvpos]
    refine le_setDist hS hT ?_
    intro u hu w hw
    rw [div_le_iff₀ hvpos, ← dist_needleMap a v u w]
    exact setDist_le_dist hu hw

end NeedleMetric

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. The
scale-invariance lemmas of item 2 are listed first. -/

#print axioms setDist_smul
#print axioms setDist_smul_div
#print axioms volume_smul_euclidean
#print axioms volume_smul_cross_eq
#print axioms mul_setDist_le_setDist_smul
#print axioms IsPartition3.smul

#print axioms LogConcaveDensity.measure_apply
#print axioms LogConcaveDensity.uniform
#print axioms LogConcaveDensity.gaussian
#print axioms setDist_comm
#print axioms setDist_nonneg
#print axioms inter_eq_empty_of_setDist_pos
#print axioms disjoint_of_setDist_pos
#print axioms le_setDist
#print axioms setDist_le_dist
#print axioms densDist_le_one
#print axioms densDist_const_mul
#print axioms isPartition3_self
#print axioms isPartition3_diff
#print axioms IsPartition3.preimage
#print axioms IsLogConcave.comp_needleMap
#print axioms IsPartition3.comp_needleMap
#print axioms dist_needleMap
#print axioms setDist_le_norm_smul_setDist_preimage

end Arlib
