/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.BrunnSharp
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.KLS97Sharp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure

/-!
# The step-length function `s_α` of Lovász–Vempala

This file formalises §3 ("Bounding the step-size") of

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SICOMP 2006.

For a convex body `K ⊆ ℝⁿ`, a point `x` and a radius `t > 0` the paper writes

`σ(x,t) = vol(K ∩ (x + tB)) / vol(tB)`

for the fraction of the ball of radius `t` around `x` that lies in `K`, and, for a fixed
threshold `α`,

`s_α(x) = sup {t : σ(x,t) ≥ α}`.

`s_α(x)` measures how far `x` is from the boundary of `K`, in a way that is robust enough
to be *concave* — which is the paper's Lemma 3.1 and the main content of this file.

## Main definitions

* `Arlib.ballFraction K x t` — the ratio `σ(x,t)`, as a real number.
* `Arlib.stepRadiusSet K α x` — the set `{t ≥ 0 : α · vol(closedBall x t) ≤ vol(K ∩ closedBall x t)}`
  of admissible radii, phrased as an inequality between `ℝ≥0∞`-valued volumes so that no
  finiteness or positivity side condition is needed and `t = 0` is always admissible.
* `Arlib.stepRadius K α x` — `s_α(x)`, the supremum of that set.
* `Arlib.goodSet K α t` — `{x ∈ K : σ(x,t) ≥ α}`, the super-level set of `σ(·,t)`.

## Main results

* `Arlib.brunn_minkowski_sharp_euclidean` — the sharp Brunn–Minkowski inequality of
  `Arlib.brunn_minkowski_sharp`, transported from `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)`.
  This transport is *mandatory*: `Fin n → ℝ` carries the sup norm, so `Metric.closedBall` there
  is a cube, and every ball in this file is genuinely Euclidean.
* `Arlib.mem_stepRadiusSet_combo` — the geometric engine: admissible radii combine convexly.
* `Arlib.stepRadius_concaveOn` — **Lemma 3.1**: `s_α` is concave on `K`.
* `Arlib.aemeasurable_stepRadius` — `s_α` is a.e.-measurable on `K` (a corollary of Lemma 3.1:
  concave ⟹ continuous on `interior K`, and `vol(frontier K) = 0`).
* `Arlib.volume_goodSet_ge` — the distributional step of Lemma 3.4:
  `(1−α)·vol {x ∈ K : σ(x,t) ≥ α} ≥ (1 − α − 10·t√n/2)·vol K`.
* `Arlib.lintegral_stepRadius_ge` — **Lemma 3.4**:
  `∫_K s_α ≥ ((1−α)/(10√n))·vol K`.

## Lemma 3.3 is proved, not assumed

The paper's **Lemma 3.3** (= Corollary 4.6 of Kannan–Lovász–Simonovits 1997),

`∫_K vol((x + tB) \ K) dx ≤ (t√n / 2r) · vol(K) · vol(tB)`,

is *quoted* by Lovász–Vempala.  It is **proved in this repository**, at the correct order `√n`
and with an explicit absolute constant, as `Arlib.lintegral_volume_closedBall_sdiff_le_sqrt`
in `Arlib/Convexity/KLS97Sharp.lean`; the specialisation to inradius `r = 1` used here is
`Arlib.lem33_sqrt`.  It used to enter `Arlib.volume_goodSet_ge` and
`Arlib.lintegral_stepRadius_ge` as a visible inline `∀`-hypothesis `hLem33`; that hypothesis is
gone.  `Arlib.lintegral_stepRadius_ge` now discharges it from `hball : closedBall z 1 ⊆ K`,
which is exactly the paper's "Suppose `K` contains a unit ball", and `volume_goodSet_ge` still
takes the inequality inline (it is the purely distributional step and needs no convexity).

**The constant.**  What is proved is the `10√n` form,
`∫_K vol((x + tB) \ K) dx ≤ (10·t√n / 2r)·vol(K)·vol(tB)`, not the paper's `C = 1`.  This is a
constant-factor loss in the majorant used by `KLS97Sharp.lean`'s route — the exponential
envelope `e^{2−λh}` in place of the Gaussian, plus `(1+x)ⁿ − 1 ≤ nx·e^{nx}` — **not** evidence
of an error in KLS97; that file's docstring has the breakdown (the route's true asymptotics is
`√(2π)·t√n/2r`, and the ball itself attains `1/√(2π)` against the printed `1/2`).  The cost
downstream is that Lemma 3.4 reads `∫_K s_α ≥ ((1−α)/(10√n))·vol K` instead of
`((1−α)/√n)·vol K` — the same order in `n`, which is all the conductance bound needs.

## Lemma 3.2 lives next door

**Lemma 3.2** (`F(x) ≥ s_α(x)/32` for `α ≥ 63/64`, with `F` the median hit-and-run step
length) is proved in `Arlib/Convexity/HitAndRunStep.lean`, as
`Arlib.stepRadius_le_medianStep`.  It is not here because `F` is defined by the hit-and-run
kernel of `Arlib/MarkovChains/Continuous/HitAndRun.lean`, which this file does not import.

Two things worth knowing from that file:

* The paper's displayed intermediate bound `p ≤ 1 − α + 2^{-n} ≤ 1/32` needs `2^{-n} ≤ 1/64`,
  i.e. `n ≥ 6`, which the paper does not state — so the *printed proof* has a gap for
  `n ≤ 5`.  **Lemma 3.2 itself is nevertheless true for every `n ≥ 1`**, and is proved there
  with no dimension hypothesis: the gap is an artefact of weakening the cone volume
  `p·(vol(sB) − vol((s/2)B))` to `p·vol(sB) − vol((s/2)B)`.
* `Arlib.theta_mul_stepRadius_le` below is exactly the concavity step §4 of the paper uses,
  and the §4 chain `s(x) ≤ (|x−p|/|u−p|)·s(u) ≤ 32(|q−p|/|u−p|)·F(u)` runs with `≤`
  throughout, so Lemma 3.2 is applied there in the correct direction.  (An earlier reading
  of a lossy text extraction of §4 suspected otherwise; it was mistaken.)

## Design notes

* **Closed balls.** The paper writes `x + tB` without specifying open or closed; we use
  `Metric.closedBall`, which changes no volume and makes `K ∩ closedBall x t` compact when `K`
  is, so that the Minkowski combinations appearing in the Brunn–Minkowski step are honestly
  measurable rather than merely outer-measurable.
* **`t = 0` is always admissible.** The paper's `sup` is over a set that can be empty (take `α`
  close to `1` and `x` a corner of `K`: then `σ(x,t) < α` for every `t > 0`), and it silently
  reads `sup ∅ = 0`. We instead build `t = 0` into `stepRadiusSet` — where the defining
  inequality reads `α · 0 ≤ vol {x}`, i.e. `0 ≤ 0`, and so holds vacuously. This makes
  `stepRadiusSet` nonempty for every `x ∈ K`, gives `stepRadius` the intended value `0` at a
  corner, and is what makes the concavity proof go through with no case split.
-/

open MeasureTheory Set Pointwise
open scoped ENNReal

namespace Arlib

/-! ### The sharp Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`

`Arlib.brunn_minkowski_sharp` lives on `Fin n → ℝ`.  The measurable-space structure, the
additive group structure and the `ℝ`-scalar action of `EuclideanSpace ℝ (Fin n)` are the same
ones, transported along `WithLp.toLp`, and `PiLp.volume_preserving_toLp` says Lebesgue measure
is transported too; so the inequality transports verbatim.  Only the *norm* differs, and
Brunn–Minkowski does not mention the norm. -/

section BrunnMinkowskiEuclidean

variable {n : ℕ}

/-- Lebesgue measure on `EuclideanSpace ℝ (Fin n)` is the pushforward of Lebesgue measure on
`Fin n → ℝ`, so volumes may be computed on preimages. Holds for *all* sets, measurable or not,
because `MeasurableEquiv.toLp` is a measurable equivalence. -/
private lemma volume_eq_volume_preimage_toLp (S : Set (EuclideanSpace ℝ (Fin n))) :
    volume S = volume ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' S) := by
  conv_lhs => rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  rw [show (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        = (MeasurableEquiv.toLp 2 (Fin n → ℝ) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) from rfl,
    MeasurableEquiv.map_apply]

private lemma preimage_toLp_add (X Y : Set (EuclideanSpace ℝ (Fin n))) :
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' (X + Y)
      = (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' X
        + (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' Y := by
  ext z
  simp only [Set.mem_preimage, Set.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨WithLp.ofLp a, by simpa using ha, WithLp.ofLp b, by simpa using hb, by
      simpa using congrArg WithLp.ofLp hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨_, ha, _, hb, by simp [← hab]⟩

private lemma preimage_toLp_smul (c : ℝ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' (c • X)
      = c • ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' X) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_smul_set]
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨WithLp.ofLp a, by simpa using ha, by simpa using congrArg WithLp.ofLp hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨_, ha, by simp [← hab]⟩

/-- **The sharp (`1/n`-concave) Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`.**

The transport of `Arlib.brunn_minkowski_sharp` to the Euclidean norm.  As there, no finiteness
hypothesis is needed, nonemptiness of `A` and `B` is not removable, and the Minkowski sum need
not be measurable (`volume` is used as an outer measure on the right). -/
theorem brunn_minkowski_sharp_euclidean {n : ℕ} (hn : n ≠ 0) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ (1 / (n : ℝ))
        + ENNReal.ofReal (1 - lam) * volume B ^ (1 / (n : ℝ))
      ≤ volume (lam • A + (1 - lam) • B) ^ (1 / (n : ℝ)) := by
  have hmeas : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      MeasurableSet ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' S) := fun _ hS =>
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable hS
  have hne : ∀ S : Set (EuclideanSpace ℝ (Fin n)), S.Nonempty →
      ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' S).Nonempty := by
    rintro S ⟨y, hy⟩
    exact ⟨WithLp.ofLp y, by simpa using hy⟩
  have key := brunn_minkowski_sharp (n := n) hn hlam0 hlam1
    (hmeas A hA) (hmeas B hB) (hne A hAne) (hne B hBne)
  rw [← volume_eq_volume_preimage_toLp A, ← volume_eq_volume_preimage_toLp B,
    ← preimage_toLp_smul, ← preimage_toLp_smul, ← preimage_toLp_add,
    ← volume_eq_volume_preimage_toLp] at key
  exact key

end BrunnMinkowskiEuclidean

/-! ### Volumes of Euclidean balls -/

section BallVolume

variable {n : ℕ}

/-- `vol(closedBall x t) = tⁿ · vol(B)`, with `B` the unit ball at the origin. -/
lemma volume_closedBall_euclidean {t : ℝ} (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin n)) :
    volume (Metric.closedBall x t)
      = ENNReal.ofReal t ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [Measure.addHaar_closedBall volume x ht, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow ht]

lemma volume_euclideanUnitBall_ne_zero :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
  (Metric.measure_ball_pos volume 0 one_pos).ne'

/-- `(a ^ n) ^ (1/n) = a` in `ℝ≥0∞`. -/
private lemma rpow_inv_npow {n : ℕ} (hn : n ≠ 0) (a : ℝ≥0∞) : (a ^ n) ^ (1 / (n : ℝ)) = a := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← ENNReal.rpow_natCast a n, ← ENNReal.rpow_mul, mul_one_div, div_self hn',
    ENNReal.rpow_one]

end BallVolume

/-! ### `σ(x,t)`, the admissible radii, and `s_α` -/

section Definitions

variable {n : ℕ}

/-- `σ(x,t) = vol(K ∩ (x + tB)) / vol(tB)`, the fraction of the ball of radius `t` about `x`
occupied by `K`.  Real-valued; the junk value at `t = 0` is `0 / 0 = 0`. -/
noncomputable def ballFraction (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (volume (K ∩ Metric.closedBall x t)).toReal / (volume (Metric.closedBall x t)).toReal

/-- The set `{t ≥ 0 : σ(x,t) ≥ α}` of radii at which `K` still occupies an `α` fraction of the
ball of radius `t` about `x`, written as an inequality between `ℝ≥0∞`-valued volumes.

Writing it this way rather than as `α ≤ ballFraction K x t` has two advantages: no finiteness
side condition is needed, and `t = 0` is automatically a member (both sides are `0`), so the
set is never empty for `x ∈ K` and its supremum is not a junk value. -/
def stepRadiusSet (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧
    ENNReal.ofReal α * volume (Metric.closedBall x t) ≤ volume (K ∩ Metric.closedBall x t)}

/-- `s_α(x) = sup {t : σ(x,t) ≥ α}`, the paper's step radius. -/
noncomputable def stepRadius (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup (stepRadiusSet K α x)

lemma zero_mem_stepRadiusSet (hn : n ≠ 0) (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : (0 : ℝ) ∈ stepRadiusSet K α x := by
  refine ⟨le_rfl, ?_⟩
  have h : volume (Metric.closedBall x (0 : ℝ)) = 0 := by
    rw [volume_closedBall_euclidean le_rfl, ENNReal.ofReal_zero, zero_pow hn, zero_mul]
  rw [h, mul_zero]
  exact bot_le

lemma stepRadiusSet_nonempty (hn : n ≠ 0) (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : (stepRadiusSet K α x).Nonempty :=
  ⟨0, zero_mem_stepRadiusSet hn K α x⟩

lemma nonneg_of_mem_stepRadiusSet {K : Set (EuclideanSpace ℝ (Fin n))} {α : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : t ∈ stepRadiusSet K α x) : 0 ≤ t := ht.1

/-- For `t > 0` and `0 ≤ α`, membership in `stepRadiusSet` really is the paper's `σ(x,t) ≥ α`.
`K` is assumed to have finite volume, which is automatic for a body. -/
lemma mem_stepRadiusSet_iff_ballFraction {K : Set (EuclideanSpace ℝ (Fin n))} {α : ℝ}
    (hα : 0 ≤ α) {x : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : 0 < t)
    (hKfin : volume K ≠ ⊤) :
    t ∈ stepRadiusSet K α x ↔ α ≤ ballFraction K x t := by
  have hball0 : volume (Metric.closedBall x t) ≠ 0 := by
    rw [volume_closedBall_euclidean ht.le]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr ht).ne')
      volume_euclideanUnitBall_ne_zero
  have hballtop : volume (Metric.closedBall x t) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hinter : volume (K ∩ Metric.closedBall x t) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin (measure_mono Set.inter_subset_left)
  have hpos : 0 < (volume (Metric.closedBall x t)).toReal :=
    ENNReal.toReal_pos hball0 hballtop
  unfold ballFraction stepRadiusSet
  rw [Set.mem_setOf_eq, le_div_iff₀ hpos]
  constructor
  · rintro ⟨-, h⟩
    have := ENNReal.toReal_mono hinter h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα] at this
  · intro h
    refine ⟨ht.le, ?_⟩
    have : ENNReal.ofReal (α * (volume (Metric.closedBall x t)).toReal)
        ≤ ENNReal.ofReal ((volume (K ∩ Metric.closedBall x t)).toReal) :=
      ENNReal.ofReal_le_ofReal h
    rwa [ENNReal.ofReal_mul hα, ENNReal.ofReal_toReal hballtop,
      ENNReal.ofReal_toReal hinter] at this

end Definitions

/-! ### Lemma 3.1: `s_α` is concave -/

section Concavity

variable {n : ℕ}

/-- The convex combination of two "caps" `K ∩ (xᵢ + tᵢB)` sits inside the cap at the combined
centre and the combined radius.  This is the elementary half of Lemma 3.1: both the convexity
of `K` and the convexity of the ball are used. -/
lemma smul_add_smul_cap_subset {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {x₁ x₂ : EuclideanSpace ℝ (Fin n)} {t₁ t₂ : ℝ} :
    lam • (K ∩ Metric.closedBall x₁ t₁) + (1 - lam) • (K ∩ Metric.closedBall x₂ t₂)
      ⊆ K ∩ Metric.closedBall (lam • x₁ + (1 - lam) • x₂) (lam * t₁ + (1 - lam) * t₂) := by
  rintro z ⟨-, ⟨a, ⟨haK, haB⟩, rfl⟩, -, ⟨b, ⟨hbK, hbB⟩, rfl⟩, rfl⟩
  have h1' : (0 : ℝ) ≤ 1 - lam := by linarith
  refine ⟨hK haK hbK h0 h1' (by ring), ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hz : lam • a + (1 - lam) • b - (lam • x₁ + (1 - lam) • x₂)
      = lam • (a - x₁) + (1 - lam) • (b - x₂) := by
    simp only [smul_sub]; abel
  rw [hz]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg h1']
  have ha : ‖a - x₁‖ ≤ t₁ := by rwa [← dist_eq_norm, ← Metric.mem_closedBall]
  have hb : ‖b - x₂‖ ≤ t₂ := by rwa [← dist_eq_norm, ← Metric.mem_closedBall]
  exact add_le_add (by nlinarith) (by nlinarith)

/-- **The engine of Lemma 3.1.**  Admissible radii combine convexly: if `t₁` is admissible at
`x₁` and `t₂` is admissible at `x₂`, then `λt₁ + (1-λ)t₂` is admissible at `λx₁ + (1-λ)x₂`.

This is exactly the paper's argument — contain the Minkowski combination of the two caps in the
combined cap, and apply the sharp Brunn–Minkowski inequality — with the `λ = 1/2` of the paper
replaced by a general weight. -/
theorem mem_stepRadiusSet_combo (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) {α : ℝ}
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {x₁ x₂ : EuclideanSpace ℝ (Fin n)} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ stepRadiusSet K α x₁) (ht₂ : t₂ ∈ stepRadiusSet K α x₂) :
    lam * t₁ + (1 - lam) * t₂ ∈ stepRadiusSet K α (lam • x₁ + (1 - lam) • x₂) := by
  obtain ⟨ht₁0, ht₁v⟩ := ht₁
  obtain ⟨ht₂0, ht₂v⟩ := ht₂
  have h1' : (0 : ℝ) ≤ 1 - lam := by linarith
  set x : EuclideanSpace ℝ (Fin n) := lam • x₁ + (1 - lam) • x₂ with hxdef
  set t : ℝ := lam * t₁ + (1 - lam) * t₂ with htdef
  have ht0 : 0 ≤ t := by positivity
  refine ⟨ht0, ?_⟩
  set A₁ : Set (EuclideanSpace ℝ (Fin n)) := K ∩ Metric.closedBall x₁ t₁ with hA₁
  set A₂ : Set (EuclideanSpace ℝ (Fin n)) := K ∩ Metric.closedBall x₂ t₂ with hA₂
  have hA₁m : MeasurableSet A₁ := hKm.inter measurableSet_closedBall
  have hA₂m : MeasurableSet A₂ := hKm.inter measurableSet_closedBall
  have hA₁ne : A₁.Nonempty := ⟨x₁, hx₁, Metric.mem_closedBall_self ht₁0⟩
  have hA₂ne : A₂.Nonempty := ⟨x₂, hx₂, Metric.mem_closedBall_self ht₂0⟩
  -- Brunn–Minkowski on the two caps
  have hbm := brunn_minkowski_sharp_euclidean hn h0 h1 hA₁m hA₂m hA₁ne hA₂ne
  -- the combination is contained in the combined cap
  have hsub : lam • A₁ + (1 - lam) • A₂ ⊆ K ∩ Metric.closedBall x t :=
    smul_add_smul_cap_subset hKc h0 h1
  have hmono : volume (lam • A₁ + (1 - lam) • A₂) ^ (1 / (n : ℝ))
      ≤ volume (K ∩ Metric.closedBall x t) ^ (1 / (n : ℝ)) :=
    ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity)
  -- lower bound the two terms on the left of Brunn–Minkowski
  set c : ℝ≥0∞ := (ENNReal.ofReal α) ^ (1 / (n : ℝ))
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 / (n : ℝ)) with hc
  have hcap : ∀ (y : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
      ENNReal.ofReal α * volume (Metric.closedBall y r) ≤ volume (K ∩ Metric.closedBall y r) →
      c * ENNReal.ofReal r ≤ volume (K ∩ Metric.closedBall y r) ^ (1 / (n : ℝ)) := by
    intro y r hr hcond
    have := ENNReal.rpow_le_rpow hcond (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    refine le_trans (le_of_eq ?_) this
    rw [volume_closedBall_euclidean hr, ← mul_assoc,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
      rpow_inv_npow hn]
    rw [hc]; ring
  have hL₁ := hcap x₁ t₁ ht₁0 ht₁v
  have hL₂ := hcap x₂ t₂ ht₂0 ht₂v
  -- assemble
  have hstep : c * ENNReal.ofReal t ≤ volume (K ∩ Metric.closedBall x t) ^ (1 / (n : ℝ)) := by
    refine le_trans (le_of_eq ?_) (le_trans (add_le_add
      (mul_le_mul' (le_refl (ENNReal.ofReal lam)) hL₁)
      (mul_le_mul' (le_refl (ENNReal.ofReal (1 - lam))) hL₂)) (hbm.trans hmono))
    rw [htdef, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1']
    ring
  -- undo the `1/n`-th root
  have hfinal : (ENNReal.ofReal α * volume (Metric.closedBall x t)) ^ (1 / (n : ℝ))
      ≤ volume (K ∩ Metric.closedBall x t) ^ (1 / (n : ℝ)) := by
    refine le_trans (le_of_eq ?_) hstep
    rw [volume_closedBall_euclidean ht0, ← mul_assoc,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
      rpow_inv_npow hn, hc]
    ring
  have hnn : (0 : ℝ) < (n : ℝ) := by positivity
  have := ENNReal.rpow_le_rpow hfinal (le_of_lt hnn)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hnn.ne',
    ENNReal.rpow_one, ENNReal.rpow_one] at this

/-- `stepRadiusSet` is bounded above once `K` has finite volume and `α > 0`: a ball of radius
`t` about any point has volume `tⁿ·vol(B)`, and an `α`-fraction of that cannot exceed
`vol K`. -/
lemma bddAbove_stepRadiusSet (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKfin : volume K ≠ ⊤) {α : ℝ} (hα : 0 < α) (x : EuclideanSpace ℝ (Fin n)) :
    BddAbove (stepRadiusSet K α x) := by
  set Vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hVb
  have hVb0 : Vb ≠ 0 := volume_euclideanUnitBall_ne_zero
  have hVbtop : Vb ≠ ⊤ := measure_ball_lt_top.ne
  have hVbpos : 0 < Vb.toReal := ENNReal.toReal_pos hVb0 hVbtop
  refine ⟨max 1 ((volume K).toReal / (α * Vb.toReal)), ?_⟩
  rintro t ⟨ht0, ht⟩
  have hle : ENNReal.ofReal (α * t ^ n) * Vb ≤ volume K := by
    refine le_trans (le_of_eq ?_) (ht.trans (measure_mono Set.inter_subset_left))
    rw [volume_closedBall_euclidean ht0, ← ENNReal.ofReal_pow ht0, ← mul_assoc,
      ← ENNReal.ofReal_mul hα.le, ← hVb]
  have hreal : α * t ^ n * Vb.toReal ≤ (volume K).toReal := by
    have := ENNReal.toReal_mono hKfin hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hpow : t ^ n ≤ (volume K).toReal / (α * Vb.toReal) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  by_cases h : t ≤ 1
  · exact h.trans (le_max_left _ _)
  · have h1 : (1 : ℝ) ≤ t := le_of_lt (lt_of_not_ge h)
    have : t ≤ t ^ n := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ n := pow_le_pow_right₀ h1 (Nat.one_le_iff_ne_zero.mpr hn)
    exact this.trans (hpow.trans (le_max_right _ _))

lemma stepRadius_nonneg (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKfin : volume K ≠ ⊤) {α : ℝ} (hα : 0 < α) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ stepRadius K α x :=
  le_csSup (bddAbove_stepRadiusSet hn hKfin hα x) (zero_mem_stepRadiusSet hn K α x)

/-- If every `a·t ≤ c` for `t` in a nonempty set `S` and `0 ≤ a`, then `a · sSup S ≤ c`. -/
private lemma mul_csSup_le_of_forall {S : Set ℝ} (hne : S.Nonempty) {a c : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ∈ S, a * t ≤ c) : a * sSup S ≤ c := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · obtain ⟨t, ht⟩ := hne
    have hc := h t ht
    rw [← h0] at hc ⊢
    simpa using hc
  · have hS : sSup S ≤ c / a :=
      csSup_le hne fun t ht => (le_div_iff₀ h0).mpr (by nlinarith [h t ht])
    calc a * sSup S ≤ a * (c / a) := by nlinarith
      _ = c := by field_simp

/-- **Lemma 3.1 of Lovász–Vempala.**  For any threshold `α > 0`, the step radius `s_α` is a
concave function on the convex body `K`.

The paper proves midpoint concavity; we get the full convex-combination form for free, since
`Arlib.mem_stepRadiusSet_combo` is proved with a general weight. -/
theorem stepRadius_concaveOn (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    {α : ℝ} (hα : 0 < α) :
    ConcaveOn ℝ K (stepRadius K α) := by
  refine ⟨hKc, ?_⟩
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha1 : a ≤ 1 := by linarith
  set x : EuclideanSpace ℝ (Fin n) := a • x₁ + (1 - a) • x₂ with hxdef
  have hbdd : BddAbove (stepRadiusSet K α x) := bddAbove_stepRadiusSet hn hKfin hα x
  have hS₁ne := stepRadiusSet_nonempty hn K α x₁
  have hS₂ne := stepRadiusSet_nonempty hn K α x₂
  have hstep : ∀ t₂ ∈ stepRadiusSet K α x₂,
      (1 - a) * t₂ ≤ stepRadius K α x - a * stepRadius K α x₁ := by
    intro t₂ ht₂
    have h1 : a * stepRadius K α x₁ ≤ stepRadius K α x - (1 - a) * t₂ := by
      refine mul_csSup_le_of_forall hS₁ne ha fun t₁ ht₁ => ?_
      have hmem := mem_stepRadiusSet_combo hn hKc hKm ha ha1 hx₁ hx₂ ht₁ ht₂
      have hcs := le_csSup hbdd hmem
      unfold stepRadius
      linarith
    linarith
  have h2 := mul_csSup_le_of_forall hS₂ne (by linarith : (0:ℝ) ≤ 1 - a) hstep
  simp only [smul_eq_mul]
  unfold stepRadius at h2 ⊢
  linarith

/-- A convenient repackaging of concavity used in §4 of the paper: on the segment from a point
`p ∈ K` to a point `u ∈ K`, the step radius at `θ • u + (1-θ) • p` is at least `θ · s(u)`.
Only `s(p) ≥ 0` is used at the far endpoint. -/
theorem theta_mul_stepRadius_le (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤) {α : ℝ} (hα : 0 < α)
    {p u : EuclideanSpace ℝ (Fin n)} (hp : p ∈ K) (hu : u ∈ K)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * stepRadius K α u ≤ stepRadius K α (θ • u + (1 - θ) • p) := by
  have hconc := stepRadius_concaveOn hn hKc hKm hKfin hα
  have := hconc.2 hu hp h0 (by linarith : (0:ℝ) ≤ 1 - θ) (by ring)
  have hpnn := stepRadius_nonneg hn hKfin hα p
  simp only [smul_eq_mul] at this
  nlinarith

end Concavity

/-! ### Towards Lemma 3.4

Lemma 3.4 of the paper says `∫_K s_α ≥ ((1−α)/√n)·vol K` for a body containing a unit ball.
Its proof has two halves.  The first — proved here as `Arlib.volume_goodSet_ge` — converts the
paper's Lemma 3.3 into a lower bound on the measure of `{x ∈ K : σ(x,t) ≥ α}`.  The second is
the layer-cake identity `∫_K s_α = ∫₀^∞ vol {x ∈ K : s_α(x) ≥ t} dt`, which is *not* proved
here; see the module-level note. -/

section Lemma34

variable {n : ℕ}

/-- `x ↦ vol(K ∩ (x + tB))` is measurable: it is a section measure of a measurable subset of
the product, so Fubini's measurability lemma applies. -/
lemma measurable_volume_inter_closedBall {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (t : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => volume (K ∩ Metric.closedBall x t)) := by
  have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ K ∧ dist p.2 p.1 ≤ t} :=
    (measurable_snd hK).inter
      (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const)
  have heq : ∀ x : EuclideanSpace ℝ (Fin n),
      K ∩ Metric.closedBall x t
        = Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            p.2 ∈ K ∧ dist p.2 p.1 ≤ t} := by
    intro x; ext y; simp [Metric.mem_closedBall]
  simp only [heq]
  exact measurable_measure_prodMk_left hs

/-- `x ↦ vol((x + tB) \ K)` is measurable, for the same reason. -/
lemma measurable_volume_closedBall_diff {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (t : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => volume (Metric.closedBall x t \ K)) := by
  have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      dist p.2 p.1 ≤ t ∧ p.2 ∉ K} :=
    (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const).inter
      (measurable_snd hK).compl
  have heq : ∀ x : EuclideanSpace ℝ (Fin n),
      Metric.closedBall x t \ K
        = Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            dist p.2 p.1 ≤ t ∧ p.2 ∉ K} := by
    intro x; ext y; simp [Metric.mem_closedBall]
  simp only [heq]
  exact measurable_measure_prodMk_left hs

/-- `{x ∈ K : σ(x,t) ≥ α}`, the set of points of `K` at which the radius `t` is still
admissible. -/
def goodSet (K : Set (EuclideanSpace ℝ (Fin n))) (α t : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ K ∧ t ∈ stepRadiusSet K α x}

lemma goodSet_subset {K : Set (EuclideanSpace ℝ (Fin n))} {α t : ℝ} : goodSet K α t ⊆ K :=
  fun _ h => h.1

/-- Membership in `goodSet` witnesses that `t` is below the step radius. -/
lemma le_stepRadius_of_mem_goodSet (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKfin : volume K ≠ ⊤) {α : ℝ} (hα : 0 < α) {t : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ goodSet K α t) : t ≤ stepRadius K α x :=
  le_csSup (bddAbove_stepRadiusSet hn hKfin hα x) hx.2

lemma measurableSet_goodSet {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {α t : ℝ} (ht : 0 ≤ t) : MeasurableSet (goodSet K α t) := by
  have hrw : goodSet K α t
      = K ∩ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal α *
          (ENNReal.ofReal t ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
            ≤ volume (K ∩ Metric.closedBall x t)} := by
    ext x
    simp only [goodSet, stepRadiusSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      volume_closedBall_euclidean ht x]
    tauto
  rw [hrw]
  exact hK.inter (measurableSet_le measurable_const (measurable_volume_inter_closedBall hK t))

/-- **The distributional half of Lemma 3.4.**

Given the paper's Lemma 3.3 — *quoted*, not proved, by Lovász–Vempala from Corollary 4.6 of
Kannan–Lovász–Simonovits 1997, and **proved in this repository** as
`Arlib.lintegral_volume_closedBall_sdiff_le_sqrt` / `Arlib.lem33_sqrt`
(`Arlib/Convexity/KLS97Sharp.lean`) — this is exactly the paper's step

> `∫_K σ(x,t) dx ≤ α·vol(K) + (1−α)·vol({x ∈ K : σ(x,t) ≥ α})` , hence
> `vol({x ∈ K : σ(x,t) ≥ α}) ≥ (1 − 10·t√n / (2(1−α)))·vol(K)`.

The Lemma 3.3 inequality is still taken here as an inline hypothesis, because this step is
*purely distributional*: it uses neither convexity nor closedness of `K`, only measurability
and finite volume, and so it would be wrong to bolt those hypotheses on merely to discharge the
input.  The discharge happens one level up, in `Arlib.lintegral_stepRadius_ge`, which carries
`hKc`, `hKcl` and `hball : closedBall z 1 ⊆ K` and calls `Arlib.lem33_sqrt`.  **No caller needs
to supply Lemma 3.3 as an assumption any more**, and no `hLem33` binder survives past this
theorem.

The constant is `10√n`, not the paper's `√n`: `KLS97Sharp.lean` proves the `√n` *order* with an
explicit absolute constant `C = 10`, a constant-factor loss in its exponential-envelope
majorant rather than any error in KLS97 (see that file's docstring).

The conclusion is stated multiplied through by `(1 − α)` so that no `ℝ≥0∞` subtraction or
division appears. -/
theorem volume_goodSet_ge (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {t : ℝ} (ht : 0 < t)
    (hLem33 : ∫⁻ x in K, volume (Metric.closedBall x t \ K)
        ≤ ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K
            * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t)) :
    ENNReal.ofReal (1 - α - t * (10 * Real.sqrt n) / 2) * volume K
      ≤ ENNReal.ofReal (1 - α) * volume (goodSet K α t) := by
  classical
  -- notation
  set V : ℝ≥0∞ := ENNReal.ofReal t ^ n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    with hVdef
  have hball : ∀ x : EuclideanSpace ℝ (Fin n), volume (Metric.closedBall x t) = V :=
    fun x => volume_closedBall_euclidean ht.le x
  have hV0 : V ≠ 0 := by
    rw [hVdef]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr ht).ne')
      volume_euclideanUnitBall_ne_zero
  have hVtop : V ≠ ⊤ := by rw [← hball 0]; exact measure_closedBall_lt_top.ne
  clear_value V
  set f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x => volume (K ∩ Metric.closedBall x t) with hfdef
  set g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x => volume (Metric.closedBall x t \ K) with hgdef
  have hfm : Measurable f := measurable_volume_inter_closedBall hKm t
  have hgm : Measurable g := measurable_volume_closedBall_diff hKm t
  have hfle : ∀ x, f x ≤ V := by
    intro x; rw [hfdef, ← hball x]; exact measure_mono Set.inter_subset_right
  have hfg : ∀ x, f x + g x = V := by
    intro x
    show volume (K ∩ Metric.closedBall x t) + volume (Metric.closedBall x t \ K) = V
    rw [← hball x, Set.inter_comm]
    exact measure_inter_add_sdiff _ hKm
  -- the total integral
  have htotal : (∫⁻ x in K, f x) + (∫⁻ x in K, g x) = V * volume K := by
    rw [← lintegral_add_left hfm]
    simp_rw [hfg]
    rw [setLIntegral_const]
  -- the good set
  set A : Set (EuclideanSpace ℝ (Fin n)) := goodSet K α t with hAdef
  have hAm : MeasurableSet A := measurableSet_goodSet hKm ht.le
  have hAsub : A ⊆ K := goodSet_subset
  have hKsplit : volume K = volume A + volume (K \ A) := by
    rw [← measure_union Set.disjoint_sdiff_right (hKm.diff hAm), Set.union_sdiff_cancel hAsub]
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hKfin (measure_mono hAsub)
  have hDfin : volume (K \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin (measure_mono Set.sdiff_subset)
  -- split the integral over `A` and its complement in `K`
  have hsplit : (∫⁻ x in K, f x) = (∫⁻ x in A, f x) + (∫⁻ x in K \ A, f x) := by
    rw [← lintegral_union (hKm.diff hAm) Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hAsub]
  have hAbound : (∫⁻ x in A, f x) ≤ V * volume A :=
    le_trans (setLIntegral_mono' hAm fun x _ => hfle x) (by rw [setLIntegral_const])
  have hDbound : (∫⁻ x in K \ A, f x) ≤ ENNReal.ofReal α * V * volume (K \ A) := by
    refine le_trans (setLIntegral_mono' (hKm.diff hAm) fun x hx => ?_) (by rw [setLIntegral_const])
    rcases le_or_gt (f x) (ENNReal.ofReal α * V) with h | h
    · exact h
    · exact absurd ⟨hx.1, ht.le, by rw [hball x]; exact h.le⟩ hx.2
  -- combine, in `ℝ≥0∞`
  have hmain : V * volume K
      ≤ V * volume A + ENNReal.ofReal α * V * volume (K \ A)
        + ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K * V := by
    calc V * volume K = (∫⁻ x in K, f x) + (∫⁻ x in K, g x) := htotal.symm
      _ ≤ ((∫⁻ x in A, f x) + (∫⁻ x in K \ A, f x))
            + ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K * V := by
          rw [← hsplit]
          exact add_le_add le_rfl (by rw [← hball 0]; exact hLem33)
      _ ≤ V * volume A + ENNReal.ofReal α * V * volume (K \ A)
            + ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K * V :=
          add_le_add (add_le_add hAbound hDbound) le_rfl
  -- pass to real numbers
  set Vr : ℝ := V.toReal with hVr
  set vA : ℝ := (volume A).toReal with hvA
  set vD : ℝ := (volume (K \ A)).toReal with hvD
  have hVrpos : 0 < Vr := ENNReal.toReal_pos hV0 hVtop
  have hvAnn : 0 ≤ vA := ENNReal.toReal_nonneg
  have hvDnn : 0 ≤ vD := ENNReal.toReal_nonneg
  have hvK : (volume K).toReal = vA + vD := by
    rw [hKsplit, ENNReal.toReal_add hAfin hDfin]
  have hC : (0 : ℝ) ≤ t * (10 * Real.sqrt n) / 2 := by positivity
  have hrhstop : V * volume A + ENNReal.ofReal α * V * volume (K \ A)
      + ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K * V ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hVtop hAfin,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop) hDfin⟩, ?_⟩
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) hVtop
  have hreal : Vr * (vA + vD)
      ≤ Vr * vA + α * Vr * vD + t * (10 * Real.sqrt n) / 2 * (vA + vD) * Vr := by
    have hmono := ENNReal.toReal_mono hrhstop hmain
    have hA1 : V * volume A ≠ ⊤ := ENNReal.mul_ne_top hVtop hAfin
    have hA2 : ENNReal.ofReal α * V * volume (K \ A) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop) hDfin
    have hA3 : ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K * V ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) hVtop
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hA1, hA2⟩) hA3,
      ENNReal.toReal_add hA1 hA2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hα0, ENNReal.toReal_ofReal hC, hvK] at hmono
    exact hmono
  -- the algebraic rearrangement
  have hkey : (1 - α - t * (10 * Real.sqrt n) / 2) * (vA + vD) ≤ (1 - α) * vA := by nlinarith
  -- and back to `ℝ≥0∞`
  rcases le_or_gt (1 - α - t * (10 * Real.sqrt n) / 2) 0 with hsign | hsign
  · rw [ENNReal.ofReal_eq_zero.mpr hsign, zero_mul]
    exact bot_le
  · have h1 : ENNReal.ofReal ((1 - α - t * (10 * Real.sqrt n) / 2) * (volume K).toReal)
        ≤ ENNReal.ofReal ((1 - α) * vA) := by
      rw [hvK]; exact ENNReal.ofReal_le_ofReal hkey
    rwa [ENNReal.ofReal_mul hsign.le, ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - α),
      ENNReal.ofReal_toReal hKfin, hvA, ENNReal.ofReal_toReal hAfin] at h1

/-! ### Measurability of `s_α`

A concave function is continuous on the interior of its domain, and the frontier of a convex
set is Lebesgue-null; so `s_α` is a.e.-measurable on `K` with no further work. -/

lemma continuousOn_stepRadius (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤) {α : ℝ} (hα : 0 < α) :
    ContinuousOn (stepRadius K α) (interior K) :=
  (stepRadius_concaveOn hn hKc hKm hKfin hα).continuousOn_interior

lemma aemeasurable_stepRadius (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    {α : ℝ} (hα : 0 < α) :
    AEMeasurable (stepRadius K α) (volume.restrict K) := by
  have hae : K =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] interior K := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [← hKcl.frontier_eq]
      exact hKc.addHaar_frontier volume
    · simp [Set.sdiff_eq_empty.mpr interior_subset]
  rw [Measure.restrict_congr_set hae]
  exact (continuousOn_stepRadius hn hKc hKm hKfin hα).aemeasurable measurableSet_interior

/-! ### The elementary integral behind Lemma 3.4 -/

/-- `∫₀^∞ (b − ct)₊ dt = b²/(2c)`; only the `≥` half is needed. -/
private lemma ofReal_sq_div_le_lintegral {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ENNReal.ofReal (b ^ 2 / (2 * c))
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (b - c * t) := by
  set T : ℝ := b / c with hT
  have hT0 : 0 < T := div_pos hb hc
  have hmono : (∫⁻ t in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (b - c * t))
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (b - c * t) :=
    lintegral_mono_set (fun x hx => hx.1)
  refine le_trans (le_of_eq ?_) hmono
  have hcont : Continuous (fun t : ℝ => b - c * t) := by continuity
  have hintble : IntegrableOn (fun t : ℝ => b - c * t) (Set.Ioc (0 : ℝ) T) :=
    (hcont.integrableOn_Icc (a := (0:ℝ)) (b := T)).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] fun t : ℝ => b - c * t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    have hcx : c * x ≤ c * T := mul_le_mul_of_nonneg_left hx.2 hc.le
    rw [hT, mul_div_cancel₀ _ hc.ne'] at hcx
    show (0 : ℝ) ≤ b - c * x
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hintble hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hT0.le]
  have h1 : ∫ x in (0 : ℝ)..T, (b - c * x)
      = (∫ _x in (0 : ℝ)..T, b) - ∫ x in (0 : ℝ)..T, c * x :=
    intervalIntegral.integral_sub intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
  have h2 : ∫ x in (0 : ℝ)..T, (c * x) = c * ∫ x in (0 : ℝ)..T, x :=
    intervalIntegral.integral_const_mul c _
  rw [h1, h2, intervalIntegral.integral_const, integral_id, hT]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- **Lemma 3.4 of Lovász–Vempala.**  `∫_K s_α ≥ ((1−α)/(10√n))·vol(K)`.

**This statement has no assumed inputs.**  The paper's Lemma 3.3 — Corollary 4.6 of
Kannan–Lovász–Simonovits 1997, which Lovász–Vempala quote rather than prove — used to appear
here as an inline `∀`-hypothesis `hLem33`.  It is now *proved*, in
`Arlib/Convexity/KLS97Sharp.lean`, and discharged inside this proof by
`Arlib.lem33_sqrt hn hKc hKcl hKfin hball`.  What replaces the hypothesis is
`hball : Metric.closedBall z 1 ⊆ K` — exactly the paper's own "Suppose `K` contains a unit
ball" for Lemma 3.4, and the `r = 1` instance of Lemma 3.3's inradius hypothesis.  `hKcl` was
already present and is what `KLS97Sharp.lean` needs (its cap step uses the metric projection
onto `K`).

**The constant.**  The conclusion is `((1−α)/(10√n))·vol K`, where the paper writes
`((1−α)/√n)·vol K`.  The factor `10` is inherited from `Arlib.lem33_sqrt`, which proves Lemma
3.3 in the form `(10·t√n/2r)·vol(K)·vol(tB)`.  That is a constant-factor loss in the majorant
used by the proof route there — an exponential envelope `e^{2−λh}` in place of the Gaussian,
and `(1+x)ⁿ − 1 ≤ nx·e^{nx}` — **not** an error in KLS97, whose `C = 1` is consistent with
everything proved here; `KLS97Sharp.lean`'s docstring has the breakdown.  The order in `n` is
unchanged, which is all the downstream conductance bound uses.

Everything else is proved too: the distributional step is `Arlib.volume_goodSet_ge`, the
measurability of `s_α` comes from its concavity (Lemma 3.1) via
`Arlib.aemeasurable_stepRadius`, and the layer-cake identity is Mathlib's
`MeasureTheory.lintegral_eq_lintegral_meas_le`.

The integral is the lower Lebesgue integral of `ENNReal.ofReal ∘ s_α`, which is the honest
reading of `∫_K s(x) dx` for a nonnegative function and needs no integrability hypothesis. -/
theorem lintegral_stepRadius_ge (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K) :
    ENNReal.ofReal ((1 - α) / (10 * Real.sqrt n)) * volume K
      ≤ ∫⁻ x in K, ENNReal.ofReal (stepRadius K α x) := by
  have hLem33 : ∀ t : ℝ, 0 < t → ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (t * (10 * Real.sqrt n) / 2) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
    Arlib.lem33_sqrt hn hKc hKcl hKfin hball
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hb : (0 : ℝ) < 1 - α := by linarith
  set c : ℝ := 5 * Real.sqrt n with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hs_nn : 0 ≤ᵐ[volume.restrict K] stepRadius K α :=
    Filter.Eventually.of_forall fun x => stepRadius_nonneg hn hKfin hα0 x
  have hs_meas := aemeasurable_stepRadius hn hKc hKcl hKm hKfin hα0
  rw [lintegral_eq_lintegral_meas_le _ hs_nn hs_meas]
  -- the layer measures are bounded below by `Arlib.volume_goodSet_ge`
  have hlow : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (1 - α - c * t) * volume K
        ≤ ENNReal.ofReal (1 - α) *
            (volume.restrict K) {x : EuclideanSpace ℝ (Fin n) | t ≤ stepRadius K α x} := by
    intro t ht
    have h1 := volume_goodSet_ge hn hKm hKfin hα0.le hα1 ht (hLem33 t ht)
    have hgm : MeasurableSet (goodSet K α t) := measurableSet_goodSet hKm ht.le
    have h2 : volume (goodSet K α t)
        ≤ (volume.restrict K) {x : EuclideanSpace ℝ (Fin n) | t ≤ stepRadius K α x} := by
      calc volume (goodSet K α t) = (volume.restrict K) (goodSet K α t) := by
            rw [Measure.restrict_apply hgm, Set.inter_eq_left.mpr goodSet_subset]
        _ ≤ _ := measure_mono fun x hx => le_stepRadius_of_mem_goodSet hn hKfin hα0 hx
    refine le_trans ?_ (mul_le_mul' (le_refl (ENNReal.ofReal (1 - α))) h2)
    rw [show c * t = t * (10 * Real.sqrt n) / 2 by rw [hc]; ring]
    exact h1
  -- integrate the pointwise bound over `t`
  have hstep : ENNReal.ofReal ((1 - α) ^ 2 / (2 * c)) * volume K
      ≤ ENNReal.ofReal (1 - α) * ∫⁻ t in Set.Ioi (0 : ℝ),
          (volume.restrict K) {x : EuclideanSpace ℝ (Fin n) | t ≤ stepRadius K α x} := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((1 - α) ^ 2 / (2 * c)) * volume K
        ≤ (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 - α - c * t)) * volume K :=
          mul_le_mul' (ofReal_sq_div_le_lintegral hb hcpos) le_rfl
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 - α - c * t) * volume K :=
          (lintegral_mul_const' _ _ hKfin).symm
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hlow t ht
  -- cancel the common factor `ofReal (1 - α)`
  have key : ENNReal.ofReal (1 - α) * (ENNReal.ofReal ((1 - α) / (10 * Real.sqrt n)) * volume K)
      ≤ ENNReal.ofReal (1 - α) * ∫⁻ t in Set.Ioi (0 : ℝ),
          (volume.restrict K) {x : EuclideanSpace ℝ (Fin n) | t ≤ stepRadius K α x} := by
    refine le_trans (le_of_eq ?_) hstep
    rw [← mul_assoc, ← ENNReal.ofReal_mul hb.le]
    congr 2
    rw [hc]
    field_simp
    norm_num
  simp only [mul_comm (ENNReal.ofReal (1 - α))] at key
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hb).ne'
    ENNReal.ofReal_ne_top).mp key

end Lemma34

/-! ### Axiom profile -/

section AxiomCheck

#print axioms brunn_minkowski_sharp_euclidean
#print axioms volume_closedBall_euclidean
#print axioms volume_euclideanUnitBall_ne_zero
#print axioms zero_mem_stepRadiusSet
#print axioms stepRadiusSet_nonempty
#print axioms nonneg_of_mem_stepRadiusSet
#print axioms mem_stepRadiusSet_iff_ballFraction
#print axioms smul_add_smul_cap_subset
#print axioms mem_stepRadiusSet_combo
#print axioms bddAbove_stepRadiusSet
#print axioms stepRadius_nonneg
#print axioms stepRadius_concaveOn
#print axioms theta_mul_stepRadius_le
#print axioms measurable_volume_inter_closedBall
#print axioms measurable_volume_closedBall_diff
#print axioms goodSet_subset
#print axioms le_stepRadius_of_mem_goodSet
#print axioms measurableSet_goodSet
#print axioms volume_goodSet_ge
#print axioms continuousOn_stepRadius
#print axioms aemeasurable_stepRadius
#print axioms lintegral_stepRadius_ge

end AxiomCheck

end Arlib
