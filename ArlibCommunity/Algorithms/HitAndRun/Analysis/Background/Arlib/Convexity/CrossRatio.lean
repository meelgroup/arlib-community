/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Chords of a convex body and the cross-ratio distance

This file formalises the non-Euclidean distance used throughout

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SICOMP 2006,

and taken there from Lovász, *Hit-and-run mixes fast* (Math. Prog. 1999).  In the words of §2:

> Let `u, v` be two distinct points in `K`, let `ℓ(u,v)` denote the line through `u` and `v`,
> and let `p, q` be the endpoints of the segment `ℓ(u,v) ∩ K`, so that the points appear in the
> order `p, u, v, q` along `ℓ(u,v)`.  Then
> `d_K(u,v) = |u−v| |p−q| / (|p−u| |v−q|)`.

## Main definitions

* `Arlib.chordParam K u v` — the parameters `t` with `AffineMap.lineMap u v t ∈ K`, i.e. the
  chord `ℓ(u,v) ∩ K` read in the coordinate in which `u ↦ 0` and `v ↦ 1`.
* `Arlib.chordLow`, `Arlib.chordHigh` — the two endpoints of that parameter interval.
* `Arlib.chordStart` (`= p`), `Arlib.chordEnd` (`= q`) — the endpoints of the chord itself.
* `Arlib.crossRatioDist K u v` (`= d_K(u,v)`) — the cross-ratio distance.

## Main results

* `Arlib.chordParam_eq_Icc` — the chord-endpoint machinery: for a convex, closed, bounded `K`
  the parameter set is exactly `Icc (chordLow) (chordHigh)`, so `p` and `q` really are *the*
  endpoints; `Arlib.chordStart_mem`, `Arlib.chordEnd_mem` put them in `K` and
  `Arlib.chord_eq_segment` identifies `K ∩ ℓ(u,v)` with the segment `[p,q]`.
* `Arlib.crossRatioDist_eq_param` — the closed form
  `d_K(u,v) = (b − a) / ((−a)(b − 1))` in the chord coordinate, where `a = chordLow ≤ 0` and
  `b = chordHigh ≥ 1`.  Every later result is read off from this.
* `Arlib.crossRatioDist_comm` — **symmetry**, `d_K(u,v) = d_K(v,u)`.
* `Arlib.crossRatioDist_nonneg`, `Arlib.crossRatioDist_pos` — nonnegativity, and strict
  positivity away from the boundary.
* `Arlib.div_dist_chord_le_crossRatioDist`, `Arlib.dist_div_diam_le_crossRatioDist` —
  `d_K(u,v) ≥ |u−v| / |p−q| ≥ |u−v| / diam K`.
* `Arlib.mul_dist_chordStart_chordEnd` — the rearrangement of the definition that §4 of the
  paper consumes: `|u−v|·|p−q| = d_K(u,v) · |p−u| · |v−q|`.
* `Arlib.chordLow_neg_of_mem_interior`, `Arlib.one_lt_chordHigh_of_mem_interior` — the
  nondegeneracy hypotheses `a < 0` and `b > 1` hold at interior points.

## What is *not* here, and why

`d_K` is **not** a metric, and this file does not pretend otherwise.  What is a metric is the
*Hilbert metric* `log (1 + d_K(u,v))` — indeed
`1 + d_K(u,v) = (|p−v|/|p−u|) · (|q−u|/|q−v|)` is the classical projective cross ratio of
`(p, q; u, v)`, and its logarithm satisfies the triangle inequality.  That triangle inequality
is a projective-geometry argument (a Menelaus/perspectivity computation) with no support in
Mathlib v4.32, so it is **not proved here** and no definition in this file claims it.  The
pieces of "metric" that *are* true of `d_K` and are needed by the walk's analysis —
symmetry, nonnegativity, strict positivity for `u ≠ v`, and the comparison with the Euclidean
distance — are all proved below.

## Degenerate values

`d_K(u,v)` is defined by a quotient, and Lean's `x / 0 = 0`.  The denominator `|p−u|·|v−q|`
vanishes exactly when `u` or `v` is an endpoint of the chord, where the true value is `+∞`;
there `crossRatioDist` takes the junk value `0`.  Every lemma below that could be affected
carries the nondegeneracy hypotheses `chordLow < 0` and `1 < chordHigh` explicitly (they hold
whenever `u` and `v` are interior points of `K`).
-/

open Set Metric

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v : E}

/-! ### The chord in its natural coordinate -/

/-- The chord `ℓ(u,v) ∩ K` read in the affine coordinate on `ℓ(u,v)` that sends `u` to `0` and
`v` to `1`: the set of `t : ℝ` with `u + t(v − u) ∈ K`. -/
def chordParam (K : Set E) (u v : E) : Set ℝ :=
  (AffineMap.lineMap u v : ℝ → E) ⁻¹' K

lemma mem_chordParam {t : ℝ} : t ∈ chordParam K u v ↔ AffineMap.lineMap u v t ∈ K := Iff.rfl

lemma lineMap_apply' (u v : E) (t : ℝ) : (AffineMap.lineMap u v : ℝ → E) t = t • (v - u) + u := by
  simp [AffineMap.lineMap_apply]

lemma zero_mem_chordParam (hu : u ∈ K) : (0 : ℝ) ∈ chordParam K u v := by
  simpa [mem_chordParam] using hu

lemma one_mem_chordParam (hv : v ∈ K) : (1 : ℝ) ∈ chordParam K u v := by
  simpa [mem_chordParam] using hv

lemma chordParam_nonempty (hu : u ∈ K) : (chordParam K u v).Nonempty :=
  ⟨0, zero_mem_chordParam hu⟩

lemma convex_chordParam (hK : Convex ℝ K) : Convex ℝ (chordParam K u v) :=
  hK.affine_preimage (AffineMap.lineMap u v)

lemma isClosed_chordParam (hK : IsClosed K) : IsClosed (chordParam K u v) :=
  hK.preimage (AffineMap.lineMap_continuous)

/-- If `K` is bounded and `u ≠ v` then only a bounded set of parameters lands in `K`. -/
lemma isBounded_chordParam (hK : Bornology.IsBounded K) (huv : u ≠ v) :
    Bornology.IsBounded (chordParam K u v) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK
  have hvu : 0 < ‖v - u‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => huv h.symm
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨(R + ‖u‖) / ‖v - u‖, ?_⟩
  intro t ht
  have hmem : t • (v - u) + u ∈ K := by rwa [mem_chordParam, lineMap_apply'] at ht
  have hnorm : ‖t • (v - u) + u‖ ≤ R := by
    have := hR hmem
    rwa [mem_closedBall, dist_zero_right] at this
  have : |t| * ‖v - u‖ ≤ R + ‖u‖ := by
    have h1 : ‖t • (v - u)‖ ≤ ‖t • (v - u) + u‖ + ‖u‖ := by
      calc ‖t • (v - u)‖ = ‖(t • (v - u) + u) - u‖ := by abel_nf
        _ ≤ ‖t • (v - u) + u‖ + ‖u‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs] at h1
    linarith
  rw [mem_closedBall, Real.dist_eq, sub_zero, le_div_iff₀ hvu]
  exact this

lemma bddAbove_chordParam (hK : Bornology.IsBounded K) (huv : u ≠ v) :
    BddAbove (chordParam K u v) := (isBounded_chordParam hK huv).bddAbove

lemma bddBelow_chordParam (hK : Bornology.IsBounded K) (huv : u ≠ v) :
    BddBelow (chordParam K u v) := (isBounded_chordParam hK huv).bddBelow

/-- The parameter of the chord endpoint on the far side of `u`. -/
noncomputable def chordLow (K : Set E) (u v : E) : ℝ := sInf (chordParam K u v)

/-- The parameter of the chord endpoint on the far side of `v`. -/
noncomputable def chordHigh (K : Set E) (u v : E) : ℝ := sSup (chordParam K u v)

/-- `p`, the endpoint of the chord `ℓ(u,v) ∩ K` beyond `u`. -/
noncomputable def chordStart (K : Set E) (u v : E) : E :=
  AffineMap.lineMap u v (chordLow K u v)

/-- `q`, the endpoint of the chord `ℓ(u,v) ∩ K` beyond `v`. -/
noncomputable def chordEnd (K : Set E) (u v : E) : E :=
  AffineMap.lineMap u v (chordHigh K u v)

lemma chordLow_nonpos (hK : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) :
    chordLow K u v ≤ 0 :=
  csInf_le (bddBelow_chordParam hK huv) (zero_mem_chordParam hu)

lemma one_le_chordHigh (hK : Bornology.IsBounded K) (huv : u ≠ v) (hv : v ∈ K) :
    1 ≤ chordHigh K u v :=
  le_csSup (bddAbove_chordParam hK huv) (one_mem_chordParam hv)

lemma chordLow_le_chordHigh (hK : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K)
    (hv : v ∈ K) : chordLow K u v ≤ chordHigh K u v :=
  le_trans (chordLow_nonpos hK huv hu) (le_trans zero_le_one (one_le_chordHigh hK huv hv))

/-! ### The chord really is a segment with endpoints `p` and `q` -/

/-- **Chord-endpoint machinery.**  For a convex, closed, bounded `K` containing `u` and `v`, the
parameter set of the chord is exactly the closed interval between its infimum and supremum. -/
theorem chordParam_eq_Icc (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) :
    chordParam K u v = Icc (chordLow K u v) (chordHigh K u v) := by
  have hne := chordParam_nonempty (v := v) hu
  have hba := bddAbove_chordParam hKb huv
  have hbb := bddBelow_chordParam hKb huv
  apply Subset.antisymm
  · exact fun t ht => ⟨csInf_le hbb ht, le_csSup hba ht⟩
  · have hlo : chordLow K u v ∈ chordParam K u v :=
      (isClosed_chordParam hKcl).csInf_mem hne hbb
    have hhi : chordHigh K u v ∈ chordParam K u v :=
      (isClosed_chordParam hKcl).csSup_mem hne hba
    exact ((convex_chordParam hKc).ordConnected).out hlo hhi

lemma chordStart_mem (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (huv : u ≠ v) (hu : u ∈ K) (hv : v ∈ K) : chordStart K u v ∈ K := by
  have : chordLow K u v ∈ chordParam K u v := by
    rw [chordParam_eq_Icc hKc hKcl hKb huv hu]
    exact ⟨le_rfl, chordLow_le_chordHigh hKb huv hu hv⟩
  exact this

lemma chordEnd_mem (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (huv : u ≠ v) (hu : u ∈ K) (hv : v ∈ K) : chordEnd K u v ∈ K := by
  have : chordHigh K u v ∈ chordParam K u v := by
    rw [chordParam_eq_Icc hKc hKcl hKb huv hu]
    exact ⟨chordLow_le_chordHigh hKb huv hu hv, le_rfl⟩
  exact this

/-- The chord `K ∩ ℓ(u,v)` is exactly the segment `[p, q]`. -/
theorem chord_eq_segment (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (huv : u ≠ v) (hu : u ∈ K) (hv : v ∈ K) :
    K ∩ Set.range (AffineMap.lineMap u v : ℝ → E)
      = segment ℝ (chordStart K u v) (chordEnd K u v) := by
  have hle := chordLow_le_chordHigh hKb huv hu hv
  have himg : K ∩ Set.range (AffineMap.lineMap u v : ℝ → E)
      = (AffineMap.lineMap u v : ℝ → E) '' (chordParam K u v) := by
    ext z
    constructor
    · rintro ⟨hzK, t, rfl⟩
      exact ⟨t, hzK, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, t, rfl⟩
  rw [himg, chordParam_eq_Icc hKc hKcl hKb huv hu, ← segment_eq_Icc hle,
    image_segment ℝ (AffineMap.lineMap u v)]
  rfl

/-! ### Nondegeneracy at interior points -/

lemma chordLow_neg_of_mem_interior (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ interior K) : chordLow K u v < 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
  have hvu : 0 < ‖v - u‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact fun h => huv h.symm
  set t : ℝ := -(ε / (2 * ‖v - u‖)) with htdef
  have ht0 : t < 0 := by
    rw [htdef, neg_neg_iff_pos]; positivity
  have hmem : t ∈ chordParam K u v := by
    rw [mem_chordParam]
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, dist_eq_norm, lineMap_apply', add_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, htdef, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / (2 * ‖v - u‖))]
    have hne : ‖v - u‖ ≠ 0 := hvu.ne'
    have hcalc : ε / (2 * ‖v - u‖) * ‖v - u‖ = ε / 2 := by field_simp
    rw [hcalc]
    linarith
  exact lt_of_le_of_lt (csInf_le (bddBelow_chordParam hKb huv) hmem) ht0

lemma one_lt_chordHigh_of_mem_interior (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hv : v ∈ interior K) : 1 < chordHigh K u v := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hv
  have hvu : 0 < ‖v - u‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact fun h => huv h.symm
  set t : ℝ := 1 + ε / (2 * ‖v - u‖) with htdef
  have hpos : 0 < ε / (2 * ‖v - u‖) := by positivity
  have ht1 : 1 < t := by rw [htdef]; linarith
  have hmem : t ∈ chordParam K u v := by
    rw [mem_chordParam]
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, dist_eq_norm, lineMap_apply']
    have hrw : t • (v - u) + u - v = (t - 1) • (v - u) := by
      rw [sub_smul, one_smul]; abel
    rw [hrw, norm_smul, Real.norm_eq_abs, htdef, add_sub_cancel_left,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / (2 * ‖v - u‖))]
    have hne : ‖v - u‖ ≠ 0 := hvu.ne'
    have hcalc : ε / (2 * ‖v - u‖) * ‖v - u‖ = ε / 2 := by field_simp
    rw [hcalc]
    linarith
  exact lt_of_lt_of_le ht1 (le_csSup (bddAbove_chordParam hKb huv) hmem)

/-! ### Distances along the chord -/

lemma dist_lineMap_left (u v : E) (t : ℝ) :
    dist ((AffineMap.lineMap u v : ℝ → E) t) u = |t| * dist u v := by
  rw [lineMap_apply', dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    dist_eq_norm, ← norm_neg (u - v), neg_sub]

lemma dist_lineMap_right (u v : E) (t : ℝ) :
    dist v ((AffineMap.lineMap u v : ℝ → E) t) = |1 - t| * dist u v := by
  have hrw : v - (t • (v - u) + u) = (1 - t) • (v - u) := by
    rw [sub_smul, one_smul]; abel
  rw [lineMap_apply', dist_eq_norm, hrw, norm_smul, Real.norm_eq_abs, dist_eq_norm,
    ← norm_neg (u - v), neg_sub]

lemma dist_lineMap_lineMap' (u v : E) (s t : ℝ) :
    dist ((AffineMap.lineMap u v : ℝ → E) s) ((AffineMap.lineMap u v : ℝ → E) t)
      = |s - t| * dist u v := by
  have hrw : s • (v - u) + u - (t • (v - u) + u) = (s - t) • (v - u) := by
    rw [sub_smul]; abel
  rw [lineMap_apply', lineMap_apply', dist_eq_norm, hrw, norm_smul, Real.norm_eq_abs,
    dist_eq_norm, ← norm_neg (u - v), neg_sub]

/-! ### Reversing the chord

Swapping `u` and `v` reverses the affine coordinate on the line, `t ↦ 1 − t`, and hence
exchanges the two endpoints of the chord. -/

lemma lineMap_swap (u v : E) (t : ℝ) :
    (AffineMap.lineMap v u : ℝ → E) t = (AffineMap.lineMap u v : ℝ → E) (1 - t) := by
  rw [lineMap_apply', lineMap_apply', sub_smul, one_smul, smul_sub, smul_sub]
  abel

lemma chordParam_swap (K : Set E) (u v : E) :
    chordParam K v u = (fun t : ℝ => 1 - t) '' chordParam K u v := by
  ext t
  constructor
  · intro h
    rw [mem_chordParam, lineMap_swap] at h
    exact ⟨1 - t, h, by ring⟩
  · rintro ⟨s, hs, rfl⟩
    rw [mem_chordParam] at hs
    rw [mem_chordParam, lineMap_swap, show (1 : ℝ) - (1 - s) = s by ring]
    exact hs

private lemma sInf_one_sub_image {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    sInf ((fun t : ℝ => 1 - t) '' S) = 1 - sSup S := by
  obtain ⟨M, hM⟩ := hbdd
  have hbb : BddBelow ((fun t : ℝ => 1 - t) '' S) :=
    ⟨1 - M, by rintro _ ⟨s, hs, rfl⟩; have := hM hs; linarith⟩
  refine le_antisymm ?_ (le_csInf (hne.image _) ?_)
  · have h : sSup S ≤ 1 - sInf ((fun t : ℝ => 1 - t) '' S) := by
      refine csSup_le hne fun s hs => ?_
      have := csInf_le hbb (Set.mem_image_of_mem (fun t : ℝ => 1 - t) hs)
      linarith
    linarith
  · rintro _ ⟨s, hs, rfl⟩
    have := le_csSup ⟨M, hM⟩ hs
    linarith

private lemma sSup_one_sub_image {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) :
    sSup ((fun t : ℝ => 1 - t) '' S) = 1 - sInf S := by
  obtain ⟨m, hm⟩ := hbdd
  have hba : BddAbove ((fun t : ℝ => 1 - t) '' S) :=
    ⟨1 - m, by rintro _ ⟨s, hs, rfl⟩; have := hm hs; linarith⟩
  refine le_antisymm (csSup_le (hne.image _) ?_) ?_
  · rintro _ ⟨s, hs, rfl⟩
    have := csInf_le ⟨m, hm⟩ hs
    linarith
  · have h : 1 - sSup ((fun t : ℝ => 1 - t) '' S) ≤ sInf S := by
      refine le_csInf hne fun s hs => ?_
      have := le_csSup hba (Set.mem_image_of_mem (fun t : ℝ => 1 - t) hs)
      linarith
    linarith

lemma chordLow_swap (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) :
    chordLow K v u = 1 - chordHigh K u v := by
  unfold chordLow chordHigh
  rw [chordParam_swap]
  exact sInf_one_sub_image (chordParam_nonempty hu) (bddAbove_chordParam hKb huv)

lemma chordHigh_swap (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) :
    chordHigh K v u = 1 - chordLow K u v := by
  unfold chordLow chordHigh
  rw [chordParam_swap]
  exact sSup_one_sub_image (chordParam_nonempty hu) (bddBelow_chordParam hKb huv)

/-! ### The cross-ratio distance -/

/-- **The cross-ratio (Hilbert) distance** `d_K(u,v) = |u−v| |p−q| / (|p−u| |v−q|)`, where
`p` and `q` are the endpoints of the chord of `K` through `u` and `v`, in the order
`p, u, v, q`. -/
noncomputable def crossRatioDist (K : Set E) (u v : E) : ℝ :=
  dist u v * dist (chordStart K u v) (chordEnd K u v) /
    (dist (chordStart K u v) u * dist v (chordEnd K u v))

/-- **The closed form of `d_K` in the chord coordinate.**  With `a = chordLow ≤ 0` and
`b = chordHigh ≥ 1`, all four Euclidean lengths in the definition are multiples of `|u−v|`,
which cancels, leaving `d_K(u,v) = (b − a) / ((−a)(b − 1))`.

No nondegeneracy is needed: when `a = 0` or `b = 1` both sides are `0` because Lean's
division by zero is `0`. -/
theorem crossRatioDist_eq_param (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) :
    crossRatioDist K u v
      = (chordHigh K u v - chordLow K u v) /
          (-chordLow K u v * (chordHigh K u v - 1)) := by
  have ha : chordLow K u v ≤ 0 := chordLow_nonpos hKb huv hu
  have hb : 1 ≤ chordHigh K u v := one_le_chordHigh hKb huv hv
  have hd : (0 : ℝ) < dist u v := dist_pos.mpr huv
  have hdd : dist u v * dist u v ≠ 0 := by positivity
  unfold crossRatioDist chordStart chordEnd
  rw [dist_lineMap_lineMap', dist_lineMap_left, dist_lineMap_right,
    abs_of_nonpos (by linarith : chordLow K u v - chordHigh K u v ≤ 0),
    abs_of_nonpos ha, abs_of_nonpos (by linarith : (1:ℝ) - chordHigh K u v ≤ 0)]
  rw [show dist u v * (-(chordLow K u v - chordHigh K u v) * dist u v)
        = dist u v * dist u v * (chordHigh K u v - chordLow K u v) by ring,
    show -chordLow K u v * dist u v * (-(1 - chordHigh K u v) * dist u v)
        = dist u v * dist u v * (-chordLow K u v * (chordHigh K u v - 1)) by ring,
    mul_div_mul_left _ _ hdd]

/-- **Symmetry.**  Swapping `u` and `v` reverses the chord, exchanging `p` with `q`, and the
defining expression is invariant. -/
theorem crossRatioDist_comm (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) : crossRatioDist K u v = crossRatioDist K v u := by
  rw [crossRatioDist_eq_param hKb huv hu hv,
    crossRatioDist_eq_param hKb huv.symm hv hu,
    chordLow_swap hKb huv hu, chordHigh_swap hKb huv hu]
  ring_nf

lemma crossRatioDist_nonneg (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) : 0 ≤ crossRatioDist K u v := by
  have ha : chordLow K u v ≤ 0 := chordLow_nonpos hKb huv hu
  have hb : 1 ≤ chordHigh K u v := one_le_chordHigh hKb huv hv
  rw [crossRatioDist_eq_param hKb huv hu hv]
  apply div_nonneg (by linarith)
  exact mul_nonneg (by linarith) (by linarith)

/-- Away from the boundary (`a < 0` and `b > 1`, e.g. for interior points), `d_K(u,v) > 0`
for `u ≠ v`. -/
lemma crossRatioDist_pos (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) (hv : v ∈ K)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v) : 0 < crossRatioDist K u v := by
  rw [crossRatioDist_eq_param hKb huv hu hv]
  exact div_pos (by linarith) (mul_pos (by linarith) (by linarith))

/-- The rearrangement of the definition consumed by §4 of the paper:
`|u−v| · |p−q| = d_K(u,v) · |p−u| · |v−q|`. -/
theorem mul_dist_chordStart_chordEnd (huv : u ≠ v)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v) :
    dist u v * dist (chordStart K u v) (chordEnd K u v)
      = crossRatioDist K u v * (dist (chordStart K u v) u * dist v (chordEnd K u v)) := by
  have hd : (0 : ℝ) < dist u v := dist_pos.mpr huv
  have h1 : dist (chordStart K u v) u = -chordLow K u v * dist u v := by
    unfold chordStart; rw [dist_lineMap_left, abs_of_nonpos ha.le]
  have h2 : dist v (chordEnd K u v) = (chordHigh K u v - 1) * dist u v := by
    unfold chordEnd
    rw [dist_lineMap_right, abs_of_nonpos (by linarith : (1:ℝ) - chordHigh K u v ≤ 0)]
    ring
  have hne : dist (chordStart K u v) u * dist v (chordEnd K u v) ≠ 0 := by
    refine ne_of_gt ?_
    rw [h1, h2]
    exact mul_pos (mul_pos (by linarith) hd) (mul_pos (by linarith) hd)
  unfold crossRatioDist
  rw [div_mul_cancel₀ _ hne]

/-- `d_K(u,v) ≥ |u−v| / |p−q|`: the cross-ratio distance dominates the Euclidean distance
measured in units of the chord length. -/
theorem div_dist_chord_le_crossRatioDist (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v) :
    dist u v / dist (chordStart K u v) (chordEnd K u v) ≤ crossRatioDist K u v := by
  have hd : (0 : ℝ) < dist u v := dist_pos.mpr huv
  have hpq : dist (chordStart K u v) (chordEnd K u v)
      = (chordHigh K u v - chordLow K u v) * dist u v := by
    unfold chordStart chordEnd
    rw [dist_lineMap_lineMap',
      abs_of_nonpos (by linarith : chordLow K u v - chordHigh K u v ≤ 0)]
    ring
  rw [hpq, crossRatioDist_eq_param hKb huv hu hv]
  set a := chordLow K u v with hadef
  set b := chordHigh K u v with hbdef
  have hba : (0 : ℝ) < b - a := by linarith
  have hden : (0 : ℝ) < -a * (b - 1) := mul_pos (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by positivity) hden]
  have key : -a * (b - 1) ≤ (b - a) * (b - a) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hd.le]

/-- `d_K(u,v) ≥ |u−v| / diam K`. -/
theorem dist_div_diam_le_crossRatioDist (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (huv : u ≠ v) (hu : u ∈ K) (hv : v ∈ K)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v) :
    dist u v / Metric.diam K ≤ crossRatioDist K u v := by
  refine le_trans ?_ (div_dist_chord_le_crossRatioDist hKb huv hu hv ha hb)
  have hd : (0 : ℝ) < dist u v := dist_pos.mpr huv
  have hp := chordStart_mem hKc hKcl hKb huv hu hv
  have hq := chordEnd_mem hKc hKcl hKb huv hu hv
  have hle : dist (chordStart K u v) (chordEnd K u v) ≤ Metric.diam K :=
    Metric.dist_le_diam_of_mem hKb hp hq
  have hpos : (0 : ℝ) < dist (chordStart K u v) (chordEnd K u v) := by
    have hpq : dist (chordStart K u v) (chordEnd K u v)
        = (chordHigh K u v - chordLow K u v) * dist u v := by
      unfold chordStart chordEnd
      rw [dist_lineMap_lineMap',
        abs_of_nonpos (by linarith : chordLow K u v - chordHigh K u v ≤ 0)]
      ring
    rw [hpq]
    exact mul_pos (by linarith) hd
  exact div_le_div_of_nonneg_left hd.le hpos hle

/-! ### Axiom profile -/

section AxiomCheck

#print axioms mem_chordParam
#print axioms lineMap_apply'
#print axioms zero_mem_chordParam
#print axioms one_mem_chordParam
#print axioms chordParam_nonempty
#print axioms convex_chordParam
#print axioms isClosed_chordParam
#print axioms isBounded_chordParam
#print axioms bddAbove_chordParam
#print axioms bddBelow_chordParam
#print axioms chordLow_nonpos
#print axioms one_le_chordHigh
#print axioms chordLow_le_chordHigh
#print axioms chordParam_eq_Icc
#print axioms chordStart_mem
#print axioms chordEnd_mem
#print axioms chord_eq_segment
#print axioms chordLow_neg_of_mem_interior
#print axioms one_lt_chordHigh_of_mem_interior
#print axioms dist_lineMap_left
#print axioms dist_lineMap_right
#print axioms dist_lineMap_lineMap'
#print axioms lineMap_swap
#print axioms chordParam_swap
#print axioms chordLow_swap
#print axioms chordHigh_swap
#print axioms crossRatioDist_eq_param
#print axioms crossRatioDist_comm
#print axioms crossRatioDist_nonneg
#print axioms crossRatioDist_pos
#print axioms mul_dist_chordStart_chordEnd
#print axioms div_dist_chord_le_crossRatioDist
#print axioms dist_div_diam_le_crossRatioDist

end AxiomCheck

end Arlib
