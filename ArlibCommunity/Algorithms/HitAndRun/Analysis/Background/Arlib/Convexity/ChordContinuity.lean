/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.IsoConcaveWeight

/-!
# Continuity of the chord endpoints and of the cross-ratio distance

`Arlib/Convexity/CrossRatio.lean` defines the chord of a convex body `K` through two points
`u ≠ v` in the affine coordinate `t ↦ u + t(v − u)`, its endpoints
`Arlib.chordLow ≤ 0` and `1 ≤ Arlib.chordHigh`, and the cross-ratio distance
`Arlib.crossRatioDist`.  Until this file the repository had **no** continuity statement about
any of them.

This file supplies the missing modulus and spends it on one binder.
-/

open Set Metric

namespace Arlib

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-! ### The cone lemma -/

/-- **The cone lemma.**  If `K` is convex, contains the closed ball `B(x, σ)` and the point `y`,
then it contains the ball of radius `(1 − λ)σ` around the point `x + λ(y − x)` of the segment:
the convex hull of `{y} ∪ B(x,σ)` is a cone that shrinks linearly. -/
theorem closedBall_lineMap_subset (hKc : Convex ℝ K) {x y : E} {σ : ℝ}
    (hball : Metric.closedBall x σ ⊆ K) (hy : y ∈ K) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Metric.closedBall ((AffineMap.lineMap x y : ℝ → E) lam) ((1 - lam) * σ) ⊆ K := by
  rcases eq_or_lt_of_le hlam1 with rfl | hlt
  · intro z hz
    have : dist z ((AffineMap.lineMap x y : ℝ → E) 1) ≤ 0 := by
      simpa using hz
    have hz' : z = (AffineMap.lineMap x y : ℝ → E) 1 := by
      have := dist_nonneg (x := z) (y := (AffineMap.lineMap x y : ℝ → E) 1)
      have h0 : dist z ((AffineMap.lineMap x y : ℝ → E) 1) = 0 := le_antisymm ‹_› this
      exact dist_eq_zero.mp h0
    rw [hz']
    simpa using hy
  · have hpos : (0 : ℝ) < 1 - lam := by linarith
    intro z hz
    have hzd : dist z ((AffineMap.lineMap x y : ℝ → E) lam) ≤ (1 - lam) * σ :=
      Metric.mem_closedBall.mp hz
    set w : E := z - (AffineMap.lineMap x y : ℝ → E) lam with hwdef
    have hwn : ‖w‖ ≤ (1 - lam) * σ := by rwa [hwdef, ← dist_eq_norm]
    set x' : E := x + (1 - lam)⁻¹ • w with hx'def
    have hx'K : x' ∈ K := by
      refine hball (Metric.mem_closedBall.mpr ?_)
      rw [hx'def, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos)]
      rw [inv_mul_le_iff₀ hpos]
      linarith [hwn]
    have hcomb : (1 - lam) • x' + lam • y = z := by
      rw [hx'def, hwdef, lineMap_apply', smul_add, smul_inv_smul₀ (ne_of_gt hpos)]
      module
    have := hKc hx'K hy (le_of_lt hpos) hlam0 (by ring)
    rwa [hcomb] at this

#print axioms closedBall_lineMap_subset

set_option linter.unusedSectionVars false in
/-- An interior point has a *closed* ball inside `K`. -/
lemma exists_closedBall_subset_of_mem_interior {u : E} (hu : u ∈ interior K) :
    ∃ σ : ℝ, 0 < σ ∧ Metric.closedBall u σ ⊆ K := by
  obtain ⟨σ, hσ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
  refine ⟨σ / 2, by linarith, fun z hz => interior_subset (hball ?_)⟩
  rw [Metric.mem_closedBall] at hz
  exact Metric.mem_ball.mpr (by linarith)

#print axioms exists_closedBall_subset_of_mem_interior

/-- Moving the two base points of a line moves the point at a fixed parameter by a controlled
amount.  This is the only norm estimate the continuity proof needs. -/
lemma dist_lineMap_lineMap_le (u v u' v' : E) (t : ℝ) :
    dist ((AffineMap.lineMap u' v' : ℝ → E) t) ((AffineMap.lineMap u v : ℝ → E) t)
      ≤ |1 - t| * dist u' u + |t| * dist v' v := by
  rw [lineMap_apply', lineMap_apply', dist_eq_norm]
  have hrw : t • (v' - u') + u' - (t • (v - u) + u) = (1 - t) • (u' - u) + t • (v' - v) := by
    module
  rw [hrw]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← dist_eq_norm, ← dist_eq_norm]

#print axioms dist_lineMap_lineMap_le

/-! ### The modulus for `chordHigh` -/

/-- **Lower half of the modulus.**  `chordHigh` cannot drop by more than `ε` under a small
perturbation of the two base points, provided the first one is interior.

The witness is explicit: take the parameter `t = max 0 (b − ε/2)` just short of the chord
endpoint `b`, put the chord endpoint `y = u + b(v − u)` and the ball `B(u,σ) ⊆ K` into
`Arlib.closedBall_lineMap_subset`, and read off that `K` contains a ball of the *fixed* radius
`(1 − t/b)σ` around `u + t(v − u)`. -/
theorem exists_sub_lt_chordHigh (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {u v : E} (hu : u ∈ interior K) (huv : u ≠ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u' v' : E, dist u' u < δ → dist v' v < δ →
      chordHigh K u v - ε < chordHigh K u' v' := by
  obtain ⟨σ, hσ, hball⟩ := exists_closedBall_subset_of_mem_interior hu
  have huK : u ∈ K := interior_subset hu
  have hduv : 0 < dist u v := dist_pos.mpr huv
  set b := chordHigh K u v with hbdef
  have hb0 : 0 ≤ b := le_csSup (bddAbove_chordParam hKb huv) (zero_mem_chordParam huK)
  have hbpos : 0 < b := by
    have hs : (0 : ℝ) < σ / (2 * dist u v) := by positivity
    have hmem : σ / (2 * dist u v) ∈ chordParam K u v := by
      rw [mem_chordParam]
      refine hball (Metric.mem_closedBall.mpr ?_)
      rw [dist_lineMap_left, abs_of_nonneg hs.le]
      have : σ / (2 * dist u v) * dist u v = σ / 2 := by field_simp
      rw [this]; linarith
    exact lt_of_lt_of_le hs (le_csSup (bddAbove_chordParam hKb huv) hmem)
  have hbmem : (AffineMap.lineMap u v : ℝ → E) b ∈ K := by
    have hIcc := chordParam_eq_Icc hKc hKcl hKb huv huK
    have ha0 : chordLow K u v ≤ 0 := chordLow_nonpos hKb huv huK
    have : b ∈ chordParam K u v := by rw [hIcc]; exact ⟨le_trans ha0 hb0, le_rfl⟩
    exact this
  set t := max 0 (b - ε / 2) with htdef
  have ht0 : 0 ≤ t := le_max_left _ _
  have htb : t < b := max_lt hbpos (by linarith)
  have htgt : b - ε < t := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  set lam := t / b with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam < 1 := (div_lt_one hbpos).mpr htb
  set r := (1 - lam) * σ with hrdef
  have hr : 0 < r := by rw [hrdef]; have : 0 < 1 - lam := by linarith
                        positivity
  have hlb : lam * b = t := by rw [hlamdef]; field_simp
  have heq : (AffineMap.lineMap u ((AffineMap.lineMap u v : ℝ → E) b) : ℝ → E) lam
      = (AffineMap.lineMap u v : ℝ → E) t := by
    rw [lineMap_apply', lineMap_apply', lineMap_apply', ← hlb]
    module
  have key : Metric.closedBall ((AffineMap.lineMap u v : ℝ → E) t) r ⊆ K := by
    have := closedBall_lineMap_subset hKc hball hbmem hlam0 hlam1.le
    rwa [heq] at this
  refine ⟨min (dist u v / 2) (r / (2 * (1 + 2 * t))), by positivity, ?_⟩
  intro u' v' hu' hv'
  have hδ1 : dist u' u < dist u v / 2 := lt_of_lt_of_le hu' (min_le_left _ _)
  have hδ1' : dist v' v < dist u v / 2 := lt_of_lt_of_le hv' (min_le_left _ _)
  have hδ2 : dist u' u < r / (2 * (1 + 2 * t)) := lt_of_lt_of_le hu' (min_le_right _ _)
  have hδ2' : dist v' v < r / (2 * (1 + 2 * t)) := lt_of_lt_of_le hv' (min_le_right _ _)
  have hu'v' : u' ≠ v' := by
    have h1 : dist u v ≤ dist u u' + (dist u' v' + dist v' v) :=
      le_trans (dist_triangle u u' v) (by gcongr; exact dist_triangle u' v' v)
    rw [dist_comm u u'] at h1
    exact dist_pos.mp (by linarith)
  have hmem : t ∈ chordParam K u' v' := by
    rw [mem_chordParam]
    refine key (Metric.mem_closedBall.mpr ?_)
    have hbd := dist_lineMap_lineMap_le u v u' v' t
    have habs1 : |1 - t| ≤ 1 + t := abs_le.mpr ⟨by linarith, by linarith⟩
    have habs2 : |t| = t := abs_of_nonneg ht0
    have hpos2 : (0 : ℝ) < 2 * (1 + 2 * t) := by linarith
    have hkey : (1 + 2 * t) * (r / (2 * (1 + 2 * t))) = r / 2 := by field_simp
    have : |1 - t| * dist u' u + |t| * dist v' v ≤ (1 + 2 * t) * (r / (2 * (1 + 2 * t))) := by
      rw [habs2]
      have e1 : |1 - t| * dist u' u ≤ (1 + t) * (r / (2 * (1 + 2 * t))) := by
        apply mul_le_mul habs1 hδ2.le dist_nonneg (by linarith)
      have e2 : t * dist v' v ≤ t * (r / (2 * (1 + 2 * t))) := by
        exact mul_le_mul_of_nonneg_left hδ2'.le ht0
      nlinarith [e1, e2]
    rw [hkey] at this
    linarith [hbd, this]
  exact lt_of_lt_of_le htgt (le_csSup (bddAbove_chordParam hKb hu'v') hmem)

#print axioms exists_sub_lt_chordHigh

/-- **Upper half of the modulus.**  `chordHigh` cannot jump up by more than `ε` under a small
perturbation of the two base points, provided the first one is interior.

Same cone, run at the *perturbed* pair: if `chordHigh K u' v'` reached `b + ε` then `K` would
contain a ball of the fixed radius `(1 − s/(b+ε))·σ/2` around `u' + s(v' − u')` with
`s = b + ε/2`, hence — for `u'`, `v'` close enough — the point `u + s(v − u)`, which is beyond
the chord of `K` through `u` and `v`. -/
theorem exists_chordHigh_lt_add (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {u v : E} (hu : u ∈ interior K) (huv : u ≠ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u' v' : E, dist u' u < δ → dist v' v < δ →
      chordHigh K u' v' < chordHigh K u v + ε := by
  obtain ⟨σ, hσ, hball⟩ := exists_closedBall_subset_of_mem_interior hu
  have huK : u ∈ K := interior_subset hu
  have hduv : 0 < dist u v := dist_pos.mpr huv
  set b := chordHigh K u v with hbdef
  have hb0 : 0 ≤ b := le_csSup (bddAbove_chordParam hKb huv) (zero_mem_chordParam huK)
  set s := b + ε / 2 with hsdef
  set T := b + ε with hTdef
  have hs0 : 0 < s := by positivity
  have hsT : s < T := by rw [hsdef, hTdef]; linarith
  have hT0 : 0 < T := lt_trans hs0 hsT
  have hwnotK : (AffineMap.lineMap u v : ℝ → E) s ∉ K := by
    intro hcon
    have hmem : s ∈ chordParam K u v := hcon
    have hle : s ≤ b := le_csSup (bddAbove_chordParam hKb huv) hmem
    rw [hsdef] at hle
    linarith
  set lam := s / T with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam < 1 := (div_lt_one hT0).mpr hsT
  set ρ := (1 - lam) * (σ / 2) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    have : 0 < 1 - lam := by linarith
    positivity
  refine ⟨min (σ / 2) (min (dist u v / 2) (ρ / (2 * (1 + 2 * s)))), by positivity, ?_⟩
  intro u' v' hu' hv'
  have hδ0 : dist u' u < σ / 2 := lt_of_lt_of_le hu' (min_le_left _ _)
  have hδ0' : dist v' v < σ / 2 := lt_of_lt_of_le hv' (min_le_left _ _)
  have hδ1 : dist u' u < dist u v / 2 :=
    lt_of_lt_of_le hu' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1' : dist v' v < dist u v / 2 :=
    lt_of_lt_of_le hv' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ2 : dist u' u < ρ / (2 * (1 + 2 * s)) :=
    lt_of_lt_of_le hu' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ2' : dist v' v < ρ / (2 * (1 + 2 * s)) :=
    lt_of_lt_of_le hv' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hball' : Metric.closedBall u' (σ / 2) ⊆ K := by
    intro z hz
    refine hball (Metric.mem_closedBall.mpr ?_)
    have h1 : dist z u ≤ dist z u' + dist u' u := dist_triangle _ _ _
    have h2 : dist z u' ≤ σ / 2 := Metric.mem_closedBall.mp hz
    linarith
  have hu'K : u' ∈ K := hball' (Metric.mem_closedBall_self (by linarith))
  have hu'v' : u' ≠ v' := by
    have h1 : dist u v ≤ dist u u' + (dist u' v' + dist v' v) :=
      le_trans (dist_triangle u u' v) (by gcongr; exact dist_triangle u' v' v)
    rw [dist_comm u u'] at h1
    exact dist_pos.mp (by linarith)
  by_contra hcon
  rw [not_lt] at hcon
  have hTmem : (AffineMap.lineMap u' v' : ℝ → E) T ∈ K := by
    have hIcc := chordParam_eq_Icc hKc hKcl hKb hu'v' hu'K
    have ha0 : chordLow K u' v' ≤ 0 := chordLow_nonpos hKb hu'v' hu'K
    have : T ∈ chordParam K u' v' := by
      rw [hIcc]; exact ⟨by linarith, hcon⟩
    exact this
  have hlT : lam * T = s := by rw [hlamdef]; field_simp
  have heq : (AffineMap.lineMap u' ((AffineMap.lineMap u' v' : ℝ → E) T) : ℝ → E) lam
      = (AffineMap.lineMap u' v' : ℝ → E) s := by
    rw [lineMap_apply', lineMap_apply', lineMap_apply', ← hlT]
    module
  have key : Metric.closedBall ((AffineMap.lineMap u' v' : ℝ → E) s) ρ ⊆ K := by
    have := closedBall_lineMap_subset hKc hball' hTmem hlam0 hlam1.le
    rwa [heq] at this
  refine hwnotK (key (Metric.mem_closedBall.mpr ?_))
  rw [dist_comm]
  have hbd := dist_lineMap_lineMap_le u v u' v' s
  have habs1 : |1 - s| ≤ 1 + s := abs_le.mpr ⟨by linarith, by linarith⟩
  have habs2 : |s| = s := abs_of_nonneg hs0.le
  have hkey : (1 + 2 * s) * (ρ / (2 * (1 + 2 * s))) = ρ / 2 := by field_simp
  have hchain : |1 - s| * dist u' u + |s| * dist v' v
      ≤ (1 + 2 * s) * (ρ / (2 * (1 + 2 * s))) := by
    rw [habs2]
    have e1 : |1 - s| * dist u' u ≤ (1 + s) * (ρ / (2 * (1 + 2 * s))) :=
      mul_le_mul habs1 hδ2.le dist_nonneg (by linarith)
    have e2 : s * dist v' v ≤ s * (ρ / (2 * (1 + 2 * s))) :=
      mul_le_mul_of_nonneg_left hδ2'.le hs0.le
    nlinarith [e1, e2]
  rw [hkey] at hchain
  linarith [hbd, hchain]

#print axioms exists_chordHigh_lt_add

/-! ### Continuity of the chord endpoints

The set of admissible pairs,

    `{p : E × E | p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2}`,

is **open**, so `ContinuousOn` on it is `ContinuousAt` at each of its points. -/

set_option linter.unusedSectionVars false in
/-- The set of pairs of distinct interior points is open. -/
lemma isOpen_interiorPair (K : Set E) :
    IsOpen {p : E × E | p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2} := by
  have h1 : IsOpen {p : E × E | p.1 ∈ interior K} := isOpen_interior.preimage continuous_fst
  have h2 : IsOpen {p : E × E | p.2 ∈ interior K} := isOpen_interior.preimage continuous_snd
  have h3 : IsOpen {p : E × E | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact h1.inter (h2.inter h3)

#print axioms isOpen_interiorPair

/-- **`chordHigh` is continuous at a pair whose first point is interior.**  Only the first
point has to be interior: the perturbation argument places its ball at `u`. -/
theorem continuousAt_chordHigh (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {p : E × E} (hu : p.1 ∈ interior K) (huv : p.1 ≠ p.2) :
    ContinuousAt (fun q : E × E => chordHigh K q.1 q.2) p := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_sub_lt_chordHigh hKc hKcl hKb hu huv hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_chordHigh_lt_add hKc hKcl hKb hu huv hε
  refine ⟨min δ₁ δ₂, by positivity, ?_⟩
  rintro ⟨u', v'⟩ hq
  rw [Prod.dist_eq] at hq
  have hpu : dist u' p.1 < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hq
  have hpv : dist v' p.2 < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hq
  have hA := h₁ u' v' (lt_of_lt_of_le hpu (min_le_left _ _))
    (lt_of_lt_of_le hpv (min_le_left _ _))
  have hB := h₂ u' v' (lt_of_lt_of_le hpu (min_le_right _ _))
    (lt_of_lt_of_le hpv (min_le_right _ _))
  simp only [Real.dist_eq, abs_lt]
  constructor <;> linarith

#print axioms continuousAt_chordHigh

/-- **`chordLow` is continuous at a pair of distinct interior points.**  Read off from
`Arlib.chordHigh_swap`'s companion `Arlib.chordLow_swap`: `a_K(u,v) = 1 − b_K(v,u)`. -/
theorem continuousAt_chordLow (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {p : E × E} (hu : p.1 ∈ interior K) (hv : p.2 ∈ interior K)
    (huv : p.1 ≠ p.2) :
    ContinuousAt (fun q : E × E => chordLow K q.1 q.2) p := by
  have hswapc : ContinuousAt (fun q : E × E => chordHigh K q.2 q.1) p := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := exists_sub_lt_chordHigh hKc hKcl hKb hv (Ne.symm huv) hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_chordHigh_lt_add hKc hKcl hKb hv (Ne.symm huv) hε
    refine ⟨min δ₁ δ₂, by positivity, ?_⟩
    rintro ⟨u', v'⟩ hq
    rw [Prod.dist_eq] at hq
    have hpu : dist u' p.1 < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hq
    have hpv : dist v' p.2 < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hq
    have hA := h₁ v' u' (lt_of_lt_of_le hpv (min_le_left _ _))
      (lt_of_lt_of_le hpu (min_le_left _ _))
    have hB := h₂ v' u' (lt_of_lt_of_le hpv (min_le_right _ _))
      (lt_of_lt_of_le hpu (min_le_right _ _))
    simp only [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hconst : ContinuousAt (fun _ : E × E => (1 : ℝ)) p := continuousAt_const
  refine ContinuousAt.congr (hconst.sub hswapc) ?_
  filter_upwards [(isOpen_interiorPair K).mem_nhds ⟨hu, hv, huv⟩] with q hq
  exact (chordLow_swap hKb (Ne.symm hq.2.2) (interior_subset hq.2.1)).symm

#print axioms continuousAt_chordLow

/-- **`chordHigh` is continuous on pairs of distinct interior points.** -/
theorem continuousOn_chordHigh (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) :
    ContinuousOn (fun p : E × E => chordHigh K p.1 p.2)
      {p : E × E | p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2} :=
  fun _ hp => (continuousAt_chordHigh hKc hKcl hKb hp.1 hp.2.2).continuousWithinAt

#print axioms continuousOn_chordHigh

/-- **`chordLow` is continuous on pairs of distinct interior points.** -/
theorem continuousOn_chordLow (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) :
    ContinuousOn (fun p : E × E => chordLow K p.1 p.2)
      {p : E × E | p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2} :=
  fun _ hp => (continuousAt_chordLow hKc hKcl hKb hp.1 hp.2.1 hp.2.2).continuousWithinAt

#print axioms continuousOn_chordLow

/-! ### Continuity of the cross-ratio distance -/

/-- **`crossRatioDist` is continuous at a pair of distinct interior points.**

`Arlib.crossRatioDist_eq_param` turns `d_K` into `(b − a)/((−a)(b − 1))` on the whole
neighbourhood, and at interior points `a < 0 < 1 < b` keeps the denominator away from `0`. -/
theorem continuousAt_crossRatioDist (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {p : E × E} (hu : p.1 ∈ interior K) (hv : p.2 ∈ interior K)
    (huv : p.1 ≠ p.2) :
    ContinuousAt (fun q : E × E => crossRatioDist K q.1 q.2) p := by
  have ha := continuousAt_chordLow hKc hKcl hKb hu hv huv
  have hb := continuousAt_chordHigh hKc hKcl hKb hu huv
  have hnum : ContinuousAt (fun q : E × E => chordHigh K q.1 q.2 - chordLow K q.1 q.2) p :=
    hb.sub ha
  have hden : ContinuousAt
      (fun q : E × E => -chordLow K q.1 q.2 * (chordHigh K q.1 q.2 - 1)) p :=
    ha.neg.mul (hb.sub continuousAt_const)
  have hane : chordLow K p.1 p.2 < 0 := chordLow_neg_of_mem_interior hKb huv hu
  have hbne : 1 < chordHigh K p.1 p.2 := one_lt_chordHigh_of_mem_interior hKb huv hv
  have hd0 : -chordLow K p.1 p.2 * (chordHigh K p.1 p.2 - 1) ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) (by linarith))
  refine ContinuousAt.congr (hnum.div hden hd0) ?_
  filter_upwards [(isOpen_interiorPair K).mem_nhds ⟨hu, hv, huv⟩] with q hq
  exact (crossRatioDist_eq_param hKb hq.2.2 (interior_subset hq.1)
    (interior_subset hq.2.1)).symm

#print axioms continuousAt_crossRatioDist

/-- **`crossRatioDist` is continuous on pairs of distinct interior points.** -/
theorem continuousOn_crossRatioDist (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) :
    ContinuousOn (fun p : E × E => crossRatioDist K p.1 p.2)
      {p : E × E | p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2} :=
  fun _ hp => (continuousAt_crossRatioDist hKc hKcl hKb hp.1 hp.2.1 hp.2.2).continuousWithinAt

#print axioms continuousOn_crossRatioDist

end General

/-! ### Two scalar estimates

Both are elementary, and both are stated separately only because the assembly below would
otherwise carry a case split inside a 100-line proof. -/

section Scalar

/-- **Clamping into `[a,b]` costs at most the endpoint error.**  If `r` lies in `[a', b']` and
each endpoint of `[a,b]` is within `η` of the corresponding endpoint of `[a', b']`, then
`r` is within `η` of its clamp `max a (min r b)`.  (`a ≤ 0 ≤ b` is what makes the clamp
land in `[a,b]`.) -/
theorem abs_sub_clamp_le {a b a' b' r η : ℝ} (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    (hr1 : a' ≤ r) (hr2 : r ≤ b') (hA : |a - a'| ≤ η) (hB : |b - b'| ≤ η) :
    |r - max a (min r b)| ≤ η := by
  have hη : 0 ≤ η := le_trans (abs_nonneg _) hA
  have hA' : a - a' ≤ η := le_trans (le_abs_self _) hA
  have hB' : b' - b ≤ η := by
    have h := le_abs_self (b' - b)
    rw [abs_sub_comm] at h
    linarith
  rcases le_total r b with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total a r with h2 | h2
    · rw [max_eq_right h2, sub_self, abs_zero]
      exact hη
    · rw [max_eq_left h2, abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_right h1, max_eq_right (le_trans ha0 hb0), abs_of_nonneg (by linarith)]
    linarith

#print axioms abs_sub_clamp_le

/-- `min 1 ·` is `1`-Lipschitz. -/
theorem abs_min_one_sub_le (x y : ℝ) : |min 1 x - min 1 y| ≤ |x - y| := by
  have key : ∀ s t : ℝ, min 1 s - min 1 t ≤ |s - t| := by
    intro s t
    rcases le_total 1 t with h | h
    · have h1 : min 1 t = 1 := min_eq_left h
      have h2 : min 1 s ≤ 1 := min_le_left _ _
      have h3 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
      linarith
    · have h1 : min 1 t = t := min_eq_right h
      have h2 : min 1 s ≤ s := min_le_right _ _
      have h3 : s - t ≤ |s - t| := le_abs_self _
      linarith
  rw [abs_sub_le_iff]
  refine ⟨key x y, ?_⟩
  rw [abs_sub_comm]
  exact key y x

#print axioms abs_min_one_sub_le

end Scalar

/-! ### Moving a point of one chord onto a nearby chord

The hypothesis of `htrans` bounds `g` at points of the chord through `u₀, v₀`; the conclusion
asks for a bound at points of the chord through the *perturbed* pair `u, v`.  The bridge is:
read the point in the chord coordinate, **clamp** the parameter into the unperturbed chord's
parameter interval, and note that clamping moves it by at most the endpoint error `η`. -/

section Chord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- **The chord-to-chord transfer.**  A point `x ∈ K` on the line through `u, v` is within
`|1−r|·|u−u₀| + |r|·|v−v₀| + η·|u₀−v₀|` of a point of `K` on the line through `u₀, v₀`,
where `r` is `x`'s chord parameter and `η` bounds the movement of both chord endpoints. -/
theorem exists_mem_chord_dist_le (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) {u v u₀ v₀ x : E} {r η : ℝ}
    (huv : u ≠ v) (hu₀v₀ : u₀ ≠ v₀) (hu₀K : u₀ ∈ K) (hv₀K : v₀ ∈ K)
    (hxK : x ∈ K) (hx : x = (AffineMap.lineMap u v : ℝ → E) r)
    (hA : |chordLow K u₀ v₀ - chordLow K u v| ≤ η)
    (hB : |chordHigh K u₀ v₀ - chordHigh K u v| ≤ η) :
    ∃ s : ℝ, (AffineMap.lineMap u₀ v₀ : ℝ → E) s ∈ K ∧
      dist x ((AffineMap.lineMap u₀ v₀ : ℝ → E) s)
        ≤ |1 - r| * dist u u₀ + |r| * dist v v₀ + η * dist u₀ v₀ := by
  have hrmem : r ∈ chordParam K u v := by rw [mem_chordParam, ← hx]; exact hxK
  have hra : chordLow K u v ≤ r := csInf_le (bddBelow_chordParam hKb huv) hrmem
  have hrb : r ≤ chordHigh K u v := le_csSup (bddAbove_chordParam hKb huv) hrmem
  have ha0 : chordLow K u₀ v₀ ≤ 0 := chordLow_nonpos hKb hu₀v₀ hu₀K
  have hb1 : 1 ≤ chordHigh K u₀ v₀ := one_le_chordHigh hKb hu₀v₀ hv₀K
  refine ⟨max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀)), ?_, ?_⟩
  · have hmem : max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀)) ∈ chordParam K u₀ v₀ := by
      rw [chordParam_eq_Icc hKc hKcl hKb hu₀v₀ hu₀K]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    exact hmem
  · have hclamp : |r - max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀))| ≤ η :=
      abs_sub_clamp_le ha0 (by linarith) hra hrb hA hB
    have h1 : dist x ((AffineMap.lineMap u₀ v₀ : ℝ → E) r)
        ≤ |1 - r| * dist u u₀ + |r| * dist v v₀ := by
      rw [hx]; exact dist_lineMap_lineMap_le u₀ v₀ u v r
    have h2 : dist ((AffineMap.lineMap u₀ v₀ : ℝ → E) r)
        ((AffineMap.lineMap u₀ v₀ : ℝ → E)
          (max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀))))
        = |r - max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀))| * dist u₀ v₀ :=
      dist_lineMap_lineMap' u₀ v₀ _ _
    have h3 := dist_triangle x ((AffineMap.lineMap u₀ v₀ : ℝ → E) r)
      ((AffineMap.lineMap u₀ v₀ : ℝ → E)
        (max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀))))
    have h4 : |r - max (chordLow K u₀ v₀) (min r (chordHigh K u₀ v₀))| * dist u₀ v₀
        ≤ η * dist u₀ v₀ := mul_le_mul_of_nonneg_right hclamp dist_nonneg
    rw [h2] at h3
    linarith

#print axioms exists_mem_chord_dist_le

end Chord

/-! ### The `htrans` binder, discharged

`Arlib.conductance_hitAndRun_ge_of_transfer_of_localization`
(`Arlib/Convexity/IsoConcaveWeight.lean`) carries three binders.  The statement below is the
second of them, `htrans`, **copied verbatim** from that declaration and proved. -/

section Transfer

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

set_option maxHeartbeats 1000000 in
/-- **The chord transfer.**  For a continuous `g` on a convex body `K` satisfying the chord
bound on `U₁ × U₂`, compacts `C₁ ⊆ U₁` and `C₂ ⊆ U₂` strictly inside `interior K`, and any
`ε > 0`, there is a radius `ρ > 0` such that the chord bound still holds, with `+ ε` of slack,
for every pair within `ρ` of `C₁` and `C₂`.

The proof is: `crossRatioDist` and the two chord endpoints are uniformly continuous on the
compact `cthickening τ C₁ ×ˢ cthickening τ C₂` (this is what
`Arlib.continuousOn_chordLow`, `Arlib.continuousOn_chordHigh` and
`Arlib.continuousOn_crossRatioDist` buy); `Arlib.exists_mem_chord_dist_le` moves the point `x`
of the perturbed chord onto the unperturbed one at a cost controlled by those moduli; and `g`
is uniformly continuous on the compact `K`.  The `ε` is split `ε/2 + ε/2` between the modulus
of `g` and the modulus of `min 1 (d_K ·) / 3`. -/
theorem htrans_of_compact (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) :
    ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε := by
  intro g U₁ U₂ hgc _hg0 _hg3 _hm₁ _hm₂ _hU₁K _hU₂K hUdisj hchord ε hε C₁ C₂ hC₁ hC₂
    hC₁U hC₂U hC₁int hC₂int hC₁ne hC₂ne
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨c₁, hc₁⟩ := hC₁ne
  have hR0 : 0 ≤ R :=
    le_trans dist_nonneg (Metric.mem_closedBall.mp (hR (interior_subset (hC₁int hc₁))))
  have hdisjC : Disjoint C₁ C₂ := hUdisj.mono hC₁U hC₂U
  obtain ⟨sep, hsep, hsepd⟩ :=
    exists_sep_of_disjoint_isCompact hC₁ hC₂ ⟨c₁, hc₁⟩ hC₂ne hdisjC
  obtain ⟨τ₁, hτ₁, hτ₁sub⟩ := hC₁.exists_cthickening_subset_open isOpen_interior hC₁int
  obtain ⟨τ₂, hτ₂, hτ₂sub⟩ := hC₂.exists_cthickening_subset_open isOpen_interior hC₂int
  obtain ⟨τ, hτ0, hττ₁, hττ₂, hτsep⟩ :
      ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₁ ∧ τ ≤ τ₂ ∧ τ ≤ sep / 4 :=
    ⟨min (min τ₁ τ₂) (sep / 4), lt_min (lt_min hτ₁ hτ₂) (by linarith),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _⟩
  -- the two thickenings, and what they are good for
  have hD₁mem : ∀ y ∈ Metric.cthickening τ C₁, ∃ z ∈ C₁, dist y z ≤ τ := by
    intro y hy
    rw [hC₁.cthickening_eq_biUnion_closedBall hτ0.le] at hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨z, hz, Metric.mem_closedBall.mp hyz⟩
  have hD₂mem : ∀ y ∈ Metric.cthickening τ C₂, ∃ z ∈ C₂, dist y z ≤ τ := by
    intro y hy
    rw [hC₂.cthickening_eq_biUnion_closedBall hτ0.le] at hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨z, hz, Metric.mem_closedBall.mp hyz⟩
  have hD₁int : Metric.cthickening τ C₁ ⊆ interior K := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hD₁mem y hy
    exact hτ₁sub (Metric.mem_cthickening_of_dist_le y z τ₁ C₁ hz (le_trans hyz hττ₁))
  have hD₂int : Metric.cthickening τ C₂ ⊆ interior K := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hD₂mem y hy
    exact hτ₂sub (Metric.mem_cthickening_of_dist_le y z τ₂ C₂ hz (le_trans hyz hττ₂))
  have hDsep : ∀ y ∈ Metric.cthickening τ C₁, ∀ w ∈ Metric.cthickening τ C₂,
      sep / 2 ≤ dist y w := by
    intro y hy w hw
    obtain ⟨z, hz, hyz⟩ := hD₁mem y hy
    obtain ⟨z', hz', hwz'⟩ := hD₂mem w hw
    have h3 : sep ≤ dist z z' := hsepd z hz z' hz'
    have h4 : dist z z' ≤ dist z y + (dist y w + dist w z') :=
      le_trans (dist_triangle z y z') (by gcongr; exact dist_triangle y w z')
    rw [dist_comm z y] at h4
    linarith
  have hDsubS : (Metric.cthickening τ C₁) ×ˢ (Metric.cthickening τ C₂) ⊆
      {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        p.1 ∈ interior K ∧ p.2 ∈ interior K ∧ p.1 ≠ p.2} := by
    rintro ⟨y, w⟩ ⟨hy, hw⟩
    refine ⟨hD₁int hy, hD₂int hw, ?_⟩
    have := hDsep y hy w hw
    exact dist_pos.mp (by linarith)
  have hDcpt : IsCompact ((Metric.cthickening τ C₁) ×ˢ (Metric.cthickening τ C₂)) :=
    hC₁.cthickening.prod hC₂.cthickening
  -- the four moduli
  obtain ⟨δg, hδg, hgu⟩ := Metric.uniformContinuousOn_iff.mp
    (hKcpt.uniformContinuousOn_of_continuous hgc.continuousOn) (ε / 2) (by linarith)
  obtain ⟨M, hM0, hMdef⟩ : ∃ M : ℝ, 0 ≤ M ∧ M = 4 * R / sep :=
    ⟨4 * R / sep, by positivity, rfl⟩
  obtain ⟨η, hη0, hηR⟩ : ∃ η : ℝ, 0 < η ∧ η * (2 * R) ≤ δg / 4 :=
    ⟨δg / (4 * (2 * R + 1)), div_pos hδg (by linarith), by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith⟩
  obtain ⟨ρ₂, hρ₂0, hρ₂M⟩ : ∃ c : ℝ, 0 < c ∧ (1 + 2 * M) * c ≤ δg / 4 :=
    ⟨δg / (4 * (1 + 2 * M)), div_pos hδg (by linarith), le_of_eq (by field_simp)⟩
  obtain ⟨δa, hδa, hau⟩ := Metric.uniformContinuousOn_iff.mp
    (hDcpt.uniformContinuousOn_of_continuous
      ((continuousOn_chordLow hKc hKcl hKb).mono hDsubS)) η hη0
  obtain ⟨δb, hδb, hbu⟩ := Metric.uniformContinuousOn_iff.mp
    (hDcpt.uniformContinuousOn_of_continuous
      ((continuousOn_chordHigh hKc hKcl hKb).mono hDsubS)) η hη0
  obtain ⟨δd, hδd, hdd⟩ := Metric.uniformContinuousOn_iff.mp
    (hDcpt.uniformContinuousOn_of_continuous
      ((continuousOn_crossRatioDist hKc hKcl hKb).mono hDsubS)) (3 * ε / 2) (by linarith)
  refine ⟨min (min τ ρ₂) (min δa (min δb δd)),
    lt_min (lt_min hτ0 hρ₂0) (lt_min hδa (lt_min hδb hδd)), ?_⟩
  intro u hu v hv x hxK hxline
  obtain ⟨r, hr⟩ := hxline
  obtain ⟨u₀, hu₀C, hu₀d⟩ := hC₁.exists_infDist_eq_dist ⟨c₁, hc₁⟩ u
  obtain ⟨v₀, hv₀C, hv₀d⟩ := hC₂.exists_infDist_eq_dist hC₂ne v
  rw [hu₀d] at hu
  rw [hv₀d] at hv
  have huD : u ∈ Metric.cthickening τ C₁ :=
    Metric.mem_cthickening_of_dist_le u u₀ τ C₁ hu₀C
      (le_of_lt (lt_of_lt_of_le hu (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hvD : v ∈ Metric.cthickening τ C₂ :=
    Metric.mem_cthickening_of_dist_le v v₀ τ C₂ hv₀C
      (le_of_lt (lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hu₀D : u₀ ∈ Metric.cthickening τ C₁ :=
    Metric.mem_cthickening_of_dist_le u₀ u₀ τ C₁ hu₀C (by simpa using hτ0.le)
  have hv₀D : v₀ ∈ Metric.cthickening τ C₂ :=
    Metric.mem_cthickening_of_dist_le v₀ v₀ τ C₂ hv₀C (by simpa using hτ0.le)
  have huvsep : sep / 2 ≤ dist u v := hDsep u huD v hvD
  have huv : u ≠ v := dist_pos.mp (by linarith)
  have hu₀v₀d : sep ≤ dist u₀ v₀ := hsepd u₀ hu₀C v₀ hv₀C
  have hu₀v₀ : u₀ ≠ v₀ := dist_pos.mp (by linarith)
  have huK : u ∈ K := interior_subset (hD₁int huD)
  have hu₀K : u₀ ∈ K := interior_subset (hC₁int hu₀C)
  have hv₀K : v₀ ∈ K := interior_subset (hC₂int hv₀C)
  have hp : ((u₀, v₀) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈
      (Metric.cthickening τ C₁) ×ˢ (Metric.cthickening τ C₂) := ⟨hu₀D, hv₀D⟩
  have hq : ((u, v) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈
      (Metric.cthickening τ C₁) ×ˢ (Metric.cthickening τ C₂) := ⟨huD, hvD⟩
  have hpq : dist ((u₀, v₀) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      ((u, v) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      < min (min τ ρ₂) (min δa (min δb δd)) := by
    rw [Prod.dist_eq]
    exact max_lt (by rw [dist_comm]; exact hu) (by rw [dist_comm]; exact hv)
  have hA : |chordLow K u₀ v₀ - chordLow K u v| ≤ η := by
    have h : dist (chordLow K u₀ v₀) (chordLow K u v) < η :=
      hau (u₀, v₀) hp (u, v) hq (lt_of_lt_of_le hpq (le_trans (min_le_right _ _) (min_le_left _ _)))
    rw [Real.dist_eq] at h
    exact h.le
  have hB : |chordHigh K u₀ v₀ - chordHigh K u v| ≤ η := by
    have h : dist (chordHigh K u₀ v₀) (chordHigh K u v) < η :=
      hbu (u₀, v₀) hp (u, v) hq (lt_of_lt_of_le hpq
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    rw [Real.dist_eq] at h
    exact h.le
  have hrM : |r| ≤ M := by
    have h1 : dist x u = |r| * dist u v := by rw [hr]; exact dist_lineMap_left u v r
    have hx0 : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR hxK)
    have hu0 : dist u 0 ≤ R := Metric.mem_closedBall.mp (hR huK)
    have h2 : dist x u ≤ 2 * R := by
      have ht := dist_triangle x 0 u
      rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) u] at ht
      linarith
    have h5 : |r| * sep ≤ |r| * (2 * dist u v) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg r)
    have h6 : |r| * (2 * dist u v) = 2 * (|r| * dist u v) := by ring
    rw [h6, ← h1] at h5
    rw [hMdef, le_div_iff₀ hsep]
    linarith
  obtain ⟨s, hsK, hsd⟩ :=
    exists_mem_chord_dist_le hKc hKcl hKb huv hu₀v₀ hu₀K hv₀K hxK hr hA hB
  have hdist : dist x ((AffineMap.lineMap u₀ v₀ : ℝ → EuclideanSpace ℝ (Fin n)) s) < δg := by
    have hab := abs_le.mp hrM
    have habs1 : |1 - r| ≤ 1 + M :=
      abs_le.mpr ⟨by linarith [hab.2], by linarith [hab.1]⟩
    have hdu : dist u u₀ ≤ ρ₂ :=
      le_of_lt (lt_of_lt_of_le hu (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hdv : dist v v₀ ≤ ρ₂ :=
      le_of_lt (lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_right _ _)))
    have e1 : |1 - r| * dist u u₀ ≤ (1 + M) * ρ₂ :=
      mul_le_mul habs1 hdu dist_nonneg (by linarith)
    have e2 : |r| * dist v v₀ ≤ M * ρ₂ := mul_le_mul hrM hdv dist_nonneg hM0
    have hu₀v₀R : dist u₀ v₀ ≤ 2 * R := by
      have h1 : dist u₀ 0 ≤ R := Metric.mem_closedBall.mp (hR hu₀K)
      have h2 : dist v₀ 0 ≤ R := Metric.mem_closedBall.mp (hR hv₀K)
      have ht := dist_triangle u₀ 0 v₀
      rw [dist_comm (0 : EuclideanSpace ℝ (Fin n)) v₀] at ht
      linarith
    have e3 : η * dist u₀ v₀ ≤ η * (2 * R) := mul_le_mul_of_nonneg_left hu₀v₀R hη0.le
    have e12 : (1 + M) * ρ₂ + M * ρ₂ = (1 + 2 * M) * ρ₂ := by ring
    linarith [hsd, e1, e2, e3, hηR, hρ₂M, hδg]
  have hgclose : dist (g x) (g ((AffineMap.lineMap u₀ v₀ : ℝ → EuclideanSpace ℝ (Fin n)) s))
      < ε / 2 := hgu x hxK _ hsK hdist
  have hgxt : g ((AffineMap.lineMap u₀ v₀ : ℝ → EuclideanSpace ℝ (Fin n)) s)
      ≤ min 1 (crossRatioDist K u₀ v₀) / 3 :=
    hchord u₀ (hC₁U hu₀C) v₀ (hC₂U hv₀C) _ hsK ⟨s, rfl⟩
  have hdcr : |crossRatioDist K u₀ v₀ - crossRatioDist K u v| < 3 * ε / 2 := by
    have h : dist (crossRatioDist K u₀ v₀) (crossRatioDist K u v) < 3 * ε / 2 :=
      hdd (u₀, v₀) hp (u, v) hq (lt_of_lt_of_le hpq
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
    rwa [Real.dist_eq] at h
  have hmin : |min 1 (crossRatioDist K u₀ v₀) - min 1 (crossRatioDist K u v)| < 3 * ε / 2 :=
    lt_of_le_of_lt (abs_min_one_sub_le _ _) hdcr
  rw [Real.dist_eq] at hgclose
  have h1 := abs_lt.mp hgclose
  have h2 := abs_lt.mp hmin
  linarith [h1.1, h1.2, h2.1, h2.2, hgxt]

#print axioms htrans_of_compact

open ProbabilityTheory Metric MeasureTheory MarkovChains in
/-- **The consumer, with `htrans` discharged.**

`Arlib.conductance_hitAndRun_ge_of_transfer_of_localization` fed `Arlib.htrans_of_compact`.
The residual binders are exactly two: `hLem41` (Lemma 4.1) and `hloc` (the Localization
Lemma for continuous integrands with the needle inside the body).  `htrans` is gone.

This composition is also the vacuity check on `Arlib.htrans_of_compact`: the binder is not
retyped here, it is *applied*, so a statement that drifted from the one
`Arlib/Convexity/IsoConcaveWeight.lean` asks for by a single clause would be a type error. -/
theorem conductance_hitAndRun_ge_of_localization (hn : 1 ≤ n)
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_transfer_of_localization hn hKc hKcl hKm hKb hball hD hLem41
    (htrans_of_compact hKc hKcl hKb) hloc

#print axioms conductance_hitAndRun_ge_of_localization

end Transfer
