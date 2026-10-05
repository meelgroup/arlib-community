/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyWalk
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Isoperimetry
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyConductanceSharp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cousins–Vempala's `cor:overlap`, at separation `δ/√n`

Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*,
`cor:overlap` (`1409.6011/vol3_journal.tex:612`), derived there from `lem:overlap` (`:581`)
and, underneath, Lemma 3.5 of [KLS95] (`:592`):

> For a partition `S, S̄` of a convex body `K` and `u ∈ S`, `v ∈ S̄` with `‖u - v‖ < δ/√n`
> and `d_h(u,v) < 1/4`, one step of the speedy walk satisfies `P_u(S̄) + P_v(S) > 1/20`.

## The point: separation `δ/√n`, not `δ/n`

Both overlap estimates already in this repository —
`Arlib.MarkovChains.one_le_speedyWalk_add_speedyWalk_compl` (`SpeedyWalk.lean`) and
`Arlib.MarkovChains.mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl`
(`MetropolisConductance.lean`) — carry the error term `n‖u-v‖/(2δ)`, so the separation they
force is `δ/n`.  That factor `√n` is the difference between a polynomial and an exponential
conductance bound, and closing it is the content of this file.

The crude term comes from `Arlib.MarkovChains.volume_ball_le_volume_inter_ball_add`
(`BallWalkConductance.lean`), which bounds `vol(B(u,δ) \ B(v,δ))` by an *annulus* of
thickness `‖u-v‖`, of relative volume `≈ n‖u-v‖/δ`.  The truth is that the crescent is an
*equatorial slab* of the same thickness, of relative volume `≈ ‖u-v‖√n/(δ√(2π))`: the ball's
mass concentrates in a band of width `δ/√n` about any equator.  The sharp bound is
`volume_ball_le_volume_inter_ball_add_sqrt`, with the explicit constant

    vol(B(u,δ))  ≤  vol(B(u,δ) ∩ B(v,δ))  +  (‖u-v‖/δ)·√((n+1)/(2π))·vol(B(u,δ)).

`√((n+1)/(2π))` is the sharp `V_{n-1}/V_n` ratio of consecutive unit-ball volumes; it is
obtained from `Γ(x+1/2) ≤ √x·Γ(x)` (`gamma_add_half_le_sqrt_mul`), i.e. from log-convexity
of `Γ`, applied to Mathlib's `EuclideanSpace.volume_ball`.  At `‖u-v‖ = δ/√n` the loss is
`√((n+1)/(2πn)) ≤ √(3/(4π)) < 1/2` for `n ≥ 2` (`lens_defect_le_half`) — a constant, which
is exactly the KLS-style statement at `vol3_journal.tex:592`.

## What is proved, and what is assumed

* `ell_le_speedyWalk_add_speedyWalk_compl_sqrt` — **unconditional** (no convexity, no
  floor): `ℓ(u) ≤ P_u(T) + P_v(Tᶜ) + (‖u-v‖/δ)·√((n+1)/(2π))`.  This is the file's real
  content and is a strict sharpening of `ell_le_ballWalk_add_ballWalk_compl`.
* `overlap_speedyWalk` — `cor:overlap`'s conclusion `1 ≤ 20·(P_u(Tᶜ) + P_v(T))`, in exactly
  the binder shape `Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap` demands,
  **plus one hypothesis the paper does not have**: the local-conductance floor
  `11 ≤ 20·ℓ(x)` for `x ∈ K`.
* `conductance_speedyGaussian_ge_of_ell` — `thm:speedyconductance` with `hoverlap`
  discharged by `exact overlap_speedyWalk …`.

**Why the floor.**  The paper's `lem:overlap` uses Lemma 3.5 of [KLS95],
`vol(K ∩ B(u,δ) ∩ B(v,δ)) ≥ min{ℓ(u),ℓ(v)}·vol(δBₙ)/(e+1)`, which trades the ball for the
*body*: it needs no floor on `ℓ`.  Its proof is a polar decomposition of the star-shaped set
`K ∩ B(u,δ)` about `u`, which Mathlib does not support today, and it is **not proved here**.
The slab argument's translation step (`P₃ + (v-u) ⊆ B(u,δ) ∩ B(v,δ)`) is a *measure*
identity and breaks when intersected with `K`, since `K + (v-u) ⊄ K`.  So what is available
is `P_u(Tᶜ) + P_v(T) ≥ ℓ(u) - 1/2`, whence the floor `ℓ ≥ 1/20 + 1/2 = 11/20`.  This floor
is satisfiable (`exists_overlap_speedyWalk_witness`, at `K = ℝ²`) but **fails for every
bounded convex body**, where `ℓ → 1/2` at the boundary.  So `overlap_speedyWalk` is not a
proof of `cor:overlap`; `ell_le_speedyWalk_add_speedyWalk_compl_sqrt` is an unconditional
`√n` improvement over what the repository had, and the remaining gap is exactly KLS95 3.5.

## No rate claim

`thm:iso` is unproved here, and so is KLS95 Lemma 3.5.  Nothing below asserts, or may be
quoted as asserting, a polynomial mixing time.

## Main results

* `gamma_add_half_le_sqrt_mul`, `sqrt_pi_pow_div_gamma_le`, `volume_ball_succ_ratio` — the
  unit-ball volume ratio `Vₙ ≤ √((n+2)/(2π))·Vₙ₊₁`.
* `volume_slab_le` — the equatorial slab, by Fubini on `EuclideanSpace`.
* `volume_ball_le_volume_inter_ball_add_sqrt` — **the crux**, the sharp lens estimate.
* `ell_le_speedyWalk_add_speedyWalk_compl_sqrt` — the sharp one-step overlap.
* `lens_defect_le_half`, `overlap_speedyWalk`, `conductance_speedyGaussian_ge_of_ell`.
* `exists_overlap_speedyWalk_witness` — the non-vacuity witness.

## References

Cousins and Vempala, §4.1 (`1409.6011/vol3_journal.tex:509–700`).
Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a localization
lemma* (1995), Lemma 3.5 — cited by the paper, **not** formalised here.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open scoped ENNReal

/-! ## 1. A Gamma-function ratio -/

/-- **`Γ(x + 1/2) ≤ √x · Γ(x)`.**  Immediate from the log-convexity of `Γ`
(`Real.convexOn_log_Gamma`) at the midpoint of `x` and `x + 1`:
`Γ(x+1/2)² ≤ Γ(x)·Γ(x+1) = x·Γ(x)²`. -/
theorem gamma_add_half_le_sqrt_mul {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ≤ Real.sqrt x * Real.Gamma x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hG1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos hx1
  have hGh : 0 < Real.Gamma (x + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (ne_of_gt hx)
  have hc := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hx1)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [Function.comp_apply, smul_eq_mul] at hc
  rw [show (1/2 : ℝ) * x + (1/2) * (x + 1) = x + 1/2 by ring, hrec,
    Real.log_mul (ne_of_gt hx) (ne_of_gt hG)] at hc
  have hlog : Real.log (Real.Gamma (x + 1/2)) ≤ Real.log (Real.sqrt x * Real.Gamma x) := by
    rw [Real.log_mul (ne_of_gt hsx) (ne_of_gt hG), Real.log_sqrt hx.le]
    linarith
  exact (Real.log_le_log_iff hGh (by positivity)).1 hlog

/-! ## 2. The unit-ball volume ratio `Vₙ ≤ √((n+2)/(2π))·Vₙ₊₁` -/

/-- The real content of `volume_ball_succ_ratio`: with `V_k = √π^k / Γ(k/2+1)` the volume of
the unit `k`-ball, `V_{n+1} ≤ √((n+3)/(2π)) · V_{n+2}`.

Equivalently `Γ(x+1/2) ≤ √x·Γ(x)` at `x = (n+3)/2`, since
`√((n+3)/(2π))·√π = √((n+3)/2)`. -/
theorem sqrt_pi_pow_div_gamma_le (n : ℕ) :
    Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2 + 1)
      ≤ Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi))
        * (Real.sqrt Real.pi ^ (n + 2) / Real.Gamma (((n : ℝ) + 2) / 2 + 1)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hx : (0 : ℝ) < ((n : ℝ) + 3) / 2 := by positivity
  have e1 : ((n : ℝ) + 1) / 2 + 1 = ((n : ℝ) + 3) / 2 := by ring
  have e2 : ((n : ℝ) + 2) / 2 + 1 = ((n : ℝ) + 3) / 2 + 1 / 2 := by ring
  have hG1 : 0 < Real.Gamma (((n : ℝ) + 3) / 2) := Real.Gamma_pos_of_pos hx
  have hG2 : 0 < Real.Gamma (((n : ℝ) + 3) / 2 + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgam := gamma_add_half_le_sqrt_mul hx
  -- `√((n+3)/(2π))·√π = √((n+3)/2)`
  have hsq : Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)) * Real.sqrt Real.pi
      = Real.sqrt (((n : ℝ) + 3) / 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [e1, e2, div_le_iff₀ hG1]
  have hpow : Real.sqrt Real.pi ^ (n + 2) = Real.sqrt Real.pi ^ (n + 1) * Real.sqrt Real.pi := by
    ring
  rw [hpow]
  have key : Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi))
      * (Real.sqrt Real.pi ^ (n + 1) * Real.sqrt Real.pi
        / Real.Gamma (((n : ℝ) + 3) / 2 + 1 / 2))
      * Real.Gamma (((n : ℝ) + 3) / 2)
      = Real.sqrt Real.pi ^ (n + 1) * Real.sqrt (((n : ℝ) + 3) / 2)
        * Real.Gamma (((n : ℝ) + 3) / 2) / Real.Gamma (((n : ℝ) + 3) / 2 + 1 / 2) := by
    field_simp
    nlinarith [hsq, Real.sqrt_nonneg (((n : ℝ) + 3) / 2),
      Real.sqrt_nonneg (((n : ℝ) + 3) / (2 * Real.pi)),
      pow_nonneg hsp.le (n + 1)]
  rw [key, le_div_iff₀ hG2]
  have hpp : (0 : ℝ) ≤ Real.sqrt Real.pi ^ (n + 1) := pow_nonneg hsp.le _
  nlinarith [hgam, hG1, hpp]

/-- **The unit-ball volume ratio.**  In `ℝ^{n+2}`, the `(n+1)`-dimensional unit ball is
smaller than `√((n+3)/(2π))` times the `(n+2)`-dimensional one, after correcting for the
missing factor of `δ`:

    δ · vol_{n+1}(δ Bₙ₊₁)  ≤  √((n+3)/(2π)) · vol_{n+2}(δ Bₙ₊₂).

This is the sharp constant `V_k/V_{k+1} ≈ √(k/(2π))`; the crude bound `V_k/V_{k+1} ≤ k`
is what costs the repository's existing overlap estimates a factor `√n`. -/
theorem volume_ball_succ_ratio (n : ℕ) (δ : ℝ) :
    ENNReal.ofReal δ * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ)
      ≤ ENNReal.ofReal (Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) δ) := by
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hstep : ENNReal.ofReal δ * (ENNReal.ofReal δ ^ (n + 1)) = ENNReal.ofReal δ ^ (n + 2) := by
    ring
  calc ENNReal.ofReal δ * (ENNReal.ofReal δ ^ (n + 1)
        * ENNReal.ofReal (Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n : ℝ) + 1) / 2 + 1)))
      = ENNReal.ofReal δ ^ (n + 2)
        * ENNReal.ofReal (Real.sqrt Real.pi ^ (n + 1)
          / Real.Gamma (((n : ℝ) + 1) / 2 + 1)) := by rw [← mul_assoc, hstep]
    _ ≤ ENNReal.ofReal δ ^ (n + 2)
        * ENNReal.ofReal (Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi))
          * (Real.sqrt Real.pi ^ (n + 2) / Real.Gamma (((n : ℝ) + 2) / 2 + 1))) := by
        gcongr
        exact sqrt_pi_pow_div_gamma_le n
    _ = ENNReal.ofReal (Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
        * (ENNReal.ofReal δ ^ (n + 2)
          * ENNReal.ofReal (Real.sqrt Real.pi ^ (n + 2)
            / Real.Gamma (((n : ℝ) + 2) / 2 + 1))) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        ring

/-! ## 3. The equatorial slab -/

/-- **The volume of a coordinate slab through a ball.**  In `ℝ^{n+1}`,

    vol({x : |x₀| ≤ h, ‖x‖ < δ})  ≤  2h · vol_n(δ Bₙ),

by the product inclusion `slab ∩ ball ⊆ [-h,h] × δBₙ`. -/
theorem volume_slab_le (n : ℕ) {h δ : ℝ} (hδ : 0 ≤ δ) :
    volume {x : EuclideanSpace ℝ (Fin (n + 1)) |
        |x 0| ≤ h ∧ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ}
      ≤ ENNReal.ofReal (2 * h) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
  classical
  set C : Set (Fin n → ℝ) := {z | ∑ j, z j ^ 2 < δ ^ 2} with hCdef
  have hCm : MeasurableSet C := by
    refine measurableSet_lt (Finset.measurable_sum (f := fun (j : Fin n) (z : Fin n → ℝ) =>
      z j ^ 2) _ fun j _ => ?_) measurable_const
    exact (measurable_pi_apply j).pow_const 2
  set B : Set (Fin (n + 1) → ℝ) := {y | |y 0| ≤ h ∧ ∑ i, y i ^ 2 < δ ^ 2} with hBdef
  have hBm : MeasurableSet B := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le ((measurable_pi_apply (0 : Fin (n + 1))).abs) measurable_const
    · refine measurableSet_lt (Finset.measurable_sum (f := fun (j : Fin (n + 1))
        (z : Fin (n + 1) → ℝ) => z j ^ 2) _ fun j _ => ?_) measurable_const
      exact (measurable_pi_apply j).pow_const 2
  -- the slab in `EuclideanSpace` is the `ofLp`-preimage of `B`
  have hslab : volume {x : EuclideanSpace ℝ (Fin (n + 1)) |
      |x 0| ≤ h ∧ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ} = volume B := by
    have hpre := (PiLp.volume_preserving_ofLp (Fin (n + 1))).measure_preimage hBm.nullMeasurableSet
    rw [← hpre]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hBdef,
      EuclideanSpace.ball_zero_eq δ hδ]
  -- the cross-section in `EuclideanSpace` is the `ofLp`-preimage of `C`
  have hcross : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) = volume C := by
    have hpre := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hCm.nullMeasurableSet
    rw [← hpre]
    congr 1
    ext x
    simp only [Set.mem_preimage, hCdef, Set.mem_setOf_eq, EuclideanSpace.ball_zero_eq δ hδ]
  rw [hslab, hcross]
  -- `B` sits inside the product slab
  have hsub : B ⊆ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
      (Set.Icc (-h) h ×ˢ C) := by
    rintro y ⟨hy0, hy⟩
    have hsplit : ∑ i, y i ^ 2 = y 0 ^ 2 + ∑ j : Fin n, y j.succ ^ 2 := Fin.sum_univ_succ _
    have hrest : ∑ j : Fin n, y j.succ ^ 2 < δ ^ 2 := by nlinarith [sq_nonneg (y 0)]
    refine ⟨?_, ?_⟩
    · exact Set.mem_Icc.2 (abs_le.1 hy0)
    · show ∑ j : Fin n, _ ^ 2 < δ ^ 2
      simpa [Fin.tail] using hrest
  calc volume B
      ≤ volume ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
          (Set.Icc (-h) h ×ˢ C)) := measure_mono hsub
    _ = (volume : Measure (ℝ × (Fin n → ℝ))) (Set.Icc (-h) h ×ˢ C) :=
        (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ)
          0).measure_preimage (measurableSet_Icc.prod hCm).nullMeasurableSet
    _ = ENNReal.ofReal (2 * h) * volume C := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
        congr 2
        ring

/-! ## 4. The sharp lens estimate -/

/-- The coordinate slab of `EuclideanSpace` is measurable. -/
theorem measurableSet_coordSlab (m : ℕ) (h δ : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin (m + 1)) |
      |x 0| ≤ h ∧ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) δ} := by
  have hB : MeasurableSet {y : Fin (m + 1) → ℝ | |y 0| ≤ h} :=
    measurableSet_le ((measurable_pi_apply (0 : Fin (m + 1))).abs) measurable_const
  have hpre : MeasurableSet
      ((@WithLp.ofLp 2 (Fin (m + 1) → ℝ)) ⁻¹' {y : Fin (m + 1) → ℝ | |y 0| ≤ h}) :=
    (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable hB
  exact MeasurableSet.inter hpre measurableSet_ball

/-- **The sharp lens estimate — the crux.**  For `u, v ∈ ℝ^{n+2}` at distance `t` and any
radius `δ > 0`,

    vol(B(u,δ))  ≤  vol(B(u,δ) ∩ B(v,δ))  +  (t/δ)·√((n+3)/(2π)) · vol(B(u,δ)).

The two balls lose, relatively, at most `(t/δ)·√((n+3)/(2π)) ≈ t√(n)/(δ√(2π))` by
intersecting.  This is the estimate at `vol3_journal.tex:592` in KLS form: at separation
`t = δ/√n` a *constant* fraction of the ball survives.

Contrast `Arlib.MarkovChains.volume_ball_le_volume_inter_ball_add`
(`BallWalkConductance.lean`), whose loss is `n·t/(2δ)` — larger by a factor `≈ √n·√(π/2)`.
That factor is exactly the gap between separation `δ/n` and separation `δ/√n`, and hence
between an exponentially small and a polynomially small conductance bound.

The proof is the equatorial-slab decomposition.  Writing `w = v - u` and
`σ(x) = ⟪x - u, w⟫`, the ball splits into `{σ > t²/2}`, `{|σ| ≤ t²/2}` and `{σ ≤ -t²/2}`;
the first lies in `B(v,δ)`, the third *translated by `w`* lies in `B(u,δ) ∩ B(v,δ)` and is
disjoint from the first, and the middle piece is a slab of width `t` through the ball,
whose volume `volume_slab_le` bounds by `t · vol_{n+1}(δBₙ₊₁)` and `volume_ball_succ_ratio`
converts into `(t/δ)·√((n+3)/(2π)) · vol_{n+2}(δBₙ₊₂)`. -/
theorem volume_ball_le_volume_inter_ball_add_sqrt (n : ℕ)
    (u v : EuclideanSpace ℝ (Fin (n + 2))) {δ : ℝ} (hδ : 0 < δ) :
    volume (Metric.ball u δ)
      ≤ volume (Metric.ball u δ ∩ Metric.ball v δ)
        + ENNReal.ofReal (dist u v / δ * Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
          * volume (Metric.ball u δ) := by
  classical
  rcases eq_or_ne u v with rfl | hne
  · rw [Set.inter_self]
    exact le_self_add
  set w : EuclideanSpace ℝ (Fin (n + 2)) := v - u with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set t : ℝ := ‖w‖ with htdef
  have ht0 : 0 < t := norm_pos_iff.2 hw0
  have hdist : dist u v = t := by rw [dist_eq_norm, htdef, hwdef, norm_sub_rev]
  -- the linear functional `σ`
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin (n + 2)) => ⟪x - u, w⟫_ℝ :=
    (continuous_id.sub continuous_const).inner continuous_const
  have hmeasσ : Measurable fun x : EuclideanSpace ℝ (Fin (n + 2)) => ⟪x - u, w⟫_ℝ :=
    hcont.measurable
  have hsig : ∀ x : EuclideanSpace ℝ (Fin (n + 2)),
      ⟪x - v, w⟫_ℝ = ⟪x - u, w⟫_ℝ - t ^ 2 := by
    intro x
    have hx : x - v = (x - u) - w := by rw [hwdef]; abel
    rw [hx, inner_sub_left, real_inner_self_eq_norm_sq, ← htdef]
  -- the two half-space inclusions
  have hin1 : ∀ x, x ∈ Metric.ball u δ → t ^ 2 / 2 ≤ ⟪x - u, w⟫_ℝ → x ∈ Metric.ball v δ := by
    intro x hx hs
    have h1 : ‖x - u‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have hx' : x - v = (x - u) - w := by rw [hwdef]; abel
    have h2 : ‖x - v‖ ^ 2 = ‖x - u‖ ^ 2 - 2 * ⟪x - u, w⟫_ℝ + t ^ 2 := by
      rw [hx', norm_sub_sq_real, ← htdef]
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (x - v), norm_nonneg (x - u)]
  have hin2 : ∀ x, x ∈ Metric.ball v δ → ⟪x - u, w⟫_ℝ ≤ t ^ 2 / 2 → x ∈ Metric.ball u δ := by
    intro x hx hs
    have h1 : ‖x - v‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have hx' : x - u = (x - v) + w := by rw [hwdef]; abel
    have h2 : ‖x - u‖ ^ 2 = ‖x - v‖ ^ 2 + 2 * ⟪x - v, w⟫_ℝ + t ^ 2 := by
      rw [hx', norm_add_sq_real, ← htdef]
    rw [hsig x] at h2
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (x - v), norm_nonneg (x - u)]
  -- the three pieces
  set P1 : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
    Metric.ball u δ ∩ {x | t ^ 2 / 2 < ⟪x - u, w⟫_ℝ} with hP1def
  set P2 : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
    Metric.ball u δ ∩ {x | |⟪x - u, w⟫_ℝ| ≤ t ^ 2 / 2} with hP2def
  set P3 : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
    Metric.ball u δ ∩ {x | ⟪x - u, w⟫_ℝ ≤ -(t ^ 2 / 2)} with hP3def
  set Q : Set (EuclideanSpace ℝ (Fin (n + 2))) := (fun y => y - w) ⁻¹' P3 with hQdef
  have hP1m : MeasurableSet P1 :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hmeasσ)
  have hP2m : MeasurableSet P2 :=
    measurableSet_ball.inter (measurableSet_le hmeasσ.abs measurable_const)
  have hP3m : MeasurableSet P3 :=
    measurableSet_ball.inter (measurableSet_le hmeasσ measurable_const)
  have hQm : MeasurableSet Q := by
    rw [hQdef]
    exact hP3m.preimage (measurable_id.sub_const w)
  -- `P1` and `Q` are disjoint subsets of the lens
  have hP1sub : P1 ⊆ Metric.ball u δ ∩ Metric.ball v δ := by
    rintro x ⟨hx, hs⟩
    exact ⟨hx, hin1 x hx (le_of_lt hs)⟩
  have hQsub : Q ⊆ Metric.ball u δ ∩ Metric.ball v δ := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyv : y ∈ Metric.ball v δ := by
      have : y - v = (y - w) - u := by rw [hwdef]; abel
      rw [Metric.mem_ball, dist_eq_norm, this]
      rwa [Metric.mem_ball, dist_eq_norm] at hy1
    have hkey : ⟪y - u, w⟫_ℝ ≤ t ^ 2 / 2 := by
      have hEq : ⟪y - w - u, w⟫_ℝ = ⟪y - u, w⟫_ℝ - t ^ 2 := by
        have hx : y - w - u = (y - u) - w := by abel
        rw [hx, inner_sub_left, real_inner_self_eq_norm_sq, ← htdef]
      have := hy2
      simp only [Set.mem_setOf_eq] at this
      rw [hEq] at this
      linarith
    exact ⟨hin2 y hyv hkey, hyv⟩
  have hdisj : Disjoint P1 Q := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hxQ
    obtain ⟨-, hx3⟩ := hxQ
    simp only [Set.mem_setOf_eq] at hx1 hx3
    have hEq : ⟪x - w - u, w⟫_ℝ = ⟪x - u, w⟫_ℝ - t ^ 2 := by
      have hx : x - w - u = (x - u) - w := by abel
      rw [hx, inner_sub_left, real_inner_self_eq_norm_sq, ← htdef]
    rw [hEq] at hx3
    linarith
  have hQvol : volume Q = volume P3 := by
    rw [hQdef, show (fun y : EuclideanSpace ℝ (Fin (n + 2)) => y - w)
      = (fun y => y + (-w)) from funext fun y => (sub_eq_add_neg y w)]
    exact measure_preimage_add_right volume (-w) P3
  have hlens : volume P1 + volume P3 ≤ volume (Metric.ball u δ ∩ Metric.ball v δ) := by
    rw [← hQvol, ← measure_union hdisj hQm]
    exact measure_mono (Set.union_subset hP1sub hQsub)
  -- the ball is covered by the three pieces
  have hcov : volume (Metric.ball u δ) ≤ volume P1 + volume P2 + volume P3 := by
    have hsub : Metric.ball u δ ⊆ P1 ∪ P2 ∪ P3 := by
      intro x hx
      rcases lt_trichotomy (⟪x - u, w⟫_ℝ) (t ^ 2 / 2) with hc | hc | hc
      · by_cases hc2 : ⟪x - u, w⟫_ℝ ≤ -(t ^ 2 / 2)
        · exact Or.inr ⟨hx, hc2⟩
        · exact Or.inl (Or.inr ⟨hx, abs_le.2 ⟨le_of_lt (not_le.1 hc2), le_of_lt hc⟩⟩)
      · refine Or.inl (Or.inr ⟨hx, abs_le.2 ⟨?_, le_of_eq hc⟩⟩)
        nlinarith [sq_nonneg t]
      · exact Or.inl (Or.inl ⟨hx, hc⟩)
    calc volume (Metric.ball u δ) ≤ volume (P1 ∪ P2 ∪ P3) := measure_mono hsub
      _ ≤ volume (P1 ∪ P2) + volume P3 := measure_union_le _ _
      _ ≤ volume P1 + volume P2 + volume P3 := by
          gcongr
          exact measure_union_le _ _
  -- the middle piece is a slab
  have hslab : volume P2 ≤ ENNReal.ofReal t
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ) := by
    -- an orthonormal basis whose first vector is `w/t`
    set wh : EuclideanSpace ℝ (Fin (n + 2)) := t⁻¹ • w with hwhdef
    have hwh1 : ‖wh‖ = 1 := by
      rw [hwhdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0, ← htdef]
      field_simp
    haveI : Unique (({0} : Set (Fin (n + 2))) : Type) := Set.uniqueSingleton _
    have hon : Orthonormal ℝ (({0} : Set (Fin (n + 2))).restrict (fun _ => wh)) := by
      constructor
      · intro i
        change ‖wh‖ = 1
        exact hwh1
      · intro i j hij
        exact absurd (Subsingleton.elim i j) hij
    have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2)))
        = Fintype.card (Fin (n + 2)) := by simp
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
    have hb0 : b 0 = wh := hb 0 rfl
    set S : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
      {y | |y 0| ≤ t / 2 ∧ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) δ} with hSdef
    have hSm : MeasurableSet S := measurableSet_coordSlab (n + 1) (t / 2) δ
    -- `P2` is the preimage of `S` under `x ↦ b.repr (x - u)`
    have hP2eq : P2 = (fun x => b.repr (x - u)) ⁻¹' S := by
      ext x
      simp only [hP2def, hSdef, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [b.repr.norm_map, b.repr_apply_apply, hb0, hwhdef, real_inner_smul_left,
        real_inner_comm (x - u) w]
      have habs : |t⁻¹ * ⟪x - u, w⟫_ℝ| = t⁻¹ * |⟪x - u, w⟫_ℝ| := by
        rw [abs_mul, abs_inv, abs_of_pos ht0]
      rw [habs]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1⟩
        have hcalc : t⁻¹ * (t ^ 2 / 2) = t / 2 := by field_simp
        calc t⁻¹ * |⟪x - u, w⟫_ℝ| ≤ t⁻¹ * (t ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = t / 2 := hcalc
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt ht0)
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht0), one_mul] at hmul
        calc |⟪x - u, w⟫_ℝ| ≤ t * (t / 2) := hmul
          _ = t ^ 2 / 2 := by ring
    have hvolP2 : volume P2 = volume S := by
      rw [hP2eq]
      have hstep1 : volume ((fun x : EuclideanSpace ℝ (Fin (n + 2)) => x - u) ⁻¹'
          (b.repr ⁻¹' S)) = volume (b.repr ⁻¹' S) := by
        rw [show (fun x : EuclideanSpace ℝ (Fin (n + 2)) => x - u)
          = (fun x => x + (-u)) from funext fun x => sub_eq_add_neg x u]
        exact measure_preimage_add_right volume (-u) _
      rw [show ((fun x => b.repr (x - u)) ⁻¹' S)
        = ((fun x : EuclideanSpace ℝ (Fin (n + 2)) => x - u) ⁻¹' (b.repr ⁻¹' S)) from rfl,
        hstep1]
      exact (b.measurePreserving_repr).measure_preimage hSm.nullMeasurableSet
    rw [hvolP2]
    have := volume_slab_le (n + 1) (h := t / 2) hδ.le
    calc volume S ≤ ENNReal.ofReal (2 * (t / 2))
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ) := this
      _ = ENNReal.ofReal t * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ) := by
          congr 2
          ring
  -- convert the slab bound into a fraction of the ambient ball
  have hratio : ENNReal.ofReal t * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) δ)
      ≤ ENNReal.ofReal (t / δ * Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
        * volume (Metric.ball u δ) := by
    have hb := volume_ball_succ_ratio n δ
    have hsplit : ENNReal.ofReal t = ENNReal.ofReal (t / δ) * ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [volume_ball_eq u δ, hsplit, mul_assoc,
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ t / δ), mul_assoc]
    gcongr
  calc volume (Metric.ball u δ) ≤ volume P1 + volume P2 + volume P3 := hcov
    _ = volume P1 + volume P3 + volume P2 := by ring
    _ ≤ volume (Metric.ball u δ ∩ Metric.ball v δ) + volume P2 := by gcongr
    _ ≤ volume (Metric.ball u δ ∩ Metric.ball v δ)
          + ENNReal.ofReal (t / δ * Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
            * volume (Metric.ball u δ) := by
        gcongr
        exact hslab.trans hratio
    _ = volume (Metric.ball u δ ∩ Metric.ball v δ)
          + ENNReal.ofReal (dist u v / δ * Real.sqrt (((n : ℝ) + 3) / (2 * Real.pi)))
            * volume (Metric.ball u δ) := by rw [hdist]

/-! ## 5. The one-step overlap estimate for the speedy walk -/

/-- **The sharp one-step overlap bound for the speedy walk.**  For measurable `K`, any
`u, v` and any measurable `T`, in dimension `n ≥ 2`,

    ℓ(u)  ≤  P_u(T) + P_v(Tᶜ)  +  (‖u-v‖/δ)·√((n+1)/(2π)).

This is `Arlib.MarkovChains.ell_le_ballWalk_add_ballWalk_compl` /
`Arlib.MarkovChains.mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl` with the
error term `n‖u-v‖/(2δ)` replaced by the sharp `(‖u-v‖/δ)·√((n+1)/(2π))` — smaller by a
factor `≈ √(nπ/2)`.  Consequently the separation forced by a small overlap is `δ/√n`, not
`δ/n`.

No convexity is used: only the lens estimate
`volume_ball_le_volume_inter_ball_add_sqrt`. -/
theorem ell_le_speedyWalk_add_speedyWalk_compl_sqrt {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    (u v : EuclideanSpace ℝ (Fin n)) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) :
    ell K δ u ≤ speedyWalk K δ u T + speedyWalk K δ v Tᶜ
      + ENNReal.ofReal (dist u v / δ * Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set C : Set (EuclideanSpace ℝ (Fin (m + 2))) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  have hCm : MeasurableSet C := measurableSet_ball.inter measurableSet_ball
  have hCu : C ⊆ Metric.ball u δ := Set.inter_subset_left
  have hCv : C ⊆ Metric.ball v δ := Set.inter_subset_right
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 2))) δ) with hvbdef
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  have hbu : volume (Metric.ball u δ) = vb := volume_ball_eq u δ
  have hCtop : volume C ≠ ⊤ :=
    ne_top_of_le_ne_top (hbu ▸ hvbtop) (measure_mono hCu)
  -- both one-step laws dominate the uniform law on `C ∩ K`, normalised by `vol(δBₙ)`
  have hdom : ∀ (x : EuclideanSpace ℝ (Fin (m + 2))) (A : Set (EuclideanSpace ℝ (Fin (m + 2)))),
      MeasurableSet A → C ⊆ Metric.ball x δ →
      vb⁻¹ * volume (A ∩ (C ∩ K)) ≤ speedyWalk K δ x A := by
    intro x A hA hsub
    rw [speedyWalk_apply_set hK δ x hA]
    refine le_trans ?_ le_self_add
    have hle : volume (Metric.ball x δ ∩ K) ≤ vb :=
      le_trans (measure_mono Set.inter_subset_left) (le_of_eq (volume_ball_eq x δ))
    have hsub2 : A ∩ (C ∩ K) ⊆ A ∩ (Metric.ball x δ ∩ K) :=
      fun y hy => ⟨hy.1, hsub hy.2.1, hy.2.2⟩
    exact mul_le_mul' (ENNReal.inv_le_inv.2 hle) (measure_mono hsub2)
  have h1 : vb⁻¹ * volume (T ∩ (C ∩ K)) ≤ speedyWalk K δ u T := hdom u T hT hCu
  have h2 : vb⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ speedyWalk K δ v Tᶜ := hdom v Tᶜ hT.compl hCv
  have h3 : volume (T ∩ (C ∩ K)) + volume (Tᶜ ∩ (C ∩ K)) = volume (C ∩ K) := by
    have h := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rwa [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at h
  have hsum : vb⁻¹ * volume (C ∩ K) ≤ speedyWalk K δ u T + speedyWalk K δ v Tᶜ := by
    rw [← h3, mul_add]
    exact add_le_add h1 h2
  -- the lens estimate, in the form `vol(B_u \ C) ≤ r·vol(δBₙ)`
  set r : ℝ := dist u v / δ * Real.sqrt (((m : ℝ) + 3) / (2 * Real.pi)) with hrdef
  have hlens := volume_ball_le_volume_inter_ball_add_sqrt m u v hδ
  rw [hbu, ← hCdef, ← hrdef] at hlens
  have hdiff : volume (Metric.ball u δ \ C) ≤ ENNReal.ofReal r * vb := by
    have hEq : volume C + volume (Metric.ball u δ \ C) = vb := by
      have h := measure_inter_add_sdiff (μ := volume) (Metric.ball u δ) hCm
      rwa [Set.inter_eq_self_of_subset_right hCu, hbu] at h
    have hle : volume C + volume (Metric.ball u δ \ C)
        ≤ volume C + ENNReal.ofReal r * vb := by
      rw [hEq]; exact hlens
    exact (ENNReal.add_le_add_iff_left hCtop).1 hle
  have hbK : volume (Metric.ball u δ ∩ K) ≤ volume (C ∩ K) + ENNReal.ofReal r * vb := by
    have hsubset : Metric.ball u δ ∩ K ⊆ (C ∩ K) ∪ (Metric.ball u δ \ C) := by
      rintro x ⟨hx1, hx2⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hx2⟩
      · exact Or.inr ⟨hx1, hxC⟩
    calc volume (Metric.ball u δ ∩ K)
        ≤ volume ((C ∩ K) ∪ (Metric.ball u δ \ C)) := measure_mono hsubset
      _ ≤ volume (C ∩ K) + volume (Metric.ball u δ \ C) := measure_union_le _ _
      _ ≤ _ := by gcongr
  have hcast : ((((m + 2 : ℕ) : ℝ) + 1) / (2 * Real.pi)) = (((m : ℝ) + 3) / (2 * Real.pi)) := by
    push_cast
    ring
  rw [ell_apply, hbu, ENNReal.div_eq_inv_mul, hcast, ← hrdef]
  calc vb⁻¹ * volume (Metric.ball u δ ∩ K)
      ≤ vb⁻¹ * (volume (C ∩ K) + ENNReal.ofReal r * vb) := by gcongr
    _ = vb⁻¹ * volume (C ∩ K) + ENNReal.ofReal r * (vb⁻¹ * vb) := by ring
    _ = vb⁻¹ * volume (C ∩ K) + ENNReal.ofReal r := by
        rw [ENNReal.inv_mul_cancel hvb0 hvbtop, mul_one]
    _ ≤ speedyWalk K δ u T + speedyWalk K δ v Tᶜ + ENNReal.ofReal r := by gcongr

/-- **The lens defect is at most `1/2` at separation `δ/√n`, for `n ≥ 2`.**

    (‖u-v‖/δ)·√((n+1)/(2π))  ≤  1/2   whenever  ‖u-v‖ ≤ δ/√n  and  n ≥ 2,

because `(n+1)/(2πn) ≤ 1/4 ⟺ 4(n+1) ≤ 2πn`, which holds for `n ≥ 2` since `π > 3`.  It
**fails at `n = 1`** (`8 ≤ 2π` is false), which is exactly why `2 ≤ n` is assumed. -/
theorem lens_defect_le_half {n : ℕ} (hn : 2 ≤ n) {δ t : ℝ} (hδ : 0 < δ)
    (htδ : t ≤ δ / Real.sqrt n) :
    t / δ * Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi)) ≤ 1 / 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hA : (0 : ℝ) ≤ ((n : ℝ) + 1) / (2 * Real.pi) := by positivity
  have hfrac : t / δ ≤ 1 / Real.sqrt n := by
    rw [div_le_div_iff₀ hδ hs]
    rw [le_div_iff₀ hs] at htδ
    linarith
  have hquarter : ((n : ℝ) + 1) / (2 * Real.pi) / (n : ℝ) ≤ 1 / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsplit : Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi)) / Real.sqrt n
      = Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi) / (n : ℝ)) := (Real.sqrt_div hA _).symm
  have hhalf : Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi) / (n : ℝ)) ≤ 1 / 2 := by
    have h := Real.sqrt_le_sqrt hquarter
    rwa [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at h
  calc t / δ * Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi))
      ≤ (1 / Real.sqrt n) * Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi)) := by
        gcongr
    _ = Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi)) / Real.sqrt n := by ring
    _ = Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi) / (n : ℝ)) := hsplit
    _ ≤ 1 / 2 := hhalf

/-- **`cor:overlap` for the speedy walk, at separation `δ/√n`**
(`1409.6011/vol3_journal.tex:612`), in exactly the shape
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap` binder demands, so that

    exact overlap_speedyWalk hn hK hδ hell h

discharges it for `P := speedyWalk K δ`.

For `u ∈ T`, `v ∉ T` in `K` with `‖u - v‖ < δ/√n`,

    1  ≤  20 · (P_u(Tᶜ) + P_v(T)).

**The local-conductance floor `hell` is a genuine extra hypothesis, and is *not* in the
paper.**  Cousins–Vempala derive `cor:overlap` from Lemma 3.5 of [KLS95], which bounds
`vol(K ∩ B(u,δ) ∩ B(v,δ))` below by `min{ℓ(u),ℓ(v)}·vol(δBₙ)/(e+1)` using convexity, with no
floor on `ℓ` at all.  That lemma is **not proved in this repository** (it needs a polar
decomposition of `K ∩ B(u,δ)` that Mathlib does not have), and what replaces it here is the
elementary chain "lens estimate + `vol(K ∩ B(u,δ)) ≤ vol(δBₙ)`", which only gives
`P_u(Tᶜ) + P_v(T) ≥ ℓ(u) - 1/2`.  Hence the floor `ℓ ≥ 11/20`, written division-free as
`11 ≤ 20·ℓ(x)`: it is `1/20 + 1/2`, and `1/2` is `lens_defect_le_half`.

The hypotheses `u ∈ T`, `v ∉ T` and `d_h(u,v) < 1/4` are not used; they are carried only so
the statement matches the consumer's binder.  In particular this is *stronger* than
`cor:overlap` in those three respects and *weaker* in requiring `hell`. -/
theorem overlap_speedyWalk {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    (hell : ∀ x ∈ K, (11 : ℝ≥0∞) ≤ 20 * ell K δ x)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  intro T hT u v _ huK _ _ hsep _
  set S : ℝ≥0∞ := speedyWalk K δ u Tᶜ + speedyWalk K δ v T with hSdef
  have hmain := ell_le_speedyWalk_add_speedyWalk_compl_sqrt hn hK hδ u v hT.compl
  rw [compl_compl] at hmain
  set r : ℝ := dist u v / δ * Real.sqrt (((n : ℝ) + 1) / (2 * Real.pi)) with hrdef
  have hr : r ≤ 1 / 2 := by
    rw [hrdef, dist_eq_norm]
    exact lens_defect_le_half hn hδ (le_of_lt hsep)
  have hr' : (20 : ℝ≥0∞) * ENNReal.ofReal r ≤ 10 := by
    rw [show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    rw [show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hkey : (11 : ℝ≥0∞) ≤ 20 * S + 10 := by
    calc (11 : ℝ≥0∞) ≤ 20 * ell K δ u := hell u huK
      _ ≤ 20 * (S + ENNReal.ofReal r) := by gcongr
      _ = 20 * S + 20 * ENNReal.ofReal r := by ring
      _ ≤ 20 * S + 10 := by gcongr
  by_contra hcon
  rw [not_le] at hcon
  have hlt : (20 : ℝ≥0∞) * S + 10 < 1 + 10 :=
    ENNReal.add_lt_add_right (by norm_num) hcon
  rw [show (1 : ℝ≥0∞) + 10 = 11 by norm_num] at hlt
  exact absurd hkey (not_le.2 hlt)

/-! ## 6. Non-vacuity, and the composition with `thm:speedyconductance` -/

/-- **Non-vacuity witness for `overlap_speedyWalk`.**  Every hypothesis holds
*simultaneously* at `n = 2`, `K = ℝ²`, `δ = 1`, `u = 0`, `v = (1/2, 0)`,
`T = B(0, 1/4)`, `h ≡ 1`:

* `ℓ ≡ 1` on `K = ℝ²`, so the floor `11 ≤ 20·ℓ` holds with room to spare;
* `u ∈ T`, `v ∉ T` (since `‖v‖ = 1/2 > 1/4`);
* `‖u - v‖ = 1/2 < 1/√2 = δ/√n`;
* `d_h(u,v) = 0 < 1/4`, and `1/4 < 1`, so `Arlib.densDist_le_one` does not make the
  density branch unsatisfiable.

**What this witness does *not* show, and the honest caveat.**  The floor `11 ≤ 20·ℓ(x)`
for *every* `x ∈ K` fails for every bounded convex body: at a boundary point of a convex
body `ℓ(x) → 1/2 < 11/20`.  So `overlap_speedyWalk` is non-vacuous but does **not** apply
to a convex body, only to bodies with no `δ`-thin boundary (`K = ℝⁿ` being the extreme
case).  The unconditional statement of this file is
`ell_le_speedyWalk_add_speedyWalk_compl_sqrt`, which has no floor at all; the floor is the
price of not having Lemma 3.5 of [KLS95]. -/
theorem exists_overlap_speedyWalk_witness :
    ∃ (K T : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ)
      (u v : EuclideanSpace ℝ (Fin 2)) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      MeasurableSet K ∧ MeasurableSet T ∧ 0 < δ ∧
      (∀ x ∈ K, (11 : ℝ≥0∞) ≤ 20 * ell K δ x) ∧
      u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < δ / Real.sqrt ((2 : ℕ) : ℝ) ∧ densDist h u v < 1 / 4 ∧
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  classical
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℝ) with hvdef
  have hvnorm : ‖v‖ = 1 / 2 := by
    rw [hvdef, PiLp.norm_single]
    rw [Real.norm_eq_abs]
    norm_num
  have hellu : ∀ x : EuclideanSpace ℝ (Fin 2), ell (Set.univ) (1 : ℝ) x = 1 := by
    intro x
    rw [ell_apply, Set.inter_univ,
      ENNReal.div_self (Metric.measure_ball_pos volume x (by norm_num)).ne'
        measure_ball_lt_top.ne]
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hs0 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by rw [hcast2]; norm_num)
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) < 2 := by
    have h1 : Real.sqrt ((2 : ℕ) : ℝ) ^ 2 = ((2 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg ((2 : ℕ) : ℝ), h1, hcast2]
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 2)) - v‖ < (1 : ℝ) / Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvnorm, div_lt_div_iff₀ (by norm_num) hs0]
    nlinarith [hs2]
  have hvT : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]
    norm_num
  have hfloor : ∀ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2))),
      (11 : ℝ≥0∞) ≤ 20 * ell (Set.univ) (1 : ℝ) x := by
    intro x _
    rw [hellu x]
    norm_num
  have hdens : densDist (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) 0 v < 1 / 4 := by
    simp [densDist]
  refine ⟨Set.univ, Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), 1, 0, v, fun _ => 1,
    MeasurableSet.univ, measurableSet_ball, by norm_num, hfloor,
    Metric.mem_ball_self (by norm_num), Set.mem_univ _, Set.mem_univ _, hvT, hsep, hdens, ?_⟩
  exact overlap_speedyWalk (n := 2) (by norm_num) MeasurableSet.univ (by norm_num) hfloor
    (fun _ => 1) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) measurableSet_ball 0 v
    (Metric.mem_ball_self (by norm_num)) (Set.mem_univ _) (Set.mem_univ _) hvT hsep hdens

/-- **`hoverlap` discharged, in `thm:speedyconductance`.**  This is
`Arlib.MarkovChains.conductance_speedyGaussian_ge` with its overlap hypothesis supplied by
`overlap_speedyWalk` — literally `exact overlap_speedyWalk hn hK hδ hell h` — for the
speedy walk `P = speedyWalk K δ`.  Only `hiso` (`thm:iso`, unproved in this repository) and
the local-conductance floor `hell` remain.

**This is not a polynomial-time statement and may not be quoted as one**: `hiso` is a
hypothesis, and `hell` restricts `K` (see `exists_overlap_speedyWalk_witness`). -/
theorem conductance_speedyGaussian_ge_of_ell {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hmass : 0 < ∫ x, h x)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hell : ∀ x ∈ K, (11 : ℝ≥0∞) ≤ 20 * ell K δ x)
    (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpi : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      pi A = ENNReal.ofReal (∫ x in A, h x) / ENNReal.ofReal (∫ x, h x))
    (hrev : IsReversible (speedyWalk K δ) pi) (hpiK : pi Kᶜ = 0)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n ≤ densDist h u v) →
      δ * Real.log 2 / Real.sqrt n / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ (∫ x, h x) * ∫ x in S₃, h x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyWalk K δ) pi :=
  conductance_speedyGaussian_ge hn hσ hδ hδσ hh0 hmass hK (speedyWalk K δ) pi hpi hrev hpiK
    (overlap_speedyWalk hn hK hδ hell h) hiso

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.gamma_add_half_le_sqrt_mul
#print axioms Arlib.MarkovChains.sqrt_pi_pow_div_gamma_le
#print axioms Arlib.MarkovChains.volume_ball_succ_ratio
#print axioms Arlib.MarkovChains.volume_slab_le
#print axioms Arlib.MarkovChains.measurableSet_coordSlab
#print axioms Arlib.MarkovChains.volume_ball_le_volume_inter_ball_add_sqrt
#print axioms Arlib.MarkovChains.ell_le_speedyWalk_add_speedyWalk_compl_sqrt
#print axioms Arlib.MarkovChains.lens_defect_le_half
#print axioms Arlib.MarkovChains.overlap_speedyWalk
#print axioms Arlib.MarkovChains.exists_overlap_speedyWalk_witness
#print axioms Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell
