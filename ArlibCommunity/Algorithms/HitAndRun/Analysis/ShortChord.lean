/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.ChordPoint

/-!
# Short chords are rare

The capped chord sampling can only give up often on a short chord.  `shrunk K c δ`, the
body shrunk towards the centre `c` of its unit ball by the factor `1 − δ`, consists of
points every chord through which is long:

* `ball_subset_of_mem_shrunk`: if `x ∈ shrunk K c δ`, the ball of radius `δ` around `x` is
  in `K` (a convex combination of `K` and the unit ball), so every chord through `x` has
  length at least `2δ` (`two_mul_le_volume_chordSet`);
* `target_shrunk_compl_le`: the uniform law on `K` gives the rest of `K` mass at most
  `n · δ`, because the shrunk body has volume `(1 − δ)ⁿ · vol K` (`1 − (1 − δ)ⁿ ≤ nδ`).
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Foundations.MarkovChainTheory (chordSet)

variable {n : ℕ}

/-- The body shrunk towards `c` by the factor `1 − δ`. -/
def shrunk (K : Set (State n)) (c : State n) (δ : ℝ) : Set (State n) :=
  (fun y => c + (1 - δ) • (y - c)) '' K

variable {K : Set (State n)} {c : State n} {δ : ℝ}

/-- Every point of the shrunk body has a ball of radius `δ` around it in `K`. -/
theorem add_mem_of_mem_shrunk (hKc : Convex ℝ K) (hball : closedBall c 1 ⊆ K)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : State n} (hx : x ∈ shrunk K c δ) {v : State n}
    (hv : ‖v‖ ≤ δ) : x + v ∈ K := by
  obtain ⟨k, hk, rfl⟩ := hx
  have hb : c + δ⁻¹ • v ∈ K := hball (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hδ0)]
    exact (inv_mul_le_one₀ hδ0).2 hv)
  have heq : c + (1 - δ) • (k - c) + v = (1 - δ) • k + δ • (c + δ⁻¹ • v) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hδ0.ne', one_smul]
    module
  rw [heq]
  exact hKc hk hb (by linarith) hδ0.le (by ring)

/-- **Chords through the shrunk body are long**: every unit direction's chord contains
`[-δ, δ]`. -/
theorem Icc_subset_chordSet_of_mem_shrunk (hKc : Convex ℝ K) (hball : closedBall c 1 ⊆ K)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : State n} (hx : x ∈ shrunk K c δ) {θ : State n}
    (hθ : ‖θ‖ = 1) : Icc (-δ) δ ⊆ chordSet K x θ := by
  intro t ht
  rw [ArlibCommunity.Foundations.MarkovChainTheory.mem_chordSet_iff]
  refine add_mem_of_mem_shrunk hKc hball hδ0 hδ1 hx ?_
  rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_le]
  exact ht

theorem two_mul_le_volume_chordSet (hKc : Convex ℝ K) (hball : closedBall c 1 ⊆ K)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : State n} (hx : x ∈ shrunk K c δ) {θ : State n}
    (hθ : ‖θ‖ = 1) : ENNReal.ofReal (2 * δ) ≤ volume (chordSet K x θ) := by
  calc ENNReal.ofReal (2 * δ) = volume (Icc (-δ) δ) := by rw [Real.volume_Icc]; ring_nf
    _ ≤ _ := measure_mono (Icc_subset_chordSet_of_mem_shrunk hKc hball hδ0 hδ1 hx hθ)

/-- The shrunk body is the preimage of `K` under the inverse homothety. -/
theorem shrunk_eq_preimage (hδ1 : δ < 1) :
    shrunk K c δ = (fun x => c + (1 - δ)⁻¹ • (x - c)) ⁻¹' K := by
  have hne : (1 - δ) ≠ 0 := by linarith
  ext x
  simp only [shrunk, mem_image, mem_preimage]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hne, one_smul, add_sub_cancel]
    exact hk
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]

theorem measurableSet_shrunk (hK : MeasurableSet K) (hδ1 : δ < 1) :
    MeasurableSet (shrunk K c δ) := by
  rw [shrunk_eq_preimage hδ1]
  exact hK.preimage (by fun_prop)

theorem shrunk_subset (hKc : Convex ℝ K) (hball : closedBall c 1 ⊆ K) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) : shrunk K c δ ⊆ K := by
  rintro _ ⟨k, hk, rfl⟩
  have hc : c ∈ K := hball (mem_closedBall_self zero_le_one)
  have heq : c + (1 - δ) • (k - c) = (1 - δ) • k + δ • c := by module
  show c + (1 - δ) • (k - c) ∈ K
  rw [heq]
  exact hKc hk hc (by linarith) hδ0 (by ring)

/-- The shrunk body has volume `(1 − δ)ⁿ · vol K`. -/
theorem volume_shrunk (hδ1 : δ ≤ 1) :
    volume (shrunk K c δ) = ENNReal.ofReal ((1 - δ) ^ n) * volume K := by
  have himage : shrunk K c δ = AffineMap.homothety c (1 - δ) '' K := by
    ext x
    simp only [shrunk, AffineMap.homothety_apply, mem_image, vsub_eq_sub, vadd_eq_add]
    constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, hk, by rw [add_comm]⟩
  rw [himage, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ) n)]

/-- **The uniform law on `K` gives the rest of `K` mass at most `n · δ`.** -/
theorem target_shrunk_compl_le (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hball : closedBall c 1 ⊆ K) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    target K (shrunk K c δ)ᶜ ≤ ENNReal.ofReal (n * δ) := by
  have hsub := shrunk_subset hKc hball hδ0 hδ1.le
  have hSm := measurableSet_shrunk (c := c) hK hδ1
  have hK0 : volume K ≠ 0 := fun h => by
    have := measure_mono (μ := volume) hball
    rw [h, nonpos_iff_eq_zero] at this
    exact (measure_closedBall_pos volume c one_pos).ne' this
  have hKtop : volume K ≠ ⊤ := hKb.measure_lt_top.ne
  have hdiff : volume (K ∩ (shrunk K c δ)ᶜ) = volume K - volume (shrunk K c δ) := by
    rw [← sdiff_eq, measure_sdiff hsub hSm.nullMeasurableSet
      (measure_ne_top_of_subset hsub hKtop)]
  rw [target, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hSm.compl,
    inter_comm, hdiff, volume_shrunk hδ1.le]
  have hfac : volume K - ENNReal.ofReal ((1 - δ) ^ n) * volume K =
      (1 - ENNReal.ofReal ((1 - δ) ^ n)) * volume K := by
    rw [ENNReal.sub_mul (fun _ _ => hKtop), one_mul]
  rw [hfac, ← mul_assoc, mul_comm _ (1 - _), mul_assoc, ENNReal.inv_mul_cancel hK0 hKtop,
    mul_one, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (pow_nonneg (by linarith) n)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -δ) n
  rw [← sub_eq_add_neg] at this
  linarith

end ArlibCommunity.Algorithms.HitAndRun
