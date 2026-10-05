/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailHazardReduction

/-!
# Shell geometry and the initial Markov split for the LV tail
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

variable {n : ℕ}

theorem norm_needleMap_le_center_add
    (p e : EuclideanSpace ℝ (Fin n)) (z t : ℝ) :
    ‖needleMap p e t‖ ≤ ‖needleMap p e z‖ + ‖e‖ * |t - z| := by
  have hmap : needleMap p e t = needleMap p e z + (t - z) • e := by
    simp_rw [needleMap_apply]
    module
  rw [hmap]
  calc
    ‖needleMap p e z + (t - z) • e‖ ≤ ‖needleMap p e z‖ + ‖(t - z) • e‖ :=
      norm_add_le _ _
    _ = ‖needleMap p e z‖ + ‖e‖ * |t - z| := by
      rw [norm_smul, Real.norm_eq_abs]
      ring

/-- The coarser shell comparison avoiding quadratic-root intersection arithmetic. -/
theorem abs_sub_gt_of_norm_needleMap_gt_shell
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0) {z t M : ℝ} (hM : 0 < M)
    (hz : ‖needleMap p e z‖ ≤ Real.sqrt M) (k : ℕ)
    (hout : Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * k) <
      ‖needleMap p e t‖) :
    Real.sqrt 2 * (Real.sqrt M / ‖e‖) +
        4 * Real.sqrt 3 * (Real.sqrt M / ‖e‖) * k < |t - z| := by
  have heN : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have htri := norm_needleMap_le_center_add p e z t
  by_contra h
  have habs : |t - z| ≤ Real.sqrt 2 * (Real.sqrt M / ‖e‖) +
      4 * Real.sqrt 3 * (Real.sqrt M / ‖e‖) * k := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left habs heN.le
  have he0 : ‖e‖ ≠ 0 := ne_of_gt heN
  field_simp [he0] at hmul
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

/-- Markov supplies the half-mass premise at the first right grid point. -/
theorem rightHalf_at_sqrtTwo_of_variance
    {a b z s : ℝ} {D : ℝ → ℝ} (_hab : a ≤ b) (hs : 0 < s)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDint : IntervalIntegrable D volume a b)
    (hvar : (∫ t in a..b, (t - z) ^ 2 * D t) ≤ s ^ 2 * ∫ t in a..b, D t)
    (hrb : z + Real.sqrt 2 * s ≤ b) (haz : a ≤ z) :
    (∫ t in a..b, D t) ≤ 2 * ∫ t in a..(z + Real.sqrt 2 * s), D t := by
  let r := z + Real.sqrt 2 * s
  have hzr : z ≤ r := by
    dsimp [r]
    nlinarith [Real.sqrt_nonneg 2]
  have har : a ≤ r := haz.trans hzr
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqint : IntervalIntegrable (fun t => (t - z) ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hsqtail := Arlib.intervalIntegrable_of_subinterval hsqint har hrb le_rfl
  have hconsttail := (Arlib.intervalIntegrable_of_subinterval hDint har hrb le_rfl).const_mul
    (2 * s ^ 2)
  have hlower : (2 * s ^ 2) * (∫ t in r..b, D t) ≤
      ∫ t in r..b, (t - z) ^ 2 * D t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hrb hconsttail hsqtail ?_
    intro t ht
    have htz : Real.sqrt 2 * s ≤ t - z := by dsimp [r] at ht; linarith [ht.1]
    have hsq : 2 * s ^ 2 ≤ (t - z) ^ 2 := by
      nlinarith [sq_nonneg (t - z - Real.sqrt 2 * s), Real.sqrt_nonneg 2, hs2]
    exact mul_le_mul_of_nonneg_right hsq (hD0 t ⟨har.trans ht.1, ht.2⟩)
  have hleft0 : 0 ≤ ∫ t in a..r, (t - z) ^ 2 * D t :=
    intervalIntegral.integral_nonneg har fun t ht =>
      mul_nonneg (sq_nonneg _) (hD0 t ⟨ht.1, ht.2.trans hrb⟩)
  have haddsq := intervalIntegral.integral_add_adjacent_intervals
    (Arlib.intervalIntegrable_of_subinterval hsqint le_rfl har hrb) hsqtail
  have htailTotal : (∫ t in r..b, (t - z) ^ 2 * D t) ≤
      ∫ t in a..b, (t - z) ^ 2 * D t := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (Arlib.intervalIntegrable_of_subinterval hDint le_rfl har hrb)
    (Arlib.intervalIntegrable_of_subinterval hDint har hrb le_rfl)
  dsimp [r] at *
  nlinarith [sq_pos_of_pos hs]

/-- Reflected Markov half-mass premise at the first left grid point. -/
theorem leftHalf_at_sqrtTwo_of_variance
    {a b z s : ℝ} {D : ℝ → ℝ} (_hab : a ≤ b) (hs : 0 < s)
    (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t) (hDint : IntervalIntegrable D volume a b)
    (hvar : (∫ t in a..b, (t - z) ^ 2 * D t) ≤ s ^ 2 * ∫ t in a..b, D t)
    (hal : a ≤ z - Real.sqrt 2 * s) (hzb : z ≤ b) :
    (∫ t in a..b, D t) ≤ 2 * ∫ t in (z - Real.sqrt 2 * s)..b, D t := by
  let l := z - Real.sqrt 2 * s
  have hlz : l ≤ z := by
    dsimp [l]
    nlinarith [Real.sqrt_nonneg 2]
  have hlb : l ≤ b := hlz.trans hzb
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqint : IntervalIntegrable (fun t => (t - z) ^ 2 * D t) volume a b :=
    hDint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hsqtail := Arlib.intervalIntegrable_of_subinterval hsqint le_rfl hal hlb
  have hconsttail := (Arlib.intervalIntegrable_of_subinterval hDint le_rfl hal hlb).const_mul
    (2 * s ^ 2)
  have hlower : (2 * s ^ 2) * (∫ t in a..l, D t) ≤
      ∫ t in a..l, (t - z) ^ 2 * D t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hal hconsttail hsqtail ?_
    intro t ht
    have htz : t - z ≤ -(Real.sqrt 2 * s) := by dsimp [l] at ht; linarith [ht.2]
    have hsq : 2 * s ^ 2 ≤ (t - z) ^ 2 := by
      nlinarith [sq_nonneg (t - z + Real.sqrt 2 * s), Real.sqrt_nonneg 2, hs2]
    exact mul_le_mul_of_nonneg_right hsq (hD0 t ⟨ht.1, ht.2.trans hlb⟩)
  have hright0 : 0 ≤ ∫ t in l..b, (t - z) ^ 2 * D t :=
    intervalIntegral.integral_nonneg hlb fun t ht =>
      mul_nonneg (sq_nonneg _) (hD0 t ⟨hal.trans ht.1, ht.2⟩)
  have haddsq := intervalIntegral.integral_add_adjacent_intervals hsqtail
    (Arlib.intervalIntegrable_of_subinterval hsqint hal hlb le_rfl)
  have htailTotal : (∫ t in a..l, (t - z) ^ 2 * D t) ≤
      ∫ t in a..b, (t - z) ^ 2 * D t := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (Arlib.intervalIntegrable_of_subinterval hDint le_rfl hal hlb)
    (Arlib.intervalIntegrable_of_subinterval hDint hal hlb le_rfl)
  dsimp [l] at *
  nlinarith [sq_pos_of_pos hs]

/-- Right-tail dyadic decay, with Markov's initial half-mass factor included. -/
theorem rightTail_pow_two_succ_le_mass
    {a b z s : ℝ} {D : ℝ → ℝ} (hab : a ≤ b) (hs : 0 < s)
    (hDlc : LogConcaveOn (Icc a b) D) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b) (hz : z ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - z) ^ 2 * D t) ≤ s ^ 2 * ∫ t in a..b, D t)
    (N : ℕ) (hrNb : z + Real.sqrt 2 * s + 4 * Real.sqrt 3 * s * N ≤ b) :
    (2 : ℝ) ^ (N + 1) *
        (∫ t in (z + Real.sqrt 2 * s + 4 * Real.sqrt 3 * s * N)..b, D t) ≤
      ∫ t in a..b, D t := by
  let step : ℝ := 4 * Real.sqrt 3 * s
  let u : ℕ → ℝ := fun k => z + Real.sqrt 2 * s + step * k
  have hstep0 : 0 ≤ step := by dsimp [step]; positivity
  have hbase0 : 0 ≤ Real.sqrt 2 * s := mul_nonneg (Real.sqrt_nonneg _) hs.le
  have hu0 : u 0 = z + Real.sqrt 2 * s := by simp [u]
  have huN : u N = z + Real.sqrt 2 * s + 4 * Real.sqrt 3 * s * N := by rfl
  have hau0 : a ≤ u 0 := by rw [hu0]; linarith [hz.1]
  have huNb : u N ≤ b := by rw [huN]; exact hrNb
  have hu0N : u 0 ≤ u N := by
    dsimp [u]
    nlinarith [mul_nonneg hstep0 (Nat.cast_nonneg N)]
  have hgrid : ∀ k < N, a ≤ u k ∧ u k ≤ u (k + 1) ∧ u (k + 1) ≤ b ∧
      u (k + 1) - u k = 4 * Real.sqrt 3 * s := by
    intro k hk
    have hcast : (k : ℝ) ≤ k + 1 := by norm_num
    have hcastN : (k + 1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.2 hk)
    have hkk : step * (k : ℝ) ≤ step * (k + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hstep0
    have hkN : step * (k + 1 : ℝ) ≤ step * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hcastN hstep0
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hu0k : u 0 ≤ u k := by
        dsimp [u]
        nlinarith [mul_nonneg hstep0 (Nat.cast_nonneg k)]
      exact hau0.trans hu0k
    · simpa [u, Nat.cast_add, Nat.cast_one] using
        add_le_add_left hkk (z + Real.sqrt 2 * s)
    · exact (show u (k + 1) ≤ u N by
        simpa [u, Nat.cast_add, Nat.cast_one] using
          add_le_add_left hkN (z + Real.sqrt 2 * s)).trans huNb
    · dsimp [u, step]
      push_cast
      ring
  have hhalf0 := rightHalf_at_sqrtTwo_of_variance hab hs hD0 hDint hvar
    (by rw [← hu0]; exact hu0N.trans huNb) hz.1
  have hhalf : ∀ k ≤ N, (∫ t in a..b, D t) ≤ 2 * ∫ t in a..u k, D t := by
    intro k hk
    have hcast : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hu0k : u 0 ≤ u k := by
      dsimp [u]
      nlinarith [mul_nonneg hstep0 hcast]
    have hcastN : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hukN : u k ≤ u N := by
      simpa [u] using add_le_add_left (mul_le_mul_of_nonneg_left hcastN hstep0)
        (z + Real.sqrt 2 * s)
    have hukb := hukN.trans huNb
    have hmid0 : 0 ≤ ∫ t in u 0..u k, D t :=
      intervalIntegral.integral_nonneg hu0k fun t ht => hD0 t ⟨hau0.trans ht.1, ht.2.trans hukb⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hDint le_rfl hau0 (hu0N.trans huNb))
      (Arlib.intervalIntegrable_of_subinterval hDint hau0 hu0k hukb)
    rw [← hu0] at hhalf0
    nlinarith
  have hp := oneDim_logConcave_rightTail_pow_two hs hDlc hD0 hDint hz hvar u N hgrid hhalf
  have htail0 : 2 * (∫ t in u 0..b, D t) ≤ ∫ t in a..b, D t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hDint le_rfl hau0 (hu0N.trans huNb))
      (Arlib.intervalIntegrable_of_subinterval hDint hau0 (hu0N.trans huNb) le_rfl)
    rw [← hu0] at hhalf0
    nlinarith
  have hp2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (2 : ℝ) ^ (N + 1) *
        (∫ t in (z + Real.sqrt 2 * s + 4 * Real.sqrt 3 * s * N)..b, D t) =
      2 * ((2 : ℝ) ^ N * ∫ t in u N..b, D t) := by rw [huN, pow_succ]; ring
    _ ≤ 2 * (∫ t in u 0..b, D t) := hp2
    _ ≤ ∫ t in a..b, D t := htail0

/-- Left-tail dyadic decay, with Markov's initial half-mass factor included. -/
theorem leftTail_pow_two_succ_le_mass
    {a b z s : ℝ} {D : ℝ → ℝ} (hab : a ≤ b) (hs : 0 < s)
    (hDlc : LogConcaveOn (Icc a b) D) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume a b) (hz : z ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - z) ^ 2 * D t) ≤ s ^ 2 * ∫ t in a..b, D t)
    (N : ℕ) (halN : a ≤ z - Real.sqrt 2 * s - 4 * Real.sqrt 3 * s * N) :
    (2 : ℝ) ^ (N + 1) *
        (∫ t in a..(z - Real.sqrt 2 * s - 4 * Real.sqrt 3 * s * N), D t) ≤
      ∫ t in a..b, D t := by
  let step : ℝ := 4 * Real.sqrt 3 * s
  let u : ℕ → ℝ := fun k => z - Real.sqrt 2 * s - step * N + step * k
  have hstep0 : 0 ≤ step := by dsimp [step]; positivity
  have hu0 : u 0 = z - Real.sqrt 2 * s - 4 * Real.sqrt 3 * s * N := by
    dsimp [u, step]
    ring
  have huN : u N = z - Real.sqrt 2 * s := by dsimp [u]; ring
  have hau0 : a ≤ u 0 := by rw [hu0]; exact halN
  have huNb : u N ≤ b := by rw [huN]; nlinarith [hz.2, Real.sqrt_nonneg 2]
  have hu0N : u 0 ≤ u N := by
    dsimp [u]
    nlinarith [mul_nonneg hstep0 (Nat.cast_nonneg N)]
  have hgrid : ∀ k < N, a ≤ u k ∧ u k ≤ u (k + 1) ∧ u (k + 1) ≤ b ∧
      u (k + 1) - u k = 4 * Real.sqrt 3 * s := by
    intro k hk
    have hcast : (k : ℝ) ≤ k + 1 := by norm_num
    have hcastN : (k + 1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.2 hk)
    have hkk := mul_le_mul_of_nonneg_left hcast hstep0
    have hkN := mul_le_mul_of_nonneg_left hcastN hstep0
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hau0.trans (show u 0 ≤ u k by
        dsimp [u]
        nlinarith [mul_nonneg hstep0 (Nat.cast_nonneg k)])
    · simpa [u, Nat.cast_add, Nat.cast_one] using hkk
    · exact (show u (k + 1) ≤ u N by
        dsimp [u]
        push_cast at hkN ⊢
        nlinarith).trans huNb
    · dsimp [u, step]
      push_cast
      ring
  have hhalfN := leftHalf_at_sqrtTwo_of_variance hab hs hD0 hDint hvar
    (by rw [← huN]; exact hau0.trans hu0N) hz.2
  have hhalf : ∀ k ≤ N, (∫ t in a..b, D t) ≤ 2 * ∫ t in u k..b, D t := by
    intro k hk
    have hcastN : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hukN : u k ≤ u N := by
      have hh := mul_le_mul_of_nonneg_left hcastN hstep0
      dsimp [u]
      nlinarith
    have hauk : a ≤ u k := hau0.trans (show u 0 ≤ u k by
      dsimp [u]
      nlinarith [mul_nonneg hstep0 (Nat.cast_nonneg k)])
    have hmid0 : 0 ≤ ∫ t in u k..u N, D t :=
      intervalIntegral.integral_nonneg hukN fun t ht => hD0 t ⟨hauk.trans ht.1, ht.2.trans huNb⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hDint hauk hukN huNb)
      (Arlib.intervalIntegrable_of_subinterval hDint (hauk.trans hukN) huNb le_rfl)
    rw [← huN] at hhalfN
    nlinarith
  have hp := oneDim_logConcave_leftTail_pow_two hs hDlc hD0 hDint hz hvar u N hgrid hhalf
  have htailN : 2 * (∫ t in a..u N, D t) ≤ ∫ t in a..b, D t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hDint le_rfl (hau0.trans hu0N) huNb)
      (Arlib.intervalIntegrable_of_subinterval hDint (hau0.trans hu0N) huNb le_rfl)
    rw [← huN] at hhalfN
    nlinarith
  have hp2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (2 : ℝ) ^ (N + 1) *
        (∫ t in a..(z - Real.sqrt 2 * s - 4 * Real.sqrt 3 * s * N), D t) =
      2 * ((2 : ℝ) ^ N * ∫ t in a..u 0, D t) := by rw [hu0, pow_succ]; ring
    _ ≤ 2 * (∫ t in a..u N, D t) := hp2
    _ ≤ ∫ t in a..b, D t := htailN

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.abs_sub_gt_of_norm_needleMap_gt_shell
#print axioms Ttc.CVAdaptive.rightHalf_at_sqrtTwo_of_variance
#print axioms Ttc.CVAdaptive.leftHalf_at_sqrtTwo_of_variance
#print axioms Ttc.CVAdaptive.rightTail_pow_two_succ_le_mass
#print axioms Ttc.CVAdaptive.leftTail_pow_two_succ_le_mass
