/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.ConcaveProfileIso

/-!
# A direct log-concave hazard step for moment-radius tails

This is the analytic step needed for a weaker, but still logarithmic-radius, replacement of
Lovasz--Vempala Lemma 5.7.  It avoids the exponential-extremizer theorem.  Hensley's bound and
one-dimensional log-concave hazard monotonicity give isoperimetric coefficient
`1 / (2 * sqrt 3 * s)` for a profile with second moment at most `s^2`.  Consequently a right
tail is halved whenever its threshold is advanced by `4 * sqrt 3 * s`, once at least half of
the mass lies to its left.  Reflection gives the identical left-tail statement.

Iterating the step yields decay `2^{-k}` outside an initial median-radius interval, hence a
truncation radius

`sqrt 2 * R + 4 * sqrt 3 * R * ceil(log_2(1/eps))`.

The only remaining global transport is localization of the ball/annulus indicators (or a
continuous approximation thereof); no affine/exponential extremizer is used in this step.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

/-- **Direct hazard tail-halving step.**  Under a second moment bound at scale `s`, if the
mass to the left of `u` is at least half the total mass, moving the threshold from `u` to
`v = u + 4*sqrt(3)*s` halves the remaining right tail. -/
theorem oneDim_logConcave_rightTail_halves
    {a b c s u v : ℝ} {w : ℝ → ℝ} (hs : 0 < s)
    (hw : LogConcaveOn (Icc a b) w)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤
      s ^ 2 * ∫ t in a..b, w t)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hstep : v - u = 4 * Real.sqrt 3 * s)
    (hhalf : (∫ t in a..b, w t) ≤ 2 * ∫ t in a..u, w t) :
    2 * (∫ t in v..b, w t) ≤ ∫ t in u..b, w t := by
  let Z : ℝ := ∫ t in a..b, w t
  let L : ℝ := ∫ t in a..u, w t
  let M : ℝ := ∫ t in u..v, w t
  let R : ℝ := ∫ t in v..b, w t
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hL0 : 0 ≤ L := intervalIntegral.integral_nonneg hau fun t ht =>
    hw0 t ⟨ht.1, by linarith [ht.2, huv, hvb]⟩
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg huv fun t ht =>
    hw0 t ⟨by linarith [ht.1, hau], by linarith [ht.2, hvb]⟩
  have hR0 : 0 ≤ R := intervalIntegral.integral_nonneg hvb fun t ht =>
    hw0 t ⟨by linarith [ht.1, hau, huv], ht.2⟩
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg (hau.trans (huv.trans hvb))
    fun t ht => hw0 t ht
  have hsum : L + M + R = Z := by
    have h1 : L + M = ∫ t in a..v, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (Arlib.intervalIntegrable_of_subinterval hint le_rfl hau (huv.trans hvb))
        (Arlib.intervalIntegrable_of_subinterval hint hau huv hvb)
    have h2 : (∫ t in a..v, w t) + R = Z :=
      intervalIntegral.integral_add_adjacent_intervals
        (Arlib.intervalIntegrable_of_subinterval hint le_rfl (hau.trans huv) hvb)
        (Arlib.intervalIntegrable_of_subinterval hint (hau.trans huv) hvb le_rfl)
    rw [h1]
    exact h2
  have hiso := Arlib.oneDim_isoperimetry_variance hs hw hw0 hint hc hvar hau huv hvb
  have hcoef :
      1 / (2 * Real.sqrt 3 * s) * ((v - u) * (L * R)) = 2 * L * R := by
    rw [hstep]
    field_simp
    ring
  rw [show (∫ t in a..u, w t) = L by rfl,
    show (∫ t in u..v, w t) = M by rfl,
    show (∫ t in v..b, w t) = R by rfl,
    show (∫ t in a..b, w t) = Z by rfl, hcoef] at hiso
  have hRM : R ≤ M := by
    rcases hZ0.eq_or_lt with hZeq | hZpos
    · have : L = 0 ∧ M = 0 ∧ R = 0 := by
        constructor
        · nlinarith
        constructor <;> nlinarith
      simp [this.2.2, this.2.1]
    · have hZL : Z ≤ 2 * L := by simpa only [Z, L] using hhalf
      have hZR : Z * R ≤ 2 * L * R :=
        mul_le_mul_of_nonneg_right hZL hR0
      have : Z * R ≤ Z * M := hZR.trans hiso
      nlinarith
  have htail : (∫ t in u..b, w t) = M + R :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hint hau huv hvb)
      (Arlib.intervalIntegrable_of_subinterval hint (hau.trans huv) hvb le_rfl)).symm
  rw [htail]
  linarith

/-- Reflected left-tail version of `oneDim_logConcave_rightTail_halves`. -/
theorem oneDim_logConcave_leftTail_halves
    {a b c s u v : ℝ} {w : ℝ → ℝ} (hs : 0 < s)
    (hw : LogConcaveOn (Icc a b) w)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤
      s ^ 2 * ∫ t in a..b, w t)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hstep : v - u = 4 * Real.sqrt 3 * s)
    (hhalf : (∫ t in a..b, w t) ≤ 2 * ∫ t in v..b, w t) :
    2 * (∫ t in a..u, w t) ≤ ∫ t in a..v, w t := by
  let Z : ℝ := ∫ t in a..b, w t
  let L : ℝ := ∫ t in a..u, w t
  let M : ℝ := ∫ t in u..v, w t
  let R : ℝ := ∫ t in v..b, w t
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hL0 : 0 ≤ L := intervalIntegral.integral_nonneg hau fun t ht =>
    hw0 t ⟨ht.1, by linarith [ht.2, huv, hvb]⟩
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg huv fun t ht =>
    hw0 t ⟨by linarith [ht.1, hau], by linarith [ht.2, hvb]⟩
  have hR0 : 0 ≤ R := intervalIntegral.integral_nonneg hvb fun t ht =>
    hw0 t ⟨by linarith [ht.1, hau, huv], ht.2⟩
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg (hau.trans (huv.trans hvb))
    fun t ht => hw0 t ht
  have hsum : L + M + R = Z := by
    have h1 : L + M = ∫ t in a..v, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (Arlib.intervalIntegrable_of_subinterval hint le_rfl hau (huv.trans hvb))
        (Arlib.intervalIntegrable_of_subinterval hint hau huv hvb)
    have h2 : (∫ t in a..v, w t) + R = Z :=
      intervalIntegral.integral_add_adjacent_intervals
        (Arlib.intervalIntegrable_of_subinterval hint le_rfl (hau.trans huv) hvb)
        (Arlib.intervalIntegrable_of_subinterval hint (hau.trans huv) hvb le_rfl)
    rw [h1]
    exact h2
  have hiso := Arlib.oneDim_isoperimetry_variance hs hw hw0 hint hc hvar hau huv hvb
  have hcoef :
      1 / (2 * Real.sqrt 3 * s) * ((v - u) * (L * R)) = 2 * L * R := by
    rw [hstep]
    field_simp
    ring
  rw [show (∫ t in a..u, w t) = L by rfl,
    show (∫ t in u..v, w t) = M by rfl,
    show (∫ t in v..b, w t) = R by rfl,
    show (∫ t in a..b, w t) = Z by rfl, hcoef] at hiso
  have hLM : L ≤ M := by
    rcases hZ0.eq_or_lt with hZeq | hZpos
    · have : L = 0 ∧ M = 0 ∧ R = 0 := by
        constructor
        · nlinarith
        constructor <;> nlinarith
      simp [this.1, this.2.1]
    · have hZR : Z ≤ 2 * R := by simpa only [Z, R] using hhalf
      have hZL : Z * L ≤ 2 * L * R := by
        nlinarith [mul_le_mul_of_nonneg_left hZR hL0]
      have : Z * L ≤ Z * M := hZL.trans hiso
      nlinarith
  have htail : (∫ t in a..v, w t) = L + M :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Arlib.intervalIntegrable_of_subinterval hint le_rfl hau (huv.trans hvb))
      (Arlib.intervalIntegrable_of_subinterval hint hau huv hvb)).symm
  rw [htail]
  linarith

/-- Iterated right-tail decay along a grid of `4*sqrt(3)*s` shells.  The half-mass premise is
listed at each grid point so this lemma is directly reusable after either a Markov estimate or
monotonicity of the cumulative mass has established it. -/
theorem oneDim_logConcave_rightTail_pow_two
    {a b c s : ℝ} {w : ℝ → ℝ} (hs : 0 < s)
    (hw : LogConcaveOn (Icc a b) w)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤
      s ^ 2 * ∫ t in a..b, w t)
    (u : ℕ → ℝ) (N : ℕ)
    (hgrid : ∀ k < N, a ≤ u k ∧ u k ≤ u (k + 1) ∧ u (k + 1) ≤ b ∧
      u (k + 1) - u k = 4 * Real.sqrt 3 * s)
    (hhalf : ∀ k ≤ N, (∫ t in a..b, w t) ≤ 2 * ∫ t in a..u k, w t) :
    (2 : ℝ) ^ N * (∫ t in u N..b, w t) ≤ ∫ t in u 0..b, w t := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hN := hgrid N (Nat.lt_succ_self N)
      have hstep := oneDim_logConcave_rightTail_halves hs hw hw0 hint hc hvar
        hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 (hhalf N (Nat.le_succ N))
      have ih' := ih (fun k hk => hgrid k (hk.trans (Nat.lt_succ_self N)))
        (fun k hk => hhalf k (hk.trans (Nat.le_succ N)))
      calc
        (2 : ℝ) ^ (N + 1) * (∫ t in u (N + 1)..b, w t) =
            (2 : ℝ) ^ N * (2 * ∫ t in u (N + 1)..b, w t) := by
              rw [pow_succ]
              ring
        _ ≤ (2 : ℝ) ^ N * (∫ t in u N..b, w t) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ ∫ t in u 0..b, w t := ih'

/-- Iterated reflected left-tail decay along the same fixed-width grid. -/
theorem oneDim_logConcave_leftTail_pow_two
    {a b c s : ℝ} {w : ℝ → ℝ} (hs : 0 < s)
    (hw : LogConcaveOn (Icc a b) w)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Icc a b)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤
      s ^ 2 * ∫ t in a..b, w t)
    (u : ℕ → ℝ) (N : ℕ)
    (hgrid : ∀ k < N, a ≤ u k ∧ u k ≤ u (k + 1) ∧ u (k + 1) ≤ b ∧
      u (k + 1) - u k = 4 * Real.sqrt 3 * s)
    (hhalf : ∀ k ≤ N, (∫ t in a..b, w t) ≤ 2 * ∫ t in u k..b, w t) :
    (2 : ℝ) ^ N * (∫ t in a..u 0, w t) ≤ ∫ t in a..u N, w t := by
  induction N generalizing u with
  | zero => simp
  | succ N ih =>
      have h0 := hgrid 0 (Nat.zero_lt_succ N)
      have hstep := oneDim_logConcave_leftTail_halves hs hw hw0 hint hc hvar
        h0.1 h0.2.1 h0.2.2.1 h0.2.2.2 (hhalf 1 (Nat.succ_le_succ (Nat.zero_le N)))
      let v : ℕ → ℝ := fun k => u (k + 1)
      have ih' := ih (u := v)
        (fun k hk => by
          simpa [v, Nat.add_assoc] using hgrid (k + 1) (Nat.succ_lt_succ hk))
        (fun k hk => by simpa [v] using hhalf (k + 1) (Nat.succ_le_succ hk))
      calc
        (2 : ℝ) ^ (N + 1) * (∫ t in a..u 0, w t) =
            (2 : ℝ) ^ N * (2 * ∫ t in a..u 0, w t) := by
              rw [pow_succ]
              ring
        _ ≤ (2 : ℝ) ^ N * (∫ t in a..u 1, w t) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ ∫ t in a..u (N + 1), w t := by simpa [v] using ih'

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.oneDim_logConcave_rightTail_halves
#print axioms Ttc.CVAdaptive.oneDim_logConcave_leftTail_halves
#print axioms Ttc.CVAdaptive.oneDim_logConcave_rightTail_pow_two
#print axioms Ttc.CVAdaptive.oneDim_logConcave_leftTail_pow_two
