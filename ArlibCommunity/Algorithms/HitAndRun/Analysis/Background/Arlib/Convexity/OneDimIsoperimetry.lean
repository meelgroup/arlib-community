/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatioOneDim
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Isoperimetry

/-!
# One-dimensional isoperimetry for log-concave weights

This file proves the one-dimensional isoperimetric inequality that Cousins–Vempala's
Theorem 3.4 (`thm:iso`) is reduced to by the Localization Lemma, namely inequality
`(1d-2)` of `vol3_journal.tex:501`.

## Main results

* `Arlib.logConcaveOn_mul_le_mul_shift` — the *cross form* of log-concavity on an
  interval: for `s ≤ x` and `d ≥ 0`, `w (x + d) * w s ≤ w x * w (s + d)`. Moving mass
  from the outer pair `{s, x+d}` to the inner pair `{x, s+d}` (same sum) can only
  increase the product.
* `Arlib.massLeft_mul_le`, `Arlib.massRight_mul_le` — one-dimensional Prékopa in the
  only form needed: the *hazard ratios* `w / ∫_a^· w` and `w / ∫_·^b w` are respectively
  nonincreasing and nondecreasing, stated division-free.
* `Arlib.cheeger_mul_le` — the pointwise Cheeger inequality
  `w z * (∫_a^x w) * (∫_x^b w) ≤ w x * (∫_a^b w) ^ 2` for `x, z ∈ [a, b]`.
* `Arlib.oneDim_isoperimetry` — **the target.** For log-concave `w ≥ 0` on `[a,b]` and
  `a ≤ u ≤ v ≤ b`,
  `w z * (v − u) * (∫_a^u w) * (∫_v^b w) ≤ (∫_a^b w) ^ 2 * (∫_u^v w)`,
  i.e. `(1d-2)` with isoperimetric coefficient `w z / ∫_a^b w` for any `z ∈ [a,b]`.
* `Arlib.oneDim_isoperimetry_diameter` — the same inequality with coefficient
  `1 / (b − a)`, obtained from `Arlib.crossRatio_mul_le_crossRatio_integral`.
* `Arlib.cube_le_sq_mul_moment` — Hensley's bound: a weight bounded by `M` on `[a,b]`
  has `(∫_a^b w) ^ 3 ≤ 12 M ^ 2 * ∫_a^b (t − c) ^ 2 w` for every `c ∈ [a,b]`.
* `Arlib.oneDim_isoperimetry_isotropic` — **Lemma `lem:1d-iso`.** For a log-concave
  `w ≥ 0` on `[a,b]` whose normalised density has second moment at most `1`,
  `(1/(2√3)) * (v − u) * (∫_a^u w) * (∫_v^b w) ≤ (∫_a^b w) * (∫_u^v w)`.
* `Arlib.oneDim_isoperimetry_uniform_witness`,
  `Arlib.oneDim_isoperimetry_gaussian_witness`,
  `Arlib.oneDim_isoperimetry_isotropic_witness` — non-vacuity: explicit
  configurations satisfying every hypothesis with a strictly positive left-hand side.

## Relation to the paper

Cousins–Vempala write the coefficient of `(1d-2)` as the macro `\iso`, which
`vol3_journal.tex:65` defines to be `\ln(2)`. Their route is
Lemma `lem:1d-iso` (= Theorem 5.1 of Kannan–Lovász–Simonovits 1995) applied to the
*isotropic* rescaling of the needle density, whose variance Brascamp–Lieb pins at `≤ 1`.
Here the coefficient is `w z / ∫_a^b w` for a free sample point `z ∈ [a,b]`
(`Arlib.oneDim_isoperimetry`), and it is turned into the absolute constant `1 / (2√3) ≈
0.2887` for a density of second moment at most `1` (`Arlib.oneDim_isoperimetry_isotropic`)
via Hensley's bound. That is a factor `2.4` short of the paper's `ln 2 ≈ 0.6931`; the two
lossy steps are identified in the docstring of `Arlib.oneDim_isoperimetry_isotropic`.
Nothing below is assumed: every statement is proved, and the shortfall is slack in the
argument, not a defect in the paper.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3 (`1409.6011/vol3_journal.tex:404–508`).

Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a
localization lemma*, Discrete Comput. Geom. **13** (1995), Theorem 5.1.
-/

namespace Arlib

open MeasureTheory Set

/-! ### The cross form of log-concavity -/

section CrossShift

variable {a b : ℝ} {w : ℝ → ℝ}

/-- **The cross form of log-concavity on an interval.** For `a ≤ s ≤ x`, `0 ≤ d` and
`x + d ≤ b`,

  `w (x + d) * w s ≤ w x * w (s + d)`.

The two pairs `{s, x + d}` and `{x, s + d}` have the same sum, and the second is nested
inside the first; log-concavity says that contracting the pair increases the product.
Both `x` and `s + d` are convex combinations of `s` and `x + d` with complementary
weights, so multiplying the two defining inequalities gives the claim with the exponents
summing to `1`. -/
theorem logConcaveOn_mul_le_mul_shift (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) {s x d : ℝ}
    (has : a ≤ s) (hsx : s ≤ x) (hd : 0 ≤ d) (hxdb : x + d ≤ b) :
    w (x + d) * w s ≤ w x * w (s + d) := by
  have hms : s ∈ Set.Icc a b := ⟨has, by linarith⟩
  have hmx : x ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hmxd : x + d ∈ Set.Icc a b := ⟨by linarith, hxdb⟩
  have hmsd : s + d ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hrhs : 0 ≤ w x * w (s + d) := mul_nonneg (hw0 x hmx) (hw0 _ hmsd)
  rcases eq_or_lt_of_le (hw0 s hms) with h0 | hspos
  · rw [← h0, mul_zero]; exact hrhs
  rcases eq_or_lt_of_le (hw0 (x + d) hmxd) with h0 | hxdpos
  · rw [← h0, zero_mul]; exact hrhs
  set S : ℝ := x + d - s with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; linarith
  rcases eq_or_lt_of_le hS0 with hSz | hSpos
  · have hd0 : d = 0 := by rw [hSdef] at hSz; linarith
    have hxs : s = x := by rw [hSdef] at hSz; linarith
    subst hd0; subst hxs
    simp
  have hSne : S ≠ 0 := ne_of_gt hSpos
  set α : ℝ := d / S with hαdef
  set β : ℝ := (x - s) / S with hβdef
  have hα : 0 ≤ α := div_nonneg hd hS0
  have hβ : 0 ≤ β := div_nonneg (by linarith) hS0
  have hαβ : α + β = 1 := by
    rw [hαdef, hβdef, ← add_div, show d + (x - s) = S by rw [hSdef]; ring]
    exact div_self hSne
  have e1 : α • s + β • (x + d) = x := by
    simp only [smul_eq_mul, hαdef, hβdef]
    field_simp
    rw [hSdef]; ring
  have e2 : β • s + α • (x + d) = s + d := by
    simp only [smul_eq_mul, hαdef, hβdef]
    field_simp
    rw [hSdef]; ring
  have h1 := hw.geom_le hms hmxd hα hβ hαβ
  have h2 := hw.geom_le hms hmxd hβ hα (by linarith)
  rw [e1] at h1
  rw [e2] at h2
  have hcnn : (0 : ℝ) ≤ w s ^ β * w (x + d) ^ α :=
    mul_nonneg (Real.rpow_nonneg hspos.le _) (Real.rpow_nonneg hxdpos.le _)
  have key : (w s ^ α * w (x + d) ^ β) * (w s ^ β * w (x + d) ^ α) ≤ w x * w (s + d) :=
    mul_le_mul h1 h2 hcnn (hw0 x hmx)
  calc w (x + d) * w s
      = (w s ^ α * w (x + d) ^ β) * (w s ^ β * w (x + d) ^ α) := by
        rw [show (w s ^ α * w (x + d) ^ β) * (w s ^ β * w (x + d) ^ α)
              = (w s ^ α * w s ^ β) * (w (x + d) ^ β * w (x + d) ^ α) from by ring,
          ← Real.rpow_add hspos, ← Real.rpow_add hxdpos, hαβ,
          show β + α = 1 by linarith, Real.rpow_one, Real.rpow_one, mul_comm]
    _ ≤ w x * w (s + d) := key

end CrossShift

/-! ### One-dimensional Prékopa: monotonicity of the hazard ratios

For a log-concave `w ≥ 0` on `[a,b]` the two *tail masses*

  `P x = ∫_a^x w`   and   `Q x = ∫_x^b w`

are again log-concave, which is the one-dimensional Prékopa–Leindler theorem. Only its
first-derivative consequence is needed here, and only in division-free form:
`w / P` is nonincreasing and `w / Q` is nondecreasing. Both follow by integrating the
cross form `Arlib.logConcaveOn_mul_le_mul_shift` against a translate of the domain, so
neither Prékopa–Leindler nor differentiability of `w` is used. -/

section Mass

variable {a b : ℝ} {w : ℝ → ℝ}

/-- Interval integrability restricts to a subinterval of `[a,b]`. -/
theorem intervalIntegrable_of_subinterval (hint : IntervalIntegrable w volume a b)
    {p q : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    IntervalIntegrable w volume p q := by
  refine hint.mono_set ?_
  rw [Set.uIcc_of_le hpq, Set.uIcc_of_le (hap.trans (hpq.trans hqb))]
  exact Set.Icc_subset_Icc hap hqb

/-- **One-dimensional Prékopa, left tail.** With `P x = ∫_a^x w`, the ratio `w / P` is
nonincreasing on `[a,b]`; stated without dividing, for `a ≤ x ≤ y ≤ b`,

  `w y * P x ≤ w x * P y`.

Proof: for every `t ∈ [a,x]` the cross form gives `w y * w t ≤ w x * w (t + (y - x))`;
integrating over `t ∈ [a,x]` and translating the right-hand integral back to
`[a + (y-x), y] ⊆ [a, y]` gives the claim, the discarded piece `∫_a^{a + (y-x)} w` being
nonnegative. -/
theorem massLeft_mul_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    w y * (∫ t in a..x, w t) ≤ w x * (∫ t in a..y, w t) := by
  set d : ℝ := y - x with hddef
  have hd0 : 0 ≤ d := by rw [hddef]; linarith
  have hxdy : x + d = y := by rw [hddef]; ring
  have hIax : IntervalIntegrable w volume a x :=
    intervalIntegrable_of_subinterval hint le_rfl hax (by linarith)
  have hIshift : IntervalIntegrable (fun t => w (t + d)) volume a x := by
    have hsub : IntervalIntegrable w volume (a + d) (x + d) :=
      intervalIntegrable_of_subinterval hint (by linarith) (by linarith)
        (show x + d ≤ b by rw [hxdy]; exact hyb)
    have h := hsub.comp_add_right d
    simpa using h
  have step2 : (∫ t in a..x, w y * w t) ≤ ∫ t in a..x, w x * w (t + d) := by
    refine intervalIntegral.integral_mono_on hax (hIax.const_mul _) (hIshift.const_mul _) ?_
    intro t ht
    have h := logConcaveOn_mul_le_mul_shift hw hw0 ht.1 ht.2 hd0
      (show x + d ≤ b by rw [hxdy]; exact hyb)
    rwa [hxdy] at h
  have step4 : (∫ t in (a + d)..y, w t) ≤ ∫ t in a..y, w t := by
    have hsplit : (∫ t in a..(a + d), w t) + (∫ t in (a + d)..y, w t) = ∫ t in a..y, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl (by linarith) (by linarith))
        (intervalIntegrable_of_subinterval hint (by linarith) (by linarith) hyb)
    have hnn : 0 ≤ ∫ t in a..(a + d), w t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        hw0 t ⟨ht.1, by linarith [ht.2]⟩
    linarith
  calc w y * (∫ t in a..x, w t)
      = ∫ t in a..x, w y * w t := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ t in a..x, w x * w (t + d) := step2
    _ = w x * ∫ t in (a + d)..y, w t := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right,
          hxdy]
    _ ≤ w x * ∫ t in a..y, w t :=
        mul_le_mul_of_nonneg_left step4 (hw0 x ⟨hax, by linarith⟩)

/-- **One-dimensional Prékopa, right tail.** With `Q x = ∫_x^b w`, the ratio `w / Q` is
nondecreasing on `[a,b]`; stated without dividing, for `a ≤ x ≤ y ≤ b`,

  `w x * Q y ≤ w y * Q x`.

This is `Arlib.massLeft_mul_le` reflected: for `t ∈ [y,b]` the cross form gives
`w x * w t ≤ w y * w (t − (y − x))`. -/
theorem massRight_mul_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    w x * (∫ t in y..b, w t) ≤ w y * (∫ t in x..b, w t) := by
  set d : ℝ := y - x with hddef
  have hd0 : 0 ≤ d := by rw [hddef]; linarith
  have hxdy : x + d = y := by rw [hddef]; ring
  have hIyb : IntervalIntegrable w volume y b :=
    intervalIntegrable_of_subinterval hint (by linarith) hyb le_rfl
  have hIshift : IntervalIntegrable (fun t => w (t - d)) volume y b := by
    have hsub : IntervalIntegrable w volume x (b - d) :=
      intervalIntegrable_of_subinterval hint hax (by linarith) (by linarith)
    have h := hsub.comp_sub_right d
    simpa [hxdy, sub_add_cancel] using h
  have step2 : (∫ t in y..b, w x * w t) ≤ ∫ t in y..b, w y * w (t - d) := by
    refine intervalIntegral.integral_mono_on hyb (hIyb.const_mul _) (hIshift.const_mul _) ?_
    intro t ht
    have h := logConcaveOn_mul_le_mul_shift hw hw0 hax
      (show x ≤ t - d by linarith [ht.1]) hd0 (show t - d + d ≤ b by linarith [ht.2])
    rw [sub_add_cancel, hxdy] at h
    linarith [h]
  have step4 : (∫ t in x..(b - d), w t) ≤ ∫ t in x..b, w t := by
    have hsplit : (∫ t in x..(b - d), w t) + (∫ t in (b - d)..b, w t) = ∫ t in x..b, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint hax (by linarith) (by linarith))
        (intervalIntegrable_of_subinterval hint (by linarith) (by linarith) le_rfl)
    have hnn : 0 ≤ ∫ t in (b - d)..b, w t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        hw0 t ⟨by linarith [ht.1], ht.2⟩
    linarith
  calc w x * (∫ t in y..b, w t)
      = ∫ t in y..b, w x * w t := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ t in y..b, w y * w (t - d) := step2
    _ = w y * ∫ t in x..(b - d), w t := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
          show y - d = x by rw [hddef]; ring]
    _ ≤ w y * ∫ t in x..b, w t :=
        mul_le_mul_of_nonneg_left step4 (hw0 y ⟨by linarith, hyb⟩)

end Mass

/-! ### The pointwise Cheeger inequality -/

section Cheeger

variable {a b : ℝ} {w : ℝ → ℝ}

/-- **The Cheeger inequality for a one-dimensional log-concave weight.** For every
`x, z ∈ [a,b]`,

  `w z * ((∫_a^x w) * (∫_x^b w)) ≤ w x * (∫_a^b w) ^ 2`.

Dividing by `Z = ∫_a^b w` twice this reads `w x / Z ≥ (w z / Z) · F(x)(1 − F(x))` for the
distribution function `F = (∫_a^· w)/Z`: the density is bounded below by its
Cheeger-optimal profile, with coefficient `w z / Z` for *any* sample point `z`; taking
`z` at (or near) the mode makes the coefficient `sup w / Z`.

If `x ≥ z` the right-tail hazard bound `Arlib.massRight_mul_le` gives
`w z * ∫_x^b w ≤ w x * ∫_z^b w ≤ w x * Z`, and `∫_a^x w ≤ Z` finishes; if `x ≤ z` the
left-tail bound `Arlib.massLeft_mul_le` does the same on the other side. -/
theorem cheeger_mul_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {x z : ℝ} (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b) :
    w z * ((∫ t in a..x, w t) * (∫ t in x..b, w t)) ≤ w x * (∫ t in a..b, w t) ^ 2 := by
  obtain ⟨hax, hxb⟩ := hx
  obtain ⟨haz, hzb⟩ := hz
  have hab : a ≤ b := hax.trans hxb
  have hPQ : (∫ t in a..x, w t) + (∫ t in x..b, w t) = ∫ t in a..b, w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_subinterval hint le_rfl hax hxb)
      (intervalIntegrable_of_subinterval hint hax hxb le_rfl)
  have hP0 : 0 ≤ ∫ t in a..x, w t :=
    intervalIntegral.integral_nonneg hax fun t ht => hw0 t ⟨ht.1, ht.2.trans hxb⟩
  have hQ0 : 0 ≤ ∫ t in x..b, w t :=
    intervalIntegral.integral_nonneg hxb fun t ht => hw0 t ⟨hax.trans ht.1, ht.2⟩
  have hZ0 : 0 ≤ ∫ t in a..b, w t := by linarith
  have hwx0 : 0 ≤ w x := hw0 x ⟨hax, hxb⟩
  have hwz0 : 0 ≤ w z := hw0 z ⟨haz, hzb⟩
  have hZL0 : 0 ≤ ∫ t in a..z, w t :=
    intervalIntegral.integral_nonneg haz fun t ht => hw0 t ⟨ht.1, ht.2.trans hzb⟩
  have hZR0 : 0 ≤ ∫ t in z..b, w t :=
    intervalIntegral.integral_nonneg hzb fun t ht => hw0 t ⟨haz.trans ht.1, ht.2⟩
  have hZsplit : (∫ t in a..z, w t) + (∫ t in z..b, w t) = ∫ t in a..b, w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_subinterval hint le_rfl haz hzb)
      (intervalIntegrable_of_subinterval hint haz hzb le_rfl)
  rcases le_total z x with hzx | hxz
  · -- `x` is to the right of the sample point: use the right-tail hazard bound
    have hkey : w z * (∫ t in x..b, w t) ≤ w x * ∫ t in a..b, w t := by
      have h := massRight_mul_le hw hw0 hint haz hzx hxb
      have : w x * (∫ t in z..b, w t) ≤ w x * ∫ t in a..b, w t :=
        mul_le_mul_of_nonneg_left (by linarith) hwx0
      linarith
    calc w z * ((∫ t in a..x, w t) * (∫ t in x..b, w t))
        = (∫ t in a..x, w t) * (w z * (∫ t in x..b, w t)) := by ring
      _ ≤ (∫ t in a..b, w t) * (w x * ∫ t in a..b, w t) :=
          mul_le_mul (by linarith) hkey (mul_nonneg hwz0 hQ0) hZ0
      _ = w x * (∫ t in a..b, w t) ^ 2 := by ring
  · -- `x` is to the left of the sample point: use the left-tail hazard bound
    have hkey : w z * (∫ t in a..x, w t) ≤ w x * ∫ t in a..b, w t := by
      have h := massLeft_mul_le hw hw0 hint hax hxz hzb
      have : w x * (∫ t in a..z, w t) ≤ w x * ∫ t in a..b, w t :=
        mul_le_mul_of_nonneg_left (by linarith) hwx0
      linarith
    calc w z * ((∫ t in a..x, w t) * (∫ t in x..b, w t))
        = (w z * (∫ t in a..x, w t)) * (∫ t in x..b, w t) := by ring
      _ ≤ (w x * ∫ t in a..b, w t) * (∫ t in a..b, w t) :=
          mul_le_mul hkey (by linarith) hQ0 (mul_nonneg hwx0 hZ0)
      _ = w x * (∫ t in a..b, w t) ^ 2 := by ring

end Cheeger

/-! ### The target inequality `(1d-2)` -/

section Main

variable {a b : ℝ} {w : ℝ → ℝ}

/-- **Cousins–Vempala inequality `(1d-2)`** (`vol3_journal.tex:501`).

For a nonnegative log-concave weight `w` on `[a,b]`, any sample point `z ∈ [a,b]`, and
`a ≤ u ≤ v ≤ b`,

  `w z * (v − u) * (∫_a^u w) * (∫_v^b w) ≤ (∫_a^b w) ^ 2 * (∫_u^v w)`.

Dividing by `Z ^ 2 = (∫_a^b w) ^ 2` this is exactly the paper's

  `∫_a^b w · ∫_u^v w ≥ c ‖u − v‖ · ∫_a^u w · ∫_v^b w`,

with isoperimetric coefficient `c = w z / Z`. Equivalently, for the probability measure
`π` with density `w / Z` on `[a,b]` and the three-interval partition
`S₁ = [a,u]`, `S₃ = [u,v]`, `S₂ = [v,b]`,

  `π(S₃) ≥ (w z / Z) · d(S₁,S₂) · π(S₁) · π(S₂)`,

which is Lemma `lem:1d-iso` (Theorem 5.1 of Kannan–Lovász–Simonovits 1995) for the
interval partitions that the Localization Lemma produces.

The proof integrates the Cheeger inequality `Arlib.cheeger_mul_le` over `[u,v]`: for each
`x` in that range `∫_a^u w ≤ ∫_a^x w` and `∫_v^b w ≤ ∫_x^b w`, so the constant
`w z * (∫_a^u w) * (∫_v^b w)` is dominated pointwise by `w x * Z ^ 2`. -/
theorem oneDim_isoperimetry (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {z u v : ℝ} (hz : z ∈ Set.Icc a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    w z * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
      ≤ (∫ t in a..b, w t) ^ 2 * (∫ t in u..v, w t) := by
  have hab : a ≤ b := hau.trans (huv.trans hvb)
  have hA0 : 0 ≤ ∫ t in a..u, w t :=
    intervalIntegral.integral_nonneg hau fun t ht =>
      hw0 t ⟨ht.1, by linarith [ht.2, huv, hvb]⟩
  have hD0 : 0 ≤ ∫ t in v..b, w t :=
    intervalIntegral.integral_nonneg hvb fun t ht =>
      hw0 t ⟨by linarith [ht.1, hau, huv], ht.2⟩
  have hwz0 : 0 ≤ w z := hw0 z hz
  -- the pointwise domination on `[u,v]`
  have hpt : ∀ x ∈ Set.Icc u v,
      w z * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
        ≤ w x * (∫ t in a..b, w t) ^ 2 := by
    intro x hx
    have hux : u ≤ x := hx.1
    have hxv : x ≤ v := hx.2
    have hxab : x ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
    have hP0 : 0 ≤ ∫ t in a..x, w t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        hw0 t ⟨ht.1, by linarith [ht.2]⟩
    have hAx : (∫ t in a..u, w t) ≤ ∫ t in a..x, w t := by
      have hsplit : (∫ t in a..u, w t) + (∫ t in u..x, w t) = ∫ t in a..x, w t :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_subinterval hint le_rfl hau (by linarith))
          (intervalIntegrable_of_subinterval hint hau hux (by linarith))
      have hnn : 0 ≤ ∫ t in u..x, w t :=
        intervalIntegral.integral_nonneg hux fun t ht =>
          hw0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    have hDx : (∫ t in v..b, w t) ≤ ∫ t in x..b, w t := by
      have hsplit : (∫ t in x..v, w t) + (∫ t in v..b, w t) = ∫ t in x..b, w t :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_subinterval hint (by linarith) hxv hvb)
          (intervalIntegrable_of_subinterval hint (by linarith) hvb le_rfl)
      have hnn : 0 ≤ ∫ t in x..v, w t :=
        intervalIntegral.integral_nonneg hxv fun t ht =>
          hw0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    calc w z * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
        ≤ w z * ((∫ t in a..x, w t) * (∫ t in x..b, w t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hAx hDx hD0 hP0) hwz0
      _ ≤ w x * (∫ t in a..b, w t) ^ 2 := cheeger_mul_le hw hw0 hint hxab hz
  -- integrate it over `[u,v]`
  have hmono : (∫ _t in u..v, w z * ((∫ t in a..u, w t) * (∫ t in v..b, w t)))
      ≤ ∫ x in u..v, w x * (∫ t in a..b, w t) ^ 2 :=
    intervalIntegral.integral_mono_on huv intervalIntegrable_const
      ((intervalIntegrable_of_subinterval hint hau huv hvb).mul_const _) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_mul_const]
    at hmono
  calc w z * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
      = (v - u) * (w z * ((∫ t in a..u, w t) * (∫ t in v..b, w t))) := by ring
    _ ≤ (∫ t in u..v, w t) * (∫ t in a..b, w t) ^ 2 := hmono
    _ = (∫ t in a..b, w t) ^ 2 * (∫ t in u..v, w t) := by ring

/-- **`(1d-2)` with the diameter coefficient.** For a globally log-concave `w ≥ 0` and
`a ≤ u ≤ v ≤ b`,

  `(v − u) * (∫_a^u w) * (∫_v^b w) ≤ (b − a) * (∫_a^b w) * (∫_u^v w)`,

i.e. the isoperimetric coefficient `c = 1 / (b − a)` — the *diameter* form of
Kannan–Lovász–Simonovits, with absolute constant `1`.

This is `Arlib.crossRatio_mul_le_crossRatio_integral` (Lovász–Vempala Lemma 5.9) applied
to `a < u < v < b`, together with `(u − a)(b − v) ≤ (b − a) ^ 2`. It is independent of
`Arlib.oneDim_isoperimetry`: neither coefficient dominates the other, since `w z / ∫_a^b w`
can be much larger than `1 / (b − a)` for a needle whose support is long but whose mass is
concentrated, and much smaller for a needle that is nearly uniform on a short interval. -/
theorem oneDim_isoperimetry_diameter {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hlc : IsLogConcave w) {a b u v : ℝ} (hint : IntervalIntegrable w volume a b)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
      ≤ (b - a) * ((∫ t in a..b, w t) * (∫ t in u..v, w t)) := by
  have hab : a ≤ b := hau.trans (huv.trans hvb)
  have hA0 : 0 ≤ ∫ t in a..u, w t := intervalIntegral.integral_nonneg hau fun t _ => hw0 t
  have hD0 : 0 ≤ ∫ t in v..b, w t := intervalIntegral.integral_nonneg hvb fun t _ => hw0 t
  have hZ0 : 0 ≤ ∫ t in a..b, w t := intervalIntegral.integral_nonneg hab fun t _ => hw0 t
  have hB0 : 0 ≤ ∫ t in u..v, w t := intervalIntegral.integral_nonneg huv fun t _ => hw0 t
  have hrhs : 0 ≤ (b - a) * ((∫ t in a..b, w t) * (∫ t in u..v, w t)) :=
    mul_nonneg (by linarith) (mul_nonneg hZ0 hB0)
  rcases eq_or_lt_of_le hau with h1 | h1
  · have hz : (∫ t in a..u, w t) = 0 := by rw [← h1]; exact intervalIntegral.integral_same
    rw [hz, zero_mul, mul_zero]; exact hrhs
  rcases eq_or_lt_of_le huv with h2 | h2
  · have hz : v - u = 0 := by rw [← h2]; ring
    rw [hz, zero_mul]; exact hrhs
  rcases eq_or_lt_of_le hvb with h3 | h3
  · have hz : (∫ t in v..b, w t) = 0 := by rw [h3]; exact intervalIntegral.integral_same
    rw [hz, mul_zero, mul_zero]; exact hrhs
  have hmain := crossRatio_mul_le_crossRatio_integral hw0 hlc h1 h2 h3 hint
  have hcoef : (u - a) * (b - v) ≤ (b - a) * (b - a) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hstep : (u - a) * (b - v) * ((∫ t in a..b, w t) * (∫ t in u..v, w t))
      ≤ (b - a) * (b - a) * ((∫ t in a..b, w t) * (∫ t in u..v, w t)) :=
    mul_le_mul_of_nonneg_right hcoef (mul_nonneg hZ0 hB0)
  have hba : (0 : ℝ) < b - a := by linarith
  refine le_of_mul_le_mul_left ?_ hba
  calc (b - a) * ((v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)))
      = (b - a) * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)) := by ring
    _ ≤ (u - a) * (b - v) * ((∫ t in a..b, w t) * (∫ t in u..v, w t)) := hmain
    _ ≤ (b - a) * (b - a) * ((∫ t in a..b, w t) * (∫ t in u..v, w t)) := hstep
    _ = (b - a) * ((b - a) * ((∫ t in a..b, w t) * (∫ t in u..v, w t))) := by ring

end Main

/-! ### The three-interval partition, in the vocabulary of `Arlib/Convexity/Isoperimetry.lean`

The Localization Lemma delivers the three parts of the partition as *intervals*
(`vol3_journal.tex:497`, "by a standard combinatorial argument, we can assume that
`Zᵢ = {t : (1−t)a + tb ∈ Sᵢ}` are intervals that partition `[a,b]`"). This section records
that `[a,u]`, `[v,b]`, `(u,v)` really is an `Arlib.IsPartition3` of `[a,b]` whose two outer
parts are at `Arlib.setDist` exactly `v − u`, so that `Arlib.oneDim_isoperimetry` can be
read directly as `π(S₃) ≥ c · d(S₁,S₂) · π(S₁) · π(S₂)`. -/

section Partition

variable {a b u v : ℝ}

/-- `[a,u]`, `[v,b]` and the open gap `(u,v)` form a three-way partition of `[a,b]`. -/
theorem isPartition3_Icc_split (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b) :
    IsPartition3 (Set.Icc a b) (Set.Icc a u) (Set.Icc v b) (Set.Ioo u v) where
  union := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      rcases le_or_gt x u with h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · rcases le_or_gt v x with h' | h'
        · exact Or.inl (Or.inr ⟨h', h2⟩)
        · exact Or.inr ⟨h, h'⟩
  disjoint₁₂ := Set.disjoint_left.mpr fun x hx hx' => by
    exact absurd (hx.2.trans_lt (huv.trans_le hx'.1)) (lt_irrefl x)
  disjoint₁₃ := Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  disjoint₂₃ := Set.disjoint_left.mpr fun x hx hx' => absurd hx.1 (not_le.mpr hx'.2)

/-- The two outer parts of the split are at distance exactly `v − u`: the separation the
isoperimetric inequality is stated against. -/
theorem setDist_Icc_split (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    setDist (Set.Icc a u) (Set.Icc v b) = v - u := by
  refine le_antisymm ?_ (le_setDist ⟨u, hau, le_rfl⟩ ⟨v, le_rfl, hvb⟩ fun x hx y hy => ?_)
  · have h := setDist_le_dist (Set.mem_Icc.mpr ⟨hau, le_rfl⟩)
      (Set.mem_Icc.mpr ⟨le_rfl, hvb⟩)
    rwa [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub] at h
  · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.2, hy.1])]
    linarith [hx.2, hy.1]

/-- **`Arlib.oneDim_isoperimetry` with the separation written as `Arlib.setDist`.**
For `S₁ = [a,u]`, `S₂ = [v,b]` and the gap `S₃ = (u,v)`,

  `w z * d(S₁,S₂) * (∫_{S₁} w) * (∫_{S₂} w) ≤ (∫_a^b w) ^ 2 * (∫_{S₃} w)`,

which after dividing by `(∫_a^b w) ^ 2` is `π(S₃) ≥ (w z / Z) · d(S₁,S₂) · π(S₁) · π(S₂)`. -/
theorem oneDim_isoperimetry_setDist {w : ℝ → ℝ} (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {z : ℝ} (hz : z ∈ Set.Icc a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    w z * setDist (Set.Icc a u) (Set.Icc v b)
        * ((∫ t in a..u, w t) * (∫ t in v..b, w t))
      ≤ (∫ t in a..b, w t) ^ 2 * (∫ t in u..v, w t) := by
  rw [setDist_Icc_split hau huv hvb]
  exact oneDim_isoperimetry hw hw0 hint hz hau huv hvb

end Partition

/-! ### From the second moment to the coefficient: Hensley's bound

`Arlib.oneDim_isoperimetry` has coefficient `w z / ∫_a^b w` for a free sample point `z`.
Cousins–Vempala need the coefficient in terms of the *variance* instead, because
Brascamp–Lieb (`Arlib.brascampLieb` in `GaussianCooling/Variance.lean`) is what controls
the needle, and it controls its variance. The bridge is Hensley's bound: a density
bounded by `M` has second moment at least `1 / (12 M ^ 2)`, so a density of variance at
most `1` must reach height at least `1 / (2√3)` somewhere.

The proof compares `w` against the uniform weight `M` on a window of length `k = Z / M`
placed at an endpoint, where the comparison is *pointwise*: on the window `w ≤ M` and the
factor `(t − r)² − k²` is nonpositive, off the window `w ≥ 0` and the factor is
nonnegative. Doing this at each endpoint of `[a,c]` and `[c,b]` and adding, with
`Z₁³ + Z₂³ ≥ (Z₁ + Z₂)³ / 4`, gives the constant `12` for a moment about an arbitrary
interior point `c` — no barycentre and no window-fitting side condition. -/

section Hensley

/-- `∫_r^{r+k} ((t − r)² − k²) dt = −2k³/3`: the window integral, left-anchored. -/
theorem integral_window_left (r k : ℝ) :
    (∫ t in r..(r + k), ((t - r) ^ 2 - k ^ 2)) = -(2 * k ^ 3 / 3) := by
  have h := intervalIntegral.integral_comp_sub_right (a := r) (b := r + k)
    (f := fun s : ℝ => s ^ 2 - k ^ 2) r
  simp only [sub_self, add_sub_cancel_left] at h
  rw [h, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2).intervalIntegrable _ _)
      intervalIntegrable_const, integral_pow, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

/-- `∫_{r−k}^r ((t − r)² − k²) dt = −2k³/3`: the window integral, right-anchored. -/
theorem integral_window_right (r k : ℝ) :
    (∫ t in (r - k)..r, ((t - r) ^ 2 - k ^ 2)) = -(2 * k ^ 3 / 3) := by
  have h := intervalIntegral.integral_comp_sub_right (a := r - k) (b := r)
    (f := fun s : ℝ => s ^ 2 - k ^ 2) r
  simp only [sub_self, sub_sub_cancel_left] at h
  rw [h, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2).intervalIntegrable _ _)
      intervalIntegrable_const, integral_pow, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

/-- **Hensley's bound, moment about the right endpoint.** If `0 ≤ w ≤ M` on `[p,q]` then

  `(∫_p^q w) ^ 3 ≤ 3 M ^ 2 * ∫_p^q (t − q) ^ 2 w`.

Equality for the uniform weight `M` on a window of length `Z/M` abutting `q`. -/
theorem cube_le_sq_mul_moment_right {p q M : ℝ} {w : ℝ → ℝ} (hpq : p ≤ q) (hM : 0 < M)
    (hw0 : ∀ t ∈ Set.Icc p q, 0 ≤ w t) (hwM : ∀ t ∈ Set.Icc p q, w t ≤ M)
    (hint : IntervalIntegrable w volume p q) :
    (∫ t in p..q, w t) ^ 3 ≤ 3 * M ^ 2 * ∫ t in p..q, (t - q) ^ 2 * w t := by
  set Z : ℝ := ∫ t in p..q, w t with hZdef
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg hpq hw0
  set k : ℝ := Z / M with hkdef
  have hk0 : 0 ≤ k := div_nonneg hZ0 hM.le
  have hMk : M * k = Z := by rw [hkdef]; field_simp
  have hZle : Z ≤ (q - p) * M := by
    have h := intervalIntegral.integral_mono_on hpq hint intervalIntegrable_const hwM
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  have hkq : k ≤ q - p := by rw [hkdef, div_le_iff₀ hM]; linarith
  have hpqk : p ≤ q - k := by linarith
  have hqkq : q - k ≤ q := by linarith
  have hIw : ∀ {x y : ℝ}, p ≤ x → x ≤ y → y ≤ q →
      IntervalIntegrable (fun t => ((t - q) ^ 2 - k ^ 2) * w t) volume x y := fun hx hxy hy =>
    (intervalIntegrable_of_subinterval hint hx hxy hy).continuousOn_mul
      (Continuous.continuousOn (by fun_prop))
  have hsplit : (∫ t in p..(q - k), ((t - q) ^ 2 - k ^ 2) * w t)
      + (∫ t in (q - k)..q, ((t - q) ^ 2 - k ^ 2) * w t)
      = ∫ t in p..q, ((t - q) ^ 2 - k ^ 2) * w t :=
    intervalIntegral.integral_add_adjacent_intervals (hIw le_rfl hpqk hqkq)
      (hIw hpqk hqkq le_rfl)
  have hleft : 0 ≤ ∫ t in p..(q - k), ((t - q) ^ 2 - k ^ 2) * w t := by
    refine intervalIntegral.integral_nonneg hpqk fun t ht => ?_
    exact mul_nonneg (by nlinarith [ht.2]) (hw0 t ⟨ht.1, by linarith [ht.2]⟩)
  have hright : (∫ t in (q - k)..q, ((t - q) ^ 2 - k ^ 2) * M)
      ≤ ∫ t in (q - k)..q, ((t - q) ^ 2 - k ^ 2) * w t := by
    refine intervalIntegral.integral_mono_on hqkq
      ((by fun_prop : Continuous fun t : ℝ => ((t - q) ^ 2 - k ^ 2) * M).intervalIntegrable _ _)
      (hIw hpqk hqkq le_rfl) fun t ht => ?_
    have hle : (t - q) ^ 2 - k ^ 2 ≤ 0 := by nlinarith [ht.1, ht.2]
    nlinarith [hwM t ⟨by linarith [ht.1], ht.2⟩]
  have hwin : (∫ t in (q - k)..q, ((t - q) ^ 2 - k ^ 2) * M) = -(2 * k ^ 3 / 3) * M := by
    rw [intervalIntegral.integral_mul_const, integral_window_right]
  have hexpand : (∫ t in p..q, ((t - q) ^ 2 - k ^ 2) * w t)
      = (∫ t in p..q, (t - q) ^ 2 * w t) - k ^ 2 * Z := by
    have h1 : IntervalIntegrable (fun t => (t - q) ^ 2 * w t) volume p q :=
      hint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
    have h2 : IntervalIntegrable (fun t => k ^ 2 * w t) volume p q := hint.const_mul _
    rw [show (fun t => ((t - q) ^ 2 - k ^ 2) * w t)
          = (fun t => (t - q) ^ 2 * w t - k ^ 2 * w t) from by funext t; ring,
      intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  have hMk3 : -(2 * k ^ 3 / 3) * M = -(2 * k ^ 2 * Z / 3) := by rw [← hMk]; ring
  have hmoment : k ^ 2 * Z / 3 ≤ ∫ t in p..q, (t - q) ^ 2 * w t := by
    rw [hexpand] at hsplit
    linarith [hsplit, hleft, hright, hwin, hMk3]
  calc Z ^ 3 = 3 * M ^ 2 * (k ^ 2 * Z / 3) := by rw [← hMk]; ring
    _ ≤ 3 * M ^ 2 * ∫ t in p..q, (t - q) ^ 2 * w t :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- **Hensley's bound, moment about the left endpoint.** The mirror image of
`Arlib.cube_le_sq_mul_moment_right`. -/
theorem cube_le_sq_mul_moment_left {p q M : ℝ} {w : ℝ → ℝ} (hpq : p ≤ q) (hM : 0 < M)
    (hw0 : ∀ t ∈ Set.Icc p q, 0 ≤ w t) (hwM : ∀ t ∈ Set.Icc p q, w t ≤ M)
    (hint : IntervalIntegrable w volume p q) :
    (∫ t in p..q, w t) ^ 3 ≤ 3 * M ^ 2 * ∫ t in p..q, (t - p) ^ 2 * w t := by
  set Z : ℝ := ∫ t in p..q, w t with hZdef
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg hpq hw0
  set k : ℝ := Z / M with hkdef
  have hk0 : 0 ≤ k := div_nonneg hZ0 hM.le
  have hMk : M * k = Z := by rw [hkdef]; field_simp
  have hZle : Z ≤ (q - p) * M := by
    have h := intervalIntegral.integral_mono_on hpq hint intervalIntegrable_const hwM
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  have hkq : k ≤ q - p := by rw [hkdef, div_le_iff₀ hM]; linarith
  have hppk : p ≤ p + k := by linarith
  have hpkq : p + k ≤ q := by linarith
  have hIw : ∀ {x y : ℝ}, p ≤ x → x ≤ y → y ≤ q →
      IntervalIntegrable (fun t => ((t - p) ^ 2 - k ^ 2) * w t) volume x y := fun hx hxy hy =>
    (intervalIntegrable_of_subinterval hint hx hxy hy).continuousOn_mul
      (Continuous.continuousOn (by fun_prop))
  have hsplit : (∫ t in p..(p + k), ((t - p) ^ 2 - k ^ 2) * w t)
      + (∫ t in (p + k)..q, ((t - p) ^ 2 - k ^ 2) * w t)
      = ∫ t in p..q, ((t - p) ^ 2 - k ^ 2) * w t :=
    intervalIntegral.integral_add_adjacent_intervals (hIw le_rfl hppk hpkq)
      (hIw hppk hpkq le_rfl)
  have hright : 0 ≤ ∫ t in (p + k)..q, ((t - p) ^ 2 - k ^ 2) * w t := by
    refine intervalIntegral.integral_nonneg hpkq fun t ht => ?_
    exact mul_nonneg (by nlinarith [ht.1]) (hw0 t ⟨by linarith [ht.1], ht.2⟩)
  have hleft : (∫ t in p..(p + k), ((t - p) ^ 2 - k ^ 2) * M)
      ≤ ∫ t in p..(p + k), ((t - p) ^ 2 - k ^ 2) * w t := by
    refine intervalIntegral.integral_mono_on hppk
      ((by fun_prop : Continuous fun t : ℝ => ((t - p) ^ 2 - k ^ 2) * M).intervalIntegrable _ _)
      (hIw le_rfl hppk hpkq) fun t ht => ?_
    have hle : (t - p) ^ 2 - k ^ 2 ≤ 0 := by nlinarith [ht.1, ht.2]
    nlinarith [hwM t ⟨ht.1, by linarith [ht.2]⟩]
  have hwin : (∫ t in p..(p + k), ((t - p) ^ 2 - k ^ 2) * M) = -(2 * k ^ 3 / 3) * M := by
    rw [intervalIntegral.integral_mul_const, integral_window_left]
  have hexpand : (∫ t in p..q, ((t - p) ^ 2 - k ^ 2) * w t)
      = (∫ t in p..q, (t - p) ^ 2 * w t) - k ^ 2 * Z := by
    have h1 : IntervalIntegrable (fun t => (t - p) ^ 2 * w t) volume p q :=
      hint.continuousOn_mul (Continuous.continuousOn (by fun_prop))
    have h2 : IntervalIntegrable (fun t => k ^ 2 * w t) volume p q := hint.const_mul _
    rw [show (fun t => ((t - p) ^ 2 - k ^ 2) * w t)
          = (fun t => (t - p) ^ 2 * w t - k ^ 2 * w t) from by funext t; ring,
      intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  have hMk3 : -(2 * k ^ 3 / 3) * M = -(2 * k ^ 2 * Z / 3) := by rw [← hMk]; ring
  have hmoment : k ^ 2 * Z / 3 ≤ ∫ t in p..q, (t - p) ^ 2 * w t := by
    rw [hexpand] at hsplit
    linarith [hsplit, hleft, hright, hwin, hMk3]
  calc Z ^ 3 = 3 * M ^ 2 * (k ^ 2 * Z / 3) := by rw [← hMk]; ring
    _ ≤ 3 * M ^ 2 * ∫ t in p..q, (t - p) ^ 2 * w t :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- **Hensley's bound.** For `0 ≤ w ≤ M` on `[a,b]` and any `c ∈ [a,b]`,

  `(∫_a^b w) ^ 3 ≤ 12 M ^ 2 * ∫_a^b (t − c) ^ 2 w`.

For a probability density (`∫_a^b w = 1`) this is the familiar "a density bounded by `M`
has second moment at least `1/(12 M²)`", with the uniform density as the extremal case.
No log-concavity is used. -/
theorem cube_le_sq_mul_moment {a b c M : ℝ} {w : ℝ → ℝ} (hM : 0 < M)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hwM : ∀ t ∈ Set.Icc a b, w t ≤ M)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Set.Icc a b) :
    (∫ t in a..b, w t) ^ 3 ≤ 12 * M ^ 2 * ∫ t in a..b, (t - c) ^ 2 * w t := by
  obtain ⟨hac, hcb⟩ := hc
  have h1 := cube_le_sq_mul_moment_right (p := a) (q := c) (w := w) hac hM
    (fun t ht => hw0 t ⟨ht.1, ht.2.trans hcb⟩) (fun t ht => hwM t ⟨ht.1, ht.2.trans hcb⟩)
    (intervalIntegrable_of_subinterval hint le_rfl hac hcb)
  have h2 := cube_le_sq_mul_moment_left (p := c) (q := b) (w := w) hcb hM
    (fun t ht => hw0 t ⟨hac.trans ht.1, ht.2⟩) (fun t ht => hwM t ⟨hac.trans ht.1, ht.2⟩)
    (intervalIntegrable_of_subinterval hint hac hcb le_rfl)
  have hZ : (∫ t in a..c, w t) + (∫ t in c..b, w t) = ∫ t in a..b, w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_subinterval hint le_rfl hac hcb)
      (intervalIntegrable_of_subinterval hint hac hcb le_rfl)
  have hVint : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ b →
      IntervalIntegrable (fun t => (t - c) ^ 2 * w t) volume x y := fun hx hxy hy =>
    (intervalIntegrable_of_subinterval hint hx hxy hy).continuousOn_mul
      (Continuous.continuousOn (by fun_prop))
  have hV : (∫ t in a..c, (t - c) ^ 2 * w t) + (∫ t in c..b, (t - c) ^ 2 * w t)
      = ∫ t in a..b, (t - c) ^ 2 * w t :=
    intervalIntegral.integral_add_adjacent_intervals (hVint le_rfl hac hcb)
      (hVint hac hcb le_rfl)
  have hZ1 : 0 ≤ ∫ t in a..c, w t :=
    intervalIntegral.integral_nonneg hac fun t ht => hw0 t ⟨ht.1, ht.2.trans hcb⟩
  have hZ2 : 0 ≤ ∫ t in c..b, w t :=
    intervalIntegral.integral_nonneg hcb fun t ht => hw0 t ⟨hac.trans ht.1, ht.2⟩
  have hcube : ((∫ t in a..c, w t) + (∫ t in c..b, w t)) ^ 3
      ≤ 4 * ((∫ t in a..c, w t) ^ 3 + (∫ t in c..b, w t) ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg ((∫ t in a..c, w t) - (∫ t in c..b, w t)))
      (add_nonneg hZ1 hZ2)]
  rw [← hZ, ← hV]
  nlinarith [hcube, h1, h2]

end Hensley

/-! ### The isotropic form of `lem:1d-iso` -/

section Isotropic

/-- **Lemma `lem:1d-iso` (Kannan–Lovász–Simonovits 1995, Theorem 5.1), interval form.**

Let `w ≥ 0` be log-concave on `[a,b]` with `Z = ∫_a^b w > 0`, and suppose the associated
probability density `w / Z` has second moment at most `1` about some `c ∈ [a,b]`:
`∫_a^b (t − c)² w ≤ Z`. Then for `a ≤ u ≤ v ≤ b`,

  `(1 / (2√3)) * (v − u) * (∫_a^u w) * (∫_v^b w) ≤ (∫_a^b w) * (∫_u^v w)`,

i.e. `π(S₃) ≥ (1/(2√3)) · d(S₁,S₂) · π(S₁) · π(S₂)` for the interval partition
`S₁ = [a,u]`, `S₃ = [u,v]`, `S₂ = [v,b]` of the probability measure `π = w/Z`.

**The constant.** Cousins–Vempala state this with `\iso = ln 2 ≈ 0.6931`
(`vol3_journal.tex:65`, `:439`). The constant proved here is
`1/(2√3) ≈ 0.2887`, a factor `2.4` smaller. Two steps are lossy relative to the
KLS argument: Hensley's bound `Arlib.cube_le_sq_mul_moment` is applied about an arbitrary
`c` rather than the barycentre, and `Arlib.cheeger_mul_le` bounds `F(x)(1−F(x))` by
`min(F, 1−F)` before using the hazard monotonicity. Both are genuine slack, not errors:
every statement below is proved, and `1/(2√3)` is a correct — merely non-optimal —
isoperimetric coefficient.

The proof: if `w` never came within `ε` of `Z/(2√3)` on `[a,b]` then Hensley's bound with
`M = Z/(2√3) − ε` would force `Z³ ≤ 12 M² Z < Z³`. So `w z` gets arbitrarily close to
`Z/(2√3)`, and `Arlib.oneDim_isoperimetry` at such a `z`, in the limit, is the claim. -/
theorem oneDim_isoperimetry_isotropic {a b c : ℝ} {w : ℝ → ℝ}
    (hw : LogConcaveOn (Set.Icc a b) w) (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Set.Icc a b)
    (hZpos : 0 < ∫ t in a..b, w t)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤ ∫ t in a..b, w t)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    1 / (2 * Real.sqrt 3) * ((v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)))
      ≤ (∫ t in a..b, w t) * (∫ t in u..v, w t) := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set Z : ℝ := ∫ t in a..b, w t with hZdef
  set X : ℝ := (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)) with hXdef
  set K : ℝ := Z / (2 * Real.sqrt 3) with hKdef
  have hK0 : 0 < K := div_pos hZpos (by positivity)
  have hX0 : 0 ≤ X := by
    refine mul_nonneg (by linarith) (mul_nonneg ?_ ?_)
    · exact intervalIntegral.integral_nonneg hau fun t ht =>
        hw0 t ⟨ht.1, by linarith [ht.2]⟩
    · exact intervalIntegral.integral_nonneg hvb fun t ht =>
        hw0 t ⟨by linarith [ht.1], ht.2⟩
  -- Hensley forces `w` to come arbitrarily close to `K` somewhere on `[a,b]`
  have hex : ∀ ε : ℝ, 0 < ε → ∃ z ∈ Set.Icc a b, K - ε < w z := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    rcases le_or_gt (K - ε) 0 with hMle | hMpos
    · have hZle0 : Z ≤ 0 := by
        have h := intervalIntegral.integral_mono_on (hc.1.trans hc.2) hint
          (intervalIntegrable_const (c := (0 : ℝ))) fun t ht => (hcon t ht).trans hMle
        simpa using h
      linarith
    · have hH := cube_le_sq_mul_moment (M := K - ε) hMpos hw0 hcon hint hc
      have hVZ : 12 * (K - ε) ^ 2 * (∫ t in a..b, (t - c) ^ 2 * w t)
          ≤ 12 * (K - ε) ^ 2 * Z := mul_le_mul_of_nonneg_left hvar (by positivity)
      have hKsq : 12 * K ^ 2 = Z ^ 2 := by
        have h12 : (2 * Real.sqrt 3) ^ 2 = 12 := by rw [mul_pow, hs3sq]; norm_num
        rw [hKdef, div_pow, h12]; ring
      have hstep : Z ^ 3 ≤ 12 * (K - ε) ^ 2 * Z := le_trans hH hVZ
      have hlt : 12 * (K - ε) ^ 2 < 12 * K ^ 2 := by nlinarith [hMpos, hε]
      have hself : Z ^ 3 < Z ^ 3 :=
        calc Z ^ 3 ≤ 12 * (K - ε) ^ 2 * Z := hstep
          _ < 12 * K ^ 2 * Z := mul_lt_mul_of_pos_right hlt hZpos
          _ = Z ^ 2 * Z := by rw [hKsq]
          _ = Z ^ 3 := by ring
      exact lt_irrefl _ hself
  -- transport the main inequality to those points, then let `ε → 0`
  have hmain : ∀ z ∈ Set.Icc a b, w z * X ≤ Z ^ 2 * (∫ t in u..v, w t) := by
    intro z hz
    have h := oneDim_isoperimetry hw hw0 hint hz hau huv hvb
    calc w z * X = w z * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)) := by
          rw [hXdef]; ring
      _ ≤ _ := h
  have hKX : K * X ≤ Z ^ 2 * (∫ t in u..v, w t) := by
    by_contra hcon
    push Not at hcon
    set δ : ℝ := K * X - Z ^ 2 * (∫ t in u..v, w t) with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    obtain ⟨z, hz, hzw⟩ := hex (δ / (2 * (X + 1))) (by positivity)
    have h1 := hmain z hz
    have h2 : (K - δ / (2 * (X + 1))) * X ≤ w z * X :=
      mul_le_mul_of_nonneg_right hzw.le hX0
    have h3 : δ / (2 * (X + 1)) * X ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hδ, hX0]
    nlinarith [h1, h2, h3, hδ]
  refine le_of_mul_le_mul_left ?_ hZpos
  calc Z * (1 / (2 * Real.sqrt 3) * X) = K * X := by rw [hKdef]; ring
    _ ≤ Z ^ 2 * (∫ t in u..v, w t) := hKX
    _ = Z * (Z * ∫ t in u..v, w t) := by ring

end Isotropic

/-! ### Non-vacuity

Both hypotheses lists above are satisfiable *simultaneously with a strictly positive
left-hand side*, so neither theorem is the vacuous `0 ≤ something`. The witnesses are the
two densities of the paper: the uniform weight on `[0,1]` and — the case that matters,
since it is not constant — the standard Gaussian `γ` restricted to `[-1,1]`. -/

section Witness

/-- The constant weight `1` on `[0,1]`, cut at `u = 1/4`, `v = 3/4`, satisfies every
hypothesis of `Arlib.oneDim_isoperimetry` with a strictly positive left-hand side: the
inequality it produces is `1/32 ≤ 1/2`. -/
theorem oneDim_isoperimetry_uniform_witness :
    ∃ w : ℝ → ℝ, ∃ a b z u v : ℝ,
      LogConcaveOn (Set.Icc a b) w ∧ (∀ t ∈ Set.Icc a b, 0 ≤ w t) ∧
        IntervalIntegrable w volume a b ∧ z ∈ Set.Icc a b ∧ a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        0 < w z * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)) := by
  refine ⟨fun _ => (1 : ℝ), 0, 1, 0, 1 / 4, 3 / 4,
    logConcaveOn_const (convex_Icc 0 1) zero_le_one, fun _ _ => zero_le_one,
    intervalIntegrable_const, ⟨le_rfl, zero_le_one⟩, by norm_num, by norm_num, by norm_num,
    ?_⟩
  norm_num

/-- The standard Gaussian weight on `[-1,1]`, cut at `u = -1/2`, `v = 1/2`, satisfies every
hypothesis of `Arlib.oneDim_isoperimetry` with a strictly positive left-hand side. This is
the case Cousins–Vempala actually feed to `(1d-2)`: a *non-constant* log-concave weight,
so log-concavity is doing real work in the witness. -/
theorem oneDim_isoperimetry_gaussian_witness :
    ∃ w : ℝ → ℝ, ∃ a b z u v : ℝ,
      LogConcaveOn (Set.Icc a b) w ∧ (∀ t ∈ Set.Icc a b, 0 ≤ w t) ∧
        IntervalIntegrable w volume a b ∧ z ∈ Set.Icc a b ∧ a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        0 < w z * (v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)) := by
  set w : ℝ → ℝ := fun x => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hwdef
  have hcont : Continuous w := by
    rw [hwdef]; fun_prop
  have hpos : ∀ x, 0 < w x := fun x => Real.exp_pos _
  refine ⟨w, -1, 1, 0, -(1 / 2), 1 / 2,
    (isLogConcave_gaussian (1 : ℝ)).logConcaveOn (convex_Icc _ _),
    fun t _ => (hpos t).le, hcont.intervalIntegrable _ _, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 : 0 < ∫ t in (-1 : ℝ)..(-(1 / 2)), w t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      (fun x _ => hpos x) (by norm_num)
  have h2 : 0 < ∫ t in (1 / 2 : ℝ)..1, w t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      (fun x _ => hpos x) (by norm_num)
  have h3 : 0 < w 0 := hpos 0
  have h4 : (0 : ℝ) < 1 / 2 - -(1 / 2) := by norm_num
  positivity

/-- **Non-vacuity of the isotropic form.** The constant weight `1` on `[-1,1]` — the
uniform density, which is exactly the extremal case of Hensley's bound — has second
moment `2/3` about `c = 0` against total mass `2`, so `∫ (t−c)² w ≤ ∫ w` holds with room;
`Z = 2 > 0`; and cutting at `u = -1/2`, `v = 1/2` leaves a strictly positive left-hand
side. So `Arlib.oneDim_isoperimetry_isotropic` is not vacuous: the inequality it asserts
there is `1/(8√3) ≤ 2`. -/
theorem oneDim_isoperimetry_isotropic_witness :
    ∃ w : ℝ → ℝ, ∃ a b c u v : ℝ,
      LogConcaveOn (Set.Icc a b) w ∧ (∀ t ∈ Set.Icc a b, 0 ≤ w t) ∧
        IntervalIntegrable w volume a b ∧ c ∈ Set.Icc a b ∧
        (0 < ∫ t in a..b, w t) ∧
        ((∫ t in a..b, (t - c) ^ 2 * w t) ≤ ∫ t in a..b, w t) ∧
        a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        0 < 1 / (2 * Real.sqrt 3)
            * ((v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t))) := by
  refine ⟨fun _ => (1 : ℝ), -1, 1, 0, -(1 / 2), 1 / 2,
    logConcaveOn_const (convex_Icc _ _) zero_le_one, fun _ _ => zero_le_one,
    intervalIntegrable_const, ⟨by norm_num, by norm_num⟩, ?_, ?_,
    by norm_num, by norm_num, by norm_num, ?_⟩
  · norm_num
  · norm_num [integral_pow]
  · have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    norm_num

end Witness

/-! ### Axiom audit

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms logConcaveOn_mul_le_mul_shift
#print axioms intervalIntegrable_of_subinterval
#print axioms massLeft_mul_le
#print axioms massRight_mul_le
#print axioms cheeger_mul_le
#print axioms oneDim_isoperimetry
#print axioms oneDim_isoperimetry_diameter
#print axioms oneDim_isoperimetry_uniform_witness
#print axioms oneDim_isoperimetry_gaussian_witness
#print axioms isPartition3_Icc_split
#print axioms setDist_Icc_split
#print axioms oneDim_isoperimetry_setDist
#print axioms integral_window_left
#print axioms integral_window_right
#print axioms cube_le_sq_mul_moment_right
#print axioms cube_le_sq_mul_moment_left
#print axioms cube_le_sq_mul_moment
#print axioms oneDim_isoperimetry_isotropic
#print axioms oneDim_isoperimetry_isotropic_witness

end Arlib
