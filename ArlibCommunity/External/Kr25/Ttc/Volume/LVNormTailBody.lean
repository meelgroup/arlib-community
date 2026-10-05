/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailShellGeometry

/-! # Body-level logarithmic norm tail -/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

variable {n : ℕ}

/-- The localized continuous cutoff cannot retain positive integral: the two dyadic hazard
tails already exhaust its possible positive support. -/
theorem localized_normTail_cutoff_integral_nonpos
    {p e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0) {a b M : ℝ} {N : ℕ}
    {D : ℝ → ℝ} {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hab : a ≤ b) (hM : 0 < M) (hD0 : ∀ t ∈ Icc a b, 0 ≤ D t)
    (hDlc : LogConcaveOn (Icc a b) D) (hDint : IntervalIntegrable D volume a b)
    (hmass : 0 < ∫ t in a..b, D t)
    (hnorm : (∫ t in a..b, ‖needleMap p e t‖ ^ 2 * D t) =
      M * ∫ t in a..b, D t)
    (hqc : Continuous q)
    (hqle : ∀ x, q x ≤
      {y : EuclideanSpace ℝ (Fin n) |
        Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) < ‖y‖}.indicator
          (fun _ => (1 : ℝ)) x - 1 / (2 : ℝ) ^ N) :
    ∫ t in Icc a b, q (needleMap p e t) * D t ≤ 0 := by
  let z := needleSegmentCenter a b p e
  let s := Real.sqrt M / ‖e‖
  let A := Real.sqrt 2 * s + 4 * Real.sqrt 3 * s * N
  let l₀ := z - A
  let r₀ := z + A
  let l := max a l₀
  let r := min b r₀
  let Z := ∫ t in a..b, D t
  let L := ∫ t in a..l, D t
  let R := ∫ t in r..b, D t
  have hs : 0 < s := div_pos (Real.sqrt_pos.2 hM) (norm_pos_iff.mpr he)
  have hzmem : z ∈ Icc a b := needleSegmentCenter_mem hab p e
  have hvar : (∫ t in a..b, (t - z) ^ 2 * D t) ≤ s ^ 2 * Z := by
    simpa only [z, s, Z] using
      localizedNeedle_variance_le_ambientScale he hab hM.le hD0 hDint hnorm
  have hzNorm : ‖needleMap p e z‖ ≤ Real.sqrt M := by
    simpa only [z] using norm_needleMap_segmentCenter_le_sqrtMoment he hab hM.le hD0 hDint
      hmass hnorm
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hlz : l ≤ z := by
    dsimp [l, l₀]
    exact max_le hzmem.1 (by linarith)
  have hzr : z ≤ r := by
    dsimp [r, r₀]
    exact le_min hzmem.2 (by linarith)
  have hal : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hlr : l ≤ r := hlz.trans hzr
  have hZ0 : 0 ≤ Z := hmass.le
  have hL0 : 0 ≤ L := intervalIntegral.integral_nonneg hal fun t ht =>
    hD0 t ⟨ht.1, ht.2.trans (hlr.trans hrb)⟩
  have hR0 : 0 ≤ R := intervalIntegral.integral_nonneg hrb fun t ht =>
    hD0 t ⟨(hal.trans hlr).trans ht.1, ht.2⟩
  have hleft : (2 : ℝ) ^ (N + 1) * L ≤ Z := by
    by_cases ha₀ : a ≤ l₀
    · have hlEq : l = l₀ := max_eq_right ha₀
      dsimp only [L]
      rw [hlEq]
      simpa only [l₀, A, z, s, L, Z, sub_sub] using
        leftTail_pow_two_succ_le_mass hab hs hDlc hD0 hDint hzmem hvar N (by
          simpa only [l₀, A, z, s, sub_sub] using ha₀)
    · have hlEq : l = a := max_eq_left (le_of_not_ge ha₀)
      simp [L, hlEq, hZ0]
  have hright : (2 : ℝ) ^ (N + 1) * R ≤ Z := by
    by_cases hr₀b : r₀ ≤ b
    · have hrEq : r = r₀ := min_eq_right hr₀b
      dsimp only [R]
      rw [hrEq]
      simpa only [r₀, A, z, s, R, Z, add_assoc] using
        rightTail_pow_two_succ_le_mass hab hs hDlc hD0 hDint hzmem hvar N (by
          simpa only [r₀, A, z, s, add_assoc] using hr₀b)
    · have hrEq : r = b := min_eq_left (le_of_not_ge hr₀b)
      simp [R, hrEq, hZ0]
  have hpow : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) _
  have htails : L + R ≤ Z / (2 : ℝ) ^ N := by
    apply (le_div_iff₀ hpow).2
    rw [pow_succ] at hleft hright
    nlinarith
  have hneedle : Continuous (fun t : ℝ => needleMap p e t) := by
    simp_rw [needleMap_apply]
    fun_prop
  have hqint : IntervalIntegrable (fun t => q (needleMap p e t) * D t) volume a b :=
    hDint.continuousOn_mul (hqc.comp hneedle).continuousOn
  have hqone : ∀ t, q (needleMap p e t) ≤ 1 - 1 / (2 : ℝ) ^ N := by
    intro t
    have h := hqle (needleMap p e t)
    by_cases ht : Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) <
        ‖needleMap p e t‖
    · have htmem : needleMap p e t ∈ {y : EuclideanSpace ℝ (Fin n) |
          Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) < ‖y‖} := ht
      rw [indicator_of_mem htmem] at h
      exact h
    · have hnormle : ‖needleMap p e t‖ ≤
          Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) := le_of_not_gt ht
      have ht' : needleMap p e t ∉ {y : EuclideanSpace ℝ (Fin n) |
          Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) < ‖y‖} :=
        fun hmem => (not_lt_of_ge hnormle) hmem
      rw [indicator_of_notMem ht'] at h
      linarith
  have hqmid : ∀ t ∈ Icc l r, q (needleMap p e t) ≤ -(1 / (2 : ℝ) ^ N) := by
    intro t ht
    have htl₀ : l₀ ≤ t := (le_max_right a l₀).trans ht.1
    have htr₀ : t ≤ r₀ := ht.2.trans (min_le_right b r₀)
    have habs : |t - z| ≤ A := abs_le.2 ⟨by dsimp [l₀] at htl₀; linarith,
      by dsimp [r₀] at htr₀; linarith⟩
    have hnfar : ¬ Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) <
        ‖needleMap p e t‖ := by
      intro hfar
      have := abs_sub_gt_of_norm_needleMap_gt_shell he hM hzNorm N hfar
      exact (not_lt_of_ge habs) (by simpa only [A, s] using this)
    have hnormle : ‖needleMap p e t‖ ≤
        Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) := le_of_not_gt hnfar
    have hnot : needleMap p e t ∉ {y : EuclideanSpace ℝ (Fin n) |
        Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) < ‖y‖} := by simpa
    have h := hqle (needleMap p e t)
    rw [indicator_of_notMem hnot] at h
    linarith
  have hLI := Arlib.intervalIntegrable_of_subinterval hDint le_rfl hal (hlr.trans hrb)
  have hMI := Arlib.intervalIntegrable_of_subinterval hDint hal hlr hrb
  have hRI := Arlib.intervalIntegrable_of_subinterval hDint (hal.trans hlr) hrb le_rfl
  have hqLI := Arlib.intervalIntegrable_of_subinterval hqint le_rfl hal (hlr.trans hrb)
  have hqMI := Arlib.intervalIntegrable_of_subinterval hqint hal hlr hrb
  have hqRI := Arlib.intervalIntegrable_of_subinterval hqint (hal.trans hlr) hrb le_rfl
  have hleftQ : (∫ t in a..l, q (needleMap p e t) * D t) ≤
      (1 - 1 / (2 : ℝ) ^ N) * L := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hal hqLI (hLI.const_mul _) fun t ht =>
      mul_le_mul_of_nonneg_right (hqone t) (hD0 t ⟨ht.1, ht.2.trans (hlr.trans hrb)⟩)
  have hmidQ : (∫ t in l..r, q (needleMap p e t) * D t) ≤
      -(1 / (2 : ℝ) ^ N) * (∫ t in l..r, D t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hlr hqMI (hMI.const_mul _) fun t ht =>
      mul_le_mul_of_nonneg_right (hqmid t ht) (hD0 t ⟨hal.trans ht.1, ht.2.trans hrb⟩)
  have hrightQ : (∫ t in r..b, q (needleMap p e t) * D t) ≤
      (1 - 1 / (2 : ℝ) ^ N) * R := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hrb hqRI (hRI.const_mul _) fun t ht =>
      mul_le_mul_of_nonneg_right (hqone t) (hD0 t ⟨(hal.trans hlr).trans ht.1, ht.2⟩)
  have hsplitQ₁ := intervalIntegral.integral_add_adjacent_intervals hqLI hqMI
  have hsplitQ₂ := intervalIntegral.integral_add_adjacent_intervals
    (hqLI.trans hqMI) hqRI
  have hsplitD₁ := intervalIntegral.integral_add_adjacent_intervals hLI hMI
  have hsplitD₂ := intervalIntegral.integral_add_adjacent_intervals (hLI.trans hMI) hRI
  have hqall : (∫ t in a..b, q (needleMap p e t) * D t) ≤
      L + R - Z / (2 : ℝ) ^ N := by
    have hqsum : (∫ t in a..b, q (needleMap p e t) * D t) =
        (∫ t in a..l, q (needleMap p e t) * D t) +
        (∫ t in l..r, q (needleMap p e t) * D t) +
        (∫ t in r..b, q (needleMap p e t) * D t) := by linarith
    have hDsum : Z = L + (∫ t in l..r, D t) + R := by
      dsimp only [L, R, Z]
      linarith
    rw [hqsum]
    calc
      _ ≤ (1 - 1 / (2 : ℝ) ^ N) * L +
          (-(1 / (2 : ℝ) ^ N) * (∫ t in l..r, D t)) +
          (1 - 1 / (2 : ℝ) ^ N) * R := by linarith
      _ = L + R - Z / (2 : ℝ) ^ N := by
        rw [hDsum]
        ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact hqall.trans (by linarith)

/-- Literal body-level dyadic radial tail.  The subtraction form is exactly the relative-volume
statement and avoids any normalization convention for `volume.real K`. -/
theorem body_normTail_dyadic_sub_nonpos
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M : ℝ} (hM : 0 < M) (N : ℕ) (hN : 0 < N)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    (∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) |
        Real.sqrt M * (1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N) < ‖y‖}.indicator
          (fun _ => (1 : ℝ)) x - 1 / (2 : ℝ) ^ N) ≤ 0 := by
  let C : ℝ := 1 + Real.sqrt 2 + 4 * Real.sqrt 3 * N
  let rad : ℝ := Real.sqrt M * C
  let T : ℝ := rad ^ 2
  let cTail : ℝ := 1 / (2 : ℝ) ^ N
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ 4 * Real.sqrt 3 * (N : ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg 2]
  have hrad0 : 0 ≤ rad := mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hC1)
  have hset : {y : EuclideanSpace ℝ (Fin n) | T < ‖y‖ ^ 2} =
      {y : EuclideanSpace ℝ (Fin n) | rad < ‖y‖} := by
    ext y
    dsimp only [T]
    simp only [mem_setOf_eq]
    constructor <;> intro h
    · nlinarith [norm_nonneg y]
    · nlinarith [norm_nonneg y]
  have hTM : M ≤ T := by
    dsimp [T, rad]
    rw [mul_pow, Real.sq_sqrt hM.le]
    nlinarith [sq_nonneg (C - 1)]
  have hc0 : 0 ≤ cTail := by dsimp [cTail]; positivity
  have hc1 : cTail < 1 := by
    dsimp [cTail]
    have : (1 : ℝ) < (2 : ℝ) ^ N := one_lt_pow₀ (by norm_num) hN.ne'
    exact (div_lt_one (pow_pos (by norm_num) _)).2 this
  by_contra hnot
  have hpos : 0 < ∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) | T < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x -
        cTail := by
    apply lt_of_not_ge
    simpa only [hset, C, rad, cTail] using hnot
  have hKfin : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  obtain ⟨q, hqc, hqleSq, _hqb, hqpos, hqsuppT⟩ :=
    exists_continuous_normTail_witness hKfin hc0 hc1 hpos
  have hqsuppM : ∀ x, 0 < q x → M < ‖x‖ ^ 2 := fun x hx =>
    hTM.trans_lt (hqsuppT x hx)
  obtain ⟨p, e, a, b, D, he, hab, _hseg, hD0, hDlc, hDint, hmD, hqD⟩ :=
    exists_logConcave_profile_preserving_secondMoment_and_tailCutoff hn hKc hKcl hKb
      hqc hqsuppM hmoment hqpos
  have hqleM : ∀ x, q x ≤
      {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x -
        cTail := by
    intro x
    have h := hqleSq x
    by_cases hxT : T < ‖x‖ ^ 2
    · have hxM : M < ‖x‖ ^ 2 := hTM.trans_lt hxT
      have hxTmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | T < ‖y‖ ^ 2} := hxT
      have hxMmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2} := hxM
      rw [indicator_of_mem hxTmem] at h
      rw [indicator_of_mem hxMmem]
      exact h
    · have hxTnot : x ∉ {y : EuclideanSpace ℝ (Fin n) | T < ‖y‖ ^ 2} :=
        fun hx => hxT hx
      rw [indicator_of_notMem hxTnot] at h
      by_cases hxM : M < ‖x‖ ^ 2
      · have hxMmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2} := hxM
        rw [indicator_of_mem hxMmem]
        linarith
      · have hxMnot : x ∉ {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2} :=
          fun hx => hxM hx
        rw [indicator_of_notMem hxMnot]
        exact h
  obtain ⟨hmass, hnorm⟩ := localizedNeedle_mass_pos_and_normMoment hab hc0 hD0 hDint
    hqc hqleM hmD hqD
  have hqleRad : ∀ x, q x ≤
      {y : EuclideanSpace ℝ (Fin n) | rad < ‖y‖}.indicator (fun _ => (1 : ℝ)) x -
        cTail := by
    intro x
    simpa only [← hset] using hqleSq x
  have hnonpos := localized_normTail_cutoff_integral_nonpos he hab hM hD0 hDlc hDint hmass
    hnorm hqc (by simpa only [rad, C, cTail] using hqleRad)
  exact (not_lt_of_ge hnonpos) hqD

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.localized_normTail_cutoff_integral_nonpos
#print axioms Ttc.CVAdaptive.body_normTail_dyadic_sub_nonpos
