/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationNeedleInBody

/-!
# Product inequalities from one-equality localization

This file packages the elementary reduction from the one-equality/one-inequality localization
lemma to a strict four-function product inequality.  It is the bounded-body, continuous-integrand
step needed before the one-dimensional analysis in the Gaussian cooling argument.

The output profile is the arbitrary nonnegative log-concave profile supplied by
`Arlib.hloc_needle_in_body`; no claim that it is exponential is made here.
-/

open MeasureTheory Set

namespace Arlib

variable {n : ℕ}

/-- Two strictly positive integrals over a compact convex body remain strictly positive on one
common localization needle.  The equality fed to `hloc_needle_in_body` is
`B * q₁ - A * q₂`, where `A` and `B` are the two ambient integrals. -/
theorem exists_logConcave_profile_two_pos (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K)
    {q₁ q₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hq₁c : Continuous q₁)
    (hq₂c : Continuous q₂) (hq₁pos : 0 < ∫ x in K, q₁ x)
    (hq₂pos : 0 < ∫ x in K, q₂ x) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ), a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      0 < ∫ t in Icc a b, q₁ (needleMap p e t) * D t ∧
      0 < ∫ t in Icc a b, q₂ (needleMap p e t) * D t := by
  let A : ℝ := ∫ x in K, q₁ x
  let B : ℝ := ∫ x in K, q₂ x
  have hA : 0 < A := by simpa [A] using hq₁pos
  have hB : 0 < B := by simpa [B] using hq₂pos
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hq₁int : IntegrableOn q₁ K := hq₁c.continuousOn.integrableOn_compact hKcomp
  have hq₂int : IntegrableOn q₂ K := hq₂c.continuousOn.integrableOn_compact hKcomp
  have hzero : (∫ x in K, (B * q₁ x - A * q₂ x)) = 0 := by
    rw [integral_sub (hq₁int.const_mul B) (hq₂int.const_mul A),
      integral_const_mul, integral_const_mul]
    simp only [A, B]
    ring
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hzeroD, hq₁Dpos⟩ :=
    hloc_needle_in_body hn hKc hKcl hKb
      (fun x ↦ B * q₁ x - A * q₂ x) q₁
      ((continuous_const.mul hq₁c).sub (continuous_const.mul hq₂c)) hq₁c hzero hA
  have hDon : IntegrableOn D (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hDint
  have hneedle : Continuous (needleMap p e) := continuous_needleMap p e
  have hq₁Don : IntegrableOn (fun t ↦ q₁ (needleMap p e t) * D t) (Icc a b) :=
    hDon.continuousOn_mul (hq₁c.comp hneedle).continuousOn isCompact_Icc
  have hq₂Don : IntegrableOn (fun t ↦ q₂ (needleMap p e t) * D t) (Icc a b) :=
    hDon.continuousOn_mul (hq₂c.comp hneedle).continuousOn isCompact_Icc
  have hzeroD' :
      (∫ t in Icc a b,
        B * (q₁ (needleMap p e t) * D t) - A * (q₂ (needleMap p e t) * D t)) = 0 := by
    rw [← hzeroD]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _
    ring
  have hlinear :
      B * (∫ t in Icc a b, q₁ (needleMap p e t) * D t) -
          A * (∫ t in Icc a b, q₂ (needleMap p e t) * D t) = 0 := by
    rw [integral_sub (hq₁Don.const_mul B) (hq₂Don.const_mul A),
      integral_const_mul, integral_const_mul] at hzeroD'
    exact hzeroD'
  have hq₂Dpos : 0 < ∫ t in Icc a b, q₂ (needleMap p e t) * D t := by
    by_contra hnot
    have hnonpos : (∫ t in Icc a b, q₂ (needleMap p e t) * D t) ≤ 0 :=
      le_of_not_gt hnot
    have hleft : 0 < B * (∫ t in Icc a b, q₁ (needleMap p e t) * D t) :=
      mul_pos hB hq₁Dpos
    have hright : A * (∫ t in Icc a b, q₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA.le hnonpos
    linarith
  exact ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hq₁Dpos, hq₂Dpos⟩

/-- A strict failure of a four-function product inequality over a compact convex body localizes
to a strict failure against one common nonnegative log-concave one-dimensional profile.

The positivity assumptions on the second and third ambient integrals are exactly those needed to
choose a positive separator `r` with `A₄ / A₂ < r < A₁ / A₃`.  In the Gaussian cooling
application all four functions are positive Gaussian densities (one may take `f₃ = c * g₀`
and `f₄ = g₀`), so these assumptions are automatic once the body has positive volume. -/
theorem exists_logConcave_profile_product_lt (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K)
    {f₁ f₂ f₃ f₄ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₁c : Continuous f₁) (hf₂c : Continuous f₂) (hf₃c : Continuous f₃)
    (hf₄c : Continuous f₄) (hf₂0 : ∀ x, 0 ≤ f₂ x)
    (hf₃0 : ∀ x, 0 ≤ f₃ x) (hf₄0 : ∀ x, 0 ≤ f₄ x)
    (hf₂pos : 0 < ∫ x in K, f₂ x) (hf₃pos : 0 < ∫ x in K, f₃ x)
    (hfail : (∫ x in K, f₃ x) * (∫ x in K, f₄ x) <
      (∫ x in K, f₁ x) * (∫ x in K, f₂ x)) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ), a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₄ (needleMap p e t) * D t) <
        (∫ t in Icc a b, f₁ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by
  let A₁ : ℝ := ∫ x in K, f₁ x
  let A₂ : ℝ := ∫ x in K, f₂ x
  let A₃ : ℝ := ∫ x in K, f₃ x
  let A₄ : ℝ := ∫ x in K, f₄ x
  have hA₂0 : 0 < A₂ := by simpa [A₂] using hf₂pos
  have hA₃0 : 0 < A₃ := by simpa [A₃] using hf₃pos
  have hA₄0 : 0 ≤ A₄ := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x ↦ hf₄0 x)
  have hfail' : A₃ * A₄ < A₁ * A₂ := by simpa [A₁, A₂, A₃, A₄] using hfail
  have hA₁0 : 0 < A₁ := by
    by_contra hnot
    have hA₁nonpos : A₁ ≤ 0 := le_of_not_gt hnot
    have hright : A₁ * A₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA₁nonpos hA₂0.le
    have hleft : 0 ≤ A₃ * A₄ := mul_nonneg hA₃0.le hA₄0
    linarith
  let r : ℝ := (A₁ * A₂ + A₃ * A₄) / (2 * A₂ * A₃)
  have hr₁ : 0 < A₁ - r * A₃ := by
    dsimp only [r]
    field_simp [ne_of_gt hA₂0, ne_of_gt hA₃0]
    nlinarith
  have hr₂ : 0 < r * A₂ - A₄ := by
    dsimp only [r]
    field_simp [ne_of_gt hA₂0, ne_of_gt hA₃0]
    nlinarith
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hf₁int : IntegrableOn f₁ K := hf₁c.continuousOn.integrableOn_compact hKcomp
  have hf₂int : IntegrableOn f₂ K := hf₂c.continuousOn.integrableOn_compact hKcomp
  have hf₃int : IntegrableOn f₃ K := hf₃c.continuousOn.integrableOn_compact hKcomp
  have hf₄int : IntegrableOn f₄ K := hf₄c.continuousOn.integrableOn_compact hKcomp
  have hq₁pos : 0 < ∫ x in K, (f₁ x - r * f₃ x) := by
    rw [integral_sub hf₁int (hf₃int.const_mul r), integral_const_mul]
    simpa [A₁, A₃] using hr₁
  have hq₂pos : 0 < ∫ x in K, (r * f₂ x - f₄ x) := by
    rw [integral_sub (hf₂int.const_mul r) hf₄int, integral_const_mul]
    simpa [A₂, A₄] using hr₂
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hq₁Dpos, hq₂Dpos⟩ :=
    exists_logConcave_profile_two_pos (q₁ := fun x ↦ f₁ x - r * f₃ x)
      (q₂ := fun x ↦ r * f₂ x - f₄ x) hn hKc hKcl hKb
      (hf₁c.sub (continuous_const.mul hf₃c))
      ((continuous_const.mul hf₂c).sub hf₄c) hq₁pos hq₂pos
  have hDon : IntegrableOn D (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hDint
  have hneedle : Continuous (needleMap p e) := continuous_needleMap p e
  have hfDon : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f →
      IntegrableOn (fun t ↦ f (needleMap p e t) * D t) (Icc a b) := by
    intro f hfc
    exact hDon.continuousOn_mul (hfc.comp hneedle).continuousOn isCompact_Icc
  have hf₁Don := hfDon f₁ hf₁c
  have hf₂Don := hfDon f₂ hf₂c
  have hf₃Don := hfDon f₃ hf₃c
  have hf₄Don := hfDon f₄ hf₄c
  have hlocal₁ : 0 < (∫ t in Icc a b, f₁ (needleMap p e t) * D t) -
      r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) := by
    rw [show (fun t ↦ (f₁ (needleMap p e t) - r * f₃ (needleMap p e t)) * D t) =
        (fun t ↦ f₁ (needleMap p e t) * D t -
          r * (f₃ (needleMap p e t) * D t)) by funext t; ring,
      integral_sub hf₁Don (hf₃Don.const_mul r), integral_const_mul] at hq₁Dpos
    exact hq₁Dpos
  have hlocal₂ : 0 < r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) -
      (∫ t in Icc a b, f₄ (needleMap p e t) * D t) := by
    rw [show (fun t ↦ (r * f₂ (needleMap p e t) - f₄ (needleMap p e t)) * D t) =
        (fun t ↦ r * (f₂ (needleMap p e t) * D t) -
          f₄ (needleMap p e t) * D t) by funext t; ring,
      integral_sub (hf₂Don.const_mul r) hf₄Don, integral_const_mul] at hq₂Dpos
    exact hq₂Dpos
  have hI₂0 : 0 ≤ ∫ t in Icc a b, f₂ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₂0 _) (hD0 t ht)
  have hI₃0 : 0 ≤ ∫ t in Icc a b, f₃ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₃0 _) (hD0 t ht)
  have hI₄0 : 0 ≤ ∫ t in Icc a b, f₄ (needleMap p e t) * D t :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ mul_nonneg (hf₄0 _) (hD0 t ht)
  have hrpos : 0 < r := by
    by_contra hnot
    have hrnonpos : r ≤ 0 := le_of_not_gt hnot
    have : r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrnonpos hI₂0
    linarith
  have hI₂pos : 0 < ∫ t in Icc a b, f₂ (needleMap p e t) * D t := by
    by_contra hnot
    have hI₂nonpos : (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      le_of_not_gt hnot
    have : r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hrpos.le hI₂nonpos
    linarith
  refine ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, ?_⟩
  have hfirst :
      r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) <
        (∫ t in Icc a b, f₁ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by
    apply mul_lt_mul_of_pos_right _ hI₂pos
    linarith
  have hsecond :
      (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (∫ t in Icc a b, f₄ (needleMap p e t) * D t) ≤
        (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
          (r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t)) := by
    apply mul_le_mul_of_nonneg_left _ hI₃0
    linarith
  calc
    _ ≤ (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
        (r * (∫ t in Icc a b, f₂ (needleMap p e t) * D t)) := hsecond
    _ = r * (∫ t in Icc a b, f₃ (needleMap p e t) * D t) *
        (∫ t in Icc a b, f₂ (needleMap p e t) * D t) := by ring
    _ < _ := hfirst

#print axioms exists_logConcave_profile_two_pos
#print axioms exists_logConcave_profile_product_lt

end Arlib
