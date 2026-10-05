/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailHazard
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationNeedleInBody
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLSC

/-!
# Localization bridge for the direct LV norm-tail route

This specializes the proved one-equality/one-inequality localization theorem to the two
quantities needed by a norm-tail argument: preservation of the ambient second moment and a
strictly positive continuous outer-tail cutoff.  It shows that the resulting arbitrary
`LogConcaveOn` profile is sufficient input for the hazard lemmas; no affine-power or
exponential-extremizer conclusion is requested.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

variable {n : ℕ}

/-- A positive continuous cutoff supported strictly beyond the moment radius localizes to a
nondegenerate needle, while the normalized second moment is preserved exactly. -/
theorem exists_logConcave_profile_preserving_secondMoment_and_tailCutoff
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M : ℝ} {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hqcont : Continuous q)
    (hqsupp : ∀ x, 0 < q x → M < ‖x‖ ^ 2)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0)
    (hqpos : 0 < ∫ x in K, q x) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ),
      e ≠ 0 ∧ a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      (∫ t in Icc a b, (‖needleMap p e t‖ ^ 2 - M) * D t) = 0 ∧
      0 < ∫ t in Icc a b, q (needleMap p e t) * D t := by
  have hmomentCont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 - M) := by
    fun_prop
  obtain ⟨p, e, a, b, D, hab, hseg, hD0, hDlc, hDint, hmomentD, hqD⟩ :=
    hloc_needle_in_body hn hKc hKcl hKb
      (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 - M) q
      hmomentCont hqcont hmoment hqpos
  have hene : e ≠ 0 := by
    intro he
    have hmap : ∀ t, needleMap p e t = p := by
      intro t
      simp [needleMap_apply, he]
    have hqfactor :
        (∫ t in Icc a b, q (needleMap p e t) * D t) =
          q p * ∫ t in Icc a b, D t := by
      simp_rw [hmap, ← integral_const_mul]
    have hmomentFactor :
        (∫ t in Icc a b, (‖needleMap p e t‖ ^ 2 - M) * D t) =
          (‖p‖ ^ 2 - M) * ∫ t in Icc a b, D t := by
      simp_rw [hmap, ← integral_const_mul]
    rw [hqfactor] at hqD
    have hDmass0 : 0 ≤ ∫ t in Icc a b, D t :=
      setIntegral_nonneg (μ := volume) measurableSet_Icc fun t ht => hD0 t ht
    have hqp : 0 < q p := by
      by_contra h
      have hqple : q p ≤ 0 := le_of_not_gt h
      have := mul_nonpos_of_nonpos_of_nonneg hqple hDmass0
      linarith
    have hmass : 0 < ∫ t in Icc a b, D t := by
      by_contra h
      have hmassle : (∫ t in Icc a b, D t) ≤ 0 := le_of_not_gt h
      have := mul_nonpos_of_nonneg_of_nonpos hqp.le hmassle
      linarith
    rw [hmomentFactor] at hmomentD
    have hpM : ‖p‖ ^ 2 = M := by
      nlinarith
    exact (hqsupp p hqp).ne' hpM
  exact ⟨p, e, a, b, D, hene, hab, hseg, hD0, hDlc, hDint, hmomentD, hqD⟩

/-- A strict outer-tail excess admits a continuous minorant witness supported in that tail. -/
theorem exists_continuous_normTail_witness
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKfin : volume K ≠ ⊤)
    {M c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hpos : 0 < ∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x - c) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ, Continuous q ∧
      (∀ x, q x ≤
        {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x - c) ∧
      (∀ x, |q x| ≤ 1) ∧ 0 < ∫ x in K, q x ∧
      (∀ x, 0 < q x → M < ‖x‖ ^ 2) := by
  let S : Set (EuclideanSpace ℝ (Fin n)) := {x | M < ‖x‖ ^ 2}
  have hS : IsOpen S := isOpen_lt continuous_const (continuous_norm.pow 2)
  have hlsc : LowerSemicontinuous (fun x : EuclideanSpace ℝ (Fin n) =>
      S.indicator (fun _ => (1 : ℝ)) x - c) := by
    simpa [S] using lowerSemicontinuous_indicator_sub_smul hS continuous_const
      (fun _ => zero_le_one) c
  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      |S.indicator (fun _ => (1 : ℝ)) x - c| ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact (abs_le.2 ⟨by linarith, by linarith⟩)
    · rw [indicator_of_notMem hx, zero_sub, abs_neg, abs_of_nonneg hc0]
      linarith
  obtain ⟨q, hqc, hqle, hqb, hqpos⟩ :=
    exists_continuous_le_setIntegral_pos (μ := volume) hKfin hlsc hbound (by simpa [S] using hpos)
  refine ⟨q, hqc, ?_, hqb, hqpos, ?_⟩
  · simpa [S] using hqle
  · intro x hqx
    by_contra hx
    have hxS : x ∉ S := by simpa [S] using hx
    have := hqle x
    rw [indicator_of_notMem hxS] at this
    linarith

/-- A strict body-level tail violation and the centered moment equality therefore produce a
nondegenerate arbitrary-logconcave needle carrying both violations. -/
theorem exists_logConcave_profile_of_normTail_violation
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0)
    (hpos : 0 < ∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x - c) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ),
      e ≠ 0 ∧ a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      (∫ t in Icc a b, (‖needleMap p e t‖ ^ 2 - M) * D t) = 0 ∧
      ∃ q : EuclideanSpace ℝ (Fin n) → ℝ, Continuous q ∧
        (∀ x, q x ≤
          {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x - c) ∧
        (∀ x, 0 < q x → M < ‖x‖ ^ 2) ∧
        0 < ∫ t in Icc a b, q (needleMap p e t) * D t := by
  have hKfin : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  obtain ⟨q, hqc, hqle, _hqb, hqpos, hqsupp⟩ :=
    exists_continuous_normTail_witness hKfin hc0 hc1 hpos
  obtain ⟨p, e, a, b, D, he, hab, hseg, hD0, hDlc, hDint, hm, hq⟩ :=
    exists_logConcave_profile_preserving_secondMoment_and_tailCutoff hn hKc hKcl hKb
      hqc hqsupp hmoment hqpos
  exact ⟨p, e, a, b, D, he, hab, hseg, hD0, hDlc, hDint, hm,
    q, hqc, hqle, hqsupp, hq⟩

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.exists_logConcave_profile_preserving_secondMoment_and_tailCutoff
#print axioms Ttc.CVAdaptive.exists_continuous_normTail_witness
#print axioms Ttc.CVAdaptive.exists_logConcave_profile_of_normTail_violation
