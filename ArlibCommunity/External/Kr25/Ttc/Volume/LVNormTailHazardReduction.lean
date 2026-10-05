/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailAffineNeedle

/-!
# Body-to-hazard reduction for the LV norm tail

This packages the completed localization and affine moment transport.  Any strict body-level
violation becomes a nondegenerate one-dimensional log-concave profile of positive mass, with
a center on its interval and variance bounded at scale `sqrt M / ‖e‖`.  Thus the only remaining
step toward the body-level logarithmic tail is the elementary comparison between the radial
shells and the two affine-coordinate tail grids.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set
open Arlib

variable {n : ℕ}

/-- A strict radial-tail violation reduced all the way to the exact input interface of the
one-dimensional hazard lemmas. -/
theorem exists_hazardNeedle_of_normTail_violation
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M cTail : ℝ} (hM : 0 < M) (hc0 : 0 ≤ cTail) (hc1 : cTail < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0)
    (hpos : 0 < ∫ x in K,
      {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x -
        cTail) :
    ∃ (p e : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (D : ℝ → ℝ)
        (q : EuclideanSpace ℝ (Fin n) → ℝ),
      e ≠ 0 ∧ a ≤ b ∧
      (∀ t ∈ Icc a b, needleMap p e t ∈ K) ∧
      (∀ t ∈ Icc a b, 0 ≤ D t) ∧ LogConcaveOn (Icc a b) D ∧
      IntervalIntegrable D volume a b ∧
      0 < ∫ t in a..b, D t ∧
      needleSegmentCenter a b p e ∈ Icc a b ∧
      0 < Real.sqrt M / ‖e‖ ∧
      (∫ t in a..b, (t - needleSegmentCenter a b p e) ^ 2 * D t) ≤
        (Real.sqrt M / ‖e‖) ^ 2 * ∫ t in a..b, D t ∧
      Continuous q ∧
      (∀ x, q x ≤
        {y : EuclideanSpace ℝ (Fin n) | M < ‖y‖ ^ 2}.indicator (fun _ => (1 : ℝ)) x -
          cTail) ∧
      (∀ x, 0 < q x → M < ‖x‖ ^ 2) ∧
      0 < ∫ t in Icc a b, q (needleMap p e t) * D t := by
  obtain ⟨p, e, a, b, D, he, hab, hseg, hD0, hDlc, hDint, hmomentD,
      q, hqc, hqle, hqsupp, hqpos⟩ :=
    exists_logConcave_profile_of_normTail_violation hn hKc hKcl hKb hc0 hc1
      hmoment hpos
  obtain ⟨hmass, hnorm⟩ := localizedNeedle_mass_pos_and_normMoment hab hc0 hD0 hDint
    hqc hqle hmomentD hqpos
  have hs : 0 < Real.sqrt M / ‖e‖ :=
    div_pos (Real.sqrt_pos.2 hM) (norm_pos_iff.mpr he)
  have hvar := localizedNeedle_variance_le_ambientScale he hab hM.le hD0 hDint hnorm
  exact ⟨p, e, a, b, D, q, he, hab, hseg, hD0, hDlc, hDint, hmass,
    needleSegmentCenter_mem hab p e, hs, hvar, hqc, hqle, hqsupp, hqpos⟩

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.exists_hazardNeedle_of_normTail_violation
