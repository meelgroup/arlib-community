import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing

/-!
# Scale invariance for CV18 phase kernels

The accuracy-dependent phase core can have an inradius below one.  This file
records the exact dilation identities needed to apply unit-inball KLS results
after rescaling by that inradius.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

theorem smul_inv_inter_eq_inter_smul_inv_cv18
    {r : ℝ} (hr : r ≠ 0) (A B : Set (EuclideanSpace ℝ (Fin n))) :
    r⁻¹ • (A ∩ B) = (r⁻¹ • A) ∩ (r⁻¹ • B) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    exact ⟨⟨y, hyA, rfl⟩, ⟨y, hyB, rfl⟩⟩
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hab : a = b := by
      have h := congrArg (fun z => r • z) (hax.trans hbx.symm)
      simpa [smul_smul, hr] using h
    subst b
    exact ⟨a, ⟨ha, hb⟩, hax⟩

theorem inv_smul_ball_cv18 {r delta : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) :
    r⁻¹ • Metric.ball x delta = Metric.ball (r⁻¹ • x) (delta / r) := by
  rw [_root_.smul_ball (inv_ne_zero hr.ne')]
  have hrad : ‖r⁻¹‖ * delta = delta / r := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), div_eq_mul_inv]
    ring
  rw [hrad]

theorem inv_smul_ball_inter_cv18 {r delta : ℝ} (hr : 0 < r)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    r⁻¹ • (Metric.ball x delta ∩ K) =
      Metric.ball (r⁻¹ • x) (delta / r) ∩ (r⁻¹ • K) := by
  rw [smul_inv_inter_eq_inter_smul_inv_cv18 hr.ne', inv_smul_ball_cv18 hr]

theorem volume_inv_smul_cv18 {r : ℝ} (hr : 0 < r)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume (r⁻¹ • A) = ENNReal.ofReal ((r⁻¹) ^ n) * volume A := by
  rw [Arlib.volume_smul_euclidean (inv_pos.2 hr).le]

/-- Local conductance is invariant under a simultaneous dilation of the
body, proposal radius, and current point. -/
theorem ell_inv_smul_cv18 {r delta : ℝ} (hr : 0 < r)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    ell (r⁻¹ • K) (delta / r) (r⁻¹ • x) = ell K delta x := by
  rw [ell_apply, ell_apply]
  rw [← inv_smul_ball_inter_cv18 hr K x,
    ← inv_smul_ball_cv18 hr x,
    volume_inv_smul_cv18 hr, volume_inv_smul_cv18 hr]
  let a : ENNReal := ENNReal.ofReal ((r⁻¹) ^ n)
  have ha0 : a ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  exact ENNReal.mul_div_mul_left _ _ ha0 hatop

end Arlib.MarkovChains
