/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.KLS97Sharp
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Lovász--Vempala average local conductance at the CV18 step size

This file formalizes the layer-cake and convex-body escape argument underlying
Lemma 6.3 of Lovász--Vempala.  Applied directly to the ball-walk rejection
probability, it proves the weighted average-local-conductance lower bound used
by Cousins--Vempala at their advertised Figure-1 proposal radius.

The direct formulation avoids the auxiliary smoothed density and the
unjustified pointwise comparison discussed in CV18.  The geometric input is
the sharp-order KLS convex-body escape estimate already available in the
HitAndRun development.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise

namespace Arlib.MarkovChains

variable {n : ℕ}

/-! Gaussian roundedness at one fixed quarter-mass level.  This is the
analytic input used when the Lovász--Vempala proof chooses its threshold. -/

theorem pow_mul_gaussianWeightReal_le_direct {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ^ 2 ≤ s) :
    c ^ (n - 1) * gaussianWeightReal (s / c ^ 2) y ≤
      gaussianWeightReal s y := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  set rho : ℝ := ‖y‖ ^ 2 / (2 * s) with hrhodef
  have hrho0 : 0 ≤ rho := by rw [hrhodef]; positivity
  have hrho2 : rho ≤ 1 / 2 := by
    rw [hrhodef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
    linarith
  have hgs : gaussianWeightReal s y = Real.exp (-rho) := by
    unfold gaussianWeightReal
    rw [hrhodef, neg_div]
  have hgc : gaussianWeightReal (s / c ^ 2) y =
      Real.exp (-(c ^ 2 * rho)) := by
    unfold gaussianWeightReal
    congr 1
    rw [hrhodef]
    field_simp
  rw [hgs, hgc]
  have hstep1 : c ^ (n - 1) ≤ c := by
    calc
      c ^ (n - 1) ≤ c ^ 1 := pow_le_pow_of_le_one hc.le hc1 (by omega)
      _ = c := pow_one c
  have hlog : Real.log c ≤ (c ^ 2 - 1) / 2 := by
    have h := Real.log_le_sub_one_of_pos hc2
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hc21 : c ^ 2 ≤ 1 := by nlinarith
  have hprod : 0 ≤ (1 - c ^ 2) * (1 / 2 - rho) :=
    mul_nonneg (by linarith) (by linarith)
  have hkey : Real.log c - c ^ 2 * rho ≤ -rho := by nlinarith
  calc
    c ^ (n - 1) * Real.exp (-(c ^ 2 * rho))
        ≤ c * Real.exp (-(c ^ 2 * rho)) :=
      mul_le_mul_of_nonneg_right hstep1 (Real.exp_nonneg _)
    _ = Real.exp (Real.log c) * Real.exp (-(c ^ 2 * rho)) := by
      rw [Real.exp_log hc]
    _ = Real.exp (Real.log c - c ^ 2 * rho) := by
      rw [← Real.exp_add]
      ring_nf
    _ ≤ Real.exp (-rho) := Real.exp_le_exp.2 hkey

theorem pow_mul_gaussianWeight_le_direct {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ^ 2 ≤ s) :
    ENNReal.ofReal (c ^ (n - 1)) * gaussianWeight (s / c ^ 2) y ≤
      gaussianWeight s y := by
  unfold gaussianWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (pow_mul_gaussianWeightReal_le_direct hs hc hc1 hn hy)

theorem lintegral_gaussianWeight_ball_le_direct {s c m : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1) (hn : 2 ≤ n)
    (hms : m ^ 2 ≤ s) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (c * m), gaussianWeight s x ≤
      ENNReal.ofReal c *
        ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m, gaussianWeight s x := by
  have hsmul : c • ball (0 : EuclideanSpace ℝ (Fin n)) m = ball 0 (c * m) := by
    rw [_root_.smul_ball (ne_of_gt hc), smul_zero, Real.norm_eq_abs,
      abs_of_pos hc]
  have hcn : c ^ n = c * c ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
    ring_nf
  calc
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (c * m), gaussianWeight s x
        = ∫⁻ x in c • ball (0 : EuclideanSpace ℝ (Fin n)) m,
            gaussianWeight s x := by rw [hsmul]
    _ = ENNReal.ofReal (c ^ n) *
          ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m,
            gaussianWeight (s / c ^ 2) x :=
      lintegral_gaussianWeight_smul_set_cv18 measurableSet_ball hc s
    _ = ENNReal.ofReal c *
          ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m,
            ENNReal.ofReal (c ^ (n - 1)) * gaussianWeight (s / c ^ 2) x := by
      rw [lintegral_const_mul _ (measurable_gaussianWeight _), hcn,
        ENNReal.ofReal_mul hc.le, mul_assoc]
    _ ≤ ENNReal.ofReal c *
          ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) m,
            gaussianWeight s x := by
      refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_ball fun x hx => ?_)
      have hxm : ‖x‖ < m := by
        rw [mem_ball, dist_zero_right] at hx
        exact hx
      exact pow_mul_gaussianWeight_le_direct hs hc hc1 hn
        (by nlinarith [norm_nonneg x])

/-- The Gaussian mass inside the ball of radius `min sigma 1 / 4` is at
most one quarter of the mass of any body containing the unit ball. -/
theorem gaussian_quarterBall_mass_le_direct_radius
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {inradius : ℝ} (hinradius : 0 < inradius)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) inradius ⊆ K)
    {sigma : ℝ} (hsigma : 0 < sigma) (hn : 2 ≤ n) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (min sigma inradius / 4),
        gaussianWeight (sigma ^ 2) x ≤
      ENNReal.ofReal (1 / 4) *
        ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
  have ha0 : 0 < min sigma inradius := lt_min hsigma hinradius
  have ha1 : min sigma inradius ≤ inradius := min_le_right _ _
  have has : min sigma inradius ^ 2 ≤ sigma ^ 2 := by
    have := min_le_left sigma inradius
    nlinarith
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (min sigma inradius) ⊆ K :=
    (Metric.ball_subset_ball ha1).trans hball
  calc
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (min sigma inradius / 4),
        gaussianWeight (sigma ^ 2) x
        = ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n))
            ((1 / 4 : ℝ) * min sigma inradius), gaussianWeight (sigma ^ 2) x := by
          congr 2
          ring_nf
    _ ≤ ENNReal.ofReal (1 / 4) *
          ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (min sigma inradius),
            gaussianWeight (sigma ^ 2) x :=
      lintegral_gaussianWeight_ball_le_direct (by positivity) (by norm_num)
        (by norm_num) hn has
    _ ≤ ENNReal.ofReal (1 / 4) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
      gcongr

/-- Unit-inball specialization of the scale-aware quarter-mass estimate. -/
theorem gaussian_quarterBall_mass_le_direct
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {sigma : ℝ} (hsigma : 0 < sigma) (hn : 2 ≤ n) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (min sigma 1 / 4),
        gaussianWeight (sigma ^ 2) x ≤
      ENNReal.ofReal (1 / 4) *
        ∫⁻ x in K, gaussianWeight (sigma ^ 2) x :=
  gaussian_quarterBall_mass_le_direct_radius one_pos hball hsigma hn

theorem levelSet_gaussianWeightReal_direct {s : ℝ} (hs : 0 < s)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    {x : EuclideanSpace ℝ (Fin n) | x ∈ K ∧ c ≤ gaussianWeightReal s x} =
      K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n))
        (Real.sqrt (-(2 * s * Real.log c))) := by
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hR : 0 ≤ -(2 * s * Real.log c) := by nlinarith
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_closedBall, dist_zero_right]
  refine and_congr_right fun _ => ?_
  have hiff : c ≤ gaussianWeightReal s x ↔ ‖x‖ ^ 2 ≤ -(2 * s * Real.log c) := by
    rw [show gaussianWeightReal s x = Real.exp (-‖x‖ ^ 2 / (2 * s)) from rfl,
      ← Real.log_le_iff_le_exp hc, le_div_iff₀ h2s]
    constructor <;> intro h <;> nlinarith
  rw [hiff]
  constructor
  · intro h
    calc
      ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (-(2 * s * Real.log c)) := Real.sqrt_le_sqrt h
  · intro h
    have hsq := Real.sq_sqrt hR
    nlinarith [norm_nonneg x, Real.sqrt_nonneg (-(2 * s * Real.log c))]

theorem lintegral_closedBall_eq_ball_direct (hn : n ≠ 0)
    (r : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    ∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) r, g x =
      ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) r, g x := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hae : (closedBall (0 : EuclideanSpace ℝ (Fin n)) r :
      Set (EuclideanSpace ℝ (Fin n))) =ᵐ[volume] ball 0 r := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Metric.closedBall_sdiff_ball]
      exact Measure.addHaar_sphere volume 0 r
    · rw [Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
      exact measure_empty
  rw [Measure.restrict_congr_set hae]

/-- The rejected-proposal probability, multiplied by the proposal-ball
volume, is the volume of the rejected part of the ball. -/
theorem one_sub_ell_mul_volume_ball_eq
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (x : EuclideanSpace ℝ (Fin n)) :
    (1 - ell K delta x) * volume (ball x delta) = volume (ball x delta \ K) := by
  let V : ℝ≥0∞ := volume (ball x delta)
  let A : ℝ≥0∞ := volume (ball x delta ∩ K)
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume x hdelta).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top hVtop (measure_mono Set.inter_subset_left)
  have hellV : ell K delta x * V = A := by
    rw [ell_apply]
    exact ENNReal.div_mul_cancel hV0 hVtop
  have hbad : volume (ball x delta \ K) = V - A := by
    have hset : ball x delta \ K = ball x delta \ (ball x delta ∩ K) := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hset, measure_sdiff Set.inter_subset_left
      (measurableSet_ball.inter hK).nullMeasurableSet hAtop]
  rw [hbad]
  by_cases h0 : ell K delta x = 0
  · have hA0 : A = 0 := by simpa [h0] using hellV.symm
    calc
      (1 - ell K delta x) * volume (ball x delta) = V := by simp [h0, V]
      _ = V - A := by simp [hA0]
  by_cases h1 : ell K delta x = 1
  · have hAV : A = V := by simpa [h1] using hellV.symm
    calc
      (1 - ell K delta x) * volume (ball x delta) = 0 := by simp [h1]
      _ = V - A := by simp [hAV]
  have hlt : ell K delta x < 1 := lt_of_le_of_ne
    (ell_le_one K delta x) h1
  rw [ENNReal.sub_mul (fun _ _ => hVtop), one_mul, hellV]

/-- KLS's convex-body escape estimate controls the mean rejected-proposal
probability on any inner level set. -/
theorem setLIntegral_one_sub_ell_le_of_innerBody
    (hn : n ≠ 0) {K L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hLK : L ⊆ K)
    (hLc : Convex ℝ L) (hLcl : IsClosed L) (hLfin : volume L ≠ ⊤)
    {z : EuclideanSpace ℝ (Fin n)} {r delta : ℝ}
    (hball : closedBall z r ⊆ L) (hr : 0 < r) (hdelta : 0 < delta) :
    ∫⁻ x in L, (1 - ell K delta x) ≤
      ENNReal.ofReal (10 * (delta * Real.sqrt n) / (2 * r)) * volume L := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  let V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hV0 : V ≠ 0 :=
    (Metric.measure_ball_pos volume 0 hdelta).ne'
  have hVtop : V ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hbadm : Measurable fun x : EuclideanSpace ℝ (Fin n) => 1 - ell K delta x :=
    measurable_const.sub (measurable_ell hK delta)
  have hpoint : ∀ x ∈ L,
      (1 - ell K delta x) * V ≤
        volume (closedBall x delta \ L) := by
    intro x hx
    change (1 - ell K delta x) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) delta) ≤ _
    rw [← volume_ball_eq x delta, one_sub_ell_mul_volume_ball_eq hK hdelta]
    exact measure_mono fun y hy => ⟨Metric.ball_subset_closedBall hy.1, fun hyL => hy.2 (hLK hyL)⟩
  have hmain := Arlib.lintegral_volume_closedBall_sdiff_le_sqrt
    hn hLc hLcl hLfin hball hr hdelta
  have hclosed : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) = V :=
    Measure.addHaar_closedBall_eq_addHaar_ball volume 0 delta
  rw [hclosed] at hmain
  apply (ENNReal.mul_le_mul_iff_right hV0 hVtop).1
  rw [← lintegral_const_mul _ hbadm]
  calc
    ∫⁻ x in L, V * (1 - ell K delta x)
        ≤ ∫⁻ x in L, volume (closedBall x delta \ L) :=
      setLIntegral_mono' hLcl.measurableSet fun x hx => by
        simpa [mul_comm] using hpoint x hx
    _ ≤ ENNReal.ofReal (10 * (delta * Real.sqrt n) / (2 * r)) * volume L *
          V := hmain
    _ = V * (ENNReal.ofReal (10 * (delta * Real.sqrt n) / (2 * r)) * volume L) := by ac_rfl

/-! ## Direct Lovász--Vempala layer-cake argument

The source proof of Lemma 6.3 can be applied directly to the rejected-proposal
probability.  This avoids introducing the smoothing function and therefore
avoids CV18's separate, problematic pointwise comparison `fhat ≤ ell * f`. -/

theorem gaussian_rejectedMass_le_direct_radius
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    {inradius : ℝ} (hinradius : 0 < inradius)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) inradius ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∫⁻ x in K, (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x ≤
      (ENNReal.ofReal (1 / 4) +
        ENNReal.ofReal (20 * delta * Real.sqrt n / min sigma inradius)) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hn0 : n ≠ 0 := by omega
  have hK : MeasurableSet K := hKcl.measurableSet
  let a : ℝ := min sigma inradius
  have ha0 : 0 < a := lt_min hsigma hinradius
  have ha1 : a ≤ inradius := min_le_right _ _
  let rho : ℝ := a / 4
  have hrho0 : 0 < rho := div_pos ha0 (by norm_num)
  have hrho1 : rho < inradius := by dsimp [rho]; linarith
  let tau : ℝ := Real.exp (-(rho ^ 2) / (2 * sigma ^ 2))
  have htau0 : 0 < tau := Real.exp_pos _
  have htau1 : tau ≤ 1 := by
    change Real.exp (-(rho ^ 2) / (2 * sigma ^ 2)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg rho)) (by positivity)
  let f : EuclideanSpace ℝ (Fin n) → ℝ := gaussianWeightReal (sigma ^ 2)
  have hfm : Measurable f := continuous_gaussianWeightReal (sigma ^ 2) |>.measurable
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    change 0 ≤ Real.exp (-‖x‖ ^ 2 / (2 * sigma ^ 2))
    positivity
  have hfof : ∀ x, ENNReal.ofReal (f x) = gaussianWeight (sigma ^ 2) x := fun _ => rfl
  let bad : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x => 1 - ell K delta x
  have hbadm : Measurable bad := measurable_const.sub (measurable_ell hK delta)
  have hbad1 : ∀ x, bad x ≤ 1 := fun x => tsub_le_self
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.restrict K
  let nu : Measure (EuclideanSpace ℝ (Fin n)) := mu.withDensity bad
  let level : ℝ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun t => {x | x ∈ K ∧ t ≤ f x}
  have hlevelm : ∀ t, MeasurableSet (level t) := fun t =>
    hK.inter (measurableSet_le measurable_const hfm)
  have hmu_level : ∀ t, mu {x | t ≤ f x} = volume (level t) := by
    intro t
    change (volume.restrict K) {x | t ≤ f x} = volume (level t)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hfm)]
    congr 1
    ext x
    simp only [level, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hnu_level : ∀ t, nu {x | t ≤ f x} = ∫⁻ x in level t, bad x := by
    intro t
    change (mu.withDensity bad) {x | t ≤ f x} = _
    rw [withDensity_apply _ (measurableSet_le measurable_const hfm)]
    change (∫⁻ x in {x | t ≤ f x}, bad x ∂volume.restrict K) = _
    rw [Measure.restrict_restrict (measurableSet_le measurable_const hfm)]
    congr 2
    ext x
    simp only [level, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hcake : ∀ m : Measure (EuclideanSpace ℝ (Fin n)),
      ∫⁻ x, gaussianWeight (sigma ^ 2) x ∂m =
        ∫⁻ t in Ioi (0 : ℝ), m {x | t ≤ f x} := by
    intro m
    simpa only [hfof] using
      (lintegral_eq_lintegral_meas_le m
        (Filter.Eventually.of_forall hf0) hfm.aemeasurable)
  have hleft : ∫⁻ x, gaussianWeight (sigma ^ 2) x ∂nu =
      ∫⁻ x in K, bad x * gaussianWeight (sigma ^ 2) x := by
    change (∫⁻ x, gaussianWeight (sigma ^ 2) x ∂mu.withDensity bad) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hbadm
      (measurable_gaussianWeight _)]
    change (∫⁻ x, bad x * gaussianWeight (sigma ^ 2) x ∂volume.restrict K) = _
    rfl
  have hrad : Real.sqrt (-(2 * sigma ^ 2 * Real.log tau)) = rho := by
    have hlog : Real.log tau = -(rho ^ 2) / (2 * sigma ^ 2) := by
      change Real.log (Real.exp (-(rho ^ 2) / (2 * sigma ^ 2))) = _
      rw [Real.log_exp]
    rw [hlog]
    have hs2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 hsigma.ne'
    have heq : -(2 * sigma ^ 2 * (-(rho ^ 2) / (2 * sigma ^ 2))) = rho ^ 2 := by
      field_simp
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos hrho0]
  have hlevel_tau : level tau = closedBall (0 : EuclideanSpace ℝ (Fin n)) rho := by
    have h := levelSet_gaussianWeightReal_direct (s := sigma ^ 2)
      (by positivity) htau0 htau1 K
    change {x | x ∈ K ∧ tau ≤ gaussianWeightReal (sigma ^ 2) x} = _
    rw [h, hrad]
    apply Set.inter_eq_right.2
    exact fun x hx => hball (Metric.closedBall_subset_ball hrho1 hx)
  have hquarter : ∫⁻ x in level tau, gaussianWeight (sigma ^ 2) x ≤
      ENNReal.ofReal (1 / 4) * ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
    rw [hlevel_tau, lintegral_closedBall_eq_ball_direct hn0]
    simpa [a, rho] using
      gaussian_quarterBall_mass_le_direct_radius hinradius hball hsigma hn
  let C : ℝ≥0∞ := ENNReal.ofReal (20 * delta * Real.sqrt n / a)
  have hC : ENNReal.ofReal (10 * (delta * Real.sqrt n) / (2 * rho)) = C := by
    congr 1
    dsimp [C, rho]
    field_simp
    ring_nf
  have hlow_point : ∀ t ∈ Ioc (0 : ℝ) tau,
      nu {x | t ≤ f x} ≤ C * mu {x | t ≤ f x} := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.trans htau1
    have hlev_eq := levelSet_gaussianWeightReal_direct (s := sigma ^ 2)
      (by positivity) ht.1 ht1 K
    have hLc : Convex ℝ (level t) := by
      change Convex ℝ {x | x ∈ K ∧ t ≤ gaussianWeightReal (sigma ^ 2) x}
      rw [hlev_eq]
      exact hKc.inter (convex_closedBall 0 _)
    have hLcl : IsClosed (level t) := by
      change IsClosed {x | x ∈ K ∧ t ≤ gaussianWeightReal (sigma ^ 2) x}
      rw [hlev_eq]
      exact hKcl.inter isClosed_closedBall
    have hLfin : volume (level t) ≠ ⊤ :=
      ne_top_of_le_ne_top hKfin (measure_mono fun x hx => hx.1)
    have hin : closedBall (0 : EuclideanSpace ℝ (Fin n)) rho ⊆ level t := by
      rw [← hlevel_tau]
      intro x hx
      exact ⟨hx.1, ht.2.trans hx.2⟩
    rw [hnu_level, hmu_level, ← hC]
    exact setLIntegral_one_sub_ell_le_of_innerBody hn0 hK
      (fun x hx => hx.1) hLc hLcl hLfin hin hrho0 hdelta
  have htail_mu_m : Measurable fun t => mu {x | t ≤ f x} :=
    Antitone.measurable fun s t hst => measure_mono fun x hx => hst.trans hx
  have htail_nu_m : Measurable fun t => nu {x | t ≤ f x} :=
    Antitone.measurable fun s t hst => measure_mono fun x hx => hst.trans hx
  have hlow : (∫⁻ t in Ioc (0 : ℝ) tau, nu {x | t ≤ f x}) ≤
      C * ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) tau, nu {x | t ≤ f x})
          ≤ ∫⁻ t in Ioc (0 : ℝ) tau, C * mu {x | t ≤ f x} :=
        setLIntegral_mono' measurableSet_Ioc hlow_point
      _ = C * ∫⁻ t in Ioc (0 : ℝ) tau, mu {x | t ≤ f x} := by
        rw [lintegral_const_mul _ htail_mu_m]
      _ ≤ C * ∫⁻ t in Ioi (0 : ℝ), mu {x | t ≤ f x} := by
        gcongr
        exact Ioc_subset_Ioi_self
      _ = C * ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
        rw [← hcake mu]
  let muTau : Measure (EuclideanSpace ℝ (Fin n)) := volume.restrict (level tau)
  have hhigh_point : ∀ t ∈ Ioi tau,
      nu {x | t ≤ f x} ≤ muTau {x | t ≤ f x} := by
    intro t ht
    rw [hnu_level]
    change (∫⁻ x in level t, bad x) ≤
      (volume.restrict (level tau)) {x | t ≤ f x}
    rw [Measure.restrict_apply (measurableSet_le measurable_const hfm)]
    calc
      (∫⁻ x in level t, bad x) ≤ ∫⁻ _x in level t, (1 : ℝ≥0∞) :=
        setLIntegral_mono' (hlevelm t) fun x _ => hbad1 x
      _ = volume (level t) := by simp
      _ = volume ({x | t ≤ f x} ∩ level tau) := by
        congr 1
        ext x
        simp only [level, Set.mem_ofPred_eq, Set.mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx.2, ⟨hx.1, ht.le.trans hx.2⟩⟩
        · intro hx
          exact ⟨hx.2.1, hx.1⟩
  have htail_tau_m : Measurable fun t => muTau {x | t ≤ f x} :=
    Antitone.measurable fun s t hst => measure_mono fun x hx => hst.trans hx
  have hhigh : (∫⁻ t in Ioi tau, nu {x | t ≤ f x}) ≤
      ENNReal.ofReal (1 / 4) * ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
    calc
      (∫⁻ t in Ioi tau, nu {x | t ≤ f x})
          ≤ ∫⁻ t in Ioi tau, muTau {x | t ≤ f x} :=
        setLIntegral_mono' measurableSet_Ioi hhigh_point
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), muTau {x | t ≤ f x} :=
        lintegral_mono_set (Ioi_subset_Ioi htau0.le)
      _ = ∫⁻ x in level tau, gaussianWeight (sigma ^ 2) x := by
        rw [← hcake muTau]
      _ ≤ ENNReal.ofReal (1 / 4) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := hquarter
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) tau ∪ Ioi tau :=
    (Ioc_union_Ioi_eq_Ioi htau0.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) tau) (Ioi tau) := Ioc_disjoint_Ioi le_rfl
  rw [← hleft, hcake nu, hsplit, lintegral_union measurableSet_Ioi hdisj]
  calc
    (∫⁻ t in Ioc (0 : ℝ) tau, nu {x | t ≤ f x}) +
          ∫⁻ t in Ioi tau, nu {x | t ≤ f x}
        ≤ C * (∫⁻ x in K, gaussianWeight (sigma ^ 2) x) +
          ENNReal.ofReal (1 / 4) *
            ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := add_le_add hlow hhigh
    _ = (ENNReal.ofReal (1 / 4) + C) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by
      rw [add_mul]
      ac_rfl
    _ = (ENNReal.ofReal (1 / 4) +
          ENNReal.ofReal (20 * delta * Real.sqrt n / min sigma inradius)) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x := by rfl

/-- Unit-inball specialization of the scale-aware rejected-mass estimate. -/
theorem gaussian_rejectedMass_le_direct
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta) :
    ∫⁻ x in K, (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x ≤
      (ENNReal.ofReal (1 / 4) +
        ENNReal.ofReal (20 * delta * Real.sqrt n / min sigma 1)) *
          ∫⁻ x in K, gaussianWeight (sigma ^ 2) x :=
  gaussian_rejectedMass_le_direct_radius hn hKc hKcl hKfin one_pos hball
    hsigma hdelta

/-- At the CV18/Lovász--Vempala step scale, the Gaussian-weighted average
local conductance is at least one half.  This is the direct consequence of
the preceding rejection-mass estimate. -/
theorem half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct_radius
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    {inradius : ℝ} (hinradius : 0 < inradius)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) inradius ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma inradius / (4096 * Real.sqrt n)) :
    ENNReal.ofReal (1 / 2) *
        (∫⁻ x in K, gaussianWeight (sigma ^ 2) x) ≤
      ellGaussianMeasure K delta (sigma ^ 2) Set.univ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have ha0 : 0 < min sigma inradius := lt_min hsigma hinradius
  have hratio : 20 * delta * Real.sqrt n / min sigma inradius ≤ 1 / 4 := by
    calc
      20 * delta * Real.sqrt n / min sigma inradius
          ≤ 20 * (min sigma inradius / (4096 * Real.sqrt n)) *
              Real.sqrt n / min sigma inradius := by gcongr
      _ = 20 / 4096 := by field_simp
      _ ≤ 1 / 4 := by norm_num
  have hcoeff : ENNReal.ofReal (1 / 4) +
        ENNReal.ofReal (20 * delta * Real.sqrt n / min sigma inradius) ≤
      ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  let T : ℝ≥0∞ := ∫⁻ x in K, gaussianWeight (sigma ^ 2) x
  let G : ℝ≥0∞ := ∫⁻ x in K,
    ell K delta x * gaussianWeight (sigma ^ 2) x
  let B : ℝ≥0∞ := ∫⁻ x in K,
    (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x
  let H : ℝ≥0∞ := ENNReal.ofReal (1 / 2)
  have hB : B ≤ H * T := by
    calc
      B ≤ (ENNReal.ofReal (1 / 4) +
            ENNReal.ofReal (20 * delta * Real.sqrt n / min sigma inradius)) * T :=
        gaussian_rejectedMass_le_direct_radius hn hKc hKcl hKfin hinradius hball
          hsigma hdelta
      _ ≤ H * T := by gcongr
  have hTtop : T ≠ ⊤ := by
    apply ne_top_of_le_ne_top hKfin
    change (∫⁻ x in K, gaussianWeight (sigma ^ 2) x) ≤ volume K
    simpa only [setLIntegral_one] using
      (setLIntegral_mono' hKcl.measurableSet fun x _ =>
        gaussianWeight_le_one (by positivity) x)
  have hHTtop : H * T ≠ ⊤ :=
    (ENNReal.mul_lt_top (by simp [H]) (lt_top_iff_ne_top.2 hTtop)).ne
  have hTG : T = G + B := by
    change (∫⁻ x, gaussianWeight (sigma ^ 2) x ∂volume.restrict K) =
      (∫⁻ x, ell K delta x * gaussianWeight (sigma ^ 2) x ∂volume.restrict K) +
      ∫⁻ x, (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x ∂volume.restrict K
    calc
      (∫⁻ x, gaussianWeight (sigma ^ 2) x ∂volume.restrict K) =
          ∫⁻ x, ell K delta x * gaussianWeight (sigma ^ 2) x +
            (1 - ell K delta x) * gaussianWeight (sigma ^ 2) x
              ∂volume.restrict K := by
        refine lintegral_congr fun x => ?_
        rw [← add_mul, add_tsub_cancel_of_le (ell_le_one K delta x), one_mul]
      _ = _ := lintegral_add_left
        ((measurable_ell hKcl.measurableSet delta).mul (measurable_gaussianWeight _)) _
  have hHH : H * T + H * T = T := by
    rw [← add_mul]
    change (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) * T = T
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [ellGaussianMeasure_univ]
  change H * T ≤ G
  apply (ENNReal.add_le_add_iff_right hHTtop).1
  calc
    H * T + H * T = T := hHH
    _ = G + B := hTG
    _ ≤ G + H * T := by simpa only [add_comm] using add_le_add_left hB G

/-- Unit-inball specialization of the scale-aware average-conductance bound. -/
theorem half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n)) :
    ENNReal.ofReal (1 / 2) *
        (∫⁻ x in K, gaussianWeight (sigma ^ 2) x) ≤
      ellGaussianMeasure K delta (sigma ^ 2) Set.univ :=
  half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct_radius
    hn hKc hKcl hKfin one_pos hball hsigma hdelta hstep

/-- The Lovász--Vempala lower bound also discharges the nonzero normalization
guard for the speedy stationary law. -/
theorem ellGaussianMeasure_ne_zero_of_LVStep
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n)) :
    ellGaussianMeasure K delta (sigma ^ 2) Set.univ ≠ 0 := by
  have hunit : 0 < ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      gaussianWeight (sigma ^ 2) x := by
    rw [← withDensity_apply _ measurableSet_ball]
    exact pos_iff_ne_zero.mpr
      (withDensity_gaussianWeight_unitBall_ne_zero (by positivity))
  have hGpos : 0 < ∫⁻ x in K, gaussianWeight (sigma ^ 2) x :=
    lt_of_lt_of_le hunit
      (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl)
  have hhalfpos : 0 < ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_pos.2 (by norm_num)
  exact ne_of_gt (lt_of_lt_of_le
    (ENNReal.mul_pos hhalfpos.ne' hGpos.ne')
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma hdelta hstep))

/-- At the CV18/Lovász--Vempala step scale, `t` independently restarted
proper speedy steps use at most `2 t M` raw proposals in expectation. -/
theorem half_mul_lintegral_properProposalTotalCost_le_LVStep
    (hn : 2 ≤ n) {K : Set (GaussianState n)}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : GaussianState n) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n))
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : ℕ) :
    ENNReal.ofReal (1 / 2) * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (properProposalCostedKernel K hKcl.measurableSet delta (sigma ^ 2)) mu)) ≤
      (t : ℝ≥0∞) * M := by
  exact mul_lintegral_properProposalTotalCost_le hKcl.measurableSet hdelta (sigma ^ 2)
    (ellGaussianMeasure_ne_zero_of_LVStep
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    (ellGaussianMeasure_ne_top_cv18 hKfin delta (by positivity))
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    hwarm t

/-- Markov-cutoff form of the proper-proposal cost bound at the advertised
CV18/Lovász--Vempala step scale. -/
theorem half_mul_mul_measure_properProposalTotalCost_ge_le_LVStep
    (hn : 2 ≤ n) {K : Set (GaussianState n)}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : GaussianState n) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n))
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2)))
    (t : ℕ) (cutoff : ℝ≥0∞) :
    ENNReal.ofReal (1 / 2) * cutoff *
        restartedCostExecution
          (properProposalCostedKernel K hKcl.measurableSet delta (sigma ^ 2)) mu
          {omega | cutoff ≤ restartedTotalCost t omega} ≤
      (t : ℝ≥0∞) * M := by
  exact mul_mul_measure_properProposalTotalCost_ge_le hKcl.measurableSet hdelta (sigma ^ 2)
    (ellGaussianMeasure_ne_zero_of_LVStep
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    (ellGaussianMeasure_ne_top_cv18 hKfin delta (by positivity))
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    hwarm t cutoff

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric
open scoped ENNReal

/-- The direct Lovász--Vempala average-conductance theorem at the proposal
radius displayed in CV18 Figure 1, specialized to the truncated input body. -/
theorem half_mul_lintegral_gaussianWeight_le_figureOne
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) :
    ENNReal.ofReal (1 / 2) *
        (∫⁻ x in truncatedBody q I,
          Arlib.MarkovChains.gaussianWeight sigma2 x) ≤
      Arlib.MarkovChains.ellGaussianMeasure (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2 Set.univ := by
  have hn : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hnR : (0 : ℝ) < q.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
  have hmul : (q.n : ℝ) ≤ (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) := by
    nlinarith
  have hsqrt : Real.sqrt q.n ≤
      Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps)) :=
    Real.sqrt_le_sqrt hmul
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hstep : figureOneProposalRadius q sigma2 ≤
      min (Real.sqrt sigma2) 1 / (4096 * Real.sqrt q.n) := by
    unfold figureOneProposalRadius
    gcongr
  have hKc : Convex ℝ (truncatedBody q I) :=
    (truncatedVolumeInput q I).body.convex
  have hKcl : IsClosed (truncatedBody q I) :=
    (truncatedVolumeInput q I).body.isCompact.isClosed
  have hKfin : volume (truncatedBody q I) ≠ ⊤ :=
    (truncatedVolumeInput q I).body.isCompact.measure_lt_top.ne
  have hball : ball (0 : AmbientSpace q.n) 1 ⊆ truncatedBody q I :=
    fun _ hx => unitBall_subset_truncatedBody q I (Metric.ball_subset_closedBall hx)
  have h := Arlib.MarkovChains.half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma (figureOneProposalRadius_pos q hsigma2) hstep
  simpa [Real.sq_sqrt hsigma2.le] using h

end ArlibCommunity.Algorithms.CV18
