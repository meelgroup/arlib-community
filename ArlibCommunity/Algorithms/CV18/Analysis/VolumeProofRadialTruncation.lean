/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofIdealProduct
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailExplicitVolume

/-!
# Radial truncation for the CV18 volume algorithm

This file instantiates the localization-based norm-tail theorem at the
uniform law on the input convex body.  The numerical factor in
`volumeTerminalScale` is an explicit replacement for the unspecified
absolute constant in the paper's `O(log (1 / ε))` truncation radius.
-/

open MeasureTheory Metric Set

namespace ArlibCommunity.Algorithms.CV18

open Ttc.CVAdaptive

private theorem uniformSecondMoment_pos (q : VolumeParams) (I : VolumeInput q.n) :
    0 < uniformSecondMoment I := by
  letI : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  let K : Set (AmbientSpace q.n) := I.body
  have hKtop : volume K ≠ ⊤ := I.body.isCompact.measure_lt_top.ne
  have hK0 : volume K ≠ 0 := by
    intro hzero
    have hzero' : euclideanVolume I = 0 := by simp [euclideanVolume, K, hzero]
    exact (euclideanVolume_pos q I).ne' hzero'
  have hint : IntegrableOn (fun x : AmbientSpace q.n => ‖x‖ ^ 2) K volume :=
    (continuous_norm.pow 2).continuousOn.integrableOn_compact I.body.isCompact
  have hsupport : Function.support (fun x : AmbientSpace q.n => ‖x‖ ^ 2) =
      ({0} : Set (AmbientSpace q.n))ᶜ := by
    ext x
    simp [Function.mem_support, norm_eq_zero]
  have hintegral : 0 < ∫ x in K, ‖x‖ ^ 2 := by
    apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg ‖x‖) hint).2
    rw [hsupport, Measure.restrict_apply
      ((measurableSet_singleton (0 : AmbientSpace q.n)).compl)]
    rw [inter_comm]
    change 0 < volume (K \ ({0} : Set (AmbientSpace q.n)))
    rw [measure_diff_null (measure_singleton 0)]
    exact bot_lt_iff_ne_bot.mpr hK0
  unfold uniformSecondMoment euclideanVolume
  exact div_pos hintegral (ENNReal.toReal_pos hK0 hKtop)

private theorem centered_uniformSecondMoment
    (q : VolumeParams) (I : VolumeInput q.n) :
    (∫ x in (I.body : Set (AmbientSpace q.n)),
      (‖x‖ ^ 2 - uniformSecondMoment I)) = 0 := by
  let K : Set (AmbientSpace q.n) := I.body
  have hKtop : volume K ≠ ⊤ := I.body.isCompact.measure_lt_top.ne
  have hK0 : volume K ≠ 0 := by
    intro hzero
    have hzero' : euclideanVolume I = 0 := by simp [euclideanVolume, K, hzero]
    exact (euclideanVolume_pos q I).ne' hzero'
  have hint : IntegrableOn (fun x : AmbientSpace q.n => ‖x‖ ^ 2) K volume :=
    (continuous_norm.pow 2).continuousOn.integrableOn_compact I.body.isCompact
  have hconst : IntegrableOn (fun _ : AmbientSpace q.n => uniformSecondMoment I) K volume :=
    integrableOn_const hKtop
  rw [integral_sub hint hconst, setIntegral_const, smul_eq_mul, measureReal_def]
  unfold uniformSecondMoment euclideanVolume
  change (∫ x in K, ‖x‖ ^ 2) - (volume K).toReal *
    ((∫ x in K, ‖x‖ ^ 2) / (volume K).toReal) = 0
  field_simp [ENNReal.toReal_ne_zero.mpr ⟨hK0, hKtop⟩]
  ring

private theorem explicitDyadicRadiusFactor_lt_thirtyTwoProtectedLog
    (q : VolumeParams) :
    1 + Real.sqrt 2 + 4 * Real.sqrt 3 *
        explicitDyadicTailIndex (q.eps / 8) <
      32 * protectedLog (8 / q.eps) := by
  let L := protectedLog (8 / q.eps)
  have heta0 : 0 < q.eps / 8 := div_pos q.heps.1 (by norm_num)
  have heta1 : q.eps / 8 < 1 := by linarith [q.heps.2]
  have hindex := explicitDyadicTailIndex_lt_logb_add_one heta0 heta1
  have harg : 1 / (q.eps / 8) = 8 / q.eps := by
    field_simp [q.heps.1.ne']
  rw [harg] at hindex
  have hx : 0 < Real.log (8 / q.eps) := by
    apply Real.log_pos
    rw [lt_div_iff₀ q.heps.1]
    linarith [q.heps.2]
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hbase : Real.logb 2 (8 / q.eps) < 2 * L := by
    unfold Real.logb
    have hlog_le : Real.log (8 / q.eps) ≤ L := le_max_right _ _
    have hdiv : Real.log (8 / q.eps) / Real.log 2 <
        Real.log (8 / q.eps) / (1 / 2) := by
      exact div_lt_div_of_pos_left hx (by norm_num) hlog2
    exact hdiv.trans_le (by dsimp [L]; nlinarith)
  have hN : (explicitDyadicTailIndex (q.eps / 8) : ℝ) < 2 * L + 1 :=
    hindex.trans (by linarith)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hL : 1 ≤ L := le_max_left _ _
  dsimp [L] at *
  nlinarith [mul_nonneg (show 0 ≤ (explicitDyadicTailIndex (q.eps / 8) : ℝ) by positivity)
    (sub_nonneg.mpr hsqrt3)]

private theorem explicitDyadicMomentRadius_le_terminalRadius
    (q : VolumeParams) (I : VolumeInput q.n) (hrounded : WellRounded q I) :
    explicitDyadicMomentRadius (uniformSecondMoment I) (q.eps / 8) ≤
      Real.sqrt (terminalVariance q) := by
  let M := uniformSecondMoment I
  let L := protectedLog (8 / q.eps)
  let F := 1 + Real.sqrt 2 + 4 * Real.sqrt 3 *
    explicitDyadicTailIndex (q.eps / 8)
  have hM : 0 ≤ M := (uniformSecondMoment_pos q I).le
  have hRn : 0 ≤ q.roundness * (q.n : ℝ) :=
    mul_nonneg q.roundness_pos.le (Nat.cast_nonneg _)
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hMF : Real.sqrt M * F ≤ Real.sqrt (q.roundness * (q.n : ℝ)) * (32 * L) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hrounded)
    · exact (explicitDyadicRadiusFactor_lt_thirtyTwoProtectedLog q).le
    · exact hF
    · positivity
  have hsq : (Real.sqrt (q.roundness * (q.n : ℝ)) * (32 * L)) ^ 2 ≤
      terminalVariance q := by
    have hterminal :
        1024 * q.roundness * (q.n : ℝ) * L ^ 2 ≤ terminalVariance q := by
      unfold terminalVariance volumeTerminalScale
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc
      (Real.sqrt (q.roundness * (q.n : ℝ)) * (32 * L)) ^ 2 =
          1024 * q.roundness * (q.n : ℝ) * L ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hRn]
        ring
      _ ≤ terminalVariance q := hterminal
  unfold explicitDyadicMomentRadius
  change Real.sqrt M * F ≤ Real.sqrt (terminalVariance q)
  have hbig0 : 0 ≤ Real.sqrt (q.roundness * (q.n : ℝ)) * (32 * L) := by
    have hL : 0 ≤ L := le_trans zero_le_one (le_max_left _ _)
    positivity
  exact hMF.trans ((Real.le_sqrt hbig0
    (terminalVariance_pos' q).le).2 hsq)

/-- The well-roundedness promise implies the exact radial-volume input used by
the Figure-1 accuracy proof. -/
theorem figureOneRadialTruncationBound
    (q : VolumeParams) (I : VolumeInput q.n) (hrounded : WellRounded q I) :
    FigureOneRadialTruncationBound q I := by
  let K : Set (AmbientSpace q.n) := I.body
  let eta : ℝ := q.eps / 8
  let rdyadic := explicitDyadicMomentRadius (uniformSecondMoment I) eta
  let rterminal := Real.sqrt (terminalVariance q)
  have heta0 : 0 < eta := by dsimp [eta]; exact div_pos q.heps.1 (by norm_num)
  have heta1 : eta < 1 := by dsimp [eta]; linarith [q.heps.2]
  have htailDyadic :
      (volume (K \ closedBall 0 rdyadic)).toReal ≤ eta * (volume K).toReal := by
    exact volume_sdiff_explicitDyadicMomentRadius_toReal_le
      (le_trans (by norm_num) q.dim_ok)
      I.body.convex I.body.isClosed I.body.isCompact.isBounded
      (uniformSecondMoment_pos q I) heta0 heta1 (centered_uniformSecondMoment q I)
  have hradius : rdyadic ≤ rterminal := by
    simpa [rdyadic, rterminal, eta] using
      explicitDyadicMomentRadius_le_terminalRadius q I hrounded
  have htailSubset : K \ closedBall 0 rterminal ⊆ K \ closedBall 0 rdyadic := by
    intro x hx
    exact ⟨hx.1, fun hsmall => hx.2 (closedBall_subset_closedBall hradius hsmall)⟩
  have htail :
      (volume (K \ closedBall 0 rterminal)).toReal ≤ eta * (volume K).toReal :=
    by
      have hdyTop : volume (K \ closedBall 0 rdyadic) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono diff_subset)
          I.body.isCompact.measure_lt_top)
      exact (ENNReal.toReal_mono hdyTop (measure_mono htailSubset)).trans htailDyadic
  have haddENN : volume (K ∩ closedBall 0 rterminal) +
      volume (K \ closedBall 0 rterminal) = volume K :=
    measure_inter_add_diff K measurableSet_closedBall
  have htruncTop : volume (K ∩ closedBall 0 rterminal) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) I.body.isCompact.measure_lt_top)
  have htailTop : volume (K \ closedBall 0 rterminal) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono diff_subset) I.body.isCompact.measure_lt_top)
  have hadd : (volume (K ∩ closedBall 0 rterminal)).toReal +
      (volume (K \ closedBall 0 rterminal)).toReal = (volume K).toReal := by
    rw [← ENNReal.toReal_add htruncTop htailTop, haddENN]
  unfold FigureOneRadialTruncationBound RelativeApprox Arlib.relErr
  change (1 - eta) * (volume K).toReal ≤
      (volume (K ∩ closedBall 0 rterminal)).toReal ∧
    (volume (K ∩ closedBall 0 rterminal)).toReal ≤
      (1 + eta) * (volume K).toReal
  constructor
  · nlinarith
  · have hmono : (volume (K ∩ closedBall 0 rterminal)).toReal ≤ (volume K).toReal :=
      ENNReal.toReal_mono I.body.isCompact.measure_lt_top.ne (measure_mono inter_subset_left)
    have hvol0 : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
    nlinarith

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.figureOneRadialTruncationBound
