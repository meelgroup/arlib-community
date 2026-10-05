/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisGaussian
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# The executable CV18 proposal is the standard lazy Metropolis proposal

The executable Figure-1 walk was defined independently of the abstract
continuous Markov-chain library.  This file removes two representation
differences needed before the abstract mixing theorem can be applied:

* normalizing Lebesgue measure on a closed proposal ball gives the same
  probability measure as normalizing it on the open ball used by
  `Arlib.MarkovChains.metropolisGaussian`; the boundary sphere is null;
* the executable acceptance probability is exactly one half of
  `Arlib.MarkovChains.metropolisAccept`, including the indicator of the fixed
  truncated body.

The remaining bridge is trajectory-level: relate a fixed number of these raw
lazy steps to sufficiently many proper speedy steps and compose the resulting
per-sample errors through the dependent cooling schedule.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib.MarkovChains
open scoped ENNReal

/-- Normalizing the implementation's closed proposal ball is identical to
normalizing the abstract chain's open ball. -/
theorem centeredClosedBallMeasure_eq_openBall {n : ℕ} [NeZero n]
    {radius : ℝ} (hradius : 0 < radius) :
    centeredClosedBallMeasure n radius =
      (volume (Metric.ball (0 : AmbientSpace n) radius))⁻¹ •
        volume.restrict (Metric.ball 0 radius) := by
  let finite : FiniteMeasure (AmbientSpace n) :=
    centeredClosedBallFiniteMeasure n radius
  have hfinite : finite ≠ 0 := by
    intro hzero
    have huniv : (finite : Measure (AmbientSpace n)) Set.univ = 0 := by
      rw [hzero]
      rfl
    change volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius)
      Set.univ = 0 at huniv
    rw [Measure.restrict_apply_univ] at huniv
    exact (Metric.measure_closedBall_pos volume (0 : AmbientSpace n) hradius).ne' huniv
  have hae : Metric.closedBall (0 : AmbientSpace n) radius =ᵐ[volume]
      Metric.ball 0 radius := by
    apply (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
  unfold centeredClosedBallMeasure
  change (finite.normalize : Measure (AmbientSpace n)) = _
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite]
  have hmass : (finite.mass : ENNReal) =
      volume (Metric.ball (0 : AmbientSpace n) radius) := by
    rw [FiniteMeasure.ennreal_mass]
    change volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius) Set.univ = _
    rw [Measure.restrict_apply_univ,
      Measure.addHaar_closedBall_eq_addHaar_ball]
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_inv
    (finite.mass_nonzero_iff.mpr hfinite), hmass]
  exact congrArg
    (fun mu : Measure (AmbientSpace n) =>
      (volume (Metric.ball (0 : AmbientSpace n) radius))⁻¹ • mu)
    (Measure.restrict_congr_set hae)

/-- After translation, the executable proposal measure is the usual uniform
measure on the open ball about the current state. -/
theorem uniformClosedBallMeasure_eq_openBall {n : ℕ} [NeZero n]
    (current : AmbientSpace n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure n current radius =
      (volume (Metric.ball current radius))⁻¹ •
        volume.restrict (Metric.ball current radius) := by
  have hvolume : volume (Metric.ball (0 : AmbientSpace n) radius) =
      volume (Metric.ball current radius) :=
    (volume_ball_eq current radius).symm
  have hpre : (fun z : AmbientSpace n => current + z) ⁻¹'
      Metric.ball current radius = Metric.ball 0 radius := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have hrestrict := Measure.restrict_map
    (μ := (volume : Measure (AmbientSpace n)))
    (f := fun z : AmbientSpace n => current + z)
    (s := Metric.ball current radius)
    (by fun_prop) measurableSet_ball
  rw [hpre] at hrestrict
  unfold uniformClosedBallMeasure
  rw [centeredClosedBallMeasure_eq_openBall hradius, Measure.map_smul,
    hvolume]
  exact congrArg
    (fun mu : Measure (AmbientSpace n) =>
      (volume (Metric.ball current radius))⁻¹ • mu)
    (hrestrict.symm.trans (by rw [map_add_left_eq_self]))

/-- The program's body-filtered acceptance coefficient is exactly one half
of the standard Metropolis coefficient.  Thus laziness is represented by the
coin threshold in the executable and by `lazy` in the abstract kernel. -/
theorem ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    ENNReal.ofReal
        (truncatedMetropolisAcceptance q I sigma2 current proposal) =
      (2 : ENNReal)⁻¹ *
        (truncatedBody q I).indicator
          (fun y => metropolisAccept sigma2 current y) proposal := by
  by_cases hp : proposal ∈ truncatedBody q I
  · rw [Set.indicator_of_mem hp]
    unfold truncatedMetropolisAcceptance
    rw [Set.indicator_of_mem hp]
    rw [metropolisAccept_eq_ofReal]
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    unfold gaussianWeightReal
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    rw [div_eq_mul_inv, mul_comm]
  · rw [Set.indicator_of_notMem hp]
    unfold truncatedMetropolisAcceptance
    rw [Set.indicator_of_notMem hp]
    simp

/-- The exact one-step semantic bridge: at every positive phase variance, the
kernel executed by Figure 1 is the lazy standard Gaussian Metropolis kernel
on the fixed truncated body. -/
theorem truncatedMetropolisKernel_eq_lazy_metropolisGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedMetropolisKernel q I oracle sigma2 =
      lazy (metropolisGaussian (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2) := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  let r := figureOneProposalRadius q sigma2
  have hr : 0 < r := figureOneProposalRadius_pos q hsigma2
  ext current B hB
  rw [truncatedMetropolisKernel_apply q I oracle sigma2 current hB,
    lazy_apply_set, metropolisGaussian_apply_set] <;> try exact hB
  let a : AmbientSpace q.n → ENNReal := fun y =>
    (truncatedBody q I).indicator (fun z => metropolisAccept sigma2 current z) y
  let b : ENNReal := B.indicator 1 current
  have ha : Measurable a := by
    dsimp [a]
    exact ((continuous_metropolisAccept sigma2).measurable.comp
      (measurable_const.prodMk measurable_id)).indicator
        (truncatedBody_measurable q I)
  have ha1 : ∀ y, a y ≤ 1 := by
    intro y
    dsimp [a]
    by_cases hy : y ∈ truncatedBody q I
    · rw [Set.indicator_of_mem hy]
      exact metropolisAccept_le_one sigma2 current y
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have hBind : Measurable (B.indicator (1 : AmbientSpace q.n → ENNReal)) :=
    measurable_const.indicator hB
  have hF : Measurable fun y : AmbientSpace q.n =>
      (2 : ENNReal)⁻¹ * a y * B.indicator 1 y +
        (1 - (2 : ENNReal)⁻¹ * a y) * b := by
    fun_prop
  have hmap := lintegral_map hF
    (by fun_prop : Measurable fun z : AmbientSpace q.n => current + z)
    (μ := centeredClosedBallMeasure q.n r)
  have hreject : ∀ y : AmbientSpace q.n,
      ENNReal.ofReal
          (1 - truncatedMetropolisAcceptance q I sigma2 current y) =
        1 - (2 : ENNReal)⁻¹ * a y := by
    intro y
    rw [ENNReal.ofReal_sub 1
      (truncatedMetropolisAcceptance_nonneg q I sigma2 current y),
      ENNReal.ofReal_one,
      ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept]
  simp_rw [ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept,
    hreject]
  change (∫⁻ z, (2 : ENNReal)⁻¹ * a (current + z) *
      B.indicator 1 (current + z) +
      (1 - (2 : ENNReal)⁻¹ * a (current + z)) * b
      ∂centeredClosedBallMeasure q.n r) = _
  rw [← hmap]
  change (∫⁻ y, (2 : ENNReal)⁻¹ * a y * B.indicator 1 y +
      (1 - (2 : ENNReal)⁻¹ * a y) * b
      ∂uniformClosedBallMeasure q.n current r) = _
  let ν : Measure (AmbientSpace q.n) := uniformClosedBallMeasure q.n current r
  have hν : ν = (volume (Metric.ball current r))⁻¹ •
      volume.restrict (Metric.ball current r) :=
    uniformClosedBallMeasure_eq_openBall current hr
  have haBall : (∫⁻ y, a y ∂ν) =
      metropolisMove (truncatedBody q I) r sigma2 current := by
    rw [hν, lintegral_smul_measure]
    unfold metropolisMove
    rw [ENNReal.div_eq_inv_mul]
    congr 1
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_indicator (truncatedBody_measurable q I)]
    apply lintegral_congr
    intro y
    dsimp [a]
    unfold metropolisDensity
    by_cases hb : y ∈ Metric.ball current r <;>
      by_cases hK : y ∈ truncatedBody q I <;>
      simp [hb, hK]
  have haB : (∫⁻ y, a y * B.indicator 1 y ∂ν) =
      (volume (Metric.ball current r))⁻¹ *
        ∫⁻ y in B ∩ truncatedBody q I,
          metropolisDensity sigma2 r current y := by
    rw [hν, lintegral_smul_measure]
    congr 1
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_indicator (hB.inter (truncatedBody_measurable q I))]
    apply lintegral_congr
    intro y
    dsimp [a]
    unfold metropolisDensity
    by_cases hb : y ∈ Metric.ball current r <;>
      by_cases hK : y ∈ truncatedBody q I <;>
      by_cases hE : y ∈ B <;>
      simp [hb, hK, hE]
  change (∫⁻ y, (2 : ENNReal)⁻¹ * a y * B.indicator 1 y +
      (1 - (2 : ENNReal)⁻¹ * a y) * b ∂ν) = _
  have hhalfA : (∫⁻ y, (2 : ENNReal)⁻¹ * a y ∂ν) =
      (2 : ENNReal)⁻¹ * metropolisMove
        (truncatedBody q I) r sigma2 current := by
    rw [lintegral_const_mul' _ _ (by norm_num), haBall]
  have hhalfAle : ∀ y, (2 : ENNReal)⁻¹ * a y ≤ 1 := by
    intro y
    calc
      (2 : ENNReal)⁻¹ * a y ≤ (2 : ENNReal)⁻¹ * 1 :=
        mul_le_mul le_rfl (ha1 y) bot_le bot_le
      _ ≤ 1 := by norm_num
  have hhalfAfin : (∫⁻ y, (2 : ENNReal)⁻¹ * a y ∂ν) ≠ ∞ := by
    rw [hhalfA]
    exact ENNReal.mul_ne_top (by norm_num) (by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top
        (metropolisMove_le_one (truncatedBody q I) r sigma2 current))
  have hsub : (∫⁻ y, 1 - (2 : ENNReal)⁻¹ * a y ∂ν) =
      1 - (2 : ENNReal)⁻¹ * metropolisMove
        (truncatedBody q I) r sigma2 current := by
    rw [lintegral_sub (ha.const_mul _) hhalfAfin
      (Filter.Eventually.of_forall hhalfAle), lintegral_one, measure_univ,
      hhalfA]
  rw [lintegral_add_left]
  · have hfirst : (∫⁻ y, (2 : ENNReal)⁻¹ * a y * B.indicator 1 y ∂ν) =
        (2 : ENNReal)⁻¹ * ((volume (Metric.ball current r))⁻¹ *
          ∫⁻ y in B ∩ truncatedBody q I,
            metropolisDensity sigma2 r current y) := by
        calc
          _ = ∫⁻ y, (2 : ENNReal)⁻¹ *
              (a y * B.indicator 1 y) ∂ν := by
                apply lintegral_congr
                intro y
                ring
          _ = (2 : ENNReal)⁻¹ *
              ∫⁻ y, a y * B.indicator 1 y ∂ν :=
                lintegral_const_mul' _ _ (by norm_num)
          _ = _ := by rw [haB]
    have hsecond : (∫⁻ y, (1 - (2 : ENNReal)⁻¹ * a y) * b ∂ν) =
        (1 - (2 : ENNReal)⁻¹ * metropolisMove
          (truncatedBody q I) r sigma2 current) * b := by
      calc
        _ = (∫⁻ y, 1 - (2 : ENNReal)⁻¹ * a y ∂ν) * b :=
          lintegral_mul_const b (measurable_const.sub (ha.const_mul _))
        _ = _ := by rw [hsub]
    rw [hfirst, hsecond]
    dsimp [r]
    dsimp [b]
    by_cases hcur : current ∈ B
    · simp [Set.indicator_of_mem hcur]
      let m : ENNReal := metropolisMove (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2 current
      have hm : m ≤ 1 := metropolisMove_le_one (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2 current
      have hhm : (2 : ENNReal)⁻¹ * m ≤ 1 := by
        calc
          (2 : ENNReal)⁻¹ * m ≤ (2 : ENNReal)⁻¹ * 1 :=
            mul_le_mul le_rfl hm bot_le bot_le
          _ ≤ 1 := by norm_num
      have hleftFin : 1 - (2 : ENNReal)⁻¹ * m ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
      have hprodFin : (2 : ENNReal)⁻¹ * (1 - m) ≠ ∞ :=
        ENNReal.mul_ne_top (by norm_num)
          (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      have hrightFin : (2 : ENNReal)⁻¹ * (1 - m) +
          (2 : ENNReal)⁻¹ ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨hprodFin, by norm_num⟩
      have hid : 1 - (2 : ENNReal)⁻¹ * m =
          (2 : ENNReal)⁻¹ * (1 - m) + (2 : ENNReal)⁻¹ := by
        apply (ENNReal.toReal_eq_toReal_iff' hleftFin hrightFin).mp
        rw [ENNReal.toReal_sub_of_le hhm (by simp),
          ENNReal.toReal_add hprodFin (by norm_num),
          ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_sub_of_le hm (by simp)]
        norm_num
        ring
      change (2 : ENNReal)⁻¹ * _ + (1 - (2 : ENNReal)⁻¹ * m) = _
      rw [hid]
      ring
    · simp [Set.indicator_of_notMem hcur]
  · exact ((ha.const_mul _).mul hBind)

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.centeredClosedBallMeasure_eq_openBall
#print axioms ArlibCommunity.Algorithms.CV18.uniformClosedBallMeasure_eq_openBall
#print axioms ArlibCommunity.Algorithms.CV18.ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept
#print axioms ArlibCommunity.Algorithms.CV18.truncatedMetropolisKernel_eq_lazy_metropolisGaussian
