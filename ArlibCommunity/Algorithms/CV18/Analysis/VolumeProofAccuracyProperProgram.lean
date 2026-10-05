/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperCollect
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing

/-! # Executable proper proposals on the CV18 accuracy phase body -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open Arlib.MarkovChains
open scoped ENNReal

/-- Body-filtered acceptance coefficient for a generic lazy Metropolis
proposal.  This is shared by the executable phase step and the analytic
kernel bridge below. -/
noncomputable def radialLazyMetropolisAcceptance {n : ℕ}
    (K : Set (AmbientSpace n)) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) : ℝ :=
  K.indicator (fun y =>
    lazyGaussianMetropolisAcceptance sigma2 current y) proposal

theorem radialLazyMetropolisAcceptance_nonneg {n : ℕ}
    (K : Set (AmbientSpace n)) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) :
    0 ≤ radialLazyMetropolisAcceptance K sigma2 current proposal := by
  unfold radialLazyMetropolisAcceptance
  by_cases hp : proposal ∈ K
  · rw [Set.indicator_of_mem hp]
    exact lazyGaussianMetropolisAcceptance_nonneg sigma2 current proposal
  · rw [Set.indicator_of_notMem hp]

theorem radialLazyMetropolisAcceptance_le_one {n : ℕ}
    (K : Set (AmbientSpace n)) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) :
    radialLazyMetropolisAcceptance K sigma2 current proposal ≤ 1 := by
  unfold radialLazyMetropolisAcceptance
  by_cases hp : proposal ∈ K
  · rw [Set.indicator_of_mem hp]
    exact lazyGaussianMetropolisAcceptance_le_one sigma2 current proposal
  · rw [Set.indicator_of_notMem hp]
    norm_num

theorem measurable_radialLazyMetropolisAcceptance {n : ℕ}
    {K : Set (AmbientSpace n)} (hK : MeasurableSet K) (sigma2 : ℝ) :
    Measurable fun p : AmbientSpace n × AmbientSpace n =>
      radialLazyMetropolisAcceptance K sigma2 p.1 p.2 := by
  unfold radialLazyMetropolisAcceptance
  apply Measurable.indicator
  · unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  · exact hK.preimage measurable_snd

theorem ofReal_radialLazyMetropolisAcceptance_eq_half_metropolisAccept
    {n : ℕ} (K : Set (AmbientSpace n)) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) :
    ENNReal.ofReal (radialLazyMetropolisAcceptance K sigma2 current proposal) =
      (2 : ENNReal)⁻¹ *
        K.indicator (fun y => metropolisAccept sigma2 current y) proposal := by
  by_cases hp : proposal ∈ K
  · rw [Set.indicator_of_mem hp]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_mem hp, metropolisAccept_eq_ofReal]
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
      gaussianWeightReal
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    rw [div_eq_mul_inv, mul_comm]
  · rw [Set.indicator_of_notMem hp]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_notMem hp]
    simp

/-- Direct proposal-mixture law of a lazy Metropolis step on a measurable
body. -/
noncomputable def radialLazyMetropolisLaw {n : ℕ}
    (K : Set (AmbientSpace n)) (delta sigma2 : ℝ)
    (current : AmbientSpace n) : Measure (AmbientSpace n) :=
  (uniformClosedBallMeasure n current delta).bind fun proposal =>
    ENNReal.ofReal (radialLazyMetropolisAcceptance K sigma2 current proposal) •
        Measure.dirac proposal +
      ENNReal.ofReal
        (1 - radialLazyMetropolisAcceptance K sigma2 current proposal) •
        Measure.dirac current

theorem measurable_radialLazyMetropolisProposalLaw {n : ℕ}
    {K : Set (AmbientSpace n)} (hK : MeasurableSet K) (sigma2 : ℝ)
    (current : AmbientSpace n) : Measurable fun proposal : AmbientSpace n =>
    ENNReal.ofReal (radialLazyMetropolisAcceptance K sigma2 current proposal) •
        Measure.dirac proposal +
      ENNReal.ofReal
        (1 - radialLazyMetropolisAcceptance K sigma2 current proposal) •
        Measure.dirac current := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hS]
  have hacc : Measurable fun proposal : AmbientSpace n =>
      radialLazyMetropolisAcceptance K sigma2 current proposal := by
    unfold radialLazyMetropolisAcceptance
    apply Measurable.indicator
    · unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
      fun_prop
    · exact hK
  exact ((ENNReal.measurable_ofReal.comp hacc).mul
    (measurable_one.indicator hS)).add
      ((ENNReal.measurable_ofReal.comp (measurable_const.sub hacc)).mul
        measurable_const)

set_option maxHeartbeats 800000 in
/-- The direct executable-style mixture is exactly the standard lazy
Metropolis kernel, for every measurable body. -/
theorem radialLazyMetropolisLaw_eq_lazy_metropolisGaussian
    {n : ℕ} [NeZero n] {K : Set (AmbientSpace n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (sigma2 : ℝ)
    (current : AmbientSpace n) :
    radialLazyMetropolisLaw K delta sigma2 current =
      lazy (metropolisGaussian K delta sigma2) current := by
  ext B hB
  rw [lazy_apply_set, metropolisGaussian_apply_set] <;> try exact hB
  let a : AmbientSpace n → ENNReal := fun y =>
    K.indicator (fun z => metropolisAccept sigma2 current z) y
  let b : ENNReal := B.indicator 1 current
  have ha : Measurable a := by
    dsimp [a]
    exact ((continuous_metropolisAccept sigma2).measurable.comp
      (measurable_const.prodMk measurable_id)).indicator hK
  have ha1 : ∀ y, a y ≤ 1 := by
    intro y
    dsimp [a]
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact metropolisAccept_le_one sigma2 current y
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have hBind : Measurable (B.indicator (1 : AmbientSpace n → ENNReal)) :=
    measurable_const.indicator hB
  have hinner : Measurable fun proposal : AmbientSpace n =>
      ENNReal.ofReal (radialLazyMetropolisAcceptance K sigma2 current proposal) •
          Measure.dirac proposal +
        ENNReal.ofReal
          (1 - radialLazyMetropolisAcceptance K sigma2 current proposal) •
          Measure.dirac current :=
    measurable_radialLazyMetropolisProposalLaw hK sigma2 current
  unfold radialLazyMetropolisLaw
  rw [Measure.bind_apply hB hinner.aemeasurable]
  simp_rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hB,
    smul_eq_mul]
  have hreject : ∀ y : AmbientSpace n,
      ENNReal.ofReal (1 - radialLazyMetropolisAcceptance K sigma2 current y) =
        1 - (2 : ENNReal)⁻¹ * a y := by
    intro y
    rw [ENNReal.ofReal_sub 1
      (radialLazyMetropolisAcceptance_nonneg K sigma2 current y),
      ENNReal.ofReal_one,
      ofReal_radialLazyMetropolisAcceptance_eq_half_metropolisAccept]
  simp_rw [ofReal_radialLazyMetropolisAcceptance_eq_half_metropolisAccept,
    hreject]
  let ν : Measure (AmbientSpace n) := uniformClosedBallMeasure n current delta
  have hν : ν = (volume (Metric.ball current delta))⁻¹ •
      volume.restrict (Metric.ball current delta) :=
    uniformClosedBallMeasure_eq_openBall current hdelta
  have haBall : (∫⁻ y, a y ∂ν) = metropolisMove K delta sigma2 current := by
    rw [hν, lintegral_smul_measure]
    unfold metropolisMove
    rw [ENNReal.div_eq_inv_mul]
    congr 1
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_indicator hK]
    apply lintegral_congr
    intro y
    dsimp [a]
    unfold metropolisDensity
    by_cases hb : y ∈ Metric.ball current delta <;>
      by_cases hKy : y ∈ K <;> simp [hb, hKy]
  have haB : (∫⁻ y, a y * B.indicator 1 y ∂ν) =
      (volume (Metric.ball current delta))⁻¹ *
        ∫⁻ y in B ∩ K, metropolisDensity sigma2 delta current y := by
    rw [hν, lintegral_smul_measure]
    congr 1
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_indicator (hB.inter hK)]
    apply lintegral_congr
    intro y
    dsimp [a]
    unfold metropolisDensity
    by_cases hb : y ∈ Metric.ball current delta <;>
      by_cases hKy : y ∈ K <;>
      by_cases hE : y ∈ B <;> simp [hb, hKy, hE]
  change (∫⁻ y, (2 : ENNReal)⁻¹ * a y * B.indicator 1 y +
      (1 - (2 : ENNReal)⁻¹ * a y) * b ∂ν) = _
  have hhalfA : (∫⁻ y, (2 : ENNReal)⁻¹ * a y ∂ν) =
      (2 : ENNReal)⁻¹ * metropolisMove K delta sigma2 current := by
    rw [lintegral_const_mul' _ _ (by norm_num), haBall]
  have hhalfAle : ∀ y, (2 : ENNReal)⁻¹ * a y ≤ 1 := by
    intro y
    calc
      (2 : ENNReal)⁻¹ * a y ≤ (2 : ENNReal)⁻¹ * 1 :=
        mul_le_mul le_rfl (ha1 y) bot_le bot_le
      _ ≤ 1 := by norm_num
  have hhalfAfin : (∫⁻ y, (2 : ENNReal)⁻¹ * a y ∂ν) ≠ ∞ := by
    rw [hhalfA]
    exact ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top
      ENNReal.one_ne_top (metropolisMove_le_one K delta sigma2 current))
  have hsub : (∫⁻ y, 1 - (2 : ENNReal)⁻¹ * a y ∂ν) =
      1 - (2 : ENNReal)⁻¹ * metropolisMove K delta sigma2 current := by
    rw [lintegral_sub (ha.const_mul _) hhalfAfin
      (Filter.Eventually.of_forall hhalfAle), lintegral_one, measure_univ,
      hhalfA]
  rw [lintegral_add_left]
  · have hfirst :
        (∫⁻ y, (2 : ENNReal)⁻¹ * a y * B.indicator 1 y ∂ν) =
          (2 : ENNReal)⁻¹ * ((volume (Metric.ball current delta))⁻¹ *
            ∫⁻ y in B ∩ K, metropolisDensity sigma2 delta current y) := by
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
    have hsecond :
        (∫⁻ y, (1 - (2 : ENNReal)⁻¹ * a y) * b ∂ν) =
          (1 - (2 : ENNReal)⁻¹ * metropolisMove K delta sigma2 current) * b := by
      calc
        _ = (∫⁻ y, 1 - (2 : ENNReal)⁻¹ * a y ∂ν) * b :=
          lintegral_mul_const b (measurable_const.sub (ha.const_mul _))
        _ = _ := by rw [hsub]
    rw [hfirst, hsecond]
    dsimp [b]
    by_cases hcur : current ∈ B
    · simp [Set.indicator_of_mem hcur]
      let m : ENNReal := metropolisMove K delta sigma2 current
      have hm : m ≤ 1 := metropolisMove_le_one K delta sigma2 current
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

/-- The marked proposal used by the faithful CV18 sampler.  A proper proposal
must lie in the oracle body, the fixed well-roundedness truncation, and the
accuracy-dependent phase ball used by the proved speedy-mixing theorem. -/
noncomputable def accuracyMetropolisMarkedProposalProgram (q : VolumeParams)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ accuracyPhaseRadius q sigma2 then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

/-- One lazy Metropolis proposal with the phase-proper bit retained. -/
noncomputable def accuracyMetropolisMarkedBallStep (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current (figureOneProposalRadius q sigma2))
    inferInstance fun proposal =>
      accuracyMetropolisMarkedProposalProgram q sigma2 current proposal

theorem oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (x : AmbientSpace q.n) :
    oracle.query x = true ∧
        ‖x‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖x‖ ≤ accuracyPhaseRadius q sigma2 ↔
      x ∈ accuracyPhaseTruncatedBody q I sigma2 := by
  rw [oracle.correct]
  simp only [accuracyPhaseTruncatedBody, truncatedBody, Set.mem_inter_iff,
    Metric.mem_closedBall, dist_zero_right]
  tauto

theorem accuracyMetropolisMarkedProposalProgram_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem accuracyMetropolisMarkedBallStep_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  exact accuracyMetropolisMarkedProposalProgram_queryBound
    q sigma2 current proposal

/-- The proposal probability of the executable phase membership test is the
abstract local conductance used by the proper clock. -/
theorem uniformClosedBallMeasure_accuracyPhaseTruncatedBody
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius
        (accuracyPhaseTruncatedBody q I sigma2) =
      Arlib.MarkovChains.ell (accuracyPhaseTruncatedBody q I sigma2)
        radius current := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  rw [uniformClosedBallMeasure_eq_openBall current hradius,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply
      (accuracyPhaseTruncatedBody_measurable q I sigma2),
    Arlib.MarkovChains.ell_apply, ENNReal.div_eq_inv_mul]
  congr 1
  rw [Set.inter_comm]

theorem uniformClosedBallMeasure_accuracyPhaseTruncatedBody_compl
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius
        (accuracyPhaseTruncatedBody q I sigma2)ᶜ =
      1 - Arlib.MarkovChains.ell (accuracyPhaseTruncatedBody q I sigma2)
        radius current := by
  rw [measure_compl (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (measure_ne_top _ _), measure_univ,
    uniformClosedBallMeasure_accuracyPhaseTruncatedBody
      q I sigma2 current hradius]

theorem accuracyMetropolisMarkedProposalProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).StronglyMeasurable
      oracle.query := by
  simp only [accuracyMetropolisMarkedProposalProgram,
    MembershipOracleProgram.StronglyMeasurable]
  by_cases hproper : oracle.query proposal = true ∧
      ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖proposal‖ ≤ accuracyPhaseRadius q sigma2
  · simp only [if_pos hproper, MembershipOracleProgram.runEstimate,
      MembershipOracleProgram.StronglyMeasurable]
    constructor
    · apply Measure.measurable_dirac.comp
      exact measurable_const.prodMk <|
        Measurable.ite measurableSet_Iic measurable_const measurable_const
    · exact fun _ => trivial
  · simp only [if_neg hproper, MembershipOracleProgram.runEstimate,
      MembershipOracleProgram.StronglyMeasurable]
    exact ⟨Measure.measurable_dirac.comp measurable_const, fun _ => trivial⟩

theorem accuracyMetropolisMarkedBallStep_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [accuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.StronglyMeasurable]
  let output : AmbientSpace q.n → ℝ → Bool × AmbientSpace q.n :=
    fun point coin =>
      if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖point‖ ≤ accuracyPhaseRadius q sigma2 then
        (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current point
          then point else current)
      else (false, current)
  have horacle : Measurable fun p : AmbientSpace q.n × ℝ =>
      oracle.query p.1 := oracle.measurable_query.comp measurable_fst
  have hnorm : Measurable fun p : AmbientSpace q.n × ℝ => ‖p.1‖ := by
    fun_prop
  have haccept : Measurable fun p : AmbientSpace q.n × ℝ =>
      lazyGaussianMetropolisAcceptance sigma2 current p.1 := by
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  have hterminal : MeasurableSet {p : AmbientSpace q.n × ℝ |
      ‖p.1‖ ≤ Real.sqrt (terminalVariance q)} :=
    measurableSet_le hnorm measurable_const
  have hphase : MeasurableSet {p : AmbientSpace q.n × ℝ |
      ‖p.1‖ ≤ accuracyPhaseRadius q sigma2} :=
    measurableSet_le hnorm measurable_const
  have hout : Measurable fun p : AmbientSpace q.n × ℝ => output p.1 p.2 := by
    apply Measurable.ite
    · convert ((horacle (measurableSet_singleton true)).inter hterminal).inter
          hphase using 1
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_setOf_eq]
      tauto
    · apply measurable_const.prodMk
      exact Measurable.ite (measurableSet_le measurable_snd haccept)
        measurable_fst measurable_const
    · exact measurable_const
  constructor
  · rw [show (fun point =>
        (accuracyMetropolisMarkedProposalProgram q sigma2 current point).runEstimate
          oracle.query) =
        fun point => uniformUnitIntervalMeasure.map (output point) by
      funext point
      simp only [accuracyMetropolisMarkedProposalProgram,
        MembershipOracleProgram.runEstimate]
      have hinner : (fun coin =>
          MembershipOracleProgram.runEstimate oracle.query
            (if oracle.query point = true ∧
                ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
                ‖point‖ ≤ accuracyPhaseRadius q sigma2 then
              .pure (true, if coin ≤
                lazyGaussianMetropolisAcceptance sigma2 current point
                then point else current)
            else .pure (false, current))) =
          fun coin => Measure.dirac (output point coin) := by
        funext coin
        by_cases hproper : oracle.query point = true ∧
            ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖point‖ ≤ accuracyPhaseRadius q sigma2
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
      rw [hinner]
      exact Measure.bind_dirac_eq_map uniformUnitIntervalMeasure
        (hout.comp (measurable_const.prodMk measurable_id))]
    exact measurable_measure_map_param uniformUnitIntervalMeasure hout
  · intro proposal
    exact accuracyMetropolisMarkedProposalProgram_stronglyMeasurable
      q I oracle sigma2 current proposal

/-- Forgetting the proper bit in one inner proposal gives exactly the generic
body-filtered lazy Metropolis mixture. -/
theorem map_snd_runEstimate_accuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    ((accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
      oracle.query).map Prod.snd =
      ENNReal.ofReal (radialLazyMetropolisAcceptance
          (accuracyPhaseTruncatedBody q I sigma2) sigma2 current proposal) •
        Measure.dirac proposal +
      ENNReal.ofReal (1 - radialLazyMetropolisAcceptance
          (accuracyPhaseTruncatedBody q I sigma2) sigma2 current proposal) •
        Measure.dirac current := by
  by_cases hp : proposal ∈ accuracyPhaseTruncatedBody q I sigma2
  · have heligible := (oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody
      q I oracle sigma2 proposal).mpr hp
    simp only [accuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate, heligible, true_and, if_true]
    have hpair : Measurable fun coin : ℝ =>
        (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current) :=
      measurable_const.prodMk <|
        Measurable.ite measurableSet_Iic measurable_const measurable_const
    rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hpair,
      Measure.map_map measurable_snd hpair]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_mem hp]
    exact uniformUnitInterval_map_threshold
      (lazyGaussianMetropolisAcceptance_nonneg sigma2 current proposal)
      (lazyGaussianMetropolisAcceptance_le_one sigma2 current proposal)
      proposal current
  · have hineligible : ¬ (oracle.query proposal = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖proposal‖ ≤ accuracyPhaseRadius q sigma2) := by
      rwa [oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody]
    simp only [accuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate, hineligible, if_false,
      Measure.map_dirac]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_notMem hp]
    simp

/-- The state marginal of a complete executable phase proposal is the generic
lazy Metropolis mixture on the accuracy phase body. -/
theorem map_snd_runEstimate_accuracyMetropolisMarkedBallStep_eq_radialLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    ((accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query).map Prod.snd =
      radialLazyMetropolisLaw (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 current := by
  let U := uniformClosedBallMeasure q.n current
    (figureOneProposalRadius q sigma2)
  have hproposal : AEMeasurable (fun proposal =>
      (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) U :=
    (accuracyMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable.1
  have hradial := measurable_radialLazyMetropolisProposalLaw
    (accuracyPhaseTruncatedBody_measurable q I sigma2) sigma2 current
  ext B hB
  simp only [accuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.runEstimate]
  rw [Measure.map_apply measurable_snd hB,
    Measure.bind_apply (hB.preimage measurable_snd) hproposal]
  unfold radialLazyMetropolisLaw
  rw [Measure.bind_apply hB hradial.aemeasurable]
  apply lintegral_congr
  intro proposal
  have h := congrArg (fun mu : Measure (AmbientSpace q.n) => mu B)
    (map_snd_runEstimate_accuracyMetropolisMarkedProposalProgram
      q I oracle sigma2 current proposal)
  rw [Measure.map_apply measurable_snd hB] at h
  exact h

/-- Exact state-law bridge from the faithful executable phase proposal to
the lazy analytic Metropolis kernel. -/
theorem map_snd_runEstimate_accuracyMetropolisMarkedBallStep
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    ((accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query).map Prod.snd =
      Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.metropolisGaussian
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2) current := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  rw [map_snd_runEstimate_accuracyMetropolisMarkedBallStep_eq_radialLaw]
  exact radialLazyMetropolisLaw_eq_lazy_metropolisGaussian
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (figureOneProposalRadius_pos q hsigma2) sigma2 current

/-- The improper slice of the executable phase step is exactly the local-
conductance self loop of the abstract marked kernel. -/
theorem runEstimate_accuracyMetropolisMarkedBallStep_apply_false_prod
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n)
    {t : Set (AmbientSpace q.n)} (ht : MeasurableSet t) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query
        ({false} ×ˢ t) =
      (1 - Arlib.MarkovChains.ell (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) current) * t.indicator 1 current := by
  let U := uniformClosedBallMeasure q.n current
    (figureOneProposalRadius q sigma2)
  have hset : MeasurableSet ({false} ×ˢ t) :=
    (measurableSet_singleton false).prod ht
  have hmeas : AEMeasurable (fun proposal =>
      (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) U :=
    (accuracyMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable.1
  simp only [accuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.runEstimate]
  rw [Measure.bind_apply hset hmeas]
  have hinner : ∀ proposal : AmbientSpace q.n,
      (accuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
          oracle.query ({false} ×ˢ t) =
        (accuracyPhaseTruncatedBody q I sigma2)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal := by
    intro proposal
    simp only [accuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate]
    by_cases hp : proposal ∈ accuracyPhaseTruncatedBody q I sigma2
    · simp only [(oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody
          q I oracle sigma2 proposal).mpr hp]
      rw [Measure.bind_apply hset]
      · rw [Set.indicator_of_notMem (by simpa using hp)]
        change (∫⁻ coin, Measure.dirac
            (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
              then proposal else current) ({false} ×ˢ t)
          ∂uniformUnitIntervalMeasure) = 0
        simp [Measure.dirac_apply' _ hset]
      · exact (Measure.measurable_dirac.comp <|
          measurable_const.prodMk <|
            Measurable.ite measurableSet_Iic measurable_const
              measurable_const).aemeasurable
    · have hnot : ¬ (oracle.query proposal = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ accuracyPhaseRadius q sigma2) := by
        rwa [oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody]
      simp only [hnot, if_false, MembershipOracleProgram.runEstimate]
      rw [Measure.bind_const, measure_univ, one_smul]
      change Measure.dirac (false, current) ({false} ×ˢ t) =
        (accuracyPhaseTruncatedBody q I sigma2)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal
      rw [Measure.dirac_apply' _ hset]
      by_cases hc : current ∈ t <;> simp [hp, hc]
  simp_rw [hinner]
  rw [lintegral_indicator
    (accuracyPhaseTruncatedBody_measurable q I sigma2).compl]
  rw [setLIntegral_const]
  rw [uniformClosedBallMeasure_accuracyPhaseTruncatedBody_compl
    q I sigma2 current (figureOneProposalRadius_pos q hsigma2)]
  ring

/-- The faithful executable phase proposal has exactly the abstract marked
kernel law used by the proper clock and the speedy-mixing theorems. -/
theorem runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query =
      Arlib.MarkovChains.lazyProperProposalGaussianAux
        (accuracyPhaseTruncatedBody q I sigma2)
        (accuracyPhaseTruncatedBody_measurable q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 current := by
  let mu : Measure (Bool × AmbientSpace q.n) :=
    (accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query
  let nu : Measure (Bool × AmbientSpace q.n) :=
    Arlib.MarkovChains.lazyProperProposalGaussianAux
      (accuracyPhaseTruncatedBody q I sigma2)
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2 current
  let _ : IsProbabilityMeasure mu :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      (accuracyMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current).estimateMeasurable
  let _ : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have hstate : mu.map Prod.snd = nu.map Prod.snd := by
    calc
      mu.map Prod.snd = Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.metropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2) current :=
        map_snd_runEstimate_accuracyMetropolisMarkedBallStep
          q I oracle hsigma2 current
      _ = nu.map Prod.snd :=
        (Arlib.MarkovChains.map_snd_lazyProperProposalGaussianAux_apply
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2 current).symm
  have hfalse : ∀ (t : Set (AmbientSpace q.n)), MeasurableSet t →
      mu ({false} ×ˢ t) = nu ({false} ×ˢ t) := by
    intro t ht
    rw [runEstimate_accuracyMetropolisMarkedBallStep_apply_false_prod
      q I oracle hsigma2 current ht]
    dsimp [nu]
    rw [Arlib.MarkovChains.lazyProperProposalGaussianAux_apply_set
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2 current
      ((measurableSet_singleton false).prod ht)]
    by_cases hc : current ∈ t <;> simp [hc]
  apply measure_bool_prod_ext
  intro b t ht
  cases b with
  | false => exact hfalse t ht
  | true =>
      have hpre : Prod.snd ⁻¹' t =
          ({false} ×ˢ t) ∪ ({true} ×ˢ t) := by
        ext p
        rcases p with ⟨b, x⟩
        cases b <;> simp
      have hdisj : Disjoint ({false} ×ˢ t) ({true} ×ˢ t) := by
        apply Set.disjoint_left.2
        rintro ⟨b, x⟩ hf ht'
        cases b <;> simp at hf ht'
      have hsumMu : mu ({false} ×ˢ t) + mu ({true} ×ˢ t) =
          mu.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hsumNu : nu ({false} ×ˢ t) + nu ({true} ×ˢ t) =
          nu.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hadd : mu ({false} ×ˢ t) + mu ({true} ×ˢ t) =
          nu ({false} ×ˢ t) + nu ({true} ×ˢ t) := by
        rw [hsumMu, hsumNu, hstate]
      rw [hfalse t ht] at hadd
      exact WithTop.add_left_cancel (measure_ne_top nu ({false} ×ˢ t)) hadd

/-- Homothety used by the KLS speedy-to-target rejection routine. -/
noncomputable def accuracyScaleFactor (q : VolumeParams) : ℝ :=
  1 - 1 / (2 * (q.n : ℝ))

theorem accuracyScaleFactor_pos (q : VolumeParams) :
    0 < accuracyScaleFactor q := by
  have hn : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  unfold accuracyScaleFactor
  have hle : 1 / (2 * (q.n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem accuracyScaleFactor_le_one (q : VolumeParams) :
    accuracyScaleFactor q ≤ 1 := by
  unfold accuracyScaleFactor
  exact sub_le_self 1 (by positivity)

/-- One executable KLS speedy-to-Gaussian rejection test.  The returned point
is the homothetically expanded candidate; the Boolean records acceptance. -/
noncomputable def accuracyGaussianRejectionAttempt (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else
        .pure (false, target)

theorem accuracyGaussianRejectionAttempt_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyGaussianRejectionAttempt q sigma2 current).QueryBound 1 := by
  unfold accuracyGaussianRejectionAttempt
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem accuracyGaussianRejectionAttempt_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyGaussianRejectionAttempt q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [accuracyGaussianRejectionAttempt,
    MembershipOracleProgram.StronglyMeasurable]
  let target : AmbientSpace q.n := (accuracyScaleFactor q)⁻¹ • current
  let output : ℝ → Bool × AmbientSpace q.n := fun coin =>
    if oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
        ENNReal.ofReal coin ≤ Arlib.MarkovChains.gaussianScaleAcceptance
          sigma2 (accuracyScaleFactor q) target then
      (true, target)
    else (false, target)
  have hout : Measurable output := by
    by_cases heligible : oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2
    · simp only [output, heligible.1, heligible.2.1, heligible.2.2, true_and]
      exact Measurable.ite
        (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_id)
          measurable_const)
        measurable_const measurable_const
    · have hfalse : ∀ coin : ℝ, ¬ (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ Arlib.MarkovChains.gaussianScaleAcceptance
            sigma2 (accuracyScaleFactor q) target) := by
        intro coin h
        exact heligible ⟨h.1, h.2.1, h.2.2.1⟩
      simp only [output, hfalse, if_false]
      exact measurable_const
  constructor
  · rw [show (fun coin => MembershipOracleProgram.runEstimate oracle.query
        (if oracle.query target = true ∧
            ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
            ENNReal.ofReal coin ≤ Arlib.MarkovChains.gaussianScaleAcceptance
              sigma2 (accuracyScaleFactor q) target then
          .pure (true, target) else .pure (false, target))) =
        fun coin => Measure.dirac (output coin) by
      funext coin
      by_cases h : oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ Arlib.MarkovChains.gaussianScaleAcceptance
            sigma2 (accuracyScaleFactor q) target
      · simp [h, output, MembershipOracleProgram.runEstimate]
      · simp [h, output, MembershipOracleProgram.runEstimate]]
    exact Measure.measurable_dirac.comp hout
  · intro coin
    split <;> trivial

noncomputable def accuracyGaussianRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : ENNReal :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  (accuracyPhaseTruncatedBody q I sigma2).indicator
    (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c) target

theorem accuracyGaussianRejectionAcceptance_le_one
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    accuracyGaussianRejectionAcceptance q I sigma2 current ≤ 1 := by
  unfold accuracyGaussianRejectionAcceptance
  by_cases ht : (accuracyScaleFactor q)⁻¹ • current ∈
      accuracyPhaseTruncatedBody q I sigma2
  · rw [Set.indicator_of_mem ht]
    exact Arlib.MarkovChains.gaussianScaleAcceptance_le_one hsigma2
      (accuracyScaleFactor_pos q) (accuracyScaleFactor_le_one q) _
  · rw [Set.indicator_of_notMem ht]
    exact bot_le

theorem measurable_accuracyGaussianRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (accuracyGaussianRejectionAcceptance q I sigma2) := by
  unfold accuracyGaussianRejectionAcceptance
  exact ((Arlib.MarkovChains.measurable_gaussianScaleAcceptance sigma2
      (accuracyScaleFactor q)).indicator
        (accuracyPhaseTruncatedBody_measurable q I sigma2)).comp
          ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
            (accuracyScaleFactor q)⁻¹).smul measurable_id)

noncomputable def accuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (Bool × AmbientSpace q.n) :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  let accept := accuracyGaussianRejectionAcceptance q I sigma2 current
  accept • Measure.dirac (true, target) +
    (1 - accept) • Measure.dirac (false, target)

theorem measurable_accuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (accuracyGaussianRejectionLaw q I sigma2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [accuracyGaussianRejectionLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  have htarget : Measurable fun current : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹ • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have htrue : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal)
        (true, (accuracyScaleFactor q)⁻¹ • current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk htarget)
  have hfalse : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal)
        (false, (accuracyScaleFactor q)⁻¹ • current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk htarget)
  have hacc := measurable_accuracyGaussianRejectionAcceptance q I sigma2
  exact (hacc.mul htrue).add ((measurable_const.sub hacc).mul hfalse)

theorem runEstimate_accuracyGaussianRejectionAttempt
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (accuracyGaussianRejectionAttempt q sigma2 current).runEstimate oracle.query =
      accuracyGaussianRejectionLaw q I sigma2 current := by
  let c := accuracyScaleFactor q
  let target : AmbientSpace q.n := c⁻¹ • current
  let accept := accuracyGaussianRejectionAcceptance q I sigma2 current
  have haccept : accept ≤ 1 :=
    accuracyGaussianRejectionAcceptance_le_one q I hsigma2 current
  have hacceptTop : accept ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top haccept
  have hacceptReal0 : 0 ≤ accept.toReal := ENNReal.toReal_nonneg
  have hacceptReal1 : accept.toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top haccept
  by_cases ht : target ∈ accuracyPhaseTruncatedBody q I sigma2
  · have heligible := (oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody
      q I oracle sigma2 target).mpr ht
    have hcond : ∀ coin : ℝ,
        (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) =
        (coin ≤ accept.toReal) := by
      intro coin
      have hacceptEq : accuracyGaussianRejectionAcceptance q I sigma2 current =
          Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target := by
        unfold accuracyGaussianRejectionAcceptance
        rw [Set.indicator_of_mem ht]
      rw [← hacceptEq]
      apply propext
      simpa only [heligible.1, heligible.2.1, heligible.2.2, true_and] using
        (ENNReal.ofReal_le_iff_le_toReal hacceptTop :
          ENNReal.ofReal coin ≤ accept ↔ coin ≤ accept.toReal)
    simp only [accuracyGaussianRejectionAttempt,
      MembershipOracleProgram.runEstimate]
    dsimp only [c, target] at hcond
    simp_rw [hcond]
    have hout : Measurable fun coin : ℝ =>
        if coin ≤ accept.toReal then (true, target) else (false, target) :=
      Measurable.ite measurableSet_Iic measurable_const measurable_const
    have hbind :
        (uniformUnitIntervalMeasure.bind fun value =>
          MembershipOracleProgram.runEstimate oracle.query
            (if value ≤ accept.toReal then
              MembershipOracleProgram.pure (true, target)
            else MembershipOracleProgram.pure (false, target))) =
          uniformUnitIntervalMeasure.bind fun value =>
            Measure.dirac (if value ≤ accept.toReal then
              (true, target) else (false, target)) := by
      apply Measure.bind_congr_right
      filter_upwards with value
      split <;> simp [MembershipOracleProgram.runEstimate]
    rw [hbind]
    rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hout]
    rw [uniformUnitInterval_map_threshold hacceptReal0 hacceptReal1
      (true, target) (false, target)]
    unfold accuracyGaussianRejectionLaw
    dsimp only
    rw [ENNReal.ofReal_toReal hacceptTop]
    have hcompTop : 1 - accept ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self : 1 - accept ≤ 1)
    have hcomp : ENNReal.ofReal (1 - accept.toReal) = 1 - accept := by
      rw [← ENNReal.toReal_one,
        ← ENNReal.toReal_sub_of_le haccept ENNReal.one_ne_top,
        ENNReal.ofReal_toReal hcompTop]
    rw [hcomp]
  · have hineligible : ¬ (oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2) := by
      rwa [oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody]
    have haccept0 : accept = 0 := by
      unfold accept accuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem ht]
    simp only [accuracyGaussianRejectionAttempt,
      MembershipOracleProgram.runEstimate]
    have hfalse : ∀ coin : ℝ,
        ¬ (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) := by
      intro coin h
      exact hineligible ⟨h.1, h.2.1, h.2.2.1⟩
    dsimp only [c, target] at hfalse
    simp_rw [hfalse, if_false]
    simp only [MembershipOracleProgram.runEstimate]
    rw [Measure.bind_const, measure_univ, one_smul]
    unfold accuracyGaussianRejectionLaw
    dsimp only
    rw [show accuracyGaussianRejectionAcceptance q I sigma2 current = 0 from haccept0]
    simp

theorem accuracyGaussianRejectionLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    IsProbabilityMeasure (accuracyGaussianRejectionLaw q I sigma2 current) := by
  constructor
  simp only [accuracyGaussianRejectionLaw, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le]
  exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2 current

noncomputable def accuracyGaussianRejectionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Kernel (AmbientSpace q.n) (Bool × AmbientSpace q.n) :=
  ⟨accuracyGaussianRejectionLaw q I sigma2,
    measurable_accuracyGaussianRejectionLaw q I sigma2⟩

instance accuracyGaussianRejectionKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) [Fact (0 < sigma2)] :
    IsMarkovKernel (accuracyGaussianRejectionKernel q I sigma2) :=
  ⟨accuracyGaussianRejectionLaw_isProbabilityMeasure
    q I (Fact.out : 0 < sigma2)⟩

/-- Globally capped faithful phase collector.  After each block of proper
steps it performs the two KLS rejection tests, records the transformed target
sample on success, and retains the underlying speedy endpoint as the warm
state for the next block.  Every oracle query, including rejection tests,
consumes the one shared `rawCap`. -/
noncomputable def cappedAccuracyGaussianCollectWeightsAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, _, 0, total, current => .pure (some (total, current))
  | 0, _, _ + 1, _, _ => .pure none
  | rawCap + 1, 0, samples + 1, total, current =>
      (accuracyGaussianRejectionAttempt q sigma2 current).bind fun result =>
          if result.1 then
            cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
              rawCap properStride samples (total + weight result.2) current
          else
            cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
              rawCap properStride (samples + 1) total current
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (accuracyMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        if result.1 then
          cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
            rawCap remainingProper (samples + 1) total result.2
        else
          cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
            rawCap (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedAccuracyGaussianCollectWeights (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
    rawCap properStride samples 0 current

/-- Measure-level counterpart of the faithful collector, separating the
marked proper proposal kernel `Q` from the speedy-to-target rejection kernel
`R`. -/
noncomputable def cappedAccuracyGaussianCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (Q R : Kernel S (Bool × S)) (f : S → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → S → Measure (Option (ℝ × S))
  | _, _, 0, total, current => Measure.dirac (some (total, current))
  | 0, _, _ + 1, _, _ => Measure.dirac none
  | rawCap + 1, 0, samples + 1, total, current =>
      (R current).bind fun result =>
        if result.1 then
          cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
            properStride samples (total + f result.2) current
        else
          cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
            properStride (samples + 1) total current
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (Q current).bind fun result =>
        if result.1 then
          cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
            remainingProper (samples + 1) total result.2
        else
          cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
            (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedAccuracyGaussianCollectLaw
    {S : Type*} [MeasurableSpace S]
    (Q R : Kernel S (Bool × S)) (f : S → ℝ)
    (rawCap properStride samples : ℕ) (current : S) :
    Measure (Option (ℝ × S)) :=
  cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap properStride
    samples 0 current

theorem cappedAccuracyGaussianCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (Q R : Kernel S (Bool × S)) [IsMarkovKernel Q] [IsMarkovKernel R]
    {f : S → ℝ} (hf : Measurable f) (properStride : ℕ) :
    ∀ rawCap remainingProper samples,
      Measurable (fun p : ℝ × S =>
        cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
          remainingProper samples p.1 p.2) ∧
      ∀ total current, IsProbabilityMeasure
        (cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
          remainingProper samples total current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      cases samples with
      | zero =>
          simp only [cappedAccuracyGaussianCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            infer_instance
      | succ samples =>
          simp only [cappedAccuracyGaussianCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp measurable_const
          · intro total current
            infer_instance
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          simp only [cappedAccuracyGaussianCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            infer_instance
      | succ samples =>
          cases remainingProper with
          | zero =>
              let tail : (ℝ × S) → (Bool × S) →
                  Measure (Option (ℝ × S)) := fun state result =>
                if result.1 then
                  cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
                    properStride samples (state.1 + f result.2) state.2
                else
                  cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
                    properStride (samples + 1) state.1 state.2
              have htail : Measurable fun p : (ℝ × S) × (Bool × S) =>
                  tail p.1 p.2 := by
                dsimp only [tail]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (ih properStride samples).1.comp <|
                    ((measurable_fst.comp measurable_fst).add
                      (hf.comp (measurable_snd.comp measurable_snd))).prodMk
                        (measurable_snd.comp measurable_fst)
                · exact (ih properStride (samples + 1)).1.comp <|
                    (measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp measurable_fst)
              have htailProb : ∀ state result,
                  IsProbabilityMeasure (tail state result) := by
                intro state result
                dsimp only [tail]
                split_ifs
                · exact (ih properStride samples).2 _ _
                · exact (ih properStride (samples + 1)).2 _ _
              simp only [cappedAccuracyGaussianCollectLawAux]
              constructor
              · change Measurable fun state : ℝ × S =>
                  (R state.2).bind (tail state)
                exact measurable_measure_bind_param_variable
                  (R.measurable.comp measurable_snd)
                  (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
                  htail
              · intro total current
                change IsProbabilityMeasure ((R current).bind (tail (total, current)))
                exact MeasureTheory.isProbabilityMeasure_bind
                  (htail.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable <|
                  ae_of_all _ (htailProb (total, current))
          | succ remainingProper =>
              let tail : (ℝ × S) → (Bool × S) →
                  Measure (Option (ℝ × S)) := fun state result =>
                if result.1 then
                  cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
                    remainingProper (samples + 1) state.1 result.2
                else
                  cappedAccuracyGaussianCollectLawAux Q R f properStride rawCap
                    (remainingProper + 1) (samples + 1) state.1 result.2
              have htail : Measurable fun p : (ℝ × S) × (Bool × S) =>
                  tail p.1 p.2 := by
                dsimp only [tail]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (ih remainingProper (samples + 1)).1.comp <|
                    (measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp measurable_snd)
                · exact (ih (remainingProper + 1) (samples + 1)).1.comp <|
                    (measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp measurable_snd)
              have htailProb : ∀ state result,
                  IsProbabilityMeasure (tail state result) := by
                intro state result
                dsimp only [tail]
                split_ifs
                · exact (ih remainingProper (samples + 1)).2 _ _
                · exact (ih (remainingProper + 1) (samples + 1)).2 _ _
              simp only [cappedAccuracyGaussianCollectLawAux]
              constructor
              · change Measurable fun state : ℝ × S =>
                  (Q state.2).bind (tail state)
                exact measurable_measure_bind_param_variable
                  (Q.measurable.comp measurable_snd)
                  (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
                  htail
              · intro total current
                change IsProbabilityMeasure ((Q current).bind (tail (total, current)))
                exact MeasureTheory.isProbabilityMeasure_bind
                  (htail.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable <|
                  ae_of_all _ (htailProb (total, current))

theorem cappedAccuracyGaussianCollectWeightsAux_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper samples,
    (Measurable fun state : ℝ × AmbientSpace q.n =>
      (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples state.1 state.2).runEstimate oracle.query) ∧
    (∀ total current,
      (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).StronglyMeasurable oracle.query) ∧
    (∀ total current,
      (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).runEstimate oracle.query =
      cappedAccuracyGaussianCollectLawAux
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyGaussianRejectionKernel q I sigma2) weight properStride
        rawCap remainingProper samples total current) := by
  let _ : Fact (0 < sigma2) := ⟨hsigma2⟩
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
    (accuracyPhaseTruncatedBody q I sigma2)
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let R := accuracyGaussianRejectionKernel q I sigma2
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedAccuracyGaussianCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedAccuracyGaussianCollectLawAux]
      | succ samples =>
          constructor
          · simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp measurable_const
          constructor
          · intro total current
            rw [cappedAccuracyGaussianCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedAccuracyGaussianCollectLawAux]
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          constructor
          · intro total current
            rw [cappedAccuracyGaussianCollectWeightsAux]
            trivial
          · intro total current
            simp only [cappedAccuracyGaussianCollectWeightsAux,
              MembershipOracleProgram.runEstimate,
              cappedAccuracyGaussianCollectLawAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              let next (total : ℝ) (current : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n → MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap properStride samples
                    (total + weight result.2) current
                else
                  cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap properStride (samples + 1) total current
              let nextLaw (total : ℝ) (current : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    rawCap properStride samples (total + weight result.2) current
                else
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    rawCap properStride (samples + 1) total current
              have hnextStrong : ∀ total current result,
                  (next total current result).StronglyMeasurable oracle.query := by
                intro total current
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact (ih properStride (samples + 1)).2.1 _ _
                | true => exact (ih properStride samples).2.1 _ _
              have hnextEq : ∀ total current result,
                  (next total current result).runEstimate oracle.query =
                    nextLaw total current result := by
                intro total current
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact (ih properStride (samples + 1)).2.2 _ _
                | true => exact (ih properStride samples).2.2 _ _
              have hnextLawMeasurable : ∀ total current,
                  Measurable (nextLaw total current) := by
                intro total current
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                    Q R hweight properStride rawCap properStride samples).1.comp <|
                      ((measurable_const.add
                        (hweight.comp measurable_snd)).prodMk measurable_const)
                · exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                    Q R hweight properStride rawCap properStride
                      (samples + 1)).1.comp <|
                        measurable_const.prodMk measurable_const
              have hnextRun : ∀ total current, Measurable fun result =>
                  (next total current result).runEstimate oracle.query := by
                intro total current
                rw [show (fun result =>
                    (next total current result).runEstimate oracle.query) =
                    nextLaw total current by
                  funext result
                  exact hnextEq total current result]
                exact hnextLawMeasurable total current
              have hsemantic : ∀ total current,
                  (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride (rawCap + 1) 0 (samples + 1)
                    total current).runEstimate oracle.query =
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    (rawCap + 1) 0 (samples + 1) total current := by
                intro total current
                simp only [cappedAccuracyGaussianCollectWeightsAux]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total current)
                  (accuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 current)
                  (hnextStrong total current) (hnextRun total current)]
                rw [runEstimate_accuracyGaussianRejectionAttempt
                  q I oracle hsigma2 current]
                simp_rw [hnextEq total current]
                change (R current).bind (nextLaw total current) = _
                rw [cappedAccuracyGaussianCollectLawAux]
              constructor
              · rw [show (fun state : ℝ × AmbientSpace q.n =>
                    (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                      properStride (rawCap + 1) 0 (samples + 1)
                      state.1 state.2).runEstimate oracle.query) =
                  fun state => cappedAccuracyGaussianCollectLawAux Q R weight
                    properStride (rawCap + 1) 0 (samples + 1)
                    state.1 state.2 by
                    funext state
                    exact hsemantic state.1 state.2]
                exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                  Q R hweight properStride (rawCap + 1) 0 (samples + 1)).1
              constructor
              · intro total current
                simp only [cappedAccuracyGaussianCollectWeightsAux]
                exact (accuracyGaussianRejectionAttempt_stronglyMeasurable
                  q I oracle sigma2 current).bind
                    (hnextStrong total current) (hnextRun total current)
              · exact hsemantic
          | succ remainingProper =>
              let next (total : ℝ) : Bool × AmbientSpace q.n →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap remainingProper (samples + 1)
                    total result.2
                else
                  cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap (remainingProper + 1) (samples + 1)
                    total result.2
              let nextLaw (total : ℝ) : Bool × AmbientSpace q.n →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    rawCap remainingProper (samples + 1) total result.2
                else
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    rawCap (remainingProper + 1) (samples + 1) total result.2
              have hnextStrong : ∀ total result,
                  (next total result).StronglyMeasurable oracle.query := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1) (samples + 1)).2.1 _ _
                | true => exact (ih remainingProper (samples + 1)).2.1 _ _
              have hnextEq : ∀ total result,
                  (next total result).runEstimate oracle.query =
                    nextLaw total result := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1) (samples + 1)).2.2 _ _
                | true => exact (ih remainingProper (samples + 1)).2.2 _ _
              have hnextLawMeasurable : ∀ total, Measurable (nextLaw total) := by
                intro total
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                    Q R hweight properStride rawCap remainingProper
                      (samples + 1)).1.comp <|
                        measurable_const.prodMk measurable_snd
                · exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                    Q R hweight properStride rawCap (remainingProper + 1)
                      (samples + 1)).1.comp <|
                        measurable_const.prodMk measurable_snd
              have hnextRun : ∀ total, Measurable fun result =>
                  (next total result).runEstimate oracle.query := by
                intro total
                rw [show (fun result =>
                    (next total result).runEstimate oracle.query) = nextLaw total by
                  funext result
                  exact hnextEq total result]
                exact hnextLawMeasurable total
              have hsemantic : ∀ total current,
                  (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1) total current).runEstimate oracle.query =
                  cappedAccuracyGaussianCollectLawAux Q R weight properStride
                    (rawCap + 1) (remainingProper + 1) (samples + 1)
                    total current := by
                intro total current
                simp only [cappedAccuracyGaussianCollectWeightsAux]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _ (next total)
                  (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                    q I oracle sigma2 current)
                  (hnextStrong total) (hnextRun total)]
                rw [runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
                  q I oracle hsigma2 current]
                simp_rw [hnextEq total]
                change (Q current).bind (nextLaw total) = _
                rw [cappedAccuracyGaussianCollectLawAux]
              constructor
              · rw [show (fun state : ℝ × AmbientSpace q.n =>
                    (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                      properStride (rawCap + 1) (remainingProper + 1)
                      (samples + 1) state.1 state.2).runEstimate oracle.query) =
                  fun state => cappedAccuracyGaussianCollectLawAux Q R weight
                    properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1) state.1 state.2 by
                    funext state
                    exact hsemantic state.1 state.2]
                exact (cappedAccuracyGaussianCollectLawAux_measurable_and_probability
                  Q R hweight properStride (rawCap + 1) (remainingProper + 1)
                    (samples + 1)).1
              constructor
              · intro total current
                simp only [cappedAccuracyGaussianCollectWeightsAux]
                exact (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                  q I oracle sigma2 current).bind
                    (hnextStrong total) (hnextRun total)
              · exact hsemantic

theorem cappedAccuracyGaussianCollectWeights_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) :
    (Measurable fun current =>
      (cappedAccuracyGaussianCollectWeights q sigma2 weight rawCap
        properStride samples current).runEstimate oracle.query) ∧
    (∀ current,
      (cappedAccuracyGaussianCollectWeights q sigma2 weight rawCap
        properStride samples current).StronglyMeasurable oracle.query) ∧
    (∀ current,
      (cappedAccuracyGaussianCollectWeights q sigma2 weight rawCap
        properStride samples current).runEstimate oracle.query =
      cappedAccuracyGaussianCollectLaw
        (Arlib.MarkovChains.lazyProperProposalGaussianAux
          (accuracyPhaseTruncatedBody q I sigma2)
          (accuracyPhaseTruncatedBody_measurable q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)
        (accuracyGaussianRejectionKernel q I sigma2) weight rawCap
        properStride samples current) := by
  have h := cappedAccuracyGaussianCollectWeightsAux_semantics
    q I oracle hsigma2 hweight properStride rawCap properStride samples
  constructor
  · exact h.1.comp (measurable_const.prodMk measurable_id)
  constructor
  · intro current
    exact h.2.1 0 current
  · intro current
    exact h.2.2 0 current

/-- The faithful phase collector consumes at most its single shared cap,
including both ball proposals and speedy-to-target rejection queries. -/
theorem cappedAccuracyGaussianCollectWeightsAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
    (cappedAccuracyGaussianCollectWeightsAux q sigma2 weight properStride
      rawCap remainingProper samples total current).QueryBound rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rw [cappedAccuracyGaussianCollectWeightsAux]
          exact .pure _ 0
      | succ samples =>
          rw [cappedAccuracyGaussianCollectWeightsAux]
          exact .pure _ 0
  | succ rawCap ih =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rw [cappedAccuracyGaussianCollectWeightsAux]
          exact .pure _ (rawCap + 1)
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyGaussianCollectWeightsAux]
              have htail : ∀ result : Bool × AmbientSpace q.n,
                  (if result.1 then
                    cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                      properStride rawCap properStride samples
                        (total + weight result.2) current
                  else cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap properStride (samples + 1) total
                      current).QueryBound rawCap := by
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact ih properStride (samples + 1) total current
                | true => exact ih properStride samples _ current
              have h := (accuracyGaussianRejectionAttempt_queryBound
                q sigma2 current).bind htail
              simpa [Nat.add_comm] using h
          | succ remainingProper =>
              simp only [cappedAccuracyGaussianCollectWeightsAux]
              have htail : ∀ result : Bool × AmbientSpace q.n,
                  (if result.1 then
                    cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                      properStride rawCap remainingProper (samples + 1) total
                        result.2
                  else cappedAccuracyGaussianCollectWeightsAux q sigma2 weight
                    properStride rawCap (remainingProper + 1) (samples + 1) total
                      result.2).QueryBound rawCap := by
                rintro ⟨mark, state⟩
                cases mark with
                | false =>
                    exact ih (remainingProper + 1) (samples + 1) total state
                | true => exact ih remainingProper (samples + 1) total state
              have h := (accuracyMetropolisMarkedBallStep_queryBound
                q sigma2 current).bind htail
              simpa [Nat.add_comm] using h

theorem cappedAccuracyGaussianCollectWeights_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (cappedAccuracyGaussianCollectWeights q sigma2 weight rawCap properStride
      samples current).QueryBound rawCap :=
  cappedAccuracyGaussianCollectWeightsAux_queryBound q sigma2 weight
    properStride rawCap properStride samples 0 current

end ArlibCommunity.Algorithms.CV18
