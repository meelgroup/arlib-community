/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutable

/-! # Accepted-target semantics at schedule-targeted geometry

This file transports the KLS rejection law from the old fixed radial body to
the body and proposal radius selected from the actual per-sample error budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise

noncomputable def scheduledAccuracyGaussianRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : ENNReal :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  (figureOneScheduledPhaseBody q I sigma2).indicator
    (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c) target

theorem scheduledAccuracyGaussianRejectionAcceptance_le_one
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    scheduledAccuracyGaussianRejectionAcceptance q I sigma2 current ≤ 1 := by
  unfold scheduledAccuracyGaussianRejectionAcceptance
  by_cases ht : (accuracyScaleFactor q)⁻¹ • current ∈
      figureOneScheduledPhaseBody q I sigma2
  · rw [Set.indicator_of_mem ht]
    exact Arlib.MarkovChains.gaussianScaleAcceptance_le_one hsigma2
      (accuracyScaleFactor_pos q) (accuracyScaleFactor_le_one q) _
  · rw [Set.indicator_of_notMem ht]
    exact bot_le

theorem measurable_scheduledAccuracyGaussianRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (scheduledAccuracyGaussianRejectionAcceptance q I sigma2) := by
  unfold scheduledAccuracyGaussianRejectionAcceptance
  exact ((Arlib.MarkovChains.measurable_gaussianScaleAcceptance sigma2
      (accuracyScaleFactor q)).indicator
        (figureOneScheduledPhaseBody_measurable q I sigma2)).comp
          ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
            (accuracyScaleFactor q)⁻¹).smul measurable_id)

noncomputable def scheduledBalancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : ENNReal :=
  (2 : ENNReal)⁻¹ *
    scheduledAccuracyGaussianRejectionAcceptance q I sigma2 current

theorem measurable_scheduledBalancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (scheduledBalancedAccuracyGaussianAcceptance q I sigma2) := by
  exact (measurable_scheduledAccuracyGaussianRejectionAcceptance
    q I sigma2).const_mul _

theorem scheduledBalancedAccuracyGaussianAcceptance_le_half
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current ≤
      (2 : ENNReal)⁻¹ := by
  unfold scheduledBalancedAccuracyGaussianAcceptance
  calc
    (2 : ENNReal)⁻¹ *
        scheduledAccuracyGaussianRejectionAcceptance q I sigma2 current ≤
        (2 : ENNReal)⁻¹ * 1 := mul_le_mul le_rfl
          (scheduledAccuracyGaussianRejectionAcceptance_le_one
            q I hsigma2 current) bot_le bot_le
    _ = (2 : ENNReal)⁻¹ := mul_one _

theorem oracle_and_radii_iff_mem_scheduledPhaseBody
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (x : AmbientSpace q.n) :
    oracle.query x = true ∧
        ‖x‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖x‖ ≤ figureOneScheduledPhaseRadius q sigma2 ↔
      x ∈ figureOneScheduledPhaseBody q I sigma2 := by
  rw [oracle.correct]
  simp only [figureOneScheduledPhaseBody, truncatedBody, Set.mem_inter_iff,
    Metric.mem_closedBall, dist_zero_right]
  tauto

noncomputable def scheduledBalancedAccuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (Bool × AmbientSpace q.n) :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  let accept := scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current
  accept • Measure.dirac (true, target) +
    (1 - accept) • Measure.dirac (false, target)

theorem measurable_scheduledBalancedAccuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [scheduledBalancedAccuracyGaussianRejectionLaw, Measure.add_apply,
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
  have hacc := measurable_scheduledBalancedAccuracyGaussianAcceptance
    q I sigma2
  exact (hacc.mul htrue).add ((measurable_const.sub hacc).mul hfalse)

theorem runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).runEstimate
        oracle.query =
      scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2 current := by
  let c := accuracyScaleFactor q
  let target : AmbientSpace q.n := c⁻¹ • current
  let accept := scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current
  have haccept : accept ≤ 1 :=
    (scheduledBalancedAccuracyGaussianAcceptance_le_half
      q I hsigma2 current).trans (by norm_num)
  have hacceptTop : accept ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top haccept
  have hacceptReal0 : 0 ≤ accept.toReal := ENNReal.toReal_nonneg
  have hacceptReal1 : accept.toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top haccept
  by_cases ht : target ∈ figureOneScheduledPhaseBody q I sigma2
  · have heligible := (oracle_and_radii_iff_mem_scheduledPhaseBody
      q I oracle sigma2 target).mpr ht
    have hcond : ∀ coin : ℝ,
        (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) =
        (coin ≤ accept.toReal) := by
      intro coin
      have hacceptEq :
          scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current =
            (2 : ENNReal)⁻¹ *
              Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target := by
        unfold scheduledBalancedAccuracyGaussianAcceptance
          scheduledAccuracyGaussianRejectionAcceptance
        rw [Set.indicator_of_mem ht]
      rw [← hacceptEq]
      apply propext
      simpa only [heligible.1, heligible.2.1, heligible.2.2, true_and] using
        (ENNReal.ofReal_le_iff_le_toReal hacceptTop :
          ENNReal.ofReal coin ≤ accept ↔ coin ≤ accept.toReal)
    simp only [scheduledBalancedAccuracyGaussianRejectionAttempt,
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
    rw [hbind, Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hout]
    rw [uniformUnitInterval_map_threshold hacceptReal0 hacceptReal1
      (true, target) (false, target)]
    unfold scheduledBalancedAccuracyGaussianRejectionLaw
    dsimp only
    rw [ENNReal.ofReal_toReal hacceptTop]
    have hcompTop : 1 - accept ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (tsub_le_self : 1 - accept ≤ 1)
    have hcomp : ENNReal.ofReal (1 - accept.toReal) = 1 - accept := by
      rw [← ENNReal.toReal_one,
        ← ENNReal.toReal_sub_of_le haccept ENNReal.one_ne_top,
        ENNReal.ofReal_toReal hcompTop]
    rw [hcomp]
  · have hineligible : ¬ (oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2) := by
      rwa [oracle_and_radii_iff_mem_scheduledPhaseBody]
    have haccept0 : accept = 0 := by
      unfold accept scheduledBalancedAccuracyGaussianAcceptance
        scheduledAccuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem ht, mul_zero]
    simp only [scheduledBalancedAccuracyGaussianRejectionAttempt,
      MembershipOracleProgram.runEstimate]
    have hfalse : ∀ coin : ℝ,
        ¬ (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) := by
      intro coin h
      exact hineligible ⟨h.1, h.2.1, h.2.2.1⟩
    dsimp only [c, target] at hfalse
    simp_rw [hfalse, if_false]
    simp only [MembershipOracleProgram.runEstimate]
    rw [Measure.bind_const, measure_univ, one_smul]
    unfold scheduledBalancedAccuracyGaussianRejectionLaw
    dsimp only
    rw [show scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current = 0
      from haccept0]
    simp

theorem scheduledBalancedAccuracyGaussianRejectionLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    IsProbabilityMeasure
      (scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2 current) := by
  constructor
  simp only [scheduledBalancedAccuracyGaussianRejectionLaw,
    Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le]
  exact (scheduledBalancedAccuracyGaussianAcceptance_le_half
    q I hsigma2 current).trans (by norm_num)

noncomputable def scheduledBalancedAccuracyGaussianRejectionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Kernel (AmbientSpace q.n) (Bool × AmbientSpace q.n) :=
  ⟨scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2,
    measurable_scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2⟩

instance scheduledBalancedAccuracyGaussianRejectionKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) [Fact (0 < sigma2)] :
    IsMarkovKernel
      (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2) :=
  ⟨scheduledBalancedAccuracyGaussianRejectionLaw_isProbabilityMeasure
    q I (Fact.out : 0 < sigma2)⟩

noncomputable def scheduledAccuracyGaussianAcceptedTargetLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  Arlib.condOn
    ((mu.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x)) Set.univ

noncomputable def scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  Arlib.condOn
    ((mu.withDensity
      (scheduledBalancedAccuracyGaussianAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x)) Set.univ

theorem scheduledBalancedAccuracyGaussianAcceptedTargetLaw_eq
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2 mu =
      scheduledAccuracyGaussianAcceptedTargetLaw q I sigma2 mu := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  unfold scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    scheduledAccuracyGaussianAcceptedTargetLaw
    scheduledBalancedAccuracyGaussianAcceptance
  change Arlib.condOn
      ((mu.withDensity ((2 : ENNReal)⁻¹ •
        scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map scale)
        Set.univ = _
  rw [withDensity_smul (2 : ENNReal)⁻¹
    (measurable_scheduledAccuracyGaussianRejectionAcceptance q I sigma2)]
  change Arlib.condOn (((2 : ENNReal)⁻¹ •
      mu.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
          scale) Set.univ = _
  rw [Measure.map_smul]
  exact Arlib.MarkovChains.condOn_smul_cv18 _ MeasurableSet.univ
    (by norm_num) (by norm_num)

theorem map_withDensity_scheduledAccuracyRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let c := accuracyScaleFactor q
    (mu.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => c⁻¹ • x) =
      ((mu.restrict (c • K)).map (fun x => c⁻¹ • x)).withDensity
        (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c) := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let c := accuracyScaleFactor q
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal :=
    Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hK : MeasurableSet K := figureOneScheduledPhaseBody_measurable q I sigma2
  have hcore : MeasurableSet (c • K) :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed).measurableSet
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n => c⁻¹).smul
      measurable_id
  have hg : Measurable g := by
    dsimp [g]
    exact Arlib.MarkovChains.measurable_gaussianScaleAcceptance sigma2 c
  have haccept : scheduledAccuracyGaussianRejectionAcceptance q I sigma2 =
      (c • K).indicator (fun x => g (scale x)) := by
    funext x
    unfold scheduledAccuracyGaussianRejectionAcceptance
    dsimp only [c, K, scale, g]
    by_cases hx : (accuracyScaleFactor q)⁻¹ • x ∈
        figureOneScheduledPhaseBody q I sigma2
    · have hxcore : x ∈ accuracyScaleFactor q •
          figureOneScheduledPhaseBody q I sigma2 :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne' _ _).2 hx
      simp [hx, hxcore]
    · have hxcore : x ∉ accuracyScaleFactor q •
          figureOneScheduledPhaseBody q I sigma2 := fun h =>
        hx ((Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne' _ _).1 h)
      simp [hx, hxcore]
  ext B hB
  rw [Measure.map_apply hscale hB, withDensity_apply _ (hscale hB),
    withDensity_apply _ hB]
  rw [← lintegral_indicator hB]
  have hBg : Measurable (B.indicator g) := hg.indicator hB
  rw [lintegral_map' hBg.aemeasurable hscale.aemeasurable]
  change (∫⁻ x in scale ⁻¹' B,
      scheduledAccuracyGaussianRejectionAcceptance q I sigma2 x ∂mu) =
    ∫⁻ x in c • K, B.indicator g (scale x) ∂mu
  rw [← lintegral_indicator (hscale hB), ← lintegral_indicator hcore,
    haccept]
  apply lintegral_congr
  intro x
  by_cases hxB : scale x ∈ B <;> by_cases hxK : x ∈ c • K <;>
    simp [hxB, hxK]

theorem scheduledAccuracyGaussianAcceptedTargetLaw_eq_kls
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n))
    (hcore0 : mu (accuracyScaleFactor q •
      figureOneScheduledPhaseBody q I sigma2) ≠ 0)
    (hcoretop : mu (accuracyScaleFactor q •
      figureOneScheduledPhaseBody q I sigma2) ≠ ⊤) :
    scheduledAccuracyGaussianAcceptedTargetLaw q I sigma2 mu =
      let K := figureOneScheduledPhaseBody q I sigma2
      let c := accuracyScaleFactor q
      Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let c := accuracyScaleFactor q
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal :=
    Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n => c⁻¹).smul
      measurable_id
  have hproposal :
      ((Arlib.condOn mu (c • K)).map scale).withDensity g =
        (mu (c • K))⁻¹ •
          (((mu.restrict (c • K)).map scale).withDensity g) := by
    rw [Arlib.condOn_def, Measure.map_smul, withDensity_smul_measure]
  rw [hproposal]
  have hunscaled := map_withDensity_scheduledAccuracyRejectionAcceptance
    q I sigma2 mu
  change Arlib.condOn
      ((mu.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)).map
          scale) Set.univ = _
  rw [← hunscaled]
  symm
  exact Arlib.MarkovChains.condOn_smul_cv18 _ MeasurableSet.univ
    (ENNReal.inv_ne_zero.mpr hcoretop) (ENNReal.inv_ne_top.mpr hcore0)

theorem condOn_gaussian_scheduledPhase_eq_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Arlib.condOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2))
        (figureOneScheduledPhaseBody q I sigma2) =
      Arlib.condOn
        (truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))
        (figureOneScheduledPhaseBody q I sigma2) := by
  let Z : ENNReal :=
    ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2)
  have hZreal : 0 < gaussianIntegral (truncatedBody q I) sigma2 :=
    gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2
  have hZ0 : Z⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hZtop : Z⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.2 hZreal).ne'
  have hsub : figureOneScheduledPhaseBody q I sigma2 ⊆ truncatedBody q I :=
    fun _ hx => hx.1
  rw [truncatedGaussianProbability_toMeasure q I hsigma2]
  change _ = Arlib.condOn (Z⁻¹ • truncatedGaussianMeasure q I sigma2) _
  rw [Arlib.MarkovChains.condOn_smul_cv18 _
    (figureOneScheduledPhaseBody_measurable q I sigma2) hZ0 hZtop]
  unfold truncatedGaussianMeasure
  rw [← restrict_withDensity (truncatedBody_measurable q I)]
  rw [Arlib.MarkovChains.condOn_restrict_eq_condOn_of_subset_cv18 _
    (figureOneScheduledPhaseBody_measurable q I sigma2) hsub]
  congr 2
  funext x
  simp [gaussianDensity_eq, Arlib.MarkovChains.gaussianWeight,
    Arlib.MarkovChains.gaussianWeightReal]

/-- Exact scheduled stationary target error used by the balanced transition. -/
noncomputable def scheduledBalancedStationaryTargetError
    (q : VolumeParams) : ENNReal :=
  96 * ENNReal.ofReal (figureOneScheduledCoreError q) +
    ENNReal.ofReal (figureOneScheduledRadialError q)

/-- Uniform speedy-stationary mass of the homothetic KLS core at scheduled
geometry.  The small-radius branch actually gives `1/2`; `7/16` is retained
as the common constant with the paper-step branch. -/
theorem figureOneScheduled_speedy_core_mass
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 16 : ℝ) ≤
      pi (accuracyScaleFactor q • K) := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  by_cases hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1
  · have hhalf :=
      Arlib.MarkovChains.half_le_ellGaussianProb_standardCore_radius_cv18
        hn (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledPhaseBody_convex q I sigma2)
        (figureOneScheduledPhaseInradius_pos q hsigma2)
        (ball_scheduledPhaseInradius_subset q I sigma2) hdelta
        (figureOneScheduledProposalRadius_le_inradiusStep q hsigma2 hsmall)
        hsigma2 hmass0 hmasstop
    calc
      ENNReal.ofReal (7 / 16 : ℝ) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by norm_num
      _ ≤ pi (accuracyScaleFactor q • K) := by
        simpa [pi, K, accuracyScaleFactor] using hhalf
  · have hlarge : 1 ≤ figureOneScheduledPhaseRadius q sigma2 :=
      le_of_not_ge hsmall
    have hball : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
      intro x hx
      refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
      · simpa [unitBall] using hx
      · exact hx.trans hlarge
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    have hc0 : 0 < c := by
      dsimp [c]
      have hnR : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
      have : 1 / (2 * (q.n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hc1 : c < 1 := by
      dsimp [c]
      have hnR : (0 : ℝ) < q.n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have : 0 < 1 / (2 * (q.n : ℝ)) := by positivity
      linarith
    have hcoreM : MeasurableSet (c • K) :=
      ((isClosedMap_smul_of_ne_zero hc0.ne') K
        (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed).measurableSet
    have hsub : c • K ⊆ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact (figureOneScheduledPhaseBody_convex q I sigma2).smul_mem_of_zero_mem
        (hball (Metric.mem_closedBall_self zero_le_one)) hx ⟨hc0.le, hc1.le⟩
    have hcoreVol0 : volume (c • K) ≠ 0 := by
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact mul_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 q.n))
        (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
    have hcoreVoltop : volume (c • K) ≠ ⊤ := by
      rw [Arlib.volume_smul_euclidean hc0.le]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
    have hgaussCore0 :
        (((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K)
            (c • K) ≠ 0 := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _ hcoreVol0
    have hgaussCoretop :
        (((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K)
            (c • K) ≠ ⊤ := by
      rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
      exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_top hsigma2
        hcoreM hcoreVoltop
    have hpaper :=
      Arlib.MarkovChains.standardCore_defect_and_speedyMass_cv18
        hn (figureOneScheduledPhaseBody_convex q I sigma2)
        (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed
        (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) hball
        hdelta (Real.sqrt_pos.2 hsigma2)
        (figureOneScheduledCoreError_pos q)
        (figureOneScheduledCoreError_le_one_div_sixteen q)
        (figureOneScheduledProposalRadius_le_coreStep q hsigma2)
        (by simpa [c, K, div_eq_mul_inv, mul_comm,
          Real.sq_sqrt hsigma2.le] using hgaussCore0)
        (by simpa [c, K, div_eq_mul_inv, mul_comm,
          Real.sq_sqrt hsigma2.le] using hgaussCoretop)
        (by simpa [Real.sq_sqrt hsigma2.le] using hmass0)
        (by simpa [Real.sq_sqrt hsigma2.le] using hmasstop)
    simpa [pi, K, c, accuracyScaleFactor, Real.sq_sqrt hsigma2.le] using
      hpaper.2

set_option maxHeartbeats 1000000 in
theorem scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    Arlib.TVLe
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (scheduledBalancedStationaryTargetError q) := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hcore0 : pi (accuracyScaleFactor q • K) ≠ 0 := by
    by_cases hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1
    · have hhalf :=
        Arlib.MarkovChains.half_le_ellGaussianProb_standardCore_radius_cv18
          hn (figureOneScheduledPhaseBody_measurable q I sigma2)
          (figureOneScheduledPhaseBody_convex q I sigma2)
          (figureOneScheduledPhaseInradius_pos q hsigma2)
          (ball_scheduledPhaseInradius_subset q I sigma2) hdelta
          (figureOneScheduledProposalRadius_le_inradiusStep q hsigma2 hsmall)
          hsigma2 hmass0 hmasstop
      exact ne_of_gt ((by norm_num : (0 : ENNReal) <
        ENNReal.ofReal (1 / 2 : ℝ)).trans_le (by
          simpa [pi, K, accuracyScaleFactor] using hhalf))
    · have hlarge : 1 ≤ figureOneScheduledPhaseRadius q sigma2 :=
        le_of_not_ge hsmall
      have hball : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
        intro x hx
        refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
        · simpa [unitBall] using hx
        · exact hx.trans hlarge
      let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
      have hc0 : 0 < c := by
        dsimp [c]
        have hnR : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
        have : 1 / (2 * (q.n : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      have hc1 : c < 1 := by
        dsimp [c]
        have : 0 < 1 / (2 * (q.n : ℝ)) := by
          have hnR : (0 : ℝ) < q.n := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
          positivity
        linarith
      have hcoreM : MeasurableSet (c • K) :=
        ((isClosedMap_smul_of_ne_zero hc0.ne') K
          (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed).measurableSet
      have hsub : c • K ⊆ K := by
        rintro _ ⟨x, hx, rfl⟩
        exact (figureOneScheduledPhaseBody_convex q I sigma2).smul_mem_of_zero_mem
          (hball (Metric.mem_closedBall_self zero_le_one)) hx
          ⟨hc0.le, hc1.le⟩
      have hcoreVol0 : volume (c • K) ≠ 0 := by
        rw [Arlib.volume_smul_euclidean hc0.le]
        exact mul_ne_zero
          (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 q.n))
          (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      have hcoreVoltop : volume (c • K) ≠ ⊤ := by
        rw [Arlib.volume_smul_euclidean hc0.le]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      have hgaussCore0 :
          (((volume : Measure (AmbientSpace q.n)).withDensity
            (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K)
              (c • K) ≠ 0 := by
        rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
        exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _ hcoreVol0
      have hgaussCoretop :
          (((volume : Measure (AmbientSpace q.n)).withDensity
            (Arlib.MarkovChains.gaussianWeight sigma2)).restrict K)
              (c • K) ≠ ⊤ := by
        rw [Measure.restrict_apply hcoreM, Set.inter_eq_left.2 hsub]
        exact Arlib.MarkovChains.withDensity_gaussianWeight_ne_top hsigma2
          hcoreM hcoreVoltop
      have hpaper :=
        Arlib.MarkovChains.standardCore_defect_and_speedyMass_cv18
          hn (figureOneScheduledPhaseBody_convex q I sigma2)
          (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed
          (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) hball
          hdelta (Real.sqrt_pos.2 hsigma2)
          (figureOneScheduledCoreError_pos q)
          (figureOneScheduledCoreError_le_one_div_sixteen q)
          (figureOneScheduledProposalRadius_le_coreStep q hsigma2)
          (by simpa [c, K, div_eq_mul_inv, mul_comm,
            Real.sq_sqrt hsigma2.le] using hgaussCore0)
          (by simpa [c, K, div_eq_mul_inv, mul_comm,
            Real.sq_sqrt hsigma2.le] using hgaussCoretop)
          (by simpa [Real.sq_sqrt hsigma2.le] using hmass0)
          (by simpa [Real.sq_sqrt hsigma2.le] using hmasstop)
      exact ne_of_gt ((by norm_num : (0 : ENNReal) <
        ENNReal.ofReal (7 / 16 : ℝ)).trans_le (by
          simpa [pi, K, c, accuracyScaleFactor, Real.sq_sqrt hsigma2.le]
            using hpaper.2))
  have hcoretop : pi (accuracyScaleFactor q • K) ≠ ⊤ := measure_ne_top pi _
  rw [scheduledBalancedAccuracyGaussianAcceptedTargetLaw_eq,
    scheduledAccuracyGaussianAcceptedTargetLaw_eq_kls q I sigma2 pi
      hcore0 hcoretop]
  have hstationary : Arlib.TVLe pi pi
      (ENNReal.ofReal (figureOneScheduledCoreError q)) :=
    (Arlib.TVLe.refl pi).mono bot_le
  have hcore : Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn pi (accuracyScaleFactor q • K)).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).withDensity
            (Arlib.MarkovChains.gaussianScaleAcceptance sigma2
              (accuracyScaleFactor q))) Set.univ)
      (Arlib.condOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2)) K)
      (96 * ENNReal.ofReal (figureOneScheduledCoreError q)) := by
    by_cases hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1
    · have hprop0 :
          ((volume : Measure (AmbientSpace q.n)).withDensity
            (Arlib.MarkovChains.gaussianWeight
              (sigma2 / (1 - 1 / (2 * (q.n : ℝ))) ^ 2))) K ≠ 0 :=
        Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _
          (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      have hproptop :
          ((volume : Measure (AmbientSpace q.n)).withDensity
            (Arlib.MarkovChains.gaussianWeight
              (sigma2 / (1 - 1 / (2 * (q.n : ℝ))) ^ 2))) K ≠ ⊤ :=
        Arlib.MarkovChains.withDensity_gaussianWeight_ne_top
          (by
            have hc : 0 < 1 - 1 / (2 * (q.n : ℝ)) := by
              have hnR : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
              have : 1 / (2 * (q.n : ℝ)) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                nlinarith
              linarith
            positivity)
          (figureOneScheduledPhaseBody_measurable q I sigma2)
          (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      have hsmallK := Arlib.MarkovChains.TVLe.speedyToGaussian_twoStage_cv18
        hn (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledPhaseBody_convex q I sigma2)
        (figureOneScheduledPhaseInradius_pos q hsigma2)
        (ball_scheduledPhaseInradius_subset q I sigma2)
        hdelta (figureOneScheduledProposalRadius_le_inradiusStep q hsigma2 hsmall)
        hsigma2 hmass0 hmasstop hprop0 hproptop hstationary
        ENNReal.ofReal_ne_top (by
          rw [ENNReal.ofReal_le_ofReal_iff
            (by norm_num : (0 : ℝ) ≤ 1 / 32)]
          unfold figureOneScheduledCoreError
          nlinarith [figureOnePerSampleMixingError_le_one q])
      exact hsmallK.mono (mul_le_mul' (by norm_num) le_rfl)
    · have hlarge : 1 ≤ figureOneScheduledPhaseRadius q sigma2 :=
        le_of_not_ge hsmall
      have hball : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
        intro x hx
        refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
        · simpa [unitBall] using hx
        · exact hx.trans hlarge
      have hstationarySq : Arlib.TVLe pi
          (Arlib.MarkovChains.ellGaussianProb K delta
            ((Real.sqrt sigma2) ^ 2))
          (ENNReal.ofReal (figureOneScheduledCoreError q)) := by
        simpa [Real.sq_sqrt hsigma2.le] using hstationary
      have hlargeK :=
        Arlib.MarkovChains.TVLe.speedyToGaussian_of_paperStep_of_body_cv18
          hn (figureOneScheduledPhaseBody_convex q I sigma2)
          (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed
          (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
          (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
          (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
          hball hdelta (Real.sqrt_pos.2 hsigma2)
          (figureOneScheduledCoreError_pos q)
          (figureOneScheduledCoreError_le_one_div_sixteen q)
          (figureOneScheduledProposalRadius_le_coreStep q hsigma2)
          hstationarySq ENNReal.ofReal_ne_top
          (figureOneScheduledCore_combined_le q)
      have hcEq : 1 - 1 / (2 * (q.n : ℝ)) = accuracyScaleFactor q := by
        unfold accuracyScaleFactor
        ring
      rw [show 96 * ENNReal.ofReal (figureOneScheduledCoreError q) =
        64 * ENNReal.ofReal (figureOneScheduledCoreError q) +
          32 * ENNReal.ofReal (figureOneScheduledCoreError q) by ring]
      simpa only [K, hcEq, Real.sq_sqrt hsigma2.le] using hlargeK
  have hradial := TVLe.scheduledPhase_condOn_truncatedGaussian
    q I hsigma2
  rw [condOn_gaussian_scheduledPhase_eq_truncatedGaussian q I hsigma2]
    at hcore
  change Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn pi (accuracyScaleFactor q • K)).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).withDensity
            (Arlib.MarkovChains.gaussianScaleAcceptance sigma2
              (accuracyScaleFactor q))) Set.univ)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (scheduledBalancedStationaryTargetError q)
  exact (hcore.trans hradial).mono (by
    unfold scheduledBalancedStationaryTargetError
    exact le_rfl)

theorem scheduledBalancedStationaryTargetError_le_targetBudget
    (q : VolumeParams) :
    scheduledBalancedStationaryTargetError q ≤
      figureOneCorrectedTargetBudget q := by
  simpa [scheduledBalancedStationaryTargetError,
    figureOneCorrectedTargetBudget, figureOneCorrectedTransitionBudget] using
      figureOneScheduledTargetError_le q

/-- The corrected transition allocation instantiated with the scheduled KLS
target error.  This is the concrete replacement for the formerly impossible
old fixed-radius `targetError_le` premise. -/
noncomputable def figureOneScheduledCorrectedErrorAllocation
    (q : VolumeParams) (rejectMass : ENNReal) (attempts : ℕ)
    (hreject : rejectMass ≤ 1)
    (hretry : rejectMass ^ (attempts + 1) ≤
      figureOneCorrectedRetryTailBudget q) :
    BalancedTransitionErrorAllocation (q := q) rejectMass attempts
      (scheduledBalancedStationaryTargetError q) where
  totalBudget := figureOneCorrectedTransitionBudget q
  blockBudget := figureOneCorrectedBlockBudget q attempts
  retryTailBudget := figureOneCorrectedRetryTailBudget q
  targetBudget := figureOneCorrectedTargetBudget q
  reject_le_one := hreject
  retryTail_le := hretry
  targetError_le := scheduledBalancedStationaryTargetError_le_targetBudget q
  components_le := figureOneCorrected_components_le q attempts

theorem scheduledBalancedTransitionError_le_budget
    (q : VolumeParams) {rejectMass : ENNReal} {attempts : ℕ}
    (hreject : rejectMass ≤ 1)
    (hretry : rejectMass ^ (attempts + 1) ≤
      figureOneCorrectedRetryTailBudget q) :
    figureOneCorrectedBlockBudget q attempts + rejectMass *
        balancedRetryError (figureOneCorrectedBlockBudget q attempts)
          rejectMass attempts +
      scheduledBalancedStationaryTargetError q ≤
        figureOneCorrectedTransitionBudget q := by
  exact balancedTransitionError_le_allocation
    (figureOneScheduledCorrectedErrorAllocation q rejectMass attempts
      hreject hretry)

#print axioms scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
#print axioms runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
#print axioms scheduledBalancedStationaryTargetError_le_targetBudget
#print axioms scheduledBalancedTransitionError_le_budget

end ArlibCommunity.Algorithms.CV18
