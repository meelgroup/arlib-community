/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyAcceptance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSubprobabilityMixing

/-!
# Balanced KLS rejection branches

The KLS correction already has a constant lower acceptance probability, but
its rejection probability need not have an a priori lower bound.  Multiplying
the acceptance coefficient by `1/2` leaves the law conditioned on acceptance
unchanged and makes rejection pointwise at least `1/2`.  Consequently both
normalized branches are uniformly warm for the speedy stationary law.  This
is the branch-reset invariant used by the finite retry sampler.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

private theorem ofReal_one_half_balanced :
    ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The deliberately throttled KLS acceptance coefficient. -/
noncomputable def balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : ENNReal :=
  (2 : ENNReal)⁻¹ * accuracyGaussianRejectionAcceptance q I sigma2 current

theorem measurable_balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (balancedAccuracyGaussianAcceptance q I sigma2) := by
  exact (measurable_accuracyGaussianRejectionAcceptance q I sigma2).const_mul _

theorem balancedAccuracyGaussianAcceptance_le_half
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    balancedAccuracyGaussianAcceptance q I sigma2 current ≤ (2 : ENNReal)⁻¹ := by
  unfold balancedAccuracyGaussianAcceptance
  calc
    (2 : ENNReal)⁻¹ * accuracyGaussianRejectionAcceptance q I sigma2 current
        ≤ (2 : ENNReal)⁻¹ * 1 := mul_le_mul le_rfl
          (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 current)
          bot_le bot_le
    _ = (2 : ENNReal)⁻¹ := mul_one _

theorem half_le_one_sub_balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (2 : ENNReal)⁻¹ ≤
      1 - balancedAccuracyGaussianAcceptance q I sigma2 current := by
  apply ENNReal.le_sub_of_add_le_left
    (ne_top_of_le_ne_top (by norm_num)
      (balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current))
  have h := balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current
  calc
    balancedAccuracyGaussianAcceptance q I sigma2 current + (2 : ENNReal)⁻¹
        ≤ (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := add_le_add_left h _
    _ = 1 := by
      rw [← ofReal_one_half_balanced,
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

/-- One executable balanced KLS rejection test.  This is the original test
with its acceptance threshold multiplied by `1/2`; it therefore uses exactly
one membership query and does not change the target returned on success. -/
noncomputable def balancedAccuracyGaussianRejectionAttempt (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else
        .pure (false, target)

theorem balancedAccuracyGaussianRejectionAttempt_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionAttempt q sigma2 current).QueryBound 1 := by
  unfold balancedAccuracyGaussianRejectionAttempt
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem balancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionAttempt q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [balancedAccuracyGaussianRejectionAttempt,
    MembershipOracleProgram.StronglyMeasurable]
  let target : AmbientSpace q.n := (accuracyScaleFactor q)⁻¹ • current
  let output : ℝ → Bool × AmbientSpace q.n := fun coin =>
    if oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
        ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
          Arlib.MarkovChains.gaussianScaleAcceptance sigma2
            (accuracyScaleFactor q) target then
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
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2
              (accuracyScaleFactor q) target) := by
        intro coin h
        exact heligible ⟨h.1, h.2.1, h.2.2.1⟩
      simp only [output, hfalse, if_false]
      exact measurable_const
  constructor
  · rw [show (fun coin => MembershipOracleProgram.runEstimate oracle.query
        (if oracle.query target = true ∧
            ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
            ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
              Arlib.MarkovChains.gaussianScaleAcceptance sigma2
                (accuracyScaleFactor q) target then
          .pure (true, target) else .pure (false, target))) =
        fun coin => Measure.dirac (output coin) by
      funext coin
      by_cases h : oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2
              (accuracyScaleFactor q) target
      · simp [h, output, MembershipOracleProgram.runEstimate]
      · simp [h, output, MembershipOracleProgram.runEstimate]]
    exact Measure.measurable_dirac.comp hout
  · intro coin
    split <;> trivial

/-- Exact mixture law of one balanced executable rejection attempt. -/
noncomputable def balancedAccuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (Bool × AmbientSpace q.n) :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  let accept := balancedAccuracyGaussianAcceptance q I sigma2 current
  accept • Measure.dirac (true, target) +
    (1 - accept) • Measure.dirac (false, target)

theorem measurable_balancedAccuracyGaussianRejectionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (balancedAccuracyGaussianRejectionLaw q I sigma2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [balancedAccuracyGaussianRejectionLaw, Measure.add_apply,
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
  have hacc := measurable_balancedAccuracyGaussianAcceptance q I sigma2
  exact (hacc.mul htrue).add ((measurable_const.sub hacc).mul hfalse)

theorem runEstimate_balancedAccuracyGaussianRejectionAttempt
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionAttempt q sigma2 current).runEstimate
        oracle.query =
      balancedAccuracyGaussianRejectionLaw q I sigma2 current := by
  let c := accuracyScaleFactor q
  let target : AmbientSpace q.n := c⁻¹ • current
  let accept := balancedAccuracyGaussianAcceptance q I sigma2 current
  have haccept : accept ≤ 1 :=
    (balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current).trans
      (by norm_num)
  have hacceptTop : accept ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top haccept
  have hacceptReal0 : 0 ≤ accept.toReal := ENNReal.toReal_nonneg
  have hacceptReal1 : accept.toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top haccept
  by_cases ht : target ∈ accuracyPhaseTruncatedBody q I sigma2
  · have heligible := (oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody
      q I oracle sigma2 target).mpr ht
    have hcond : ∀ coin : ℝ,
        (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) =
        (coin ≤ accept.toReal) := by
      intro coin
      have hacceptEq : balancedAccuracyGaussianAcceptance q I sigma2 current =
          (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target := by
        unfold balancedAccuracyGaussianAcceptance
          accuracyGaussianRejectionAcceptance
        rw [Set.indicator_of_mem ht]
      rw [← hacceptEq]
      apply propext
      simpa only [heligible.1, heligible.2.1, heligible.2.2, true_and] using
        (ENNReal.ofReal_le_iff_le_toReal hacceptTop :
          ENNReal.ofReal coin ≤ accept ↔ coin ≤ accept.toReal)
    simp only [balancedAccuracyGaussianRejectionAttempt,
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
    unfold balancedAccuracyGaussianRejectionLaw
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
      unfold accept balancedAccuracyGaussianAcceptance
        accuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem ht, mul_zero]
    simp only [balancedAccuracyGaussianRejectionAttempt,
      MembershipOracleProgram.runEstimate]
    have hfalse : ∀ coin : ℝ,
        ¬ (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ accuracyPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target) := by
      intro coin h
      exact hineligible ⟨h.1, h.2.1, h.2.2.1⟩
    dsimp only [c, target] at hfalse
    simp_rw [hfalse, if_false]
    simp only [MembershipOracleProgram.runEstimate]
    rw [Measure.bind_const, measure_univ, one_smul]
    unfold balancedAccuracyGaussianRejectionLaw
    dsimp only
    rw [show balancedAccuracyGaussianAcceptance q I sigma2 current = 0 from
      haccept0]
    simp

theorem balancedAccuracyGaussianRejectionLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    IsProbabilityMeasure
      (balancedAccuracyGaussianRejectionLaw q I sigma2 current) := by
  constructor
  simp only [balancedAccuracyGaussianRejectionLaw, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le]
  exact (balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current).trans
    (by norm_num)

noncomputable def balancedAccuracyGaussianRejectionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Kernel (AmbientSpace q.n) (Bool × AmbientSpace q.n) :=
  ⟨balancedAccuracyGaussianRejectionLaw q I sigma2,
    measurable_balancedAccuracyGaussianRejectionLaw q I sigma2⟩

instance balancedAccuracyGaussianRejectionKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) [Fact (0 < sigma2)] :
    IsMarkovKernel (balancedAccuracyGaussianRejectionKernel q I sigma2) :=
  ⟨balancedAccuracyGaussianRejectionLaw_isProbabilityMeasure
    q I (Fact.out : 0 < sigma2)⟩

/-- The successful slice of the balanced kernel is the balanced accepted
state submeasure followed by the same homothety as the original KLS test. -/
theorem balancedAccuracyGaussianRejectionKernel_true_prod
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) {B : Set (AmbientSpace q.n)}
    (hB : MeasurableSet B) :
    (mu.bind (balancedAccuracyGaussianRejectionKernel q I sigma2))
        ({true} ×ˢ B) =
      ((mu.withDensity (balancedAccuracyGaussianAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x)) B := by
  have hscale : Measurable (fun x : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹ • x) :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hprod : MeasurableSet ({true} ×ˢ B) :=
    (measurableSet_singleton true).prod hB
  rw [Measure.bind_apply hprod
    (balancedAccuracyGaussianRejectionKernel q I sigma2).measurable.aemeasurable]
  rw [Measure.map_apply hscale hB,
    withDensity_apply _ (hscale hB)]
  rw [← lintegral_indicator (hscale hB)]
  apply lintegral_congr
  intro current
  change (balancedAccuracyGaussianRejectionLaw q I sigma2 current)
      ({true} ×ˢ B) = _
  simp only [balancedAccuracyGaussianRejectionLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hprod]
  by_cases ht : (accuracyScaleFactor q)⁻¹ • current ∈ B
  · simp [ht, Set.indicator_of_mem, hprod]
  · simp [ht, Set.indicator_of_notMem, hprod]

/-- Normalized target-point law returned by a successful balanced attempt. -/
noncomputable def balancedAccuracyGaussianAcceptedTargetLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  Arlib.condOn
    ((mu.withDensity (balancedAccuracyGaussianAcceptance q I sigma2)).map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)) Set.univ

/-- Multiplying every acceptance probability by `1/2` does not change the
law conditioned on success. -/
theorem balancedAccuracyGaussianAcceptedTargetLaw_eq
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 mu =
      accuracyGaussianAcceptedTargetLaw q I sigma2 mu := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  unfold balancedAccuracyGaussianAcceptedTargetLaw
    accuracyGaussianAcceptedTargetLaw
  unfold balancedAccuracyGaussianAcceptance
  change Arlib.condOn
      ((mu.withDensity ((2 : ENNReal)⁻¹ •
        accuracyGaussianRejectionAcceptance q I sigma2)).map scale)
        Set.univ = _
  rw [withDensity_smul (2 : ENNReal)⁻¹
    (measurable_accuracyGaussianRejectionAcceptance q I sigma2)]
  change Arlib.condOn (((2 : ENNReal)⁻¹ •
      mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
        scale) Set.univ = _
  rw [Measure.map_smul]
  exact Arlib.MarkovChains.condOn_smul_cv18 _ MeasurableSet.univ
    (by norm_num) (by norm_num)

theorem balancedAccuracyGaussianAcceptedTargetLaw_tv_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mixed := Arlib.MarkovChains.iterate P mu0 t
    Arlib.TVLe
      (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 mixed)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError +
        32 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  rw [balancedAccuracyGaussianAcceptedTargetLaw_eq]
  exact accuracyGaussianAcceptedTargetLaw_tv_cv18 q I hsigma2 hM hwarm
    hmixError0 hmixError64 ht

/-- Current-state submeasure corresponding to a balanced successful attempt. -/
noncomputable def balancedAcceptedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity (balancedAccuracyGaussianAcceptance q I sigma2)

/-- Current-state submeasure corresponding to a balanced rejected attempt. -/
noncomputable def balancedRejectedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity (fun x => 1 - balancedAccuracyGaussianAcceptance q I sigma2 x)

theorem balancedAcceptedStateMeasure_eq_half_smul
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    balancedAcceptedStateMeasure q I sigma2 mu =
      (2 : ENNReal)⁻¹ •
        mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2) := by
  unfold balancedAcceptedStateMeasure balancedAccuracyGaussianAcceptance
  change mu.withDensity
      ((2 : ENNReal)⁻¹ • accuracyGaussianRejectionAcceptance q I sigma2) = _
  rw [withDensity_smul]
  exact measurable_accuracyGaussianRejectionAcceptance q I sigma2

theorem balancedAcceptedStateMeasure_mass_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  rw [balancedAcceptedStateMeasure_eq_half_smul,
    Measure.smul_apply, smul_eq_mul]
  have h := accuracyPhase_stationary_acceptance_ge q I hsigma2
  change ENNReal.ofReal (7 / 64 : ℝ) ≤
    (pi.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ at h
  calc
    ENNReal.ofReal (7 / 128 : ℝ) =
        (2 : ENNReal)⁻¹ * ENNReal.ofReal (7 / 64 : ℝ) := by
      rw [← ofReal_one_half_balanced,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    _ ≤ (2 : ENNReal)⁻¹ *
        (pi.withDensity
          (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      mul_le_mul' le_rfl h

theorem balancedRejectedStateMeasure_mass_ge_half
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu] :
    (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 mu Set.univ := by
  unfold balancedRejectedStateMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (2 : ENNReal)⁻¹ = ∫⁻ _x, (2 : ENNReal)⁻¹ ∂mu := by simp
    _ ≤ ∫⁻ x, 1 - balancedAccuracyGaussianAcceptance q I sigma2 x ∂mu :=
      lintegral_mono (half_le_one_sub_balancedAccuracyGaussianAcceptance
        q I hsigma2)

theorem balancedAcceptedStateMeasure_le_half_smul
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) :
    balancedAcceptedStateMeasure q I sigma2 mu ≤ (2 : ENNReal)⁻¹ • mu := by
  rw [balancedAcceptedStateMeasure_eq_half_smul]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA]
  calc
    (2 : ENNReal)⁻¹ *
        ∫⁻ x in A, accuracyGaussianRejectionAcceptance q I sigma2 x ∂mu ≤
      (2 : ENNReal)⁻¹ * ∫⁻ _x in A, (1 : ENNReal) ∂mu := by
        gcongr
        exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2 _
    _ = (2 : ENNReal)⁻¹ * mu A := by rw [setLIntegral_one]

theorem balancedRejectedStateMeasure_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) (mu : Measure (AmbientSpace q.n)) :
    balancedRejectedStateMeasure q I sigma2 mu ≤ mu := by
  unfold balancedRejectedStateMeasure
  apply Measure.le_iff.mpr
  intro A hA
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, 1 - balancedAccuracyGaussianAcceptance q I sigma2 x ∂mu) ≤
        ∫⁻ _x in A, (1 : ENNReal) ∂mu :=
      lintegral_mono fun _ => tsub_le_self
    _ = mu A := by rw [setLIntegral_one]

/-- A normalized balanced successful branch at stationarity is uniformly
warm for the same speedy stationary law. -/
theorem balancedAcceptedStationary_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    _root_.Arlib.IsWarm 16
      (Arlib.condOn
        (balancedAcceptedStateMeasure q I sigma2 pi) Set.univ) pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let branch := balancedAcceptedStateMeasure q I sigma2 pi
  have hp : ENNReal.ofReal (7 / 128 : ℝ) ≤ branch Set.univ := by
    simpa [K, delta, pi, branch] using
      balancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hp32 : (32 : ENNReal)⁻¹ ≤ branch Set.univ := by
    calc
      (32 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 32 : ℝ) := by
        rw [show (1 / 32 : ℝ) = (32 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal (7 / 128 : ℝ) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
      _ ≤ branch Set.univ := hp
  have hle : branch ≤ (2 : ENNReal)⁻¹ • pi := by
    simpa [branch] using balancedAcceptedStateMeasure_le_half_smul
      q I hsigma2 pi
  intro A hA
  rw [Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul]
  have hbranch : branch A ≤ (2 : ENNReal)⁻¹ * pi A := by
    simpa [Measure.smul_apply, smul_eq_mul] using Measure.le_iff.mp hle A hA
  calc
    (branch Set.univ)⁻¹ * branch A ≤
        (branch Set.univ)⁻¹ * ((2 : ENNReal)⁻¹ * pi A) :=
      mul_le_mul' le_rfl hbranch
    _ ≤ ((32 : ENNReal)⁻¹)⁻¹ *
        ((2 : ENNReal)⁻¹ * pi A) := by gcongr
    _ = 16 * pi A := by
      rw [← ofReal_one_half_balanced]
      rw [inv_inv]
      rw [← mul_assoc]
      have hcoeff : (32 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 16 := by
        rw [show (32 : ENNReal) = ENNReal.ofReal (32 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
        norm_num
      rw [hcoeff]

/-- A normalized balanced rejection branch at stationarity is `2`-warm. -/
theorem balancedRejectedStationary_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    _root_.Arlib.IsWarm 2
      (Arlib.condOn
        (balancedRejectedStateMeasure q I sigma2 pi) Set.univ) pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let branch := balancedRejectedStateMeasure q I sigma2 pi
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hp : (2 : ENNReal)⁻¹ ≤ branch Set.univ := by
    simpa [branch] using
      balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hle : branch ≤ pi := by
    simpa [branch] using balancedRejectedStateMeasure_le q I sigma2 pi
  intro A hA
  rw [Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul]
  have hbranch : branch A ≤ pi A := Measure.le_iff.mp hle A hA
  calc
    (branch Set.univ)⁻¹ * branch A ≤
        (branch Set.univ)⁻¹ * pi A := mul_le_mul' le_rfl hbranch
    _ ≤ ((2 : ENNReal)⁻¹)⁻¹ * pi A := by gcongr
    _ = 2 * pi A := by norm_num

/-- The normalized stationary rejection branch can be remixed with the
uniform warmness constant `2`, independently of its actual mass. -/
theorem mixesWithin_balancedRejectedStationary_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mixError : ℝ} (hmixError0 : 0 < mixError)
    (hmixError1 : mixError ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log 2 + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    let rejected := balancedRejectedStateMeasure q I sigma2 pi
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2))
      pi (Arlib.condOn rejected Set.univ) t (ENNReal.ofReal mixError) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let rejected := balancedRejectedStateMeasure q I sigma2 pi
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hrejectedLower : (2 : ENNReal)⁻¹ ≤ rejected Set.univ := by
    simpa [rejected] using
      balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hrejected0 : rejected Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le hrejectedLower
  have hrejectedTop : rejected Set.univ ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure (Arlib.condOn rejected Set.univ) :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  exact mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 (M := 2) (eps := mixError) (by norm_num)
    (by simpa [K, delta, pi, rejected] using
      balancedRejectedStationary_isWarm q I hsigma2)
    hmixError0 hmixError1 ht

/-- The normalized stationary accepted branch can seed the next sample with
the uniform warmness constant `16`. -/
theorem mixesWithin_balancedAcceptedStationary_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mixError : ℝ} (hmixError0 : 0 < mixError)
    (hmixError1 : mixError ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log 16 + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    let accepted := balancedAcceptedStateMeasure q I sigma2 pi
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2))
      pi (Arlib.condOn accepted Set.univ) t (ENNReal.ofReal mixError) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      accepted Set.univ := by
    simpa [accepted] using balancedAcceptedStateMeasure_mass_ge q I hsigma2
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 128 : ℝ)).trans_le
      hacceptedLower
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    have hle : accepted ≤ (2 : ENNReal)⁻¹ • pi := by
      simpa [accepted] using
        balancedAcceptedStateMeasure_le_half_smul q I hsigma2 pi
    exact ne_top_of_le_ne_top (by simp) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure (Arlib.condOn accepted Set.univ) :=
    Arlib.isProbabilityMeasure_condOn accepted haccepted0 hacceptedTop
  exact mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 (M := 16) (eps := mixError) (by norm_num)
    (by simpa [K, delta, pi, accepted] using
      balancedAcceptedStationary_isWarm q I hsigma2)
    hmixError0 hmixError1 ht

end ArlibCommunity.Algorithms.CV18
