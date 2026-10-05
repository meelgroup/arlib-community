/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCapAllocation

/-! # Finite-retry approximation at scheduled geometry

This file transports the balanced finite-retry measure algebra to the
error-targeted body and proposal radius used by the scheduled implementation.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

/-- The scheduled balanced accept/reject decision, retaining the unscaled
speedy state on either branch. -/
noncomputable def scheduledBalancedAccuracyDecisionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (Bool × AmbientSpace q.n) :=
  let accept := scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current
  accept • Measure.dirac (true, current) +
    (1 - accept) • Measure.dirac (false, current)

theorem measurable_scheduledBalancedAccuracyDecisionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (scheduledBalancedAccuracyDecisionLaw q I sigma2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [scheduledBalancedAccuracyDecisionLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  have htrue : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal) (true, current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk measurable_id)
  have hfalse : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal) (false, current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk measurable_id)
  have hacc := measurable_scheduledBalancedAccuracyGaussianAcceptance
    q I sigma2
  exact (hacc.mul htrue).add ((measurable_const.sub hacc).mul hfalse)

noncomputable def scheduledBalancedAccuracyDecisionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Kernel (AmbientSpace q.n) (Bool × AmbientSpace q.n) :=
  ⟨scheduledBalancedAccuracyDecisionLaw q I sigma2,
    measurable_scheduledBalancedAccuracyDecisionLaw q I sigma2⟩

instance scheduledBalancedAccuracyDecisionKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    [Fact (0 < sigma2)] :
    IsMarkovKernel (scheduledBalancedAccuracyDecisionKernel q I sigma2) := by
  constructor
  intro current
  change IsProbabilityMeasure
    (scheduledBalancedAccuracyDecisionLaw q I sigma2 current)
  constructor
  simp only [scheduledBalancedAccuracyDecisionLaw,
    Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le]
  exact (scheduledBalancedAccuracyGaussianAcceptance_le_half
    q I Fact.out current).trans (by norm_num)

theorem scheduledBalancedAccuracyGaussianRejectionKernel_map_recover
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2 current).map
        (balancedRetryRecover q) =
      scheduledBalancedAccuracyDecisionKernel q I sigma2 current := by
  have hc0 : accuracyScaleFactor q ≠ 0 := (accuracyScaleFactor_pos q).ne'
  have hrecover : Measurable (balancedRetryRecover q) :=
    measurable_balancedRetryRecover q
  change (scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2 current).map
      (balancedRetryRecover q) =
    scheduledBalancedAccuracyDecisionLaw q I sigma2 current
  unfold scheduledBalancedAccuracyGaussianRejectionLaw
    scheduledBalancedAccuracyDecisionLaw
  rw [Measure.map_add _ _ hrecover, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hrecover, Measure.map_dirac' hrecover]
  have hcancel : accuracyScaleFactor q •
      ((accuracyScaleFactor q)⁻¹ • current) = current := by
    rw [← mul_smul, mul_inv_cancel₀ hc0, one_smul]
  change scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current •
        Measure.dirac (true, accuracyScaleFactor q •
          ((accuracyScaleFactor q)⁻¹ • current)) +
      (1 - scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current) •
        Measure.dirac (false, accuracyScaleFactor q •
          ((accuracyScaleFactor q)⁻¹ • current)) = _
  rw [hcancel]

theorem scheduledBalancedAccuracyGaussianRejectionLaw_ae_snd
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2 current,
      result.2 = (accuracyScaleFactor q)⁻¹ • current := by
  unfold scheduledBalancedAccuracyGaussianRejectionLaw
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (ae_eq_dirac Prod.snd) _
  · exact Measure.ae_smul_measure (ae_eq_dirac Prod.snd) _

/-- Continuation following a recovered scheduled decision. -/
noncomputable def scheduledBalancedAccuracyTransitionDecisionTail
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride attempts : ℕ) :
    Bool × AmbientSpace q.n → Measure (Option (AmbientSpace q.n)) :=
  fun result =>
    if result.1 then
      Measure.dirac (some ((accuracyScaleFactor q)⁻¹ • result.2))
    else
      scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride attempts result.2

theorem scheduledBalancedAccuracyTransitionDecisionTail_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) :
    Measurable (scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
      proposalCap properStride attempts) ∧
    ∀ result, IsProbabilityMeasure
      (scheduledBalancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
        properStride attempts result) := by
  let E := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride
  have hE := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride attempts
  constructor
  · unfold scheduledBalancedAccuracyTransitionDecisionTail
    apply Measurable.ite
    · exact measurable_fst (measurableSet_singleton true)
    · exact Measure.measurable_dirac.comp <|
        measurable_some.comp <|
          (measurable_const : Measurable fun _ : Bool × AmbientSpace q.n =>
            (accuracyScaleFactor q)⁻¹).smul measurable_snd
    · exact hE.1.comp measurable_snd
  · intro result
    unfold scheduledBalancedAccuracyTransitionDecisionTail
    split
    · infer_instance
    · exact hE.2 result.2

noncomputable def scheduledBalancedAccuracyTransitionOptionTail
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride attempts : ℕ) :
    Option (Bool × AmbientSpace q.n) →
      Measure (Option (AmbientSpace q.n))
  | none => Measure.dirac none
  | some result => scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
      proposalCap properStride attempts result

theorem scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) :
    Measurable (scheduledBalancedAccuracyTransitionOptionTail q I sigma2
      proposalCap properStride attempts) ∧
    ∀ result, IsProbabilityMeasure
      (scheduledBalancedAccuracyTransitionOptionTail q I sigma2 proposalCap
        properStride attempts result) := by
  have htail :=
    scheduledBalancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts
  constructor
  · convert Measurable.optionElim
      (Measure.dirac (none : Option (AmbientSpace q.n))) htail.1 using 1
    ext result
    cases result <;> rfl
  · intro result
    cases result with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
    | some result => exact htail.2 result

theorem scheduledBalancedAccuracyTransitionLawAux_succ_eq_recovered
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (current : AmbientSpace q.n) :
    scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride (attempts + 1) current =
      (((scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride current).map optionSnd).bind
        (optionKernel (scheduledBalancedAccuracyDecisionKernel q I sigma2))).bind
          (scheduledBalancedAccuracyTransitionOptionTail q I sigma2 proposalCap
            properStride attempts) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  let R := scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
  let D := scheduledBalancedAccuracyDecisionKernel q I sigma2
  let T := scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
    proposalCap properStride attempts
  let OT := scheduledBalancedAccuracyTransitionOptionTail q I sigma2
    proposalCap properStride attempts
  have hT :=
    (scheduledBalancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hOT :=
    (scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hoptionD := measurable_optionKernel D
  have hpipeline :
      (((B current).map optionSnd).bind (optionKernel D)).bind OT =
        (B current).bind fun block =>
          (optionKernel D (optionSnd block)).bind OT := by
    calc
      (((B current).map optionSnd).bind (optionKernel D)).bind OT =
          ((B current).map optionSnd).bind fun state =>
            (optionKernel D state).bind OT :=
        Measure.bind_bind hoptionD.aemeasurable hOT.aemeasurable
      _ = (B current).bind fun block =>
          (optionKernel D (optionSnd block)).bind OT :=
        Measure.map_bind_eq_bind_comp (B current) measurable_optionSnd <|
          measurable_measure_bind_param_variable hoptionD
            (fun state => optionKernel_isProbabilityMeasure D state)
            (hOT.comp measurable_snd)
  rw [hpipeline]
  simp only [scheduledBalancedAccuracyTransitionLawAux]
  apply Measure.bind_congr_right
  filter_upwards with block
  cases block with
  | none =>
      dsimp only [optionSnd, optionKernel]
      rw [Measure.dirac_bind hOT]
      rfl
  | some block =>
      rcases block with ⟨ignored, mixed⟩
      dsimp only [optionSnd, optionKernel]
      rw [Measure.map_bind_eq_bind_comp (D mixed) measurable_some hOT]
      calc
        (R mixed).bind (fun result =>
              if result.1 then Measure.dirac (some result.2)
              else scheduledBalancedAccuracyTransitionLawAux q I sigma2
                proposalCap properStride attempts mixed) =
            (R mixed).bind (fun result => T (balancedRetryRecover q result)) := by
          have hsecond : ∀ᵐ result ∂R mixed,
              result.2 = (accuracyScaleFactor q)⁻¹ • mixed := by
            exact scheduledBalancedAccuracyGaussianRejectionLaw_ae_snd
              q I sigma2 mixed
          apply Measure.bind_congr_right
          filter_upwards [hsecond] with result hsecondResult
          unfold balancedRetryRecover T
            scheduledBalancedAccuracyTransitionDecisionTail
          by_cases hresult : result.1 = true
          · simp only [hresult, if_true]
            have hc0 : accuracyScaleFactor q ≠ 0 :=
              (accuracyScaleFactor_pos q).ne'
            congr 2
            rw [← mul_smul, inv_mul_cancel₀ hc0, one_smul]
          · have hfalse : result.1 = false :=
              Bool.eq_false_of_not_eq_true hresult
            simp only [hfalse, Bool.false_eq_true, if_false]
            have hc0 : accuracyScaleFactor q ≠ 0 :=
              (accuracyScaleFactor_pos q).ne'
            congr 1
            rw [hsecondResult, ← mul_smul, mul_inv_cancel₀ hc0, one_smul]
        _ = ((R mixed).map (balancedRetryRecover q)).bind T :=
          (Measure.map_bind_eq_bind_comp (R mixed)
            (measurable_balancedRetryRecover q) hT).symm
        _ = (D mixed).bind T := by
          rw [scheduledBalancedAccuracyGaussianRejectionKernel_map_recover]
        _ = (D mixed).bind (fun result => OT (some result)) := by
          apply Measure.bind_congr_right
          filter_upwards with result
          rfl

/-- The scheduled stationary decision law splits into accepted and rejected
current-state submeasures. -/
theorem bind_scheduledBalancedAccuracyDecisionKernel_eq_branches
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    mu.bind (scheduledBalancedAccuracyDecisionKernel q I sigma2) =
      (scheduledBalancedAcceptedStateMeasure q I sigma2 mu).map
          (fun x => (true, x)) +
        (scheduledBalancedRejectedStateMeasure q I sigma2 mu).map
          (fun x => (false, x)) := by
  let accept := scheduledBalancedAccuracyGaussianAcceptance q I sigma2
  let truePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (true, x)
  let falsePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (false, x)
  have haccept : Measurable accept :=
    measurable_scheduledBalancedAccuracyGaussianAcceptance q I sigma2
  have hreject : Measurable fun x => 1 - accept x :=
    measurable_const.sub haccept
  have htrue : Measurable truePoint := measurable_const.prodMk measurable_id
  have hfalse : Measurable falsePoint := measurable_const.prodMk measurable_id
  have hKtrue : Measurable fun x =>
      accept x • Measure.dirac (truePoint x) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hS]
    exact haccept.mul <| (measurable_one.indicator hS).comp htrue
  have hKfalse : Measurable fun x =>
      (1 - accept x) • Measure.dirac (falsePoint x) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hS]
    exact hreject.mul <| (measurable_one.indicator hS).comp hfalse
  change mu.bind (fun x =>
      accept x • Measure.dirac (truePoint x) +
        (1 - accept x) • Measure.dirac (falsePoint x)) = _
  rw [measure_bind_add_right mu hKtrue hKfalse]
  rw [bind_smul_dirac_eq_withDensity_map mu haccept htrue,
    bind_smul_dirac_eq_withDensity_map mu hreject hfalse]
  rfl

/-- At scheduled stationarity, a recovered decision followed by its
continuation is the accepted target submeasure plus rejected recursion. -/
theorem bind_scheduledStationaryDecision_transitionTail_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (pi : Measure (AmbientSpace q.n)) :
    (pi.bind (scheduledBalancedAccuracyDecisionKernel q I sigma2)).bind
        (scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
          proposalCap properStride attempts) =
      ((scheduledBalancedAcceptedStateMeasure q I sigma2 pi).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some +
        (scheduledBalancedRejectedStateMeasure q I sigma2 pi).bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts) := by
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
  let truePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (true, x)
  let falsePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (false, x)
  let T := scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
    proposalCap properStride attempts
  let E := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride attempts
  have hT :=
    (scheduledBalancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hE :=
    (scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have htrue : Measurable truePoint := measurable_const.prodMk measurable_id
  have hfalse : Measurable falsePoint := measurable_const.prodMk measurable_id
  rw [bind_scheduledBalancedAccuracyDecisionKernel_eq_branches]
  rw [measure_bind_add_left _ _ hT]
  rw [Measure.map_bind_eq_bind_comp accepted htrue hT,
    Measure.map_bind_eq_bind_comp rejected hfalse hT]
  have haccept : accepted.bind (fun x => T (truePoint x)) =
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some := by
    change accepted.bind (fun x =>
        Measure.dirac (some ((accuracyScaleFactor q)⁻¹ • x))) = _
    rw [Measure.bind_dirac_eq_map]
    · rw [Measure.map_map]
      · rfl
      · exact measurable_some
      · exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          (accuracyScaleFactor q)⁻¹).smul measurable_id
    · exact measurable_some.comp <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hrejected : rejected.bind (fun x => T (falsePoint x)) =
      rejected.bind E := by
    apply Measure.bind_congr_right
    filter_upwards with x
    rfl
  rw [haccept, hrejected]

theorem bind_scheduledStationaryOptionDecision_transitionTail_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (pi : Measure (AmbientSpace q.n)) :
    (((pi.map some).bind
        (optionKernel (scheduledBalancedAccuracyDecisionKernel q I sigma2))).bind
      (scheduledBalancedAccuracyTransitionOptionTail q I sigma2 proposalCap
        properStride attempts)) =
      (pi.bind (scheduledBalancedAccuracyDecisionKernel q I sigma2)).bind
        (scheduledBalancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
          properStride attempts) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let D := scheduledBalancedAccuracyDecisionKernel q I sigma2
  let T := scheduledBalancedAccuracyTransitionDecisionTail q I sigma2
    proposalCap properStride attempts
  let OT := scheduledBalancedAccuracyTransitionOptionTail q I sigma2
    proposalCap properStride attempts
  have hD := D.measurable
  have hOD := measurable_optionKernel D
  have hT :=
    (scheduledBalancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hOT :=
    (scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  calc
    (((pi.map some).bind (optionKernel D)).bind OT) =
        (pi.map some).bind fun state => (optionKernel D state).bind OT :=
      Measure.bind_bind hOD.aemeasurable hOT.aemeasurable
    _ = pi.bind (fun x => (optionKernel D (some x)).bind OT) :=
      Measure.map_bind_eq_bind_comp pi measurable_some <|
        measurable_measure_bind_param_variable hOD
          (fun state => optionKernel_isProbabilityMeasure D state)
          (hOT.comp measurable_snd)
    _ = pi.bind (fun x => (D x).bind T) := by
      apply Measure.bind_congr_right
      filter_upwards with x
      dsimp only [optionKernel]
      rw [Measure.map_bind_eq_bind_comp (D x) measurable_some hOT]
      apply Measure.bind_congr_right
      filter_upwards with result
      rfl
    _ = (pi.bind D).bind T :=
      (Measure.bind_bind hD.aemeasurable hT.aemeasurable).symm

theorem bind_scheduledBalancedAccuracyTransitionLawAux_succ_eq_pipeline
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) :
    rho.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride (attempts + 1)) =
      ((((rho.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd).bind
          (optionKernel
            (scheduledBalancedAccuracyDecisionKernel q I sigma2))).bind
        (scheduledBalancedAccuracyTransitionOptionTail q I sigma2 proposalCap
          properStride attempts)) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  let D := scheduledBalancedAccuracyDecisionKernel q I sigma2
  let OT := scheduledBalancedAccuracyTransitionOptionTail q I sigma2
    proposalCap properStride attempts
  have hB := B.measurable
  have hOD := measurable_optionKernel D
  have hOT :=
    (scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  let BM : AmbientSpace q.n → Measure (Option (AmbientSpace q.n)) :=
    fun current => (B current).map optionSnd
  have hBM : Measurable BM := by
    exact measurable_measure_map_param_variable hB
      (fun current => IsMarkovKernel.isProbabilityMeasure current)
      (measurable_optionSnd.comp measurable_snd)
  have hBMprob : ∀ current, IsProbabilityMeasure (BM current) := by
    intro current
    dsimp only [BM]
    exact Measure.isProbabilityMeasure_map measurable_optionSnd.aemeasurable
  let BD : AmbientSpace q.n →
      Measure (Option (Bool × AmbientSpace q.n)) :=
    fun current => (BM current).bind (optionKernel D)
  have hBD : Measurable BD := by
    exact measurable_measure_bind_param_variable hBM hBMprob
      (hOD.comp measurable_snd)
  have hendpoint : rho.bind BM = (rho.bind B).map optionSnd := by
    calc
      rho.bind BM = rho.bind (fun current =>
          (B current).bind fun block => Measure.dirac (optionSnd block)) := by
        apply Measure.bind_congr_right
        filter_upwards with current
        dsimp only [BM]
        rw [Measure.bind_dirac_eq_map]
        exact measurable_optionSnd
      _ = (rho.bind B).bind (fun block => Measure.dirac (optionSnd block)) :=
        (Measure.bind_bind hB.aemeasurable
          (Measure.measurable_dirac.comp measurable_optionSnd).aemeasurable).symm
      _ = (rho.bind B).map optionSnd :=
        Measure.bind_dirac_eq_map _ measurable_optionSnd
  have hpoint : rho.bind
      (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride (attempts + 1)) =
      rho.bind (fun current =>
        ((((B current).map optionSnd).bind (optionKernel D)).bind OT)) := by
    apply Measure.bind_congr_right
    filter_upwards with current
    exact scheduledBalancedAccuracyTransitionLawAux_succ_eq_recovered
      q I hsigma2 proposalCap properStride attempts current
  rw [hpoint]
  calc
    rho.bind (fun current =>
        ((((B current).map optionSnd).bind (optionKernel D)).bind OT)) =
      (rho.bind BD).bind OT := by
        change rho.bind (fun current => (BD current).bind OT) = _
        exact (Measure.bind_bind hBD.aemeasurable hOT.aemeasurable).symm
    _ = ((rho.bind BM).bind (optionKernel D)).bind OT := by
      rw [Measure.bind_bind hBM.aemeasurable hOD.aemeasurable]
    _ = ((((rho.bind B).map optionSnd).bind (optionKernel D)).bind OT) := by
      rw [hendpoint]

/-- A scheduled finite retry is dominated by the exact stationary branch
recurrence with precisely the endpoint block error. -/
theorem bind_scheduledBalancedAccuracyTransitionLawAux_succ_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    {delta : ENNReal}
    (hblock : MeasureLeUpTo
      ((rho.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) delta) :
    MeasureLeUpTo
      (rho.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
        proposalCap properStride (attempts + 1)))
      (((scheduledBalancedAcceptedStateMeasure q I sigma2 pi).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some +
        (scheduledBalancedRejectedStateMeasure q I sigma2 pi).bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts)) delta := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let D := scheduledBalancedAccuracyDecisionKernel q I sigma2
  let OT := scheduledBalancedAccuracyTransitionOptionTail q I sigma2
    proposalCap properStride attempts
  have hfirst := hblock.bind_same (measurable_optionKernel D)
    (fun state => optionKernel_isProbabilityMeasure D state)
  have hsecond := hfirst.bind_same
    (scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
    (scheduledBalancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).2
  rw [← bind_scheduledBalancedAccuracyTransitionLawAux_succ_eq_pipeline
    q I hsigma2 proposalCap properStride attempts rho] at hsecond
  rw [bind_scheduledStationaryOptionDecision_transitionTail_eq
    q I hsigma2 proposalCap properStride attempts pi] at hsecond
  rw [bind_scheduledStationaryDecision_transitionTail_eq
    q I hsigma2 proposalCap properStride attempts pi] at hsecond
  exact hsecond

/-- Starting from the normalized scheduled stationary rejection branch,
finite retries are dominated by the normalized scheduled accepted target. -/
theorem bind_scheduledBalancedRejectedTransition_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {delta : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hblock :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) delta) :
    let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
    let rejectMass := rejected Set.univ
    let rejectedProb := Arlib.condOn rejected Set.univ
    ∀ attempts,
      MeasureLeUpTo
        (rejectedProb.bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts))
        ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
          q I sigma2 pi).map some)
        (balancedRetryError delta rejectMass attempts) := by
  dsimp only
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
  let acceptMass := accepted Set.univ
  let rejectMass := rejected Set.univ
  let rejectedProb := Arlib.condOn rejected Set.univ
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    q I sigma2 pi
  let targetSome := target.map some
  let E := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride
  have hrejected0 : rejectMass ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le
      (by simpa [rejectMass, rejected] using hrejectedLower)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        scheduledBalancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass, accepted, rejected] using
      scheduledBalancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
  have hacceptedTarget :
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some =
        acceptMass • targetSome := by
    have hbase := scheduledBalancedAcceptedTargetSubmeasure_eq_mass_smul
      q I hsigma2 pi hacceptedLower
    change (accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some = _
    rw [hbase, Measure.map_smul]
  have hrejectedNormalize : rejected = rejectMass • rejectedProb := by
    exact measure_eq_mass_smul_condOn_univ rejected hrejected0 hrejectedTop
  intro attempts
  induction attempts with
  | zero =>
      change MeasureLeUpTo
        (rejectedProb.bind fun _ =>
          Measure.dirac (none : Option (AmbientSpace q.n))) targetSome 1
      rw [Measure.bind_const, measure_univ, one_smul]
      refine ⟨Measure.dirac none, ?_, by simp⟩
      apply Measure.le_iff.mpr
      intro S hS
      rw [Measure.add_apply]
      exact le_add_left le_rfl
  | succ attempts ih =>
      have hone :=
        bind_scheduledBalancedAccuracyTransitionLawAux_succ_leUpTo_stationary
          q I hsigma2 proposalCap properStride attempts rejectedProb pi hblock
      have hscaled := ih.smul (c := rejectMass)
      have hrejectedBind :
          rejected.bind (E attempts) =
            rejectMass • (rejectedProb.bind (E attempts)) := by
        rw [hrejectedNormalize, Measure.bind_smul]
      rw [← hrejectedBind] at hscaled
      have hadd := hscaled.add_left
        ((accepted.map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some)
      have htargetSum :
          acceptMass • targetSome + rejectMass • targetSome = targetSome := by
        rw [← add_smul, hmass, one_smul]
      have hresult := hone.trans hadd
      rw [hacceptedTarget, htargetSum] at hresult
      simpa only [balancedRetryError] using hresult

/-- The complete scheduled finite transition from an arbitrary first-block
law is dominated by the scheduled accepted target. -/
theorem bind_scheduledBalancedTransition_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) firstError)
    (hretryBlock :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    MeasureLeUpTo
      (rho.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map some)
      (firstError +
        scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ *
          balancedRetryError retryError
            (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
            attempts) := by
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
  let acceptMass := accepted Set.univ
  let rejectMass := rejected Set.univ
  let rejectedProb := Arlib.condOn rejected Set.univ
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    q I sigma2 pi
  let targetSome := target.map some
  let E := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride
  have hrejected0 : rejectMass ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le
      (by simpa [rejectMass, rejected] using hrejectedLower)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        scheduledBalancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass, accepted, rejected] using
      scheduledBalancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
  have hacceptedTarget :
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some =
        acceptMass • targetSome := by
    have hbase := scheduledBalancedAcceptedTargetSubmeasure_eq_mass_smul
      q I hsigma2 pi hacceptedLower
    change (accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some = _
    rw [hbase, Measure.map_smul]
  have hrejectedNormalize : rejected = rejectMass • rejectedProb :=
    measure_eq_mass_smul_condOn_univ rejected hrejected0 hrejectedTop
  have hretry := bind_scheduledBalancedRejectedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride pi hacceptedLower hrejectedLower
      hretryBlock attempts
  have hscaled := hretry.smul (c := rejectMass)
  have hrejectedBind : rejected.bind (E attempts) =
      rejectMass • (rejectedProb.bind (E attempts)) := by
    rw [hrejectedNormalize, Measure.bind_smul]
  rw [← hrejectedBind] at hscaled
  have hadd := hscaled.add_left
    ((accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some)
  have hone :=
    bind_scheduledBalancedAccuracyTransitionLawAux_succ_leUpTo_stationary
      q I hsigma2 proposalCap properStride attempts rho pi hfirstBlock
  have hresult := hone.trans hadd
  have htargetSum :
      acceptMass • targetSome + rejectMass • targetSome = targetSome := by
    rw [← add_smul, hmass, one_smul]
  rw [hacceptedTarget, htargetSum] at hresult
  simpa [rejectMass, rejected, targetSome, target] using hresult

theorem scheduledBalancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    IsProbabilityMeasure
      (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi) := by
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let acceptedTarget := accepted.map scale
  have hscale : Measurable scale := by
    dsimp only [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 128 : ℝ)).trans_le
      (by simpa [accepted] using hacceptedLower)
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    have hle := scheduledBalancedAcceptedStateMeasure_le_half_smul
      q I hsigma2 pi
    exact ne_top_of_le_ne_top (by simp) <|
      Measure.le_iff'.mp hle Set.univ
  have htargetMass : acceptedTarget Set.univ = accepted Set.univ := by
    dsimp only [acceptedTarget]
    rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
  have htarget0 : acceptedTarget Set.univ ≠ 0 := by
    rw [htargetMass]
    exact haccepted0
  have htargetTop : acceptedTarget Set.univ ≠ ⊤ := by
    rw [htargetMass]
    exact hacceptedTop
  change IsProbabilityMeasure (Arlib.condOn acceptedTarget Set.univ)
  exact Arlib.isProbabilityMeasure_condOn acceptedTarget htarget0 htargetTop

/-- Total-variation form of the scheduled finite-retry domination. -/
theorem bind_scheduledBalancedTransition_tvLe_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) firstError)
    (hretryBlock :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    Arlib.TVLe
      (rho.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map some)
      (firstError +
        scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ *
          balancedRetryError retryError
            (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
            attempts) := by
  let K := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  have hK := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.1.aemeasurable (ae_of_all _ hK.2)
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    q I sigma2 pi
  let _ : IsProbabilityMeasure target :=
    scheduledBalancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure (target.map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hdom := bind_scheduledBalancedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride attempts rho pi
      hacceptedLower hrejectedLower hfirstBlock hretryBlock
  change Arlib.TVLe (rho.bind K) (target.map some) _
  exact hdom.to_tvLe

/-- Cap-aware corrected allocation: one cap budget and one mixing budget are
charged to every scheduled block, then finite retries and the scheduled KLS
target correction still fit the per-transition budget. -/
theorem bind_scheduledBalancedTransition_tvLe_truncatedGaussian_corrected
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hfirstBlock :
      let K := figureOneScheduledPhaseBody q I sigma2
      let delta := figureOneScheduledProposalRadius q sigma2
      let pi := ellGaussianProb K delta sigma2
      MeasureLeUpTo
        ((rho.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts))
    (hretryBlock :
      let K := figureOneScheduledPhaseBody q I sigma2
      let delta := figureOneScheduledProposalRadius q sigma2
      let pi := ellGaussianProb K delta sigma2
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts))
    (hretryTail :
      let K := figureOneScheduledPhaseBody q I sigma2
      let delta := figureOneScheduledProposalRadius q sigma2
      let pi := ellGaussianProb K delta sigma2
      (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ) ^
          (attempts + 1) ≤ figureOneCorrectedRetryTailBudget q) :
    Arlib.TVLe
      (rho.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q) := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let rejectMass :=
    scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 := by
    dsimp [K]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ := by
    dsimp [K]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted := scheduledBalancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hrejected :=
    scheduledBalancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hraw := bind_scheduledBalancedTransition_tvLe_acceptedTarget
    q I hsigma2 proposalCap properStride attempts rho pi
      (by simpa [K, delta, pi] using haccepted)
      hrejected hfirstBlock hretryBlock
  have htarget := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I hsigma2
  have hcombined := hraw.trans <| htarget.map measurable_some
  apply hcombined.mono
  have hreject : rejectMass ≤ 1 := by
    dsimp only [rejectMass]
    exact (scheduledBalancedRejectedStateMeasure_mass_le
      q I hsigma2 pi (by simpa [K, delta, pi] using haccepted)).trans
        (by norm_num)
  exact scheduledBalancedTransitionError_with_cap_le_budget q hreject
    (by simpa [K, delta, pi, rejectMass] using hretryTail)

#print axioms bind_scheduledBalancedAccuracyTransitionLawAux_succ_leUpTo_stationary
#print axioms bind_scheduledBalancedRejectedTransition_leUpTo_acceptedTarget
#print axioms bind_scheduledBalancedTransition_leUpTo_acceptedTarget
#print axioms bind_scheduledBalancedTransition_tvLe_acceptedTarget
#print axioms bind_scheduledBalancedTransition_tvLe_truncatedGaussian_corrected

end ArlibCommunity.Algorithms.CV18
