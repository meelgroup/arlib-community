/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorEndpoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledInitialWarmStart

/-! # Complete scheduled phase endpoint replacement

This lifts the cap-aware one-transition exact-chance bound through every
remaining sample of a phase collector and then forgets the accumulated ratio.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open _root_.Arlib _root_.Arlib.MarkovChains

set_option maxHeartbeats 500000 in
section

theorem measurable_iteratedKernelLaw_const_from_initial
    {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (T : X → Measure S) (K : S → Measure S)
    (hT : Measurable T) (hK : Measurable K) :
    ∀ steps, Measurable fun x =>
      iteratedKernelLaw (fun _ => K) (T x) steps := by
  intro steps
  induction steps with
  | zero => exact hT
  | succ steps ih => exact Measure.measurable_bind' hK |>.comp ih

theorem bind_iteratedKernelLaw_const_from_initial
    {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (mu : Measure X) (T : X → Measure S) (K : S → Measure S)
    (hT : Measurable T) (hK : Measurable K) :
    ∀ steps,
      mu.bind (fun x => iteratedKernelLaw (fun _ => K) (T x) steps) =
        iteratedKernelLaw (fun _ => K) (mu.bind T) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hprefix : Measurable fun x =>
          iteratedKernelLaw (fun _ => K) (T x) steps :=
        measurable_iteratedKernelLaw_const_from_initial T K hT hK steps
      calc
        mu.bind (fun x =>
            iteratedKernelLaw (fun _ => K) (T x) (steps + 1)) =
          mu.bind (fun x =>
            (iteratedKernelLaw (fun _ => K) (T x) steps).bind K) := rfl
        _ = (mu.bind (fun x =>
            iteratedKernelLaw (fun _ => K) (T x) steps)).bind K :=
          (Measure.bind_bind hprefix.aemeasurable hK.aemeasurable).symm
        _ = (iteratedKernelLaw (fun _ => K) (mu.bind T) steps).bind K := by
          rw [ih]
        _ = iteratedKernelLaw (fun _ => K) (mu.bind T) (steps + 1) := rfl

/-- Starting from a probability law with the concrete scheduled warmness,
the retained endpoint after a complete nonempty collector is within one
corrected transition budget per sample of the normalized accepted target. -/
theorem map_bind_figureOneFinalScheduledTransitionCollectLaw_optionSnd_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ) (total : ℝ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) rho
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    let parameters := figureOneFinalScheduledBalancedParameters
    let cap := parameters.proposalCap q sigma2
    let stride := parameters.properStride q sigma2
    let retries := parameters.retryLimit q sigma2
    let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      ((rho.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries (samples + 1) total current).map optionSnd)
      (target.map some)
      ((samples + 1) • figureOneCorrectedTransitionBudget q) := by
  dsimp only
  let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let retries := figureOneFinalScheduledBalancedParameters.retryLimit q sigma2
  let T := scheduledBalancedAccuracyTransitionLawAux q I sigma2 cap stride retries
  let K := figureOneFinalScheduledRetainedOptionKernel q I sigma2
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
    (ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  have hT := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 cap stride retries
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hsigma2
  have hcollect := scheduledBalancedTransitionCollectLaw_measurable_and_probability
    q I hsigma2 hweight cap stride retries (samples + 1)
  have hcollectCurrent : Measurable fun current : AmbientSpace q.n =>
      scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride retries
        (samples + 1) total current := by
    change Measurable
      ((fun state : ℝ × AmbientSpace q.n =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
            retries (samples + 1) state.1 state.2) ∘
        fun current => (total, current))
    exact hcollect.1.comp (measurable_const.prodMk measurable_id)
  have hsource :
      ((rho.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries (samples + 1) total current).map optionSnd) =
        iteratedKernelLaw (fun _ => K) (rho.bind T) samples := by
    calc
      _ = rho.bind fun current =>
          (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
            retries (samples + 1) total current).map optionSnd :=
        map_bind_eq_bind_map_of_measurable rho hcollectCurrent
          measurable_optionSnd
      _ = rho.bind fun current =>
          iteratedKernelLaw (fun _ => K) (T current) samples := by
        apply Measure.bind_congr_right
        filter_upwards with current
        simpa [cap, stride, retries, T, K] using
          map_scheduledBalancedTransitionCollectLaw_optionSnd
            q I hsigma2 hweight samples total current
      _ = _ := bind_iteratedKernelLaw_const_from_initial rho T K
        (by simpa [T] using hT.1) (by simpa [K] using hK.1) samples
  have hfirst : MeasureLeUpTo (rho.bind T) (target.map some)
      (figureOneCorrectedTransitionBudget q) := by
    simpa [T, target, cap, stride, retries] using
      bind_figureOneFinalScheduledBalancedTransition_leUpTo_acceptedTarget
        q I hsigma2 rho hbaseWarm rho inferInstance
          ((IsWarm.refl rho).mono (by norm_num))
  have hiter := iterated_figureOneFinalScheduledRetainedOptionKernel_leUpTo
    q I hsigma2 (rho.bind T) hfirst samples
  rw [hsource]
  convert hiter using 1
  rw [succ_nsmul]
  exact add_comm _ _

/-- Retained endpoint kernel of a complete nonempty phase.  Its input and
output are both target-space points; internally the input is contracted to
the speedy space.  Failure is absorbing. -/
noncomputable def figureOneFinalScheduledCompleteRetainedKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (samples : ℕ) :
    Option (AmbientSpace q.n) → Measure (Option (AmbientSpace q.n))
  | none => Measure.dirac none
  | some current =>
      (scheduledBalancedTransitionCollectLaw q I sigma2 weight
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
        (samples + 1) 0 (accuracyScaleFactor q • current)).map optionSnd

theorem figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ) :
    Measurable (figureOneFinalScheduledCompleteRetainedKernel
      q I sigma2 weight samples) ∧
    ∀ state, IsProbabilityMeasure
      (figureOneFinalScheduledCompleteRetainedKernel
        q I sigma2 weight samples state) := by
  let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let retries := figureOneFinalScheduledBalancedParameters.retryLimit q sigma2
  have hcollect := scheduledBalancedTransitionCollectLaw_measurable_and_probability
    q I hsigma2 hweight cap stride retries (samples + 1)
  have hsome : Measurable fun current : AmbientSpace q.n =>
      (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
        retries (samples + 1) 0 (accuracyScaleFactor q • current)).map
          optionSnd := by
    apply (Measure.measurable_map _ measurable_optionSnd).comp
    change Measurable
      ((fun state : ℝ × AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries (samples + 1) state.1 state.2) ∘
        fun current => (0, accuracyScaleFactor q • current))
    exact hcollect.1.comp <| measurable_const.prodMk <|
      ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
        accuracyScaleFactor q).smul measurable_id)
  constructor
  · convert Measurable.optionElim
      (Measure.dirac (none : Option (AmbientSpace q.n))) hsome using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
    | some current =>
        let _ : IsProbabilityMeasure
            (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
              retries (samples + 1) 0 (accuracyScaleFactor q • current)) :=
          hcollect.2 _ _
        exact Measure.isProbabilityMeasure_map measurable_optionSnd.aemeasurable

/-- One chronological phase transports all prior exact-chance loss unchanged
and adds precisely one corrected transition budget for each collected sample.
The warm premise is imposed only on the contracted ideal live law; the actual
law may already contain an absorbing failure atom. -/
theorem bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ)
    (actualStart : Measure (Option (AmbientSpace q.n)))
    (goodRetained : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure goodRetained]
    {priorError : ENNReal}
    (hstart : MeasureLeUpTo actualStart (goodRetained.map some) priorError)
    (hgoodWarm : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (goodRetained.map fun x => accuracyScaleFactor q • x)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      (actualStart.bind
        (figureOneFinalScheduledCompleteRetainedKernel
          q I sigma2 weight samples))
      (target.map some)
      (priorError + (samples + 1) • figureOneCorrectedTransitionBudget q) := by
  dsimp only
  let G := figureOneFinalScheduledCompleteRetainedKernel
    q I sigma2 weight samples
  have hG := figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
    q I hsigma2 hweight samples
  have htransport := hstart.bind_same hG.1 hG.2
  let _ : IsProbabilityMeasure
      (goodRetained.map fun x => accuracyScaleFactor q • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hgoodPhase :=
    map_bind_figureOneFinalScheduledTransitionCollectLaw_optionSnd_leUpTo
      q I hsigma2 hweight samples 0
        (goodRetained.map fun x => accuracyScaleFactor q • x) hgoodWarm
  have hgoodEq :
      (goodRetained.map some).bind G =
        ((goodRetained.map fun x => accuracyScaleFactor q • x).bind
          fun current =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
              (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
              (samples + 1) 0 current).map optionSnd := by
    let collect : AmbientSpace q.n →
        Measure (Option (ℝ × AmbientSpace q.n)) := fun current =>
      scheduledBalancedTransitionCollectLaw q I sigma2 weight
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
        (samples + 1) 0 current
    let F : AmbientSpace q.n → Measure (Option (AmbientSpace q.n)) :=
      fun current => (collect current).map optionSnd
    have hcollect : Measurable collect := by
      change Measurable
        ((fun state : ℝ × AmbientSpace q.n =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight
            (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
            (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
            (samples + 1) state.1 state.2) ∘ fun current => (0, current))
      exact (scheduledBalancedTransitionCollectLaw_measurable_and_probability
        q I hsigma2 hweight
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
          (samples + 1)).1.comp
            (measurable_const.prodMk measurable_id)
    have hF : Measurable F := by
      exact (Measure.measurable_map _ measurable_optionSnd).comp hcollect
    have hGF : G ∘ some =
        F ∘ fun x : AmbientSpace q.n => accuracyScaleFactor q • x := by
      rfl
    calc
      (goodRetained.map some).bind G =
          goodRetained.bind (G ∘ some) :=
        map_bind_eq_bind_comp_state goodRetained measurable_some hG.1
      _ = goodRetained.bind
          (F ∘ fun x => accuracyScaleFactor q • x) := by
        rw [hGF]
      _ = (goodRetained.map fun x => accuracyScaleFactor q • x).bind F :=
        (map_bind_eq_bind_comp_state goodRetained (by fun_prop) hF).symm
      _ = ((goodRetained.map fun x => accuracyScaleFactor q • x).bind
          collect).map optionSnd :=
        (map_bind_eq_bind_map_of_measurable _ hcollect measurable_optionSnd).symm
  rw [hgoodEq] at htransport
  exact htransport.trans hgoodPhase

#print axioms map_bind_figureOneFinalScheduledTransitionCollectLaw_optionSnd_leUpTo
#print axioms bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo

end

end ArlibCommunity.Algorithms.CV18
