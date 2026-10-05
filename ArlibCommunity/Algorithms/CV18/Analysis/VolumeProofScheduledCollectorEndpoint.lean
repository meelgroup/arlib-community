/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetainedWarm

/-! # Endpoint projection of the scheduled phase collector -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 3000000 in
section

theorem measurable_iteratedKernelLaw_const_from_kernel
    {S : Type*} [MeasurableSpace S]
    (K : S → Measure S) (hK : Measurable K) :
    ∀ steps,
      Measurable fun state =>
        iteratedKernelLaw (fun _ => K) (K state) steps := by
  intro steps
  induction steps with
  | zero => exact hK
  | succ steps ih =>
      exact (Measure.measurable_bind' hK).comp ih

theorem iteratedKernelLaw_const_succ_eq_bind
    {S : Type*} [MeasurableSpace S]
    (K : S → Measure S) (hK : Measurable K) (mu : Measure S) :
    ∀ steps,
      iteratedKernelLaw (fun _ => K) mu (steps + 1) =
        mu.bind fun state =>
          iteratedKernelLaw (fun _ => K) (K state) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, ih]
      rw [Measure.bind_bind
        (measurable_iteratedKernelLaw_const_from_kernel K hK steps).aemeasurable
        hK.aemeasurable]
      rfl

noncomputable def scheduledBalancedRetainedOptionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    Option (AmbientSpace q.n) → Measure (Option (AmbientSpace q.n))
  | none => Measure.dirac none
  | some current =>
      scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit (accuracyScaleFactor q • current)

theorem scheduledBalancedRetainedOptionKernel_measurable
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride retryLimit : ℕ) :
    Measurable (scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
      properStride retryLimit) := by
  have hT := (scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride retryLimit).1
  have hsome : Measurable fun current : AmbientSpace q.n =>
      scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit (accuracyScaleFactor q • current) :=
    hT.comp <| (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  convert Measurable.optionElim
    (Measure.dirac (none : Option (AmbientSpace q.n))) hsome using 1
  funext state
  cases state <;> rfl

theorem iteratedKernelLaw_scheduledBalancedRetainedOptionKernel_none
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2)
    (proposalCap properStride retryLimit steps : ℕ) :
    iteratedKernelLaw (fun _ => scheduledBalancedRetainedOptionKernel q I sigma2
      proposalCap properStride retryLimit)
        (Measure.dirac (none : Option (AmbientSpace q.n))) steps =
      Measure.dirac none := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, ih]
      rw [Measure.dirac_bind
        (scheduledBalancedRetainedOptionKernel_measurable q I hsigma2 _ _ _)]
      rfl

/-- Forgetting the accumulated scalar from a nonempty collector run gives
exactly the retained optional-state Markov iteration. -/
theorem map_scheduledBalancedTransitionCollectLaw_optionSnd_generic
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (total : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit (samples + 1) total current).map optionSnd =
      iteratedKernelLaw
        (fun _ => scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
          properStride retryLimit)
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride retryLimit current) samples := by
  let T := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride retryLimit
  let K := scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
    properStride retryLimit
  have hK : Measurable K :=
    scheduledBalancedRetainedOptionKernel_measurable q I hsigma2 _ _ _
  have hout : Measurable (optionSnd :
      Option (ℝ × AmbientSpace q.n) → Option (AmbientSpace q.n)) :=
    measurable_optionSnd
  induction samples generalizing total current with
  | zero =>
      let tail : Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
        match result with
        | none => Measure.dirac none
        | some target => Measure.dirac (some
            (total + weight target,
              (accuracyScaleFactor q)⁻¹ • accuracyScaleFactor q • target))
      have htail : Measurable tail := by
        have hsome : Measurable fun target : AmbientSpace q.n =>
            Measure.dirac (some
              (total + weight target,
                (accuracyScaleFactor q)⁻¹ • accuracyScaleFactor q • target)) :=
          Measure.measurable_dirac.comp <| measurable_some.comp <|
            (measurable_const.add hweight).prodMk <|
              ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
                (accuracyScaleFactor q)⁻¹).smul <|
                  (measurable_const : Measurable fun _ : AmbientSpace q.n =>
                    accuracyScaleFactor q).smul measurable_id)
        convert Measurable.optionElim
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
        funext result
        cases result <;> rfl
      change ((T current).bind tail).map optionSnd = T current
      rw [map_bind_eq_bind_map_of_measurable _ htail hout]
      calc
        (T current).bind (fun result => (tail result).map optionSnd) =
            (T current).bind fun result => Measure.dirac result := by
          apply Measure.bind_congr_right
          filter_upwards with result
          cases result with
          | none =>
              rw [Measure.map_dirac' hout]
              rfl
          | some target =>
              rw [Measure.map_dirac' hout]
              simp only [optionSnd]
              congr 2
              rw [inv_smul_smul₀ (accuracyScaleFactor_pos q).ne']
        _ = T current := by
          exact Measure.bind_dirac
  | succ samples ih =>
      let tail : Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
        match result with
        | none => Measure.dirac none
        | some target =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit (samples + 1) (total + weight target)
                (accuracyScaleFactor q • target)
      have htail : Measurable tail := by
        have hstate : Measurable fun target : AmbientSpace q.n =>
            (total + weight target, accuracyScaleFactor q • target) :=
          (measurable_const.add hweight).prodMk <|
            (measurable_const : Measurable fun _ : AmbientSpace q.n =>
              accuracyScaleFactor q).smul measurable_id
        have hcollect :=
          (scheduledBalancedTransitionCollectLaw_measurable_and_probability
            q I hsigma2 hweight proposalCap properStride retryLimit
              (samples + 1)).1
        have hsome : Measurable fun target : AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit (samples + 1) (total + weight target)
                (accuracyScaleFactor q • target) := by
          change Measurable ((fun state : ℝ × AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit (samples + 1) state.1 state.2) ∘
                fun target =>
                  (total + weight target, accuracyScaleFactor q • target))
          exact hcollect.comp hstate
        convert Measurable.optionElim
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
        funext result
        cases result <;> rfl
      change ((T current).bind tail).map optionSnd = _
      rw [map_bind_eq_bind_map_of_measurable _ htail hout]
      have hpoint : (fun result : Option (AmbientSpace q.n) =>
          (tail result).map optionSnd) =
          fun result => iteratedKernelLaw (fun _ => K) (K result) samples := by
        funext result
        cases result with
        | none =>
            rw [show tail none = Measure.dirac none by rfl,
              Measure.map_dirac' hout]
            change Measure.dirac none = iteratedKernelLaw (fun _ =>
              scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
                properStride retryLimit) (Measure.dirac none) samples
            exact (iteratedKernelLaw_scheduledBalancedRetainedOptionKernel_none
              q I hsigma2 proposalCap properStride retryLimit samples).symm
        | some target =>
            simpa only [tail, K, scheduledBalancedRetainedOptionKernel] using
              ih (total := total + weight target)
                (current := accuracyScaleFactor q • target)
      rw [hpoint]
      rw [iteratedKernelLaw_const_succ_eq_bind K hK (T current) samples]

/-- Final-parameter specialization consumed by the retained-state warmness
induction. -/
theorem map_scheduledBalancedTransitionCollectLaw_optionSnd
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ) (total : ℝ) (current : AmbientSpace q.n) :
    let parameters := figureOneFinalScheduledBalancedParameters
    let cap := parameters.proposalCap q sigma2
    let stride := parameters.properStride q sigma2
    let retries := parameters.retryLimit q sigma2
    (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride retries
        (samples + 1) total current).map optionSnd =
      iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I sigma2)
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 cap stride
          retries current) samples := by
  dsimp only
  have hkernel : figureOneFinalScheduledRetainedOptionKernel q I sigma2 =
      scheduledBalancedRetainedOptionKernel q I sigma2
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2) := by
    funext state
    cases state <;> rfl
  rw [hkernel]
  exact map_scheduledBalancedTransitionCollectLaw_optionSnd_generic
    q I hsigma2 hweight
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
      samples total current

#print axioms map_scheduledBalancedTransitionCollectLaw_optionSnd

end

end ArlibCommunity.Algorithms.CV18
