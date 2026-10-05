/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorL2

/-!
# Support of a successful scheduled balanced transition

Acceptance is possible only when the contracted target belongs to the
scheduled phase body.  Consequently every successful finite-retry output is
supported on that body, independently of the starting point and of the
proper-block cutoff.  This is the support input needed to turn compactness of
the scheduled body into an executable phase-average `L²` bound.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- On the accepted branch, the scheduled rejection law can only return a
point in the scheduled phase body. -/
theorem scheduledBalancedAccuracyGaussianRejectionLaw_ae_true_mem_phaseBody
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedAccuracyGaussianRejectionLaw
        q I sigma2 current,
      result.1 = true → result.2 ∈ figureOneScheduledPhaseBody q I sigma2 := by
  let target : AmbientSpace q.n := (accuracyScaleFactor q)⁻¹ • current
  by_cases htarget : target ∈ figureOneScheduledPhaseBody q I sigma2
  · filter_upwards [scheduledBalancedAccuracyGaussianRejectionLaw_ae_snd
        q I sigma2 current] with result hresult
    intro _
    rw [hresult]
    exact htarget
  · have haccept :
        scheduledBalancedAccuracyGaussianAcceptance q I sigma2 current = 0 := by
      unfold scheduledBalancedAccuracyGaussianAcceptance
        scheduledAccuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem htarget, mul_zero]
    have hlaw :
        scheduledBalancedAccuracyGaussianRejectionLaw q I sigma2 current =
          Measure.dirac (false, target) := by
      simp [scheduledBalancedAccuracyGaussianRejectionLaw, haccept, target]
    rw [hlaw]
    simp

/-- Every successful output of the finite balanced retry transition belongs
to the scheduled phase body.  No hypothesis on the starting point is needed:
membership is enforced by the final acceptance indicator. -/
theorem scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    ∀ attempts current,
      ∀ᵐ result ∂scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride attempts current,
        match result with
        | none => True
        | some target => target ∈ figureOneScheduledPhaseBody q I sigma2 := by
  let good : Set (Option (AmbientSpace q.n)) :=
    {none} ∪ optionSomeEvent (figureOneScheduledPhaseBody q I sigma2)
  have hgood : MeasurableSet good :=
    measurableSet_option_none.union <| measurableSet_optionSomeEvent <|
      figureOneScheduledPhaseBody_measurable q I sigma2
  have hsupport : ∀ attempts current,
      ∀ᵐ result ∂scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride attempts current,
        result ∈ good := by
    intro attempts
    induction attempts with
    | zero =>
      intro current
      simp only [scheduledBalancedAccuracyTransitionLawAux]
      apply (ae_dirac_iff hgood).2
      exact Set.mem_union_left _ (Set.mem_singleton none)
    | succ attempts ih =>
      intro current
      letI : Fact (0 < sigma2) := ⟨hsigma2⟩
      let R := scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
      let tail : Option (ℝ × AmbientSpace q.n) →
          Measure (Option (AmbientSpace q.n)) := fun block =>
        match block with
        | none => Measure.dirac none
        | some block =>
            (R block.2).bind fun result =>
              if result.1 then Measure.dirac (some result.2)
              else scheduledBalancedAccuracyTransitionLawAux q I sigma2
                proposalCap properStride attempts block.2
      have htail : Measurable tail := by
        let nextResult : AmbientSpace q.n × (Bool × AmbientSpace q.n) →
            Measure (Option (AmbientSpace q.n)) := fun value =>
          if value.2.1 then Measure.dirac (some value.2.2)
          else scheduledBalancedAccuracyTransitionLawAux q I sigma2
            proposalCap properStride attempts value.1
        have hnextResult : Measurable nextResult := by
          dsimp only [nextResult]
          apply Measurable.ite
          · exact (measurable_fst.comp measurable_snd)
              (measurableSet_singleton true)
          · exact Measure.measurable_dirac.comp <|
              measurable_some.comp (measurable_snd.comp measurable_snd)
          · exact (scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
              q I hsigma2 proposalCap properStride attempts).1.comp measurable_fst
        let someTail : ℝ × AmbientSpace q.n →
            Measure (Option (AmbientSpace q.n)) := fun block =>
          (R block.2).bind fun result => nextResult (block.2, result)
        have hsomeTail : Measurable someTail := by
          exact measurable_measure_bind_param_variable
            (R.measurable.comp measurable_snd)
            (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
            (hnextResult.comp <|
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
        convert Measurable.optionElim (Measure.dirac none) hsomeTail using 1
        ext block
        cases block <;> rfl
      have hlaw :
          scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride (attempts + 1) current =
            (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
              properStride current).bind tail := by
        simp only [scheduledBalancedAccuracyTransitionLawAux]
        apply Measure.bind_congr_right
        filter_upwards with block
        cases block with
        | none => rfl
        | some block =>
            rcases block with ⟨ignored, mixed⟩
            rfl
      rw [hlaw]
      apply MeasureTheory.mem_ae_iff.mpr
      change ((scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
        properStride current).bind tail) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl htail.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with block
      cases block with
      | none =>
          change (Measure.dirac (none : Option (AmbientSpace q.n))) goodᶜ = 0
          rw [Measure.dirac_apply' _ hgood.compl]
          simp [good]
      | some block =>
          rcases block with ⟨ignored, mixed⟩
          change ((R mixed).bind fun result =>
            if result.1 then Measure.dirac (some result.2)
            else scheduledBalancedAccuracyTransitionLawAux q I sigma2
              proposalCap properStride attempts mixed) goodᶜ = 0
          rw [Measure.bind_apply hgood.compl]
          · apply lintegral_eq_zero_of_ae_eq_zero
            filter_upwards [
              scheduledBalancedAccuracyGaussianRejectionLaw_ae_true_mem_phaseBody
                q I sigma2 mixed] with result hresult
            split_ifs with haccepted
            · rw [Measure.dirac_apply' _ hgood.compl]
              have hsome : some result.2 ∈
                  optionSomeEvent (figureOneScheduledPhaseBody q I sigma2) := by
                exact hresult haccepted
              have hmem : some result.2 ∈ good :=
                Set.mem_union_right _ hsome
              simpa [Measure.dirac_apply' _ hgood.compl, hmem]
            · exact MeasureTheory.mem_ae_iff.mp (ih mixed)
          · have hbranch : Measurable fun result :
                Bool × AmbientSpace q.n =>
                if result.1 then Measure.dirac (some result.2)
                else scheduledBalancedAccuracyTransitionLawAux q I sigma2
                  proposalCap properStride attempts mixed := by
              apply Measurable.ite
              · exact measurable_fst (measurableSet_singleton true)
              · exact Measure.measurable_dirac.comp <|
                  measurable_some.comp measurable_snd
              · exact measurable_const
            exact hbranch.aemeasurable
  intro attempts current
  filter_upwards [hsupport attempts current] with result hresult
  cases result with
  | none => trivial
  | some target =>
      rcases hresult with hnone | hsome
      · simp at hnone
      · exact hsome

#print axioms scheduledBalancedAccuracyGaussianRejectionLaw_ae_true_mem_phaseBody
#print axioms scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody

end ArlibCommunity.Algorithms.CV18
