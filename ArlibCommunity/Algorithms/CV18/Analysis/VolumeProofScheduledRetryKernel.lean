/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCost

/-! # Measure kernels for schedule-targeted proper blocks and retries -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The one-sample capped proper-speedy block at scheduled body and proposal
radius.  Its scalar observation is deliberately zero; the rejection kernel
subsequently creates the accepted target coordinate. -/
noncomputable def scheduledBalancedAccuracyRetryBlockKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) :
    Kernel (AmbientSpace q.n) (Option (ℝ × AmbientSpace q.n)) where
  toFun current :=
    cappedProperCollectLaw
      (Arlib.MarkovChains.lazyProperProposalGaussianAux
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
      (fun _ => 0) proposalCap properStride 1 current
  measurable' := by
    let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    change Measurable fun current =>
      cappedProperCollectLaw Q (fun _ => 0) proposalCap properStride 1 current
    unfold cappedProperCollectLaw
    exact (cappedProperCollectLawAux_measurable_and_probability Q
      measurable_const properStride proposalCap properStride 1).1.comp
        (measurable_const.prodMk measurable_id)

instance scheduledBalancedAccuracyRetryBlockKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) [Fact (0 < sigma2)] :
    IsMarkovKernel
      (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
        properStride) := by
  constructor
  intro current
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  change IsProbabilityMeasure
    (cappedProperCollectLaw Q (fun _ => 0) proposalCap properStride 1 current)
  unfold cappedProperCollectLaw
  exact (cappedProperCollectLawAux_measurable_and_probability Q
    measurable_const properStride proposalCap properStride 1).2 0 current

/-- Full finite balanced collector law at scheduled geometry. -/
noncomputable def scheduledBalancedAccuracyRetryCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (balancedRetryCollectLawAux
    (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
      properStride)
    (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2)
    weight retryLimit retryLimit samples 0 current).map
      (balancedAccuracyRetryOutput q)

/-- Endpoint law of one scheduled finite balanced transition. -/
noncomputable def scheduledBalancedAccuracyTransitionLawAux
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) :
    ℕ → AmbientSpace q.n → Measure (Option (AmbientSpace q.n))
  | 0, _ => Measure.dirac none
  | attempts + 1, current =>
      (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
        properStride current).bind fun block =>
        match block with
        | none => Measure.dirac none
        | some (_, mixed) =>
            (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
              mixed).bind fun result =>
                if result.1 then Measure.dirac (some result.2)
                else scheduledBalancedAccuracyTransitionLawAux q I sigma2
                  proposalCap properStride attempts mixed

theorem scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    ∀ attempts,
      Measurable (scheduledBalancedAccuracyTransitionLawAux q I sigma2
        proposalCap properStride attempts) ∧
      ∀ current, IsProbabilityMeasure
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride attempts current) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
    properStride
  let R := scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2
  intro attempts
  induction attempts with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp measurable_const
      · intro current
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
  | succ attempts ih =>
      let nextResult : AmbientSpace q.n × (Bool × AmbientSpace q.n) →
          Measure (Option (AmbientSpace q.n)) := fun value =>
        if value.2.1 then Measure.dirac (some value.2.2)
        else scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride attempts value.1
      have hnextResult : Measurable nextResult := by
        dsimp only [nextResult]
        apply Measurable.ite
        · exact (measurable_fst.comp measurable_snd)
            (measurableSet_singleton true)
        · exact Measure.measurable_dirac.comp <|
            measurable_some.comp (measurable_snd.comp measurable_snd)
        · exact ih.1.comp measurable_fst
      let someTail : ℝ × AmbientSpace q.n →
          Measure (Option (AmbientSpace q.n)) := fun block =>
        (R block.2).bind fun result => nextResult (block.2, result)
      have hsomeTail : Measurable someTail := by
        dsimp only [someTail]
        exact measurable_measure_bind_param_variable
          (R.measurable.comp measurable_snd)
          (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
          (hnextResult.comp <|
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      let tail : Option (ℝ × AmbientSpace q.n) →
          Measure (Option (AmbientSpace q.n)) := fun block =>
        match block with
        | none => Measure.dirac none
        | some block => someTail block
      have htail : Measurable tail := by
        dsimp only [tail]
        convert Measurable.optionElim (Measure.dirac none) hsomeTail using 1
        ext block
        cases block <;> rfl
      have hlaw :
          scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride (attempts + 1) =
            fun current => (B current).bind tail := by
        funext current
        simp only [scheduledBalancedAccuracyTransitionLawAux]
        apply Measure.bind_congr_right
        filter_upwards with block
        cases block with
        | none => rfl
        | some block =>
            rcases block with ⟨ignored, mixed⟩
            dsimp only [tail, someTail]
      constructor
      · rw [hlaw]
        exact measurable_measure_bind_param_variable B.measurable
          (fun current => IsMarkovKernel.isProbabilityMeasure current)
          (htail.comp measurable_snd)
      · intro current
        rw [congrFun hlaw current]
        apply MeasureTheory.isProbabilityMeasure_bind htail.aemeasurable
        filter_upwards with block
        cases block with
        | none =>
            change IsProbabilityMeasure
              (Measure.dirac (none : Option (AmbientSpace q.n)))
            infer_instance
        | some block =>
            rcases block with ⟨ignored, mixed⟩
            dsimp only [tail, someTail]
            apply MeasureTheory.isProbabilityMeasure_bind
              (hnextResult.comp
                (measurable_const.prodMk measurable_id)).aemeasurable
            filter_upwards with result
            change IsProbabilityMeasure
              (if result.1 then Measure.dirac (some result.2)
               else scheduledBalancedAccuracyTransitionLawAux q I sigma2
                proposalCap properStride attempts mixed)
            cases hresult : result.1
            · simpa only [hresult, Bool.false_eq_true, if_false] using
                ih.2 mixed
            · simp only [hresult, if_true]
              infer_instance

#print axioms scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability

end ArlibCommunity.Algorithms.CV18
