/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation

/-!
# Exact history law for the executable balanced-retry collector

The finite transition law returns a target-space observation.  Its retained
speedy state is nevertheless not lost: multiplication by
`accuracyScaleFactor` recovers it.  This file iterates that recovered-state
transition and relates the resulting phase estimator to the executable
balanced-retry collector.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Iterate the finite accepted-target transition while accumulating a phase
observable.  The state carried between calls is the unscaled speedy state;
the state exposed at the end is the corresponding target-space point, exactly
as in `balancedAccuracyRetryOutput`. -/
noncomputable def balancedAccuracyTransitionCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℝ → AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n))
  | 0, total, current =>
      Measure.dirac (some (total, (accuracyScaleFactor q)⁻¹ • current))
  | samples + 1, total, current =>
      (balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
        retryLimit current).bind fun result =>
          match result with
          | none => Measure.dirac none
          | some target =>
              balancedAccuracyTransitionCollectLaw q I sigma2 weight
                proposalCap properStride retryLimit samples
                (total + weight target) (accuracyScaleFactor q • target)

theorem balancedAccuracyTransitionCollectLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples,
      Measurable (fun state : ℝ × AmbientSpace q.n =>
        balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples state.1 state.2) ∧
      ∀ total current, IsProbabilityMeasure
        (balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples total current) := by
  have htransition :=
    balancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  intro samples
  induction samples with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp <|
          measurable_some.comp <| measurable_fst.prodMk <|
            (measurable_const : Measurable fun _ : ℝ × AmbientSpace q.n =>
              (accuracyScaleFactor q)⁻¹).smul measurable_snd
      · intro total current
        change IsProbabilityMeasure
          (Measure.dirac
            (some (total, (accuracyScaleFactor q)⁻¹ • current)))
        infer_instance
  | succ samples ih =>
      let tail : (ℝ × AmbientSpace q.n) ×
          Option (AmbientSpace q.n) →
            Measure (Option (ℝ × AmbientSpace q.n)) := fun value =>
        match value.2 with
        | none => Measure.dirac none
        | some target =>
            balancedAccuracyTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (value.1.1 + weight target)
              (accuracyScaleFactor q • target)
      have hsome : Measurable fun value :
          (ℝ × AmbientSpace q.n) × AmbientSpace q.n =>
            balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples
              (value.1.1 + weight value.2)
              (accuracyScaleFactor q • value.2) := by
        exact ih.1.comp <|
          ((measurable_fst.comp measurable_fst).add
            (hweight.comp measurable_snd)).prodMk <|
              (measurable_const : Measurable fun _ :
                (ℝ × AmbientSpace q.n) × AmbientSpace q.n =>
                  accuracyScaleFactor q).smul measurable_snd
      have htail : Measurable tail := by
        dsimp only [tail]
        convert Measurable.optionElimParam
          (noneValue := fun _ : ℝ × AmbientSpace q.n =>
            Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
          (someValue := fun value =>
            balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples
              (value.1.1 + weight value.2)
              (accuracyScaleFactor q • value.2))
          (Measure.measurable_dirac.comp measurable_const) hsome using 1
        ext value
        cases value.2 <;> rfl
      have hlaw : (fun state : ℝ × AmbientSpace q.n =>
          balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit (samples + 1) state.1 state.2) =
          fun state =>
            (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride retryLimit state.2).bind
                (fun result => tail (state, result)) := by
        funext state
        simp only [balancedAccuracyTransitionCollectLaw]
        apply Measure.bind_congr_right
        filter_upwards with result
        cases result <;> rfl
      constructor
      · rw [hlaw]
        exact measurable_measure_bind_param_variable
          (htransition.1.comp measurable_snd)
          (fun state => htransition.2 state.2) htail
      · intro total current
        rw [congrFun hlaw (total, current)]
        let _ : IsProbabilityMeasure
            (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride retryLimit current) := htransition.2 current
        apply MeasureTheory.isProbabilityMeasure_bind
          (htail.comp (measurable_const.prodMk measurable_id)).aemeasurable
        filter_upwards with result
        cases result with
        | none =>
            change IsProbabilityMeasure
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
            infer_instance
        | some target => exact ih.2 _ _

/-- The same collection law with an independently specified retry budget for
the first outstanding sample.  Later samples restart with `retryLimit`, as the
executable collector does. -/
noncomputable def balancedAccuracyTransitionCollectLawFirst
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit attempts : ℕ) :
    ℕ → ℝ → AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n))
  | 0, total, current =>
      Measure.dirac (some (total, (accuracyScaleFactor q)⁻¹ • current))
  | samples + 1, total, current =>
      (balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
        attempts current).bind fun result =>
          match result with
          | none => Measure.dirac none
          | some target =>
              balancedAccuracyTransitionCollectLaw q I sigma2 weight
                proposalCap properStride retryLimit samples
                (total + weight target) (accuracyScaleFactor q • target)

theorem balancedAccuracyTransitionCollectLawFirst_full
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (total : ℝ) (current : AmbientSpace q.n) :
    balancedAccuracyTransitionCollectLawFirst q I sigma2 weight proposalCap
        properStride retryLimit retryLimit samples total current =
      balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples total current := by
  cases samples <;> rfl

/-- Mapping the internal executable collector state to its public output is
exactly iteration of the accepted-target transition with recovered retained
states.  This is the missing multi-sample law bridge: no independence or
mixing approximation is used here. -/
theorem map_balancedRetryCollectLawAux_eq_transitionCollectLawFirst
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples attempts total current,
      (balancedRetryCollectLawAux
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)
        (balancedAccuracyGaussianRejectionKernel q I sigma2)
        weight retryLimit attempts samples total current).map
          (balancedAccuracyRetryOutput q) =
        balancedAccuracyTransitionCollectLawFirst q I sigma2 weight
          proposalCap properStride retryLimit attempts samples total current := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
  let R := balancedAccuracyGaussianRejectionKernel q I sigma2
  let Out := balancedAccuracyRetryOutput q
  have hOut : Measurable Out := measurable_balancedAccuracyRetryOutput q
  have hAux := balancedRetryCollectLawAux_measurable_and_probability
    B R hweight retryLimit
  have hE := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride
  intro samples
  induction samples using Nat.strong_induction_on with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro attempts total current
          simp only [balancedRetryCollectLawAux,
            balancedAccuracyTransitionCollectLawFirst]
          rw [Measure.map_dirac' hOut]
          rfl
      | succ future =>
          intro attempts
          induction attempts with
          | zero =>
              intro total current
              simp only [balancedRetryCollectLawAux,
                balancedAccuracyTransitionCollectLawFirst,
                balancedAccuracyTransitionLawAux]
              rw [Measure.map_dirac' hOut]
              let tail : Option (AmbientSpace q.n) →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                match result with
                | none => Measure.dirac none
                | some target =>
                    balancedAccuracyTransitionCollectLaw q I sigma2 weight
                      proposalCap properStride retryLimit future
                      (total + weight target)
                      (accuracyScaleFactor q • target)
              have htail : Measurable tail := by
                dsimp only [tail]
                have hcollect :=
                  (balancedAccuracyTransitionCollectLaw_measurable_and_probability
                    q I hsigma2 hweight proposalCap properStride retryLimit
                    future).1
                have hsome : Measurable fun target : AmbientSpace q.n =>
                    balancedAccuracyTransitionCollectLaw q I sigma2 weight
                      proposalCap properStride retryLimit future
                      (total + weight target)
                      (accuracyScaleFactor q • target) :=
                  hcollect.comp <|
                    (measurable_const.add hweight).prodMk <|
                      (measurable_const : Measurable fun _ : AmbientSpace q.n =>
                        accuracyScaleFactor q).smul measurable_id
                convert Measurable.optionElim
                  (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                    hsome using 1
                ext result
                cases result <;> rfl
              exact (Measure.dirac_bind htail none).symm
          | succ attempts ihAttempts =>
              intro total current
              let nextTarget : Option (AmbientSpace q.n) →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                match result with
                | none => Measure.dirac none
                | some target =>
                    balancedAccuracyTransitionCollectLaw q I sigma2 weight
                      proposalCap properStride retryLimit future
                      (total + weight target)
                      (accuracyScaleFactor q • target)
              have hnextTarget : Measurable nextTarget := by
                dsimp only [nextTarget]
                have hcollect :=
                  (balancedAccuracyTransitionCollectLaw_measurable_and_probability
                    q I hsigma2 hweight proposalCap properStride retryLimit
                    future).1
                have hsome : Measurable fun target : AmbientSpace q.n =>
                    balancedAccuracyTransitionCollectLaw q I sigma2 weight
                      proposalCap properStride retryLimit future
                      (total + weight target)
                      (accuracyScaleFactor q • target) :=
                  hcollect.comp <|
                    (measurable_const.add hweight).prodMk <|
                      (measurable_const : Measurable fun _ : AmbientSpace q.n =>
                        accuracyScaleFactor q).smul measurable_id
                convert Measurable.optionElim
                  (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                    hsome using 1
                ext result
                cases result <;> rfl
              let rawNext (mixed : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  balancedRetryCollectLawAux B R weight retryLimit retryLimit
                    future (total + weight result.2) mixed
                else
                  balancedRetryCollectLawAux B R weight retryLimit attempts
                    (future + 1) total mixed
              have hrawNext : ∀ mixed, Measurable (rawNext mixed) := by
                intro mixed
                dsimp only [rawNext]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (hAux retryLimit future).1.comp <|
                    (measurable_const.add (hweight.comp measurable_snd)).prodMk
                      measurable_const
                · exact (hAux attempts (future + 1)).1.comp <|
                    measurable_const.prodMk measurable_const
              let rawBlock : Option (ℝ × AmbientSpace q.n) →
                  Measure (Option (ℝ × AmbientSpace q.n)) := fun block =>
                match block with
                | none => Measure.dirac none
                | some block => (R block.2).bind (rawNext block.2)
              have hrawBlock : Measurable rawBlock := by
                dsimp only [rawBlock]
                have hsome : Measurable fun block : ℝ × AmbientSpace q.n =>
                    (R block.2).bind (rawNext block.2) :=
                  measurable_measure_bind_param_variable
                    (R.measurable.comp measurable_snd)
                    (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
                    (by
                      let joint : (ℝ × AmbientSpace q.n) ×
                          (Bool × AmbientSpace q.n) →
                            Measure (Option (ℝ × AmbientSpace q.n)) :=
                        fun value => rawNext value.1.2 value.2
                      have hjoint : Measurable joint := by
                        dsimp only [joint, rawNext]
                        apply Measurable.ite
                        · exact (measurable_fst.comp measurable_snd)
                            (measurableSet_singleton true)
                        · exact (hAux retryLimit future).1.comp <|
                            ((measurable_const.add
                              (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                                (measurable_snd.comp measurable_fst))
                        · exact (hAux attempts (future + 1)).1.comp <|
                            measurable_const.prodMk
                              (measurable_snd.comp measurable_fst)
                      exact hjoint)
                convert Measurable.optionElim
                  (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                    hsome using 1
                ext block
                cases block <;> rfl
              let endpointBlock : Option (ℝ × AmbientSpace q.n) →
                  Measure (Option (AmbientSpace q.n)) := fun block =>
                match block with
                | none => Measure.dirac none
                | some block =>
                    (R block.2).bind fun result =>
                      if result.1 then Measure.dirac (some result.2)
                      else balancedAccuracyTransitionLawAux q I sigma2
                        proposalCap properStride attempts block.2
              have hendpointBlock : Measurable endpointBlock := by
                have hpoint := (hE attempts).1
                dsimp only [endpointBlock]
                have hsome : Measurable fun block : ℝ × AmbientSpace q.n =>
                    (R block.2).bind fun result =>
                      if result.1 then Measure.dirac (some result.2)
                      else balancedAccuracyTransitionLawAux q I sigma2
                        proposalCap properStride attempts block.2 := by
                  exact measurable_measure_bind_param_variable
                    (R.measurable.comp measurable_snd)
                    (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
                    (by
                      apply Measurable.ite
                      · exact (measurable_fst.comp measurable_snd)
                          (measurableSet_singleton true)
                      · exact Measure.measurable_dirac.comp <|
                          measurable_some.comp (measurable_snd.comp measurable_snd)
                      · exact hpoint.comp
                          (measurable_snd.comp measurable_fst))
                convert Measurable.optionElim
                  (Measure.dirac (none : Option (AmbientSpace q.n))) hsome using 1
                ext block
                cases block <;> rfl
              have hleft :
                  (balancedRetryCollectLawAux B R weight retryLimit
                    (attempts + 1) (future + 1) total current).map Out =
                    (B current).bind fun block =>
                      (rawBlock block).map Out := by
                let expanded : Option (ℝ × AmbientSpace q.n) →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun block =>
                  match block with
                  | none => Measure.dirac none
                  | some (_, mixed) => (R mixed).bind (rawNext mixed)
                let actual : Option (ℝ × AmbientSpace q.n) →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun block =>
                  match block with
                  | none => Measure.dirac none
                  | some (_, mixed) =>
                      (R mixed).bind fun result =>
                        if result.1 then
                          balancedRetryCollectLawAux B R weight retryLimit
                            retryLimit future (total + weight result.2) mixed
                        else
                          balancedRetryCollectLawAux B R weight retryLimit
                            attempts (future + 1) total mixed
                have hactual : actual = expanded := by
                  funext block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      rfl
                have hexpanded : expanded = rawBlock := by
                  funext block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      rfl
                have hrecursion :
                    balancedRetryCollectLawAux B R weight retryLimit
                        (attempts + 1) (future + 1) total current =
                      (B current).bind actual := by
                  simp only [balancedRetryCollectLawAux]
                  apply Measure.bind_congr_right
                  filter_upwards with block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      rfl
                rw [hrecursion, hactual, hexpanded]
                exact map_bind_eq_bind_map_of_measurable
                  (B current) hrawBlock hOut
              have hright :
                  balancedAccuracyTransitionCollectLawFirst q I sigma2 weight
                      proposalCap properStride retryLimit (attempts + 1)
                      (future + 1) total current =
                    (B current).bind fun block =>
                      (endpointBlock block).bind nextTarget := by
                rw [balancedAccuracyTransitionCollectLawFirst]
                rw [balancedAccuracyTransitionLawAux]
                let expanded : Option (ℝ × AmbientSpace q.n) →
                    Measure (Option (AmbientSpace q.n)) := fun block =>
                  match block with
                  | none => Measure.dirac none
                  | some (_, mixed) =>
                      (R mixed).bind fun result =>
                        if result.1 then Measure.dirac (some result.2)
                        else balancedAccuracyTransitionLawAux q I sigma2
                          proposalCap properStride attempts mixed
                have hexpanded : expanded = endpointBlock := by
                  funext block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      rfl
                change ((B current).bind expanded).bind nextTarget = _
                rw [hexpanded]
                have hassoc := Measure.bind_bind
                  (m := B current) hendpointBlock.aemeasurable
                  hnextTarget.aemeasurable
                exact hassoc
              rw [hleft, hright]
              apply Measure.bind_congr_right
              filter_upwards with block
              cases block with
              | none =>
                  dsimp only [rawBlock, endpointBlock]
                  rw [Measure.map_dirac' hOut,
                    Measure.dirac_bind hnextTarget]
                  rfl
              | some block =>
                  rcases block with ⟨ignored, mixed⟩
                  dsimp only [rawBlock, endpointBlock]
                  rw [map_bind_eq_bind_map_of_measurable (R mixed)
                    (hrawNext mixed) hOut]
                  let endpointResult : Bool × AmbientSpace q.n →
                      Measure (Option (AmbientSpace q.n)) := fun result =>
                    if result.1 then Measure.dirac (some result.2)
                    else balancedAccuracyTransitionLawAux q I sigma2
                      proposalCap properStride attempts mixed
                  have hendpointResult : Measurable endpointResult := by
                    dsimp only [endpointResult]
                    apply Measurable.ite
                    · exact measurable_fst (measurableSet_singleton true)
                    · exact Measure.measurable_dirac.comp <|
                        measurable_some.comp measurable_snd
                    · exact (hE attempts).1.comp measurable_const
                  rw [show ((R mixed).bind fun result =>
                        if result.1 then Measure.dirac (some result.2)
                        else balancedAccuracyTransitionLawAux q I sigma2
                          proposalCap properStride attempts mixed) =
                      (R mixed).bind endpointResult by rfl]
                  rw [Measure.bind_bind hendpointResult.aemeasurable
                    hnextTarget.aemeasurable]
                  apply Measure.bind_congr_right
                  have hsecond : ∀ᵐ result ∂R mixed,
                      result.2 = (accuracyScaleFactor q)⁻¹ • mixed :=
                    balancedAccuracyGaussianRejectionLaw_ae_snd
                      q I sigma2 mixed
                  filter_upwards [hsecond] with result hsecondResult
                  by_cases hresult : result.1 = true
                  · have hc0 : accuracyScaleFactor q ≠ 0 :=
                      (accuracyScaleFactor_pos q).ne'
                    simp only [rawNext, endpointResult, hresult, if_true]
                    rw [Measure.dirac_bind hnextTarget]
                    have hrecover : accuracyScaleFactor q • result.2 = mixed := by
                      rw [hsecondResult, ← mul_smul, mul_inv_cancel₀ hc0,
                        one_smul]
                    dsimp only [nextTarget]
                    rw [hrecover]
                    calc
                      Measure.map Out
                          (balancedRetryCollectLawAux B R weight retryLimit
                            retryLimit future (total + weight result.2) mixed) =
                        balancedAccuracyTransitionCollectLawFirst q I sigma2
                          weight proposalCap properStride retryLimit retryLimit
                          future (total + weight result.2) mixed :=
                            ihSamples future (by omega) retryLimit
                              (total + weight result.2) mixed
                      _ = balancedAccuracyTransitionCollectLaw q I sigma2
                            weight proposalCap properStride retryLimit future
                            (total + weight result.2) mixed :=
                        balancedAccuracyTransitionCollectLawFirst_full
                          q I sigma2 weight proposalCap properStride retryLimit
                            future (total + weight result.2) mixed
                  · have hfalse : result.1 = false :=
                      Bool.eq_false_of_not_eq_true hresult
                    simp only [rawNext, endpointResult, hfalse,
                      Bool.false_eq_true, if_false]
                    exact ihAttempts total mixed

/-- Exact public-law form of the multi-sample bridge. -/
theorem balancedAccuracyRetryCollectLaw_eq_transitionCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    balancedAccuracyRetryCollectLaw q I sigma2 weight proposalCap properStride
        retryLimit samples current =
      balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples 0 current := by
  unfold balancedAccuracyRetryCollectLaw
  rw [map_balancedRetryCollectLawAux_eq_transitionCollectLawFirst
    q I hsigma2 hweight]
  exact balancedAccuracyTransitionCollectLawFirst_full q I sigma2 weight
    proposalCap properStride retryLimit samples 0 current

/-- End-to-end semantic form: the distribution produced by the executable
membership-oracle collector is the recovered-state transition iteration. -/
theorem balancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
        retryLimit samples current).runEstimate oracle.query =
      balancedAccuracyTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples 0 current := by
  rw [balancedAccuracyRetryCollect_semantics q I oracle hsigma2 hweight]
  exact balancedAccuracyRetryCollectLaw_eq_transitionCollectLaw
    q I hsigma2 hweight proposalCap properStride retryLimit samples current

#print axioms balancedAccuracyTransitionCollectLaw_measurable_and_probability
#print axioms map_balancedRetryCollectLawAux_eq_transitionCollectLawFirst
#print axioms balancedAccuracyRetryCollectLaw_eq_transitionCollectLaw
#print axioms balancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw

end ArlibCommunity.Algorithms.CV18
