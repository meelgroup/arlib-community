/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledWarmSixteenTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad

/-! # Conditioned transition for a killed within-phase collector

This is the Option-state analogue of the trace live/dead argument.  A
conditioning which is `2`-warm with respect to the current killed marginal
doubles its live good/bad decomposition.  The good component is therefore
`16`-warm for the scheduled transition, while live error and absorbing dead
mass together cost twice the current retained error.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

noncomputable def retainedOptionScaledLiveLaw
    (mu : Measure (Option (AmbientSpace n)))
    (scale : AmbientSpace n → AmbientSpace n) : Measure (AmbientSpace n) :=
  (mu.restrict (scheduledRetainedSomeSet n)).map
    (scale ∘ scheduledRetainedGetDZero)

noncomputable def retainedOptionDeadLaw
    (mu : Measure (Option (AmbientSpace n))) : Measure (AmbientSpace n) :=
  mu ({none} : Set (Option (AmbientSpace n))) • Measure.dirac 0

theorem retainedOptionDeadLaw_apply_univ
    (mu : Measure (Option (AmbientSpace n))) :
    retainedOptionDeadLaw mu Set.univ =
      mu ({none} : Set (Option (AmbientSpace n))) := by
  rw [retainedOptionDeadLaw, Measure.smul_apply, smul_eq_mul, measure_univ,
    mul_one]

theorem retainedOptionScaledLiveLaw_add_dead_mass
    (mu : Measure (Option (AmbientSpace n))) [IsProbabilityMeasure mu]
    (scale : AmbientSpace n → AmbientSpace n) (hscale : Measurable scale) :
    retainedOptionScaledLiveLaw mu scale Set.univ +
        retainedOptionDeadLaw mu Set.univ = 1 := by
  rw [retainedOptionScaledLiveLaw,
    Measure.map_apply
      (hscale.comp measurable_scheduledRetainedGetDZero) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    retainedOptionDeadLaw_apply_univ]
  simp only [Set.univ_inter, scheduledRetainedSomeSet]
  rw [add_comm, measure_add_measure_compl measurableSet_option_none,
    measure_univ]

theorem retainedOptionScaledLiveLaw_mono_smul
    (mu rho : Measure (Option (AmbientSpace n))) (c : ENNReal)
    (scale : AmbientSpace n → AmbientSpace n) (hscale : Measurable scale)
    (hmu : mu ≤ c • rho) :
    retainedOptionScaledLiveLaw mu scale ≤
      c • retainedOptionScaledLiveLaw rho scale := by
  unfold retainedOptionScaledLiveLaw
  have hrestrict :
      mu.restrict (scheduledRetainedSomeSet n) ≤
        (c • rho).restrict (scheduledRetainedSomeSet n) :=
    Measure.restrict_mono Set.Subset.rfl hmu
  have hmapped := Measure.map_mono hrestrict
    (hscale.comp measurable_scheduledRetainedGetDZero)
  simpa only [Measure.restrict_smul, Measure.map_smul] using hmapped

theorem retainedOptionDeadLaw_mass_mono_smul
    (mu rho : Measure (Option (AmbientSpace n))) (c : ENNReal)
    (hmu : mu ≤ c • rho) :
    retainedOptionDeadLaw mu Set.univ ≤
      c * retainedOptionDeadLaw rho Set.univ := by
  rw [retainedOptionDeadLaw_apply_univ,
    retainedOptionDeadLaw_apply_univ]
  have h := Measure.le_iff'.mp hmu
    ({none} : Set (Option (AmbientSpace n)))
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact h

/-- Extract the live part of an Option-valued `MeasureLeUpTo` comparison,
then scale it.  The error carried by live points and the mass already at the
absorbing `none` state still share the original error budget. -/
theorem exists_retainedOptionScaledLive_good_bad_of_leUpTo
    (rho : Measure (Option (AmbientSpace n)))
    (target : Measure (AmbientSpace n)) {eta : ENNReal}
    (h : MeasureLeUpTo rho (target.map some) eta)
    (scale : AmbientSpace n → AmbientSpace n) (hscale : Measurable scale) :
    ∃ bad : Measure (AmbientSpace n),
      retainedOptionScaledLiveLaw rho scale ≤ target.map scale + bad ∧
      bad Set.univ + retainedOptionDeadLaw rho Set.univ ≤ eta := by
  obtain ⟨error, herrorDom, herrorMass⟩ := h
  let someSet := scheduledRetainedSomeSet n
  let get := scheduledRetainedGetDZero (n := n)
  let liveBad0 := (error.restrict someSet).map get
  let bad := liveBad0.map scale
  refine ⟨bad, ?_, ?_⟩
  · have hrestrict : rho.restrict someSet ≤
        ((target.map some + error).restrict someSet) :=
      Measure.restrict_mono Set.Subset.rfl herrorDom
    have hmapped := Measure.map_mono hrestrict
      (measurable_scheduledRetainedGetDZero (n := n))
    rw [Measure.restrict_add,
      Measure.map_add _ _ (measurable_scheduledRetainedGetDZero (n := n)),
      map_some_restrict_extract_eq] at hmapped
    have hscaled := Measure.map_mono hmapped hscale
    rw [Measure.map_add _ _ hscale] at hscaled
    rw [retainedOptionScaledLiveLaw]
    rw [← Measure.map_map hscale
      (measurable_scheduledRetainedGetDZero (n := n))]
    simpa [bad, liveBad0, get, someSet] using hscaled
  · have hbadMass : bad Set.univ = error someSet := by
      rw [show bad = liveBad0.map scale by rfl,
        Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
      rw [show liveBad0 = (error.restrict someSet).map get by rfl,
        Measure.map_apply
          (measurable_scheduledRetainedGetDZero (n := n)) MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    have hnone : (target.map some)
        ({none} : Set (Option (AmbientSpace n))) = 0 := by
      rw [Measure.map_apply measurable_some measurableSet_option_none]
      have hpre : (some : AmbientSpace n → Option (AmbientSpace n)) ⁻¹'
          ({none} : Set (Option (AmbientSpace n))) = ∅ := by
        ext point
        simp
      rw [hpre, measure_empty]
    have hdead : retainedOptionDeadLaw rho Set.univ ≤
        error ({none} : Set (Option (AmbientSpace n))) := by
      have hevent := Measure.le_iff'.mp herrorDom
        ({none} : Set (Option (AmbientSpace n)))
      rw [Measure.add_apply, hnone, zero_add] at hevent
      simpa [retainedOptionDeadLaw_apply_univ] using hevent
    calc
      bad Set.univ + retainedOptionDeadLaw rho Set.univ ≤
          error someSet + error ({none} : Set (Option (AmbientSpace n))) := by
        rw [hbadMass]
        exact add_le_add le_rfl hdead
      _ = error Set.univ := by
        rw [show someSet =
            ({none} : Set (Option (AmbientSpace n)))ᶜ by rfl,
          add_comm, measure_add_measure_compl measurableSet_option_none]
      _ ≤ eta := herrorMass

/-- Splitting an Option-state law into live scaled input and absorbing dead
mass commutes exactly with the final scheduled retained transition. -/
theorem bind_figureOneFinalScheduledRetainedOptionKernel_eq_live_dead
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (Option (AmbientSpace q.n))) :
    mu.bind (figureOneFinalScheduledRetainedOptionKernel q I sigma2) =
      (retainedOptionScaledLiveLaw mu
        (fun x => accuracyScaleFactor q • x)).bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2
            (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
            (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)) +
        retainedOptionDeadLaw mu Set.univ • Measure.dirac none := by
  let someSet := scheduledRetainedSomeSet q.n
  let deadSet : Set (Option (AmbientSpace q.n)) := {none}
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let state : Option (AmbientSpace q.n) → AmbientSpace q.n :=
    scale ∘ scheduledRetainedGetDZero
  let transition := scheduledBalancedAccuracyTransitionLawAux q I sigma2
    (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
    (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  let optionK := figureOneFinalScheduledRetainedOptionKernel q I sigma2
  have hscale : Measurable scale := by dsimp only [scale]; fun_prop
  have hstate : Measurable state :=
    hscale.comp measurable_scheduledRetainedGetDZero
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hoptionK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I hsigma2
  have hsplit : mu = mu.restrict someSet + mu.restrict deadSet := by
    rw [show deadSet = someSetᶜ by
        simp [deadSet, someSet, scheduledRetainedSomeSet],
      Measure.restrict_add_restrict_compl
        (measurableSet_scheduledRetainedSomeSet (n := q.n))]
  have hlive : (mu.restrict someSet).bind optionK =
      ((mu.restrict someSet).map state).bind transition := by
    rw [map_bind_eq_bind_comp_state (mu.restrict someSet) hstate htransition.1]
    apply Measure.bind_congr_right
    filter_upwards
      [ae_restrict_mem (measurableSet_scheduledRetainedSomeSet (n := q.n))]
      with current hcurrent
    cases current with
    | none => simp [someSet, scheduledRetainedSomeSet] at hcurrent
    | some point => rfl
  have hdead : (mu.restrict deadSet).bind optionK =
      (mu.restrict deadSet) Set.univ • Measure.dirac none := by
    have heq : ∀ᵐ current ∂(mu.restrict deadSet),
        optionK current = Measure.dirac none := by
      filter_upwards [ae_restrict_mem measurableSet_option_none]
        with current hcurrent
      have hnone : current = none := by simpa [deadSet] using hcurrent
      subst current
      rfl
    rw [Measure.bind_congr_right heq, Measure.bind_const]
  calc
    mu.bind optionK =
        (mu.restrict someSet + mu.restrict deadSet).bind optionK :=
      congrArg (fun law => law.bind optionK) hsplit
    _ = (mu.restrict someSet).bind optionK +
        (mu.restrict deadSet).bind optionK :=
      measure_bind_add_left _ _ hoptionK.1
    _ = ((mu.restrict someSet).map state).bind transition +
        (mu.restrict deadSet) Set.univ • Measure.dirac none := by
      rw [hlive, hdead]
    _ = _ := by
      congr 1
      rw [Measure.restrict_apply MeasurableSet.univ,
        retainedOptionDeadLaw_apply_univ]
      simp [deadSet]

/-- A `2`-warm conditioning of a killed within-phase endpoint can be advanced
one more retained transition.  Its prior retained error is charged exactly
twice, while the new transition contributes one fresh corrected budget. -/
theorem bind_figureOneFinalScheduledRetainedOptionKernel_leUpTo_of_warm_iterated_truncated
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (mu : Measure (Option (AmbientSpace q.n))) [IsProbabilityMeasure mu]
    (hwarm : Arlib.IsWarm 2 mu
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        i)) :
    MeasureLeUpTo
      (mu.bind (figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)))
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q +
        2 * (scheduledBalancedStationaryTargetError q +
          i • figureOneCorrectedTransitionBudget q)) := by
  let sigma2 := scheduleValue q phase
  have hsigma2 : 0 < sigma2 := by
    simpa [sigma2] using scheduleValue_pos q phase
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let target : Measure (AmbientSpace q.n) :=
    figureOneScheduledAcceptedTargetAt q I phase
  let rho : Measure (Option (AmbientSpace q.n)) :=
    iteratedKernelLaw
      (fun _ => figureOneFinalScheduledRetainedOptionKernel q I sigma2)
      (exact.map some) i
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := target.map scale
  let eta := scheduledBalancedStationaryTargetError q +
    i • figureOneCorrectedTransitionBudget q
  let live := retainedOptionScaledLiveLaw mu scale
  let dead := retainedOptionDeadLaw mu
  let transition := scheduledBalancedAccuracyTransitionLawAux q I sigma2
    (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
    (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  let pi := figureOneScheduledSpeedyPiAt q I phase
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure (exact.map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hoptionK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I hsigma2
  let _ : IsProbabilityMeasure rho := by
    exact iteratedKernelLaw_isProbabilityMeasure
      (fun _ => figureOneFinalScheduledRetainedOptionKernel q I sigma2)
      (exact.map some) inferInstance (fun _ => hoptionK.1)
      (fun _ state => hoptionK.2 state) i
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure pi :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I phase
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hrho : MeasureLeUpTo rho (target.map some) eta := by
    simpa [rho, target, exact, eta, sigma2, hsigma2] using
      iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_leUpTo
        q I phase i
  obtain ⟨bad, hliveRho, herrorRho⟩ :=
    exists_retainedOptionScaledLive_good_bad_of_leUpTo
      rho target hrho scale hscale
  have hetaTop : eta ≠ ⊤ := by
    dsimp only [eta]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure bad :=
    { measure_univ_lt_top := by
        apply lt_of_le_of_lt
        · exact le_trans (le_add_right le_rfl) herrorRho
        · exact lt_top_iff_ne_top.mpr hetaTop }
  have hmule : mu ≤ (2 : ENNReal) • rho :=
    (isWarm_iff_le_smul mu rho).1 (by simpa [rho, sigma2, exact] using hwarm)
  let good2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • good
  let bad2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • bad
  let _ : IsFiniteMeasure bad2 :=
    { measure_univ_lt_top := by
        rw [show bad2 = (2 : ENNReal) • bad by rfl,
          Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top bad Set.univ) }
  let _ : IsFiniteMeasure live := by
    dsimp only [live, retainedOptionScaledLiveLaw]
    infer_instance
  let _ : IsFiniteMeasure dead := by
    refine ⟨?_⟩
    rw [show dead = retainedOptionDeadLaw mu by rfl,
      retainedOptionDeadLaw_apply_univ]
    calc
      mu ({none} : Set (Option (AmbientSpace q.n))) ≤ mu Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hlive2 : live ≤ good2 + bad2 := by
    calc
      live ≤ (2 : ENNReal) • retainedOptionScaledLiveLaw rho scale :=
        retainedOptionScaledLiveLaw_mono_smul mu rho 2 scale hscale hmule
      _ ≤ (2 : ENNReal) • (good + bad) := by
        rw [Measure.le_iff]
        intro S hS
        rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
        gcongr
      _ = good2 + bad2 := by
        simp only [good2, bad2, smul_add]
  have hgood : Arlib.IsWarm 8 good pi := by
    simpa [good, target, scale, pi, sigma2,
      figureOneScheduledAcceptedTargetAt, figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_isWarm_eight q I hsigma2
  have hgood2 : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) good2 pi := by
    intro S hS
    rw [show good2 = (2 : ENNReal) • good by rfl,
      Measure.smul_apply, smul_eq_mul]
    have hg := hgood S hS
    calc
      2 * good S ≤ 16 * pi S := by
        calc
          2 * good S ≤ 2 * (8 * pi S) := by gcongr
          _ = 16 * pi S := by ring
      _ ≤ ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) * pi S := by
        gcongr
        rw [← ENNReal.ofReal_ofNat 16]
        exact ENNReal.ofReal_le_ofReal <| by
          nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hdead2 := retainedOptionDeadLaw_mass_mono_smul mu rho 2 hmule
  have herror2 : bad2 Set.univ + dead Set.univ ≤ 2 * eta := by
    rw [show bad2 = (2 : ENNReal) • bad by rfl,
      Measure.smul_apply, smul_eq_mul]
    calc
      2 * bad Set.univ + dead Set.univ ≤
          2 * bad Set.univ + 2 * retainedOptionDeadLaw rho Set.univ := by
        gcongr
      _ = 2 * (bad Set.univ + retainedOptionDeadLaw rho Set.univ) := by ring
      _ ≤ 2 * eta := by gcongr
  have hmass : live Set.univ + dead Set.univ = 1 := by
    simpa [live, dead] using
      retainedOptionScaledLiveLaw_add_dead_mass mu scale hscale
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hM16 : (1 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hmlu := measureLeUpTo_live_dead_bind_of_good_bad
    live dead good2 bad2 pi hM16 ENNReal.ofReal_ne_top hmass hlive2 hgood2
    herror2 transition htransition.1 htransition.2 (Measure.dirac none)
    (exact.map some) (fun nu hnu hwarmNu => by
      let _ : IsProbabilityMeasure nu := hnu
      let _ : IsProbabilityMeasure (nu.bind transition) :=
        isProbabilityMeasure_bind htransition.1.aemeasurable
          (ae_of_all _ htransition.2)
      apply MeasureLeUpTo.of_tvLe
      simpa [transition, pi, figureOneScheduledSpeedyPiAt, sigma2, exact] using
        bind_figureOneFinalScheduledBalancedTransition_tvLe_of_warmSixteen
          q I hsigma2 nu (by simpa [pi, figureOneScheduledSpeedyPiAt] using hwarmNu))
  rw [bind_figureOneFinalScheduledRetainedOptionKernel_eq_live_dead
    q I hsigma2 mu]
  simpa [live, dead, good2, bad2, transition, exact, eta, sigma2] using hmlu

#print axioms
  bind_figureOneFinalScheduledRetainedOptionKernel_leUpTo_of_warm_iterated_truncated

end ArlibCommunity.Algorithms.CV18
