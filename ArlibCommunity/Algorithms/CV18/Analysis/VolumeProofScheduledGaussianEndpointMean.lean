/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofOneSidedL2Transfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedL2
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTransitionSupport

/-!
# First moments of scheduled Gaussian retained endpoints

This file combines the finite-retry marginal comparison with the warm
domination of the normalized accepted law.  The resulting one-sided `L²`
transfer is the unbounded-observable replacement for an invalid uniform
bound on the Gaussian cooling ratio.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

/-- Every successful output of the retained scheduled kernel lies in the
truncated body. -/
theorem figureOneFinalScheduledRetainedOptionKernel_ae_mem_truncatedBody
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (state : Option (AmbientSpace q.n)) :
    ∀ᵐ result ∂figureOneFinalScheduledRetainedOptionKernel q I sigma2 state,
      match result with
      | none => True
      | some target => target ∈ truncatedBody q I := by
  cases state with
  | none =>
      let good : Set (Option (AmbientSpace q.n)) :=
        {none} ∪ optionSomeEvent (truncatedBody q I)
      have hgood : MeasurableSet good :=
        measurableSet_option_none.union <|
          measurableSet_optionSomeEvent (truncatedBody_measurable q I)
      have hmem : ∀ᵐ result ∂Measure.dirac
          (none : Option (AmbientSpace q.n)), result ∈ good := by
        apply (ae_dirac_iff hgood).2
        exact Set.mem_union_left _ (Set.mem_singleton none)
      filter_upwards [hmem] with result hresult
      cases result with
      | none => trivial
      | some x => exact hresult.resolve_left (by simp)
  | some current =>
      filter_upwards [
        scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody
          q I hsigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
          (accuracyScaleFactor q • current)] with result hresult
      cases result with
      | none => trivial
      | some target => exact hresult.1

/-- At every finite horizon, an exact-start retained chain is supported on
the truncated body, with `none` allowed as its absorbing failure state. -/
theorem iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_ae_mem
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ) :
    ∀ᵐ result ∂iteratedKernelLaw
      (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase))
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
      samples,
        match result with
        | none => True
        | some target => target ∈ truncatedBody q I := by
  let body : Set (Option (AmbientSpace q.n)) :=
    {none} ∪ optionSomeEvent (truncatedBody q I)
  have hbody : MeasurableSet body :=
    measurableSet_option_none.union <|
      measurableSet_optionSomeEvent (truncatedBody_measurable q I)
  have hmatch : ∀ result : Option (AmbientSpace q.n),
      result ∈ body ↔
        (match result with
        | none => True
        | some target => target ∈ truncatedBody q I) := by
    intro result
    cases result <;> simp [body, optionSomeEvent]
  cases samples with
  | zero =>
      change ∀ᵐ result ∂(truncatedGaussianProbability q I
        (scheduleValue q phase) (scheduleValue_pos q phase) :
          Measure (AmbientSpace q.n)).map some, _
      have hgood : ∀ᵐ result ∂(truncatedGaussianProbability q I
          (scheduleValue q phase) (scheduleValue_pos q phase) :
            Measure (AmbientSpace q.n)).map some, result ∈ body := by
        apply (ae_map_iff measurable_some.aemeasurable hbody).2
        filter_upwards [truncatedGaussianProbability_ae_mem q I
          (scheduleValue_pos q phase)] with x hx
        exact Set.mem_union_right _ hx
      filter_upwards [hgood] with result hresult
      exact (hmatch result).1 hresult
  | succ samples =>
      rw [iteratedKernelLaw_succ]
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
        q I (scheduleValue_pos q phase)
      let R : Kernel (Option (AmbientSpace q.n))
          (Option (AmbientSpace q.n)) := ⟨K, hK.1⟩
      letI : IsMarkovKernel R := ⟨hK.2⟩
      change ∀ᵐ result ∂R ∘ₘ iteratedKernelLaw
        (fun _ => K)
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        samples, _
      have hgood : ∀ᵐ result ∂R ∘ₘ iteratedKernelLaw
          (fun _ => K)
          ((truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
          samples, result ∈ body := by
        apply Measure.ae_comp_of_ae_ae (κ := R) hbody
        filter_upwards with state
        have hnext :=
          figureOneFinalScheduledRetainedOptionKernel_ae_mem_truncatedBody
            q I (scheduleValue_pos q phase) state
        filter_upwards [hnext] with result hresult
        exact (hmatch result).2 hresult
      filter_upwards [hgood] with result hresult
      exact (hmatch result).1 hresult

/-- The zero-filled Gaussian ratio is square-integrable under every finite
exact-start retained endpoint law.  The large compact-support bound is used
only for integrability, never multiplied by the mixing error. -/
theorem retainedOptionWeight_gaussianRatio_memLp_iterated_from_truncated
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ)
    {t : ℝ} (ht : 0 < t) (p : ENNReal) :
    MemLp
      (retainedOptionWeight
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase) t)) p
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        samples) := by
  let s := scheduleValue q phase
  have hs : 0 < s := scheduleValue_pos q phase
  let initial : Measure (Option (AmbientSpace q.n)) :=
    (truncatedGaussianProbability q I s hs :
      Measure (AmbientSpace q.n)).map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let _ : IsProbabilityMeasure initial := Measure.isProbabilityMeasure_map
    measurable_some.aemeasurable
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hs
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw (fun _ => K) initial samples) :=
    iteratedKernelLaw_isProbabilityMeasure (fun _ => K) initial inferInstance
      (fun _ => hK.1) (fun _ => hK.2) samples
  apply MemLp.of_bound
    (measurable_retainedOptionWeight
      (measurable_gaussianRatioWeight s t)).aestronglyMeasurable
    (Real.exp (terminalVariance q / (2 * s)))
  filter_upwards [
    iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_ae_mem
      q I phase samples] with result hresult
  cases result with
  | none =>
      simp [retainedOptionWeight]
      positivity
  | some x =>
      rw [Real.norm_eq_abs, abs_of_pos (by
        unfold retainedOptionWeight gaussianRatioWeight
        positivity)]
      change Real.exp (-‖x‖ ^ 2 / (2 * t)) /
          Real.exp (-‖x‖ ^ 2 / (2 * s)) ≤
        Real.exp (terminalVariance q / (2 * s))
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hsq := norm_sq_le_terminalVariance_of_mem_truncatedBody q I hresult
      have hfirst : ‖x‖ ^ 2 / (2 * s) ≤ terminalVariance q / (2 * s) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      have hneg : -‖x‖ ^ 2 / (2 * t) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg ‖x‖)) (by positivity)
      calc
        -‖x‖ ^ 2 / (2 * t) - -‖x‖ ^ 2 / (2 * s) =
            ‖x‖ ^ 2 / (2 * s) + -‖x‖ ^ 2 / (2 * t) := by ring
        _ ≤ terminalVariance q / (2 * s) + 0 := add_le_add hfirst hneg
        _ = terminalVariance q / (2 * s) := by ring

/-- Zero-filling commutes with the exact Gaussian law without changing any
finite `Lᵖ` condition. -/
theorem retainedOptionWeight_gaussianRatio_memLp_truncated_map
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (p : ENNReal) :
    MemLp (retainedOptionWeight (gaussianRatioWeight (n := q.n) s t)) p
      ((truncatedGaussianProbability q I s hs :
        Measure (AmbientSpace q.n)).map some) := by
  let f := retainedOptionWeight (gaussianRatioWeight (n := q.n) s t)
  apply (memLp_map_measure_iff
    (measurable_retainedOptionWeight
      (measurable_gaussianRatioWeight s t)).aestronglyMeasurable
    measurable_some.aemeasurable).2
  simpa [f, Function.comp_def, retainedOptionWeight] using
    gaussianRatioWeight_memLp q I hs ht p

/-- Composing the endpoint-to-accepted comparison with the accepted-to-exact
TV comparison returns to the exact Gaussian reference.  This spends a second
stationary-target error but avoids any boundedness assumption on the cooling
ratio. -/
theorem iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ) :
    MeasureLeUpTo
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        samples)
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
      (2 * scheduledBalancedStationaryTargetError q +
        samples • figureOneCorrectedTransitionBudget q) := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let target : Measure (AmbientSpace q.n) :=
    figureOneScheduledAcceptedTargetAt q I phase
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  have htargetExact : MeasureLeUpTo (target.map some) (exact.map some)
      (scheduledBalancedStationaryTargetError q) := by
    apply (MeasureLeUpTo.of_tvLe ?_).map measurable_some
    simpa [target, exact, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
        scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
          q I (scheduleValue_pos q phase)
  have h :=
    (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_leUpTo
      q I phase samples).trans htargetExact
  simpa [exact, target, two_mul, add_assoc, add_comm, add_left_comm] using h

/-- Concrete unbounded-observable endpoint transfer for a Gaussian cooling
ratio.  The error is paid at square-root scale against the exact Gaussian
second moment; no false global `exp (1/2)` support bound is used. -/
theorem integral_iterated_retainedOption_gaussianRatio_lower
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ)
    {t eta R : ℝ} (ht : 0 < t) (heta : 0 < eta) (hR : 0 < R)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          samples • figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hepsEta :
      (2 * scheduledBalancedStationaryTargetError q +
          samples • figureOneCorrectedTransitionBudget q).toReal ≤ eta ^ 2)
    (hsecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase) t x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2) :
    (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase) t x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) -
        2 * eta * R ≤
      ∫ result, retainedOptionWeight
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase) t) result
        ∂iteratedKernelLaw
          (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
            (scheduleValue q phase))
          ((truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
          samples := by
  let s := scheduleValue q phase
  let weight := gaussianRatioWeight (n := q.n) s t
  let f := retainedOptionWeight weight
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q phase)
  let exactSome : Measure (Option (AmbientSpace q.n)) := exact.map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let actual := iteratedKernelLaw (fun _ => K) exactSome samples
  let epsilon := 2 * scheduledBalancedStationaryTargetError q +
    samples • figureOneCorrectedTransitionBudget q
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure exactSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q phase)
  let _ : IsProbabilityMeasure actual :=
    iteratedKernelLaw_isProbabilityMeasure (fun _ => K) exactSome inferInstance
      (fun _ => hK.1) (fun _ => hK.2) samples
  have htv : TVLe actual exactSome epsilon := by
    exact (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
      q I phase samples).to_tvLe
  have hf : Measurable f := measurable_retainedOptionWeight
    (measurable_gaussianRatioWeight s t)
  have hf0 : ∀ result, 0 ≤ f result := by
    intro result
    cases result with
    | none => simp [f, retainedOptionWeight]
    | some x =>
        dsimp [f, weight, retainedOptionWeight, gaussianRatioWeight]
        positivity
  have hfActual : MemLp f 2 actual := by
    simpa [f, weight, actual, K, exactSome, exact, s] using
      retainedOptionWeight_gaussianRatio_memLp_iterated_from_truncated
        q I phase samples ht 2
  have hfExact : MemLp f 2 exactSome := by
    simpa [f, weight, exactSome, exact, s] using
      retainedOptionWeight_gaussianRatio_memLp_truncated_map q I
        (scheduleValue_pos q phase) ht 2
  have hsecondSome : (∫ result, f result ^ 2 ∂exactSome) ≤ R ^ 2 := by
    rw [integral_map measurable_some.aemeasurable
      (hf.pow_const 2).aestronglyMeasurable]
    simpa [f, weight, exactSome, exact, s, Function.comp_def,
      retainedOptionWeight] using hsecond
  have htransfer :=
    ArlibCommunity.Algorithms.CV18.Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt
    htv (by simpa [epsilon] using hepsilonTop) hf hf0 hfActual hfExact
      heta hR (by simpa [epsilon] using hepsEta) hsecondSome
  rw [integral_map measurable_some.aemeasurable hf.aestronglyMeasurable]
    at htransfer
  simpa [f, weight, actual, K, exactSome, exact, epsilon, s,
    Function.comp_def, retainedOptionWeight] using htransfer

#print axioms
  iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
#print axioms integral_iterated_retainedOption_gaussianRatio_lower

end ArlibCommunity.Algorithms.CV18
