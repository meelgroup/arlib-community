/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTransitionSupport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-!
# Square-integrability of executable scheduled phase averages

The scheduled rejection test restricts every successful target to a compact
phase body.  Hence any continuous nonnegative importance weight has a common
finite bound there, uniformly in the phase starting point.  The finite
collector bound then gives the `L²` premise required by the trace moment
capstone.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A continuous nonnegative observable has a nonnegative upper bound on the
compact scheduled phase body. -/
theorem exists_scheduledPhaseBody_weight_upper_bound
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ figureOneScheduledPhaseBody q I sigma2,
      weight x ≤ B := by
  let K := figureOneScheduledPhaseBody q I sigma2
  obtain ⟨B, hB⟩ :=
    (figureOneScheduledPhaseBody_isCompact q I sigma2).bddAbove_image
      hweight.continuousOn
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    refine ⟨unitBall_subset_truncatedBody q I
      (Metric.mem_closedBall_self zero_le_one), ?_⟩
    exact Metric.mem_closedBall_self
      (figureOneScheduledPhaseRadius_pos q hsigma2).le
  have hB0 : 0 ≤ B :=
    (hweight0 0).trans (hB (Set.mem_image_of_mem weight hzero))
  exact ⟨B, hB0, fun x hx => hB (Set.mem_image_of_mem weight hx)⟩

/-- A scheduled finite collector using a continuous nonnegative observable
has a square-integrable returned average, uniformly for every starting
point. -/
theorem memLp_scheduledBalancedTransitionCollect_average_of_continuous
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (proposalCap properStride retryLimit samples : ℕ)
    (hsamples : 0 < samples) (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      ((scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples 0 current).map
          (balancedCoolingAverage samples)) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_scheduledPhaseBody_weight_upper_bound q I hsigma2 hweight hweight0
  apply memLp_scheduledBalancedTransitionCollect_average q I hsigma2
    hweight.measurable hweight0 proposalCap properStride retryLimit samples
    hsamples current hB0
  intro state
  filter_upwards [scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody
    q I hsigma2 proposalCap properStride retryLimit state] with result hresult
  cases result with
  | none => trivial
  | some target => exact hB target hresult

/-- Every executable scheduled Gaussian-ratio phase has an `L²` average. -/
theorem memLp_scheduledBalancedCoolingRatioTransitionLaw_ratio
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      (scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2
        current) := by
  have hcontinuous : Continuous
      (gaussianRatioWeight (n := q.n) sigma2 tau2) := by
    unfold gaussianRatioWeight
    refine (by fun_prop : Continuous fun x : AmbientSpace q.n =>
      Real.exp (-‖x‖ ^ 2 / (2 * tau2))).div₀ (by fun_prop) ?_
    intro x
    exact Real.exp_ne_zero _
  have hsamples : 0 < figureOnePhaseSampleCount q sigma2 := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  simpa [scheduledBalancedCoolingRatioTransitionLaw] using
    memLp_scheduledBalancedTransitionCollect_average_of_continuous
      q I hsigma2 hcontinuous
      (gaussianRatioWeight_nonnegative sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      hsamples
      (accuracyScaleFactor q • current)

/-- Every executable scheduled terminal Gaussian-to-uniform phase has an
`L²` average. -/
theorem memLp_scheduledBalancedCoolingUniformTransitionLaw_ratio
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      (scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2
        current) := by
  have hcontinuous : Continuous
      (uniformRatioWeight (n := q.n) sigma2) := by
    unfold uniformRatioWeight
    fun_prop
  simpa [scheduledBalancedCoolingUniformTransitionLaw] using
    memLp_scheduledBalancedTransitionCollect_average_of_continuous
      q I hsigma2 hcontinuous (uniformRatioWeight_nonnegative sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) (figureOneSampleCount_pos q)
      (accuracyScaleFactor q • current)

/-! ## Uniform bounds and the full trace -/

/-- The compact-body bound is uniform in the collector's starting point. -/
theorem exists_scheduledBalancedTransitionCollect_average_uniform_bound
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (proposalCap properStride retryLimit samples : ℕ)
    (hsamples : 0 < samples) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ current,
      ∀ᵐ result ∂((scheduledBalancedTransitionCollectLaw q I sigma2
          weight proposalCap properStride retryLimit samples 0 current).map
            (balancedCoolingAverage samples)),
        scheduledBalancedPhaseRatio result ≤ B := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_scheduledPhaseBody_weight_upper_bound q I hsigma2 hweight hweight0
  let B := max 1 C
  have hB1 : 1 ≤ B := le_max_left _ _
  have hCB : C ≤ B := le_max_right _ _
  refine ⟨B, hB1, ?_⟩
  intro current
  have htotal := scheduledBalancedTransitionCollectLaw_ae_total_le q I hsigma2
    hweight.measurable proposalCap properStride retryLimit
      (B := B) (fun state => by
        filter_upwards [
          scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody
            q I hsigma2 proposalCap properStride retryLimit state]
          with result hresult
        cases result with
        | none => trivial
        | some target => exact (hC target hresult).trans hCB)
      samples 0 current
  have hset : MeasurableSet
      {result : Option (ℝ × AmbientSpace q.n) |
        scheduledBalancedPhaseRatio result ≤ B} :=
    measurable_scheduledBalancedPhaseRatio measurableSet_Iic
  apply (ae_map_iff (measurable_balancedCoolingAverage samples).aemeasurable
    hset).2
  filter_upwards [htotal] with result hresult
  cases result with
  | none =>
      simp only [balancedCoolingAverage, scheduledBalancedPhaseRatio]
      exact zero_le_one.trans hB1
  | some result =>
      dsimp only [ScheduledCollectedTotalLe] at hresult
      simp only [balancedCoolingAverage, scheduledBalancedPhaseRatio]
      rw [div_le_iff₀ (by exact_mod_cast hsamples)]
      simpa [mul_comm] using hresult

/-- For a fixed chronological phase, the phase observation law has a common
finite scalar bound for every incoming trace.  Dead traces emit zero. -/
theorem exists_scheduledBalancedTracePhaseObservation_ratio_bound
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ trace,
      ∀ᵐ result ∂scheduledBalancedTracePhaseObservationLaw
          parameters q I phase trace,
        scheduledBalancedPhaseRatio result ≤ B := by
  by_cases hphase : phase < terminalPhaseSteps q
  · have hcontinuous : Continuous
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) := by
      unfold gaussianRatioWeight
      refine (by fun_prop : Continuous fun x : AmbientSpace q.n =>
        Real.exp (-‖x‖ ^ 2 / (2 * scheduleValue q (phase + 1)))).div₀
          (by fun_prop) ?_
      intro x
      exact Real.exp_ne_zero _
    have hsamples : 0 < figureOnePhaseSampleCount q
        (scheduleValue q phase) := by
      unfold figureOnePhaseSampleCount
      split_ifs
      · exact figureOneFixedSampleCount_pos q
      · exact figureOneSampleCount_pos q
    obtain ⟨B, hB1, hbound⟩ :=
      exists_scheduledBalancedTransitionCollect_average_uniform_bound
        q I (scheduleValue_pos q phase) hcontinuous
        (gaussianRatioWeight_nonnegative (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (parameters.proposalCap q (scheduleValue q phase))
        (parameters.properStride q (scheduleValue q phase))
        (parameters.retryLimit q (scheduleValue q phase))
        (figureOnePhaseSampleCount q (scheduleValue q phase)) hsamples
    refine ⟨B, hB1, ?_⟩
    intro trace
    rcases trace with ⟨history, live⟩
    cases live with
    | false =>
        unfold scheduledBalancedTracePhaseObservationLaw
        apply (ae_dirac_iff
          (measurable_scheduledBalancedPhaseRatio measurableSet_Iic)).2
        simp [scheduledBalancedPhaseRatio, zero_le_one.trans hB1]
    | true =>
        unfold scheduledBalancedTracePhaseObservationLaw
        simp only [if_true, hphase]
        simpa [scheduledBalancedCoolingRatioTransitionLaw] using
          hbound (accuracyScaleFactor q • history.2.2.2)
  · have hcontinuous : Continuous
        (uniformRatioWeight (n := q.n) (terminalVariance q)) := by
      unfold uniformRatioWeight
      fun_prop
    obtain ⟨B, hB1, hbound⟩ :=
      exists_scheduledBalancedTransitionCollect_average_uniform_bound
        q I (terminalVariance_pos' q) hcontinuous
        (uniformRatioWeight_nonnegative (terminalVariance q))
        (parameters.proposalCap q (terminalVariance q))
        (parameters.properStride q (terminalVariance q))
        (parameters.retryLimit q (terminalVariance q))
        (figureOneSampleCount q) (figureOneSampleCount_pos q)
    refine ⟨B, hB1, ?_⟩
    intro trace
    rcases trace with ⟨history, live⟩
    cases live with
    | false =>
        unfold scheduledBalancedTracePhaseObservationLaw
        apply (ae_dirac_iff
          (measurable_scheduledBalancedPhaseRatio measurableSet_Iic)).2
        simp [scheduledBalancedPhaseRatio, zero_le_one.trans hB1]
    | true =>
        unfold scheduledBalancedTracePhaseObservationLaw
        simp only [if_true, hphase, if_false]
        simpa [scheduledBalancedCoolingUniformTransitionLaw] using
          hbound (accuracyScaleFactor q • history.2.2.2)

/-- The freshly appended chronological coordinate is bounded by the scalar
observation bound; a previously dead trace appends `1`, which explains the
premise `1 ≤ B`. -/
theorem scheduledBalancedTrace_append_new_coordinate_le
    (q : VolumeParams) {phase : ℕ}
    (hphase : phase < figureOneDependentPhaseCount q)
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid phase trace)
    {B : ℝ} (hB1 : 1 ≤ B)
    (result : Option (ℝ × AmbientSpace q.n))
    (hresult : scheduledBalancedPhaseRatio result ≤ B) :
    scheduledBalancedTraceChronologicalPhaseVariable q (phase + 1)
        (scheduledBalancedCoolingTraceAppend trace result) ≤ B := by
  rcases trace with ⟨history, live⟩
  have hcount : history.2.1 = phase := hvalid.1
  unfold scheduledBalancedTraceChronologicalPhaseVariable
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q phase hphase]
  cases live <;> cases result <;>
    simp only [scheduledBalancedCoolingTraceAppend, Bool.false_eq_true,
      if_false, if_true, balancedCoolingHistoryAppend]
  · simpa [hcount] using hB1
  · simpa [hcount] using hB1
  · simpa [hcount]
  · simpa [hcount, scheduledBalancedPhaseRatio] using hresult

/-- Every completed chronological coordinate of a finite scheduled trace is
almost-everywhere bounded by some finite constant. -/
theorem exists_scheduledBalancedForwardTrace_coordinate_bound
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases j,
    1 ≤ j → j ≤ phases → phases ≤ figureOneDependentPhaseCount q →
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw parameters q I phases,
          scheduledBalancedTraceChronologicalPhaseVariable q j trace ≤ B := by
  intro phases
  induction phases with
  | zero =>
      intro j hj1 hj0
      omega
  | succ phase ih =>
      intro j hj1 hjle htotal
      let prefixLaw := scheduledBalancedForwardTraceLaw parameters q I phase
      let kernel := scheduledBalancedTracePhaseKernel parameters q I phase
      have hkernel : Measurable kernel :=
        (scheduledBalancedTracePhaseKernel_measurable_and_probability
          parameters q I phase).1
      have hphaseTotal : phase < figureOneDependentPhaseCount q := by omega
      by_cases hjnew : j = phase + 1
      · subst j
        obtain ⟨B, hB1, hobs⟩ :=
          exists_scheduledBalancedTracePhaseObservation_ratio_bound
            parameters q I phase
        refine ⟨B, zero_le_one.trans hB1, ?_⟩
        let good : Set (ScheduledBalancedCoolingTrace q.n) :=
            {trace : ScheduledBalancedCoolingTrace q.n |
              scheduledBalancedTraceChronologicalPhaseVariable q (phase + 1)
                trace ≤ B}
        have hgood : MeasurableSet good :=
          (measurable_scheduledBalancedTraceChronologicalPhaseVariable
            q (phase + 1)) measurableSet_Iic
        change ∀ᵐ trace ∂prefixLaw.bind kernel,
          scheduledBalancedTraceChronologicalPhaseVariable q (phase + 1)
            trace ≤ B
        apply MeasureTheory.mem_ae_iff.mpr
        change (prefixLaw.bind kernel) goodᶜ = 0
        rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
          parameters q I phase] with trace hvalid
        unfold kernel scheduledBalancedTracePhaseKernel
        apply MeasureTheory.mem_ae_iff.mp
        apply (ae_map_iff
          ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable hgood).2
        filter_upwards [hobs trace] with result hresult
        exact scheduledBalancedTrace_append_new_coordinate_le q hphaseTotal
          hvalid hB1 result hresult
      · have hjold : j ≤ phase := by omega
        obtain ⟨B, hB0, hprefix⟩ := ih j hj1 hjold (by omega)
        refine ⟨B, hB0, ?_⟩
        let good : Set (ScheduledBalancedCoolingTrace q.n) :=
            {trace : ScheduledBalancedCoolingTrace q.n |
              scheduledBalancedTraceChronologicalPhaseVariable q j trace ≤ B}
        have hgood : MeasurableSet good :=
          (measurable_scheduledBalancedTraceChronologicalPhaseVariable q j)
            measurableSet_Iic
        change ∀ᵐ trace ∂prefixLaw.bind kernel,
          scheduledBalancedTraceChronologicalPhaseVariable q j trace ≤ B
        apply MeasureTheory.mem_ae_iff.mpr
        change (prefixLaw.bind kernel) goodᶜ = 0
        rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [hprefix,
          scheduledBalancedForwardTraceLaw_ae_valid parameters q I phase]
          with trace htrace hvalid
        apply MeasureTheory.mem_ae_iff.mp
        unfold kernel scheduledBalancedTracePhaseKernel
        apply (ae_map_iff
          ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable hgood).2
        filter_upwards with result
        simp only [Function.comp_apply, id_eq]
        rw [scheduledBalancedTraceChronologicalPhaseVariable_append_eq q hvalid
          (by omega) hj1 hjold]
        exact htrace

/-- The actual nonnegative trace variable is square-integrable on the full
finite scheduled execution law. -/
theorem memLp_scheduledBalancedForwardTrace_phaseVariable
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ figureOneDependentPhaseCount q) :
    MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  obtain ⟨B, hB0, hbound⟩ :=
    exists_scheduledBalancedForwardTrace_coordinate_bound
      figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q) j hj1 hjm le_rfl
  have hnonneg := scheduledBalancedForwardTraceLaw_ae_coordinatesNonnegative
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  have hW0 : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      0 ≤ scheduledBalancedTracePhaseVariable q j trace :=
    Filter.Eventually.of_forall
      (scheduledBalancedTracePhaseVariable_nonnegative q j)
  have hWB : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      scheduledBalancedTracePhaseVariable q j trace ≤ B := by
    filter_upwards [hbound, hnonneg] with trace hraw hcoordinates
    have hjrepr : j = (j - 1) + 1 := by omega
    have hraw0 : 0 ≤
        scheduledBalancedTraceChronologicalPhaseVariable q j trace := by
      rw [hjrepr]
      unfold scheduledBalancedTraceChronologicalPhaseVariable
      rw [balancedCoolingChronologicalPhaseVariable_apply_succ q (j - 1)
        (by omega) (some trace.1)]
      exact hcoordinates.2 (j - 1) (by omega)
    simpa [scheduledBalancedTracePhaseVariable, max_eq_right hraw0] using hraw
  exact memLp_two_of_ae_nonnegative_le
    (measurable_scheduledBalancedTracePhaseVariable q j) hB0 hW0 hWB

/-! ## Centered-to-raw second moments -/

/-- Exact centered-to-raw conversion at an arbitrary relative factor.  This
is the form consumed by the paired phase-average calculation: its variance
budget is precisely the excess `factor - 1`. -/
theorem integral_sq_le_factor_mul_integral_sq_of_centered
    {S : Type*} [MeasurableSpace S]
    {mu : Measure S} [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : MemLp f 2 mu) (factor : ℝ)
    (hcenter :
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) ≤
        (factor - 1) * (∫ x, f x ∂mu) ^ 2) :
    (∫ x, f x ^ 2 ∂mu) ≤ factor * (∫ x, f x ∂mu) ^ 2 := by
  have hcenterEq :
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) =
        (∫ x, f x ^ 2 ∂mu) - (∫ x, f x ∂mu) ^ 2 := by
    calc
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) =
          Arlib.MarkovChains.varianceReal mu f := by
        symm
        change ProbabilityTheory.variance f mu = _
        simpa using
          (ProbabilityTheory.variance_eq_integral hf.aemeasurable)
      _ = (∫ x, f x ^ 2 ∂mu) - (∫ x, f x ∂mu) ^ 2 :=
        Arlib.MarkovChains.varianceReal_eq_sub hf
  rw [hcenterEq] at hcenter
  linarith

/-- A centered second-moment estimate with coefficient three is exactly the
raw second-moment estimate used by the executable capstone.  Stating this
separately lets the paired/L² argument work with the centered numerator that
appears in the CV18 variance calculation. -/
theorem integral_sq_le_four_mul_integral_sq_of_centered_three
    {S : Type*} [MeasurableSpace S]
    {mu : Measure S} [IsProbabilityMeasure mu]
    {f : S → ℝ} (hf : MemLp f 2 mu)
    (hcenter :
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) ≤
        3 * (∫ x, f x ∂mu) ^ 2) :
    (∫ x, f x ^ 2 ∂mu) ≤ 4 * (∫ x, f x ∂mu) ^ 2 := by
  have hcenterEq :
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) =
        (∫ x, f x ^ 2 ∂mu) - (∫ x, f x ∂mu) ^ 2 := by
    calc
      (∫ x, (f x - ∫ y, f y ∂mu) ^ 2 ∂mu) =
          Arlib.MarkovChains.varianceReal mu f := by
        symm
        change ProbabilityTheory.variance f mu = _
        simpa using
          (ProbabilityTheory.variance_eq_integral hf.aemeasurable)
      _ = (∫ x, f x ^ 2 ∂mu) - (∫ x, f x ∂mu) ^ 2 :=
        Arlib.MarkovChains.varianceReal_eq_sub hf
  rw [hcenterEq] at hcenter
  linarith

/-- Consequently, for each chronological coordinate it remains to prove the
paper's centered phase-average estimate.  Square-integrability is supplied by
the executable scheduled-trace support theorem above. -/
theorem scheduledFigureOneTrace_rawSecond_four_of_centered_three
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ figureOneDependentPhaseCount q)
    (hcenter :
      (∫ trace,
          (scheduledBalancedTracePhaseVariable q j trace -
            scheduledFigureOneTraceRawMean q I j) ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        3 * scheduledFigureOneTraceRawMean q I j ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      4 * scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  apply integral_sq_le_four_mul_integral_sq_of_centered_three
    (memLp_scheduledBalancedForwardTrace_phaseVariable q I j hj1 hjm)
  simpa [scheduledFigureOneTraceRawMean] using hcenter

/-- Schedule specialization of the exact paired-variance interface. -/
theorem scheduledFigureOneTrace_rawSecond_le_of_centered
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ figureOneDependentPhaseCount q)
    (hcenter :
      (∫ trace,
          (scheduledBalancedTracePhaseVariable q j trace -
            scheduledFigureOneTraceRawMean q I j) ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (figureOneChronologicalMomentFactor q j - 1) *
          scheduledFigureOneTraceRawMean q I j ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneChronologicalMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  apply integral_sq_le_factor_mul_integral_sq_of_centered
    (memLp_scheduledBalancedForwardTrace_phaseVariable q I j hj1 hjm)
      (figureOneChronologicalMomentFactor q j)
  simpa [scheduledFigureOneTraceRawMean] using hcenter

#print axioms exists_scheduledPhaseBody_weight_upper_bound
#print axioms memLp_scheduledBalancedTransitionCollect_average_of_continuous
#print axioms memLp_scheduledBalancedCoolingRatioTransitionLaw_ratio
#print axioms memLp_scheduledBalancedCoolingUniformTransitionLaw_ratio
#print axioms exists_scheduledBalancedForwardTrace_coordinate_bound
#print axioms memLp_scheduledBalancedForwardTrace_phaseVariable
#print axioms integral_sq_le_four_mul_integral_sq_of_centered_three
#print axioms scheduledFigureOneTrace_rawSecond_four_of_centered_three
#print axioms integral_sq_le_factor_mul_integral_sq_of_centered
#print axioms scheduledFigureOneTrace_rawSecond_le_of_centered

end ArlibCommunity.Algorithms.CV18
