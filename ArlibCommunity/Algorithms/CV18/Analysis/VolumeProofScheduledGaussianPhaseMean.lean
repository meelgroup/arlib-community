/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianEndpointMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox

/-!
# First moment of the complete scheduled Gaussian phase

The paper-faithful complete-phase target draws its first retained point from
the exact truncated Gaussian and then uses the executable killed Markov tail.
Here it is identified with the retained-sum shadow so its mean can be reduced
to the endpoint marginals proved in `VolumeProofScheduledGaussianEndpointMean`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

/-- Killing an accumulated nonnegative total only on the final dead event
costs at most its `L²` norm times the square root of the death probability.
This is the usable replacement for multiplying the tiny failure probability
by the enormous compact-support supremum of an early Gaussian ratio. -/
theorem integral_retainedLiveTotal_loss_le_sqrt
    {S : Type*} [MeasurableSpace S]
    (mu : Measure (ℝ × Option S)) [IsProbabilityMeasure mu]
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1)
    (htotalMem : MemLp (fun state : ℝ × Option S => state.1) 2 mu) :
    (∫ state, state.1 ∂mu) - ∫ state, retainedLiveTotal state ∂mu ≤
      Real.sqrt (∫ state, state.1 ^ 2 ∂mu) *
        Real.sqrt (mu.real {state | state.2 = none}) := by
  let dead : Set (ℝ × Option S) := {state | state.2 = none}
  let killed : ℝ × Option S → ℝ :=
    dead.indicator (fun _ => (1 : ℝ))
  have hdead : MeasurableSet dead :=
    measurable_snd measurableSet_option_none
  have hkilled : Measurable killed := measurable_const.indicator hdead
  have hkilledMem : MemLp killed 2 mu := by
    apply MemLp.of_bound hkilled.aestronglyMeasurable 1
    filter_upwards with state
    by_cases hstate : state ∈ dead
    · simp [killed, Set.indicator_of_mem hstate]
    · simp [killed, Set.indicator_of_notMem hstate]
  have hfstInt : Integrable (fun state : ℝ × Option S => state.1) mu :=
    htotalMem.integrable (by norm_num)
  have hliveInt : Integrable (retainedLiveTotal (S := S)) mu := by
    apply Integrable.mono' hfstInt
      measurable_retainedLiveTotal.aestronglyMeasurable
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    cases state with
    | none =>
        simpa [retainedLiveTotal] using hstate0
    | some value =>
        simpa [retainedLiveTotal, Real.norm_eq_abs,
          abs_of_nonneg hstate0] using hstate0
  have hloss : (∫ state, state.1 ∂mu) -
        ∫ state, retainedLiveTotal state ∂mu =
      ∫ state, state.1 * killed state ∂mu := by
    rw [← integral_sub hfstInt hliveInt]
    apply integral_congr_ae
    filter_upwards with state
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, killed, dead]
  have hkilledSq : (∫ state, killed state ^ 2 ∂mu) = mu.real dead := by
    calc
      (∫ state, killed state ^ 2 ∂mu) = ∫ state, killed state ∂mu := by
        apply integral_congr_ae
        filter_upwards with state
        by_cases hstate : state ∈ dead <;>
          simp [killed, Set.indicator_of_mem, Set.indicator_of_notMem, hstate]
      _ = mu.real dead := by
        simpa [killed] using integral_indicator_const (μ := mu) (1 : ℝ) hdead
  rw [hloss]
  have hCS := integral_mul_le_sqrt_mul_sqrt htotalMem hkilledMem
  rw [hkilledSq] at hCS
  exact hCS

/-- Averaged form of the preceding death-loss estimate. -/
theorem integral_retainedLiveAverage_loss_le_sqrt
    {S : Type*} [MeasurableSpace S]
    (mu : Measure (ℝ × Option S)) [IsProbabilityMeasure mu]
    {count : ℕ} (hcount : 0 < count)
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1)
    (haverageMem : MemLp
      (fun state : ℝ × Option S => state.1 / (count : ℝ)) 2 mu) :
    (∫ state, state.1 / (count : ℝ) ∂mu) -
        ∫ state, retainedLiveTotal state / (count : ℝ) ∂mu ≤
      Real.sqrt (∫ state, (state.1 / (count : ℝ)) ^ 2 ∂mu) *
        Real.sqrt (mu.real {state | state.2 = none}) := by
  let dead : Set (ℝ × Option S) := {state | state.2 = none}
  let average : ℝ × Option S → ℝ := fun state =>
    state.1 / (count : ℝ)
  let liveAverage : ℝ × Option S → ℝ := fun state =>
    retainedLiveTotal state / (count : ℝ)
  let killed : ℝ × Option S → ℝ :=
    dead.indicator (fun _ => (1 : ℝ))
  have hdead : MeasurableSet dead :=
    measurable_snd measurableSet_option_none
  have hkilled : Measurable killed := measurable_const.indicator hdead
  have hkilledMem : MemLp killed 2 mu := by
    apply MemLp.of_bound hkilled.aestronglyMeasurable 1
    filter_upwards with state
    by_cases hstate : state ∈ dead
    · simp [killed, Set.indicator_of_mem hstate]
    · simp [killed, Set.indicator_of_notMem hstate]
  have havgInt : Integrable average mu :=
    haverageMem.integrable (by norm_num)
  have hliveInt : Integrable liveAverage mu := by
    apply Integrable.mono' havgInt
      (measurable_retainedLiveTotal.div_const (count : ℝ)).aestronglyMeasurable
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
    cases state with
    | none =>
        change ‖0 / (count : ℝ)‖ ≤ total / (count : ℝ)
        simp only [zero_div, norm_zero]
        exact div_nonneg hstate0 hcountR.le
    | some value =>
        change ‖total / (count : ℝ)‖ ≤ total / (count : ℝ)
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hstate0 hcountR.le)]
  have hloss : (∫ state, average state ∂mu) -
        ∫ state, liveAverage state ∂mu =
      ∫ state, average state * killed state ∂mu := by
    rw [← integral_sub havgInt hliveInt]
    apply integral_congr_ae
    filter_upwards with state
    rcases state with ⟨total, state⟩
    cases state <;> simp [average, liveAverage, retainedLiveTotal, killed, dead]
  have hkilledSq : (∫ state, killed state ^ 2 ∂mu) = mu.real dead := by
    calc
      (∫ state, killed state ^ 2 ∂mu) = ∫ state, killed state ∂mu := by
        apply integral_congr_ae
        filter_upwards with state
        by_cases hstate : state ∈ dead <;>
          simp [killed, Set.indicator_of_mem, Set.indicator_of_notMem, hstate]
      _ = mu.real dead := by
        simpa [killed] using integral_indicator_const (μ := mu) (1 : ℝ) hdead
  rw [hloss]
  have hCS := integral_mul_le_sqrt_mul_sqrt haverageMem hkilledMem
  rw [hkilledSq] at hCS
  exact hCS

/-- Real endpoint-sum identity without a global pointwise bound on the
observable.  Finite `L²` moments of the finitely many marginals are enough;
this is the form needed for early Gaussian cooling ratios. -/
theorem integral_iterated_retainedSumKernel_total_eq_sum_marginals_of_memLp
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (initial : Measure (ℝ × Option S)) [IsProbabilityMeasure initial]
    (hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1)
    (steps : ℕ)
    (hshadowMem : MemLp (fun state : ℝ × Option S => state.1) 2
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial steps))
    (hinitialMem : MemLp (fun state : ℝ × Option S => state.1) 2 initial)
    (hendpointMem : ∀ i, i < steps →
      MemLp (retainedOptionWeight weight) 2
        (iteratedKernelLaw (fun _ => K)
          (initial.map retainedSumState) (i + 1))) :
    (∫ state, state.1
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial steps) =
      (∫ state, state.1 ∂initial) +
        ∑ i ∈ Finset.range steps,
          ∫ state, retainedOptionWeight weight state
            ∂iteratedKernelLaw (fun _ => K)
              (initial.map retainedSumState) (i + 1) := by
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let endpoint : ℕ → Measure (Option S) := fun i =>
    iteratedKernelLaw (fun _ => K)
      (initial.map retainedSumState) (i + 1)
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) steps
  have hendpointProb : ∀ i, IsProbabilityMeasure (endpoint i) := by
    intro i
    dsimp only [endpoint]
    exact iteratedKernelLaw_isProbabilityMeasure
      (fun _ => K) (initial.map retainedSumState)
      (Measure.isProbabilityMeasure_map measurable_snd.aemeasurable)
      (fun _ => hK) (fun _ => hKprob) (i + 1)
  have hshadow0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 :=
    iterated_retainedSumKernel_ae_total_nonnegative
      K hK hKprob weight hweight hweight0 initial hinitial0 steps
  have hweightOpt0 : ∀ state : Option S,
      0 ≤ retainedOptionWeight weight state := by
    intro state
    cases state with
    | none => rfl
    | some state => exact hweight0 state
  have hshadowInt : Integrable (fun state : ℝ × Option S => state.1)
      shadow := hshadowMem.integrable (by norm_num)
  have hinitialInt : Integrable
      (fun state : ℝ × Option S => state.1) initial :=
    hinitialMem.integrable (by norm_num)
  have hendpointInt : ∀ i, i < steps →
      Integrable (retainedOptionWeight weight) (endpoint i) := by
    intro i hi
    let _ : IsProbabilityMeasure (endpoint i) := hendpointProb i
    exact (hendpointMem i hi).integrable (by norm_num)
  have hshadowNN : 0 ≤ ∫ state, state.1 ∂shadow :=
    integral_nonneg_of_ae hshadow0
  have hinitialNN : 0 ≤ ∫ state, state.1 ∂initial :=
    integral_nonneg_of_ae hinitial0
  have hendpointNN : ∀ i, 0 ≤
      ∫ state, retainedOptionWeight weight state ∂endpoint i :=
    fun i => integral_nonneg hweightOpt0
  have hlin := lintegral_iterated_retainedSumKernel_total_eq_sum_marginals
    K hK hKprob weight hweight hweight0 initial hinitial0 steps
  have hshadowConv : ENNReal.ofReal (∫ state, state.1 ∂shadow) =
      ∫⁻ state, ENNReal.ofReal state.1 ∂shadow :=
    ofReal_integral_eq_lintegral_ofReal hshadowInt hshadow0
  have hinitialConv : ENNReal.ofReal (∫ state, state.1 ∂initial) =
      ∫⁻ state, ENNReal.ofReal state.1 ∂initial :=
    ofReal_integral_eq_lintegral_ofReal hinitialInt hinitial0
  have hendpointConv : ∀ i, i < steps →
      ENNReal.ofReal
          (∫ state, retainedOptionWeight weight state ∂endpoint i) =
        ∫⁻ state, ENNReal.ofReal (retainedOptionWeight weight state)
          ∂endpoint i := by
    intro i hi
    exact ofReal_integral_eq_lintegral_ofReal (hendpointInt i hi)
      (ae_of_all _ hweightOpt0)
  have hENN : ENNReal.ofReal (∫ state, state.1 ∂shadow) =
      ENNReal.ofReal ((∫ state, state.1 ∂initial) +
        ∑ i ∈ Finset.range steps,
          ∫ state, retainedOptionWeight weight state ∂endpoint i) := by
    calc
      ENNReal.ofReal (∫ state, state.1 ∂shadow) =
          ∫⁻ state, ENNReal.ofReal state.1 ∂shadow := hshadowConv
      _ = (∫⁻ state, ENNReal.ofReal state.1 ∂initial) +
          ∑ i ∈ Finset.range steps,
            ∫⁻ state, ENNReal.ofReal
              (retainedOptionWeight weight state) ∂endpoint i := by
        simpa [shadow, endpoint] using hlin
      _ = ENNReal.ofReal (∫ state, state.1 ∂initial) +
          ∑ i ∈ Finset.range steps,
            ENNReal.ofReal
              (∫ state, retainedOptionWeight weight state ∂endpoint i) := by
        rw [hinitialConv]
        apply congrArg ((∫⁻ state, ENNReal.ofReal state.1 ∂initial) + ·)
        apply Finset.sum_congr rfl
        intro i hi
        exact (hendpointConv i (Finset.mem_range.mp hi)).symm
      _ = _ := by
        have hsumNN : 0 ≤ ∑ i ∈ Finset.range steps,
            ∫ state, retainedOptionWeight weight state ∂endpoint i :=
          Finset.sum_nonneg fun i _ => hendpointNN i
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hendpointNN i),
          ← ENNReal.ofReal_add hinitialNN hsumNN]
  exact (ENNReal.ofReal_eq_ofReal_iff hshadowNN
    (add_nonneg hinitialNN <| Finset.sum_nonneg fun i _ => hendpointNN i)).mp
      (by simpa [shadow, endpoint] using hENN)

set_option maxHeartbeats 1000000 in
/-- The common-tail Gaussian phase target is exactly the killed retained-sum
shadow, followed by the public output and averaging maps. -/
theorem figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    figureOneScheduledGaussianPhaseTarget q I phase =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)).map
          (balancedCoolingAverage count ∘ retainedSumOutput) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let s := scheduleValue q phase
  let t := scheduleValue q (phase + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q phase)
  let first : Measure (Option (AmbientSpace q.n)) := exact.map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let R := retainedSumKernel K weight
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial := exact.map initialMap
  let shadow := iteratedKernelLaw (fun _ => R) initial (count - 1)
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I s weight
          (figureOneFinalScheduledBalancedParameters.proposalCap q s)
          (figureOneFinalScheduledBalancedParameters.properStride q s)
          (figureOneFinalScheduledBalancedParameters.retryLimit q s)
          (count - 1) (weight point) (accuracyScaleFactor q • point)
  have hs : 0 < s := scheduleValue_pos q phase
  have hweight : Measurable weight := measurable_gaussianRatioWeight s t
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hs
  have hR := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  have hinitialMap : Measurable initialMap :=
    hweight.prodMk measurable_some
  have hout : Measurable
      (retainedSumOutput (S := AmbientSpace q.n)) :=
    measurable_retainedSumOutput
  have havg : Measurable
      (balancedCoolingAverage (n := q.n) count) :=
    measurable_balancedCoolingAverage count
  have htailCollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hs hweight
      (figureOneFinalScheduledBalancedParameters.proposalCap q s)
      (figureOneFinalScheduledBalancedParameters.properStride q s)
      (figureOneFinalScheduledBalancedParameters.retryLimit q s) (count - 1)
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I s weight
          (figureOneFinalScheduledBalancedParameters.proposalCap q s)
          (figureOneFinalScheduledBalancedParameters.properStride q s)
          (figureOneFinalScheduledBalancedParameters.retryLimit q s)
          (count - 1) (weight point) (accuracyScaleFactor q • point) := by
      exact htailCollect.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have hcollector : ∀ x,
      tail (some x) =
        (iteratedKernelLaw (fun _ => R)
          (Measure.dirac (initialMap x)) (count - 1)).map
            retainedSumOutput := by
    intro x
    have hKeq : scheduledBalancedRetainedOptionKernel q I s
        (figureOneFinalScheduledBalancedParameters.proposalCap q s)
        (figureOneFinalScheduledBalancedParameters.properStride q s)
        (figureOneFinalScheduledBalancedParameters.retryLimit q s) = K := by
      funext state
      cases state <;> rfl
    have hcollect :=
      scheduledBalancedTransitionCollectLaw_eq_map_retainedSumKernel
        q I hs hweight
        (figureOneFinalScheduledBalancedParameters.proposalCap q s)
        (figureOneFinalScheduledBalancedParameters.properStride q s)
        (figureOneFinalScheduledBalancedParameters.retryLimit q s)
        (count - 1) (weight x) x
    rw [hKeq] at hcollect
    simpa [tail, R, weight, s, initialMap] using hcollect
  have hiter : Measurable fun x : AmbientSpace q.n =>
      iteratedKernelLaw (fun _ => R) (Measure.dirac (initialMap x))
        (count - 1) :=
    (iteratedKernelLaw_dirac_measurable_and_probability
      (fun _ => R) (fun _ => hR.1) (fun _ _ => hR.2 _) (count - 1)).1.comp
        hinitialMap
  have hbindIter : exact.bind (fun x =>
      iteratedKernelLaw (fun _ => R) (Measure.dirac (initialMap x))
        (count - 1)) = shadow := by
    simpa [shadow, initial] using
      bind_iteratedKernelLaw_dirac_eq_iteratedKernelLaw_map
        (fun _ => R) (fun _ => hR.1) (fun _ _ => hR.2 _)
        exact initialMap hinitialMap (count - 1)
  have hfirstBind : first.bind tail = shadow.map retainedSumOutput := by
    calc
      first.bind tail = exact.bind (tail ∘ some) := by
        exact map_bind_eq_bind_comp_state exact measurable_some htail
      _ = exact.bind (fun x =>
          (iteratedKernelLaw (fun _ => R)
            (Measure.dirac (initialMap x)) (count - 1)).map
              retainedSumOutput) := by
        apply Measure.bind_congr_right
        filter_upwards with x
        exact hcollector x
      _ = (exact.bind fun x =>
          iteratedKernelLaw (fun _ => R)
            (Measure.dirac (initialMap x)) (count - 1)).map
              retainedSumOutput :=
        (map_bind_eq_bind_map_of_measurable exact hiter hout).symm
      _ = shadow.map retainedSumOutput := by rw [hbindIter]
  change (first.bind tail).map (balancedCoolingAverage count) =
    shadow.map (balancedCoolingAverage count ∘ retainedSumOutput)
  rw [hfirstBind, Measure.map_map havg hout]

/-- The average of the retained-sum shadow is close from below to the exact
Gaussian mean.  All finite endpoint errors are charged at their largest
horizon, so the final loss remains `2 * eta * R`, rather than growing with
the sample count after division by the count. -/
theorem integral_figureOneScheduledGaussianShadow_average_lower
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hepsEta :
      (2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q).toReal ≤ eta ^ 2)
    (hsecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2)
    (hshadowMem :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1))) :
    (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) -
        2 * eta * R ≤
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      ∫ state, state.1 / (count : ℝ)
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let steps := count - 1
  let s := scheduleValue q phase
  let t := scheduleValue q (phase + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q phase)
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial := exact.map initialMap
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  have hs : 0 < s := scheduleValue_pos q phase
  have ht : 0 < t := scheduleValue_pos q (phase + 1)
  have hcount : 0 < count := by
    dsimp only [count]
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
  have hweight : Measurable weight := measurable_gaussianRatioWeight s t
  have hweight0 : ∀ x, 0 ≤ weight x := by
    intro x
    dsimp [weight, gaussianRatioWeight]
    positivity
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hs
  have hinitialMap : Measurable initialMap := hweight.prodMk measurable_some
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure initial :=
    Measure.isProbabilityMeasure_map hinitialMap.aemeasurable
  have hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1 := by
    apply (ae_map_iff hinitialMap.aemeasurable
      (measurableSet_le measurable_const measurable_fst)).2
    exact ae_of_all exact fun x => hweight0 x
  have hinitialMem : MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2 initial := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      hinitialMap.aemeasurable).2
    simpa [initialMap, weight, Function.comp_def] using
      gaussianRatioWeight_memLp q I hs ht 2
  have hinitialState : initial.map retainedSumState = exact.map some := by
    calc
      initial.map retainedSumState = exact.map
          (retainedSumState ∘ initialMap) :=
        Measure.map_map measurable_snd hinitialMap
      _ = exact.map some := by rfl
  have hendpointMem : ∀ i, i < steps →
      MemLp (retainedOptionWeight weight) 2
        (iteratedKernelLaw (fun _ => K)
          (initial.map retainedSumState) (i + 1)) := by
    intro i hi
    rw [hinitialState]
    simpa [weight, K, exact, s] using
      retainedOptionWeight_gaussianRatio_memLp_iterated_from_truncated
        q I phase (i + 1) ht 2
  have hidentity :=
    integral_iterated_retainedSumKernel_total_eq_sum_marginals_of_memLp
      K hK.1 hK.2 weight hweight hweight0 initial hinitial0 steps
      (by simpa [shadow, steps, initial, initialMap, K, weight, exact, s, t]
        using hshadowMem)
      hinitialMem hendpointMem
  have hinitialMean : (∫ state, state.1 ∂initial) =
      ∫ x, weight x ∂exact := by
    rw [integral_map hinitialMap.aemeasurable measurable_fst.aestronglyMeasurable]
  have hendpointLower : ∀ i, i < steps →
      (∫ x, weight x ∂exact) - 2 * eta * R ≤
        ∫ state, retainedOptionWeight weight state
          ∂iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) (i + 1) := by
    intro i hi
    have hiCount : i + 1 ≤ count := by
      dsimp only [steps] at hi
      omega
    have herrorLe :
        2 * scheduledBalancedStationaryTargetError q +
            (i + 1) • figureOneCorrectedTransitionBudget q ≤
          2 * scheduledBalancedStationaryTargetError q +
            count • figureOneCorrectedTransitionBudget q := by
      apply add_le_add le_rfl
      rw [nsmul_eq_mul, nsmul_eq_mul]
      gcongr
    have hsmall :
        (2 * scheduledBalancedStationaryTargetError q +
            (i + 1) • figureOneCorrectedTransitionBudget q).toReal ≤
          eta ^ 2 :=
      (ENNReal.toReal_mono hepsilonTop herrorLe).trans hepsEta
    have hfinite :
        2 * scheduledBalancedStationaryTargetError q +
            (i + 1) • figureOneCorrectedTransitionBudget q ≠ ⊤ :=
      ne_top_of_le_ne_top hepsilonTop herrorLe
    rw [hinitialState]
    simpa [weight, K, exact, s, t] using
      integral_iterated_retainedOption_gaussianRatio_lower
        q I phase (i + 1) ht heta hR hfinite hsmall hsecond
  have hsumLower : (steps : ℝ) *
        ((∫ x, weight x ∂exact) - 2 * eta * R) ≤
      ∑ i ∈ Finset.range steps,
        ∫ state, retainedOptionWeight weight state
          ∂iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) (i + 1) := by
    calc
      (steps : ℝ) * ((∫ x, weight x ∂exact) - 2 * eta * R) =
          ∑ _i ∈ Finset.range steps,
            ((∫ x, weight x ∂exact) - 2 * eta * R) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hendpointLower i (Finset.mem_range.mp hi)
  have hshadowLower : (count : ℝ) *
        ((∫ x, weight x ∂exact) - 2 * eta * R) ≤
      ∫ state, state.1 ∂shadow := by
    rw [show count = steps + 1 by
      dsimp only [steps]
      omega]
    push_cast
    rw [show (∫ state, state.1 ∂shadow) =
        (∫ state, state.1 ∂initial) +
          ∑ i ∈ Finset.range steps,
            ∫ state, retainedOptionWeight weight state
              ∂iteratedKernelLaw (fun _ => K)
                (initial.map retainedSumState) (i + 1) by
      simpa [shadow] using hidentity,
      hinitialMean]
    have hloss0 : 0 ≤ 2 * eta * R := by positivity
    linarith
  rw [integral_div]
  apply (le_div_iff₀ hcountR).2
  simpa [mul_comm, shadow, steps, initial, initialMap, K, weight, exact, s, t,
    count] using
    hshadowLower

/-- Complete Gaussian phase target mean, including the final all-or-nothing
killing of the accumulated estimator.  The remaining death loss is expressed
in terms of a supplied normalized shadow second moment. -/
theorem integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {eta R A : ℝ} (heta : 0 < eta) (hR : 0 < R) (hA : 0 ≤ A)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hepsEta :
      (2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q).toReal ≤ eta ^ 2)
    (hsecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2)
    (hshadowMem :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)))
    (hshadowSecond :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      (∫ state, (state.1 / (count : ℝ)) ^ 2
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)) ≤ A ^ 2) :
    (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) -
        2 * eta * R -
        A * Real.sqrt
          ((iteratedKernelLaw
            (fun _ => retainedSumKernel
              (figureOneFinalScheduledRetainedOptionKernel q I
                (scheduleValue q phase))
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1))))
            ((truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
                (fun x =>
                  (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                    (scheduleValue q (phase + 1)) x, some x)))
            (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)).real
              {state | state.2 = none}) ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledGaussianPhaseTarget q I phase := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let steps := count - 1
  let s := scheduleValue q phase
  let t := scheduleValue q (phase + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q phase)
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial := exact.map initialMap
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  have hcount : 0 < count := by
    dsimp only [count]
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
  have hweight : Measurable weight := measurable_gaussianRatioWeight s t
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q phase)
  have hsum := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure initial :=
    Measure.isProbabilityMeasure_map
      (hweight.prodMk measurable_some).aemeasurable
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) steps
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight
    · intro x
      dsimp [weight, gaussianRatioWeight]
      positivity
    · apply (ae_map_iff (hweight.prodMk measurable_some).aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      filter_upwards with x
      dsimp [initialMap, weight, gaussianRatioWeight]
      positivity
  have havgMem : MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) =>
        state.1 / (count : ℝ)) 2 shadow := by
    have h := (show MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2 shadow by
        simpa [shadow, steps, initial, initialMap, K, weight, exact, s, t]
          using hshadowMem).const_mul ((count : ℝ)⁻¹)
    simpa [div_eq_mul_inv, mul_comm] using h
  have hshadowLower :=
    integral_figureOneScheduledGaussianShadow_average_lower
      q I phase heta hR hepsilonTop hepsEta hsecond hshadowMem
  have hloss := integral_retainedLiveAverage_loss_le_sqrt
    shadow hcount htotal0 havgMem
  have hsqrtSecond :
      Real.sqrt (∫ state, (state.1 / (count : ℝ)) ^ 2 ∂shadow) ≤ A := by
    rw [Real.sqrt_le_iff]
    exact ⟨hA, by
      simpa [shadow, steps, initial, initialMap, K, weight, exact, s, t]
        using hshadowSecond⟩
  have hlossA :
      (∫ state, state.1 / (count : ℝ) ∂shadow) -
          ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow ≤
        A * Real.sqrt (shadow.real {state | state.2 = none}) :=
    hloss.trans <| mul_le_mul_of_nonneg_right hsqrtSecond (Real.sqrt_nonneg _)
  have htargetMean :
      (∫ result, figureOneScheduledTraceLiveRawOutput result
          ∂figureOneScheduledGaussianPhaseTarget q I phase) =
        ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow := by
    rw [figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel]
    rw [integral_map
      ((measurable_balancedCoolingAverage count).comp
        measurable_retainedSumOutput).aemeasurable
      measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    cases state with
    | none => simp [Function.comp_def, retainedSumOutput,
        balancedCoolingAverage, figureOneScheduledTraceLiveRawOutput,
        retainedLiveTotal]
    | some value =>
        have havg0 : 0 ≤ total / (count : ℝ) :=
          div_nonneg hstate0 hcountR.le
        simp [Function.comp_def, retainedSumOutput, balancedCoolingAverage,
          figureOneScheduledTraceLiveRawOutput, retainedLiveTotal,
          max_eq_right havg0]
  rw [htargetMean]
  simpa [shadow, steps, initial, initialMap, K, weight, exact, s, t, count]
    using (sub_le_iff_le_add.mp <| hshadowLower.trans <| by
      linarith [hlossA])

/-- The retained-sum shadow dies exactly when its optional-state marginal
dies.  Hence its final death probability is controlled by the same
accumulated retry error as the retained endpoint chain. -/
theorem figureOneScheduledGaussianShadow_dead_real_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≠ ⊤) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)).real {state | state.2 = none} ≤
      (scheduledBalancedStationaryTargetError q +
        (count - 1) • figureOneCorrectedTransitionBudget q).toReal := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let steps := count - 1
  let s := scheduleValue q phase
  let t := scheduleValue q (phase + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let initial :=
    (truncatedGaussianProbability q I s (scheduleValue_pos q phase) :
      Measure (AmbientSpace q.n)).map (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let endpoint := iteratedKernelLaw (fun _ => K)
    (initial.map retainedSumState) steps
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q phase)
  have hweight : Measurable weight := measurable_gaussianRatioWeight s t
  have hinitialState : initial.map retainedSumState =
      (truncatedGaussianProbability q I s (scheduleValue_pos q phase) :
        Measure (AmbientSpace q.n)).map some := by
    calc
      initial.map retainedSumState =
          (truncatedGaussianProbability q I s
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
              (retainedSumState ∘ fun x => (weight x, some x)) :=
        Measure.map_map measurable_snd
          (hweight.prodMk measurable_some)
      _ = _ := by rfl
  have hshadowMap : shadow.map retainedSumState = endpoint := by
    simpa [shadow, endpoint] using
      map_iterated_retainedSumKernel_state K hK.1 hK.2 weight hweight
        initial steps
  have hdead : shadow {state | state.2 = none} = endpoint {none} := by
    calc
      shadow {state | state.2 = none} =
          (shadow.map retainedSumState) {none} := by
        rw [Measure.map_apply
          (show Measurable (retainedSumState (S := AmbientSpace q.n)) from
            measurable_snd)
          measurableSet_option_none]
        rfl
      _ = endpoint {none} := by rw [hshadowMap]
  have hendpoint : endpoint {none} ≤
      scheduledBalancedStationaryTargetError q +
        steps • figureOneCorrectedTransitionBudget q := by
    dsimp only [endpoint]
    rw [hinitialState]
    simpa [K, s, steps] using
      iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_none_le
        q I phase steps
  have hcount : steps ≤ count := by
    dsimp only [steps]
    omega
  have herrorLe :
      scheduledBalancedStationaryTargetError q +
          steps • figureOneCorrectedTransitionBudget q ≤
        2 * scheduledBalancedStationaryTargetError q +
          count • figureOneCorrectedTransitionBudget q := by
    apply add_le_add
    · simpa [two_mul] using
        (self_le_add_right (scheduledBalancedStationaryTargetError q)
          (scheduledBalancedStationaryTargetError q))
    · rw [nsmul_eq_mul, nsmul_eq_mul]
      gcongr
  have herrorTop :
      scheduledBalancedStationaryTargetError q +
          steps • figureOneCorrectedTransitionBudget q ≠ ⊤ :=
    ne_top_of_le_ne_top hepsilonTop herrorLe
  rw [Measure.real, hdead]
  exact ENNReal.toReal_mono herrorTop hendpoint

/-- Fully explicit version of the Gaussian phase-target lower mean bound.
The collector death term is now the scheduled stationary-target plus retry
budget, with no reference to the internal shadow law. -/
theorem integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower_explicit
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {eta R A : ℝ} (heta : 0 < eta) (hR : 0 < R) (hA : 0 ≤ A)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hepsEta :
      (2 * scheduledBalancedStationaryTargetError q +
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q).toReal ≤ eta ^ 2)
    (hsecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2)
    (hshadowMem :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)))
    (hshadowSecond :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      (∫ state, (state.1 / (count : ℝ)) ^ 2
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)) ≤ A ^ 2) :
    (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) -
        2 * eta * R -
        A * Real.sqrt
          ((scheduledBalancedStationaryTargetError q +
            (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) •
              figureOneCorrectedTransitionBudget q).toReal) ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledGaussianPhaseTarget q I phase := by
  have hbase :=
    integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower
      q I phase heta hR hA hepsilonTop hepsEta hsecond hshadowMem
        hshadowSecond
  have hdead := figureOneScheduledGaussianShadow_dead_real_le
    q I phase hepsilonTop
  dsimp only at hdead
  have hsqrt := Real.sqrt_le_sqrt hdead
  have hmul := mul_le_mul_of_nonneg_left hsqrt hA
  exact hbase.trans' (by linarith)

#print axioms figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel
#print axioms integral_retainedLiveTotal_loss_le_sqrt
#print axioms integral_retainedLiveAverage_loss_le_sqrt
#print axioms
  integral_iterated_retainedSumKernel_total_eq_sum_marginals_of_memLp
#print axioms
  integral_figureOneScheduledGaussianShadow_average_lower
#print axioms
  integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower
#print axioms figureOneScheduledGaussianShadow_dead_real_le
#print axioms
  integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower_explicit

end ArlibCommunity.Algorithms.CV18
