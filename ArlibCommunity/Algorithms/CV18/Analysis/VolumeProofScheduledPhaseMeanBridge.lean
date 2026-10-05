/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledShadowAverageMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianPhaseMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalEndpointMoments

/-!
# Bridges from pre-kill phase histories to complete scheduled targets

The executable history records every retained observation, including those
recorded before a later retry failure.  The public complete-phase target
instead returns zero when the collector eventually dies.  This file makes
that last all-or-nothing killing step explicit.  It also supplies the
corresponding retained-sum representation for the terminal uniform phase.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

noncomputable section

/-- The initialized retained-history average is exactly the average of the
retained-sum shadow.  No independence or approximation is used here. -/
theorem integral_initializedRetainedSampleHistory_average_eq_shadow
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure S) (tail : ℕ) :
    (∫ history,
        (∑ j ∈ Finset.range (tail + 1),
          retainedSampleObservation weight j history) / ((tail + 1 : ℕ) : ℝ)
      ∂iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K (i + 1))
        (initial.map retainedSampleHistoryWithFirst) tail) =
      ∫ state, state.1 / ((tail + 1 : ℕ) : ℝ)
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          (initial.map fun x => (weight x, some x)) tail := by
  let historyLaw := iteratedKernelLaw
    (fun i => retainedSampleHistoryKernel K (i + 1))
    (initial.map retainedSampleHistoryWithFirst) tail
  let toSum := retainedSampleHistoryToSum weight (tail + 1)
  let average : ℝ × Option S → ℝ := fun state =>
    state.1 / ((tail + 1 : ℕ) : ℝ)
  have htoSum : Measurable toSum :=
    measurable_retainedSampleHistoryToSum hweight (tail + 1)
  have havg : Measurable average := measurable_fst.div_const _
  have hmap := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K hK hKprob weight hweight initial tail
  rw [← hmap, integral_map htoSum.aemeasurable havg.aestronglyMeasurable]
  rfl

set_option maxHeartbeats 1000000 in
/-- The complete scheduled terminal target is the retained-sum shadow,
followed by the public output and averaging maps. -/
theorem figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel
    (q : VolumeParams) (I : VolumeInput q.n) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    figureOneScheduledTerminalPhaseTarget q I =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)).map
          (balancedCoolingAverage count ∘ retainedSumOutput) := by
  dsimp only
  let count := figureOneSampleCount q
  let s := terminalVariance q
  let weight := uniformRatioWeight (n := q.n) s
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (terminalVariance_pos' q)
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
  have hs : 0 < s := terminalVariance_pos' q
  have hweight : Measurable weight := measurable_uniformRatioWeight s
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

/-- Mapping a nonnegative retained-sum shadow through the public collector
output and averaging maps integrates exactly the live (not-yet-killed)
shadow total divided by the sample count. -/
theorem integral_map_balancedCooling_retainedSumOutput_liveRaw_eq
    {n : ℕ} (mu : Measure (ℝ × Option (AmbientSpace n)))
    {count : ℕ} (hcount : 0 < count)
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1) :
    (∫ result, figureOneScheduledTraceLiveRawOutput result
      ∂mu.map (balancedCoolingAverage count ∘ retainedSumOutput)) =
      ∫ state, retainedLiveTotal state / (count : ℝ) ∂mu := by
  have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
  rw [integral_map
    ((measurable_balancedCoolingAverage count).comp
      measurable_retainedSumOutput).aemeasurable
    measurable_figureOneScheduledTraceLiveRawOutput.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [htotal0] with state hstate0
  rcases state with ⟨total, state⟩
  cases state with
  | none =>
      simp [Function.comp_def, retainedSumOutput, balancedCoolingAverage,
        figureOneScheduledTraceLiveRawOutput, retainedLiveTotal]
  | some value =>
      have havg0 : 0 ≤ total / (count : ℝ) :=
        div_nonneg hstate0 hcountR.le
      simp [Function.comp_def, retainedSumOutput, balancedCoolingAverage,
        figureOneScheduledTraceLiveRawOutput, retainedLiveTotal,
        max_eq_right havg0]

/-- The Gaussian complete-target raw mean is exactly the live retained-sum
shadow average. -/
theorem integral_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_shadow
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
    (∫ result, figureOneScheduledTraceLiveRawOutput result
      ∂figureOneScheduledGaussianPhaseTarget q I phase) =
      ∫ state, retainedLiveTotal state / (count : ℝ)
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let initial :=
    (truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  have hcount : 0 < count := by
    dsimp only [count]
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hweight : Measurable weight := measurable_gaussianRatioWeight _ _
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q phase)
  have hinitialMap : Measurable fun x : AmbientSpace q.n =>
      (weight x, some x) := hweight.prodMk measurable_some
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight
    · exact gaussianRatioWeight_nonnegative _ _
    · apply (ae_map_iff hinitialMap.aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      exact ae_of_all _ fun x => gaussianRatioWeight_nonnegative _ _ x
  rw [figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel]
  simpa [shadow, count, weight, K, initial] using
    integral_map_balancedCooling_retainedSumOutput_liveRaw_eq
      shadow hcount htotal0

/-- The terminal complete-target raw mean is exactly the live retained-sum
shadow average. -/
theorem integral_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_shadow
    (q : VolumeParams) (I : VolumeInput q.n) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (∫ result, figureOneScheduledTraceLiveRawOutput result
      ∂figureOneScheduledTerminalPhaseTarget q I) =
      ∫ state, retainedLiveTotal state / (count : ℝ)
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1) := by
  dsimp only
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  have hcount : 0 < count := figureOneSampleCount_pos q
  have hweight : Measurable weight := measurable_uniformRatioWeight _
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (terminalVariance_pos' q)
  have hinitialMap : Measurable fun x : AmbientSpace q.n =>
      (weight x, some x) := hweight.prodMk measurable_some
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight
    · exact uniformRatioWeight_nonnegative _
    · apply (ae_map_iff hinitialMap.aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      exact ae_of_all _ fun x => uniformRatioWeight_nonnegative _ x
  rw [figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel]
  simpa [shadow, count, weight, K, initial] using
    integral_map_balancedCooling_retainedSumOutput_liveRaw_eq
      shadow hcount htotal0

/-- Canonical scheduled specialization of the exact history-to-shadow
average identity. -/
theorem integral_initializedScheduledRetainedHistory_average_eq_shadow
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) :
    (∫ history,
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) =
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
  have htail : count - 1 + 1 = count := Nat.sub_add_cancel hcount
  simpa [initializedScheduledRetainedHistoryLaw, htail] using
    integral_initializedRetainedSampleHistory_average_eq_shadow
      (figureOneFinalScheduledRetainedOptionKernel q I (scheduleValue q phase))
      (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
        q I (scheduleValue_pos q phase)).1
      (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
        q I (scheduleValue_pos q phase)).2
      (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
      (count - 1)

/-- Exact pre-kill-to-complete-target bridge for a Gaussian phase.  The
only discrepancy is the final all-or-nothing death event, charged by
Cauchy--Schwarz against the normalized shadow second moment. -/
theorem integral_initializedScheduledRetainedHistory_average_sub_target_le_death
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (haverageMem :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)
      let initial :=
        (truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) =>
        state.1 / (count : ℝ)) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1))) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)
    (∫ history,
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) -
        ∫ result, figureOneScheduledTraceLiveRawOutput result
          ∂figureOneScheduledGaussianPhaseTarget q I phase ≤
      Real.sqrt (∫ state, (state.1 / (count : ℝ)) ^ 2 ∂shadow) *
        Real.sqrt (shadow.real {state | state.2 = none}) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let initial :=
    (truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  have hcount : 0 < count := by
    dsimp only [count]
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hweight : Measurable weight := measurable_gaussianRatioWeight _ _
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q phase)
  have hsum := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  let _ : IsProbabilityMeasure initial :=
    Measure.isProbabilityMeasure_map
      (hweight.prodMk measurable_some).aemeasurable
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) (count - 1)
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight
    · exact gaussianRatioWeight_nonnegative _ _
    · apply (ae_map_iff (hweight.prodMk measurable_some).aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      exact ae_of_all _ fun x => gaussianRatioWeight_nonnegative _ _ x
  have hloss := integral_retainedLiveAverage_loss_le_sqrt
    shadow hcount htotal0 (by simpa [shadow, count, weight, K, initial] using
      haverageMem)
  rw [show (∫ history,
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) =
      ∫ state, state.1 / (count : ℝ) ∂shadow by
        simpa [shadow, count, weight, K, initial] using
          integral_initializedScheduledRetainedHistory_average_eq_shadow
            q I phase count hcount]
  rw [show (∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledGaussianPhaseTarget q I phase) =
      ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow by
        simpa [shadow, count, weight, K, initial] using
          integral_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_shadow
            q I phase]
  exact hloss

/-- The terminal initialized history, scored with the uniform-ratio weight,
is exactly the terminal retained-sum shadow average. -/
theorem integral_initializedScheduledRetainedHistory_terminal_average_eq_shadow
    (q : VolumeParams) (I : VolumeInput q.n) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (∫ history,
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I
        (terminalPhaseSteps q) (count - 1)) =
      ∫ state, state.1 / (count : ℝ)
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1) := by
  dsimp only
  have hcount : 0 < figureOneSampleCount q := figureOneSampleCount_pos q
  have htail : figureOneSampleCount q - 1 + 1 = figureOneSampleCount q :=
    Nat.sub_add_cancel hcount
  simpa [initializedScheduledRetainedHistoryLaw, htail,
    scheduleValue_terminalPhaseSteps] using
    integral_initializedRetainedSampleHistory_average_eq_shadow
      (figureOneFinalScheduledRetainedOptionKernel q I (terminalVariance q))
      (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
        q I (terminalVariance_pos' q)).1
      (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
        q I (terminalVariance_pos' q)).2
      (uniformRatioWeight (n := q.n) (terminalVariance q))
      (measurable_uniformRatioWeight (terminalVariance q))
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n))
      (figureOneSampleCount q - 1)

/-- Terminal analogue of the Gaussian pre-kill bridge: the initialized
uniform-history average loses only the accumulated total on final death. -/
theorem integral_initializedScheduledRetainedHistory_terminal_average_sub_target_le_death
    (q : VolumeParams) (I : VolumeInput q.n)
    (haverageMem :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (terminalVariance q)
      let initial :=
        (truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) =>
        state.1 / (count : ℝ)) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1))) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)
    (∫ history,
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I
        (terminalPhaseSteps q) (count - 1)) -
        ∫ result, figureOneScheduledTraceLiveRawOutput result
          ∂figureOneScheduledTerminalPhaseTarget q I ≤
      Real.sqrt (∫ state, (state.1 / (count : ℝ)) ^ 2 ∂shadow) *
        Real.sqrt (shadow.real {state | state.2 = none}) := by
  dsimp only
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  have hcount : 0 < count := figureOneSampleCount_pos q
  have hweight : Measurable weight := measurable_uniformRatioWeight _
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (terminalVariance_pos' q)
  have hsum := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  let _ : IsProbabilityMeasure initial :=
    Measure.isProbabilityMeasure_map
      (hweight.prodMk measurable_some).aemeasurable
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) (count - 1)
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight
    · exact uniformRatioWeight_nonnegative _
    · apply (ae_map_iff (hweight.prodMk measurable_some).aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      exact ae_of_all _ fun x => uniformRatioWeight_nonnegative _ x
  have hloss := integral_retainedLiveAverage_loss_le_sqrt
    shadow hcount htotal0 (by simpa [shadow, count, weight, K, initial] using
      haverageMem)
  rw [show (∫ history,
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)
      ∂initializedScheduledRetainedHistoryLaw q I
        (terminalPhaseSteps q) (count - 1)) =
      ∫ state, state.1 / (count : ℝ) ∂shadow by
        simpa [shadow, count, weight, K, initial] using
          integral_initializedScheduledRetainedHistory_terminal_average_eq_shadow
            q I]
  rw [show (∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledTerminalPhaseTarget q I) =
      ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow by
        simpa [shadow, count, weight, K, initial] using
          integral_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_shadow q I]
  exact hloss

/-- The terminal retained-sum shadow dies exactly when the optional retained
chain dies, so the existing endpoint retry estimate controls its death
probability. -/
theorem figureOneScheduledTerminalShadow_dead_real_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOneSampleCount q • figureOneCorrectedTransitionBudget q ≠ ⊤) :
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (terminalVariance q)
    let initial :=
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)).real {state | state.2 = none} ≤
      (scheduledBalancedStationaryTargetError q +
        (count - 1) • figureOneCorrectedTransitionBudget q).toReal := by
  dsimp only
  let count := figureOneSampleCount q
  let steps := count - 1
  let s := terminalVariance q
  let weight := uniformRatioWeight (n := q.n) s
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let initial :=
    (truncatedGaussianProbability q I s (terminalVariance_pos' q) :
      Measure (AmbientSpace q.n)).map (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let endpoint := iteratedKernelLaw (fun _ => K)
    (initial.map retainedSumState) steps
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (terminalVariance_pos' q)
  have hweight : Measurable weight := measurable_uniformRatioWeight s
  have hinitialState : initial.map retainedSumState =
      (truncatedGaussianProbability q I s (terminalVariance_pos' q) :
        Measure (AmbientSpace q.n)).map some := by
    calc
      initial.map retainedSumState =
          (truncatedGaussianProbability q I s (terminalVariance_pos' q) :
            Measure (AmbientSpace q.n)).map
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
          (show Measurable (retainedSumState
            (S := AmbientSpace q.n)) from measurable_snd)
          measurableSet_option_none]
        rfl
      _ = endpoint {none} := by rw [hshadowMap]
  have hendpoint : endpoint {none} ≤
      scheduledBalancedStationaryTargetError q +
        steps • figureOneCorrectedTransitionBudget q := by
    dsimp only [endpoint]
    rw [hinitialState]
    simpa [K, s, steps, scheduleValue_terminalPhaseSteps] using
      iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_none_le
        q I (terminalPhaseSteps q) steps
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

/-- Complete terminal-phase target mean.  Finite endpoint bias is charged
at the largest terminal horizon and the final all-or-nothing death is
charged by the normalized shadow second moment. -/
theorem integral_figureOneScheduledTerminalPhaseTarget_liveRaw_lower
    (q : VolumeParams) (I : VolumeInput q.n) {A : ℝ} (hA : 0 ≤ A)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOneSampleCount q • figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hshadowMem :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (terminalVariance q)
      let initial :=
        (truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)))
    (hshadowSecond :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (terminalVariance q)
      let initial :=
        (truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      (∫ state, (state.1 / (count : ℝ)) ^ 2
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)) ≤ A ^ 2) :
    figureOneIdealPhaseMean q I .terminal -
        Real.exp (1 / 2) *
          (2 * scheduledBalancedStationaryTargetError q +
            figureOneSampleCount q •
              figureOneCorrectedTransitionBudget q).toReal -
        A * Real.sqrt
          ((iteratedKernelLaw
            (fun _ => retainedSumKernel
              (figureOneFinalScheduledRetainedOptionKernel q I
                (terminalVariance q))
              (uniformRatioWeight (n := q.n) (terminalVariance q)))
            ((truncatedGaussianProbability q I (terminalVariance q)
              (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
                (fun x =>
                  (uniformRatioWeight (terminalVariance q) x, some x)))
            (figureOneSampleCount q - 1)).real
              {state | state.2 = none}) ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledTerminalPhaseTarget q I := by
  let count := figureOneSampleCount q
  let steps := count - 1
  let s := terminalVariance q
  let weight := uniformRatioWeight (n := q.n) s
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (terminalVariance_pos' q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial := exact.map initialMap
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let epsilon := 2 * scheduledBalancedStationaryTargetError q +
    count • figureOneCorrectedTransitionBudget q
  have hcount : 0 < count := figureOneSampleCount_pos q
  have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
  have hs : 0 < s := terminalVariance_pos' q
  have hweight : Measurable weight := measurable_uniformRatioWeight s
  have hweight0 : ∀ x, 0 ≤ weight x :=
    uniformRatioWeight_nonnegative s
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hs
  have hsum := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  have hinitialMap : Measurable initialMap := hweight.prodMk measurable_some
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure initial :=
    Measure.isProbabilityMeasure_map hinitialMap.aemeasurable
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) steps
  have hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1 := by
    apply (ae_map_iff hinitialMap.aemeasurable
      (measurableSet_le measurable_const measurable_fst)).2
    exact ae_of_all exact hweight0
  have hinitialMem : MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2 initial := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      hinitialMap.aemeasurable).2
    simpa [initialMap, weight, Function.comp_def] using
      uniformRatioWeight_memLp q I hs 2
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
    let endpoint := iteratedKernelLaw (fun _ => K) (exact.map some) (i + 1)
    let _ : IsProbabilityMeasure (exact.map some) :=
      Measure.isProbabilityMeasure_map measurable_some.aemeasurable
    let _ : IsProbabilityMeasure endpoint :=
      iteratedKernelLaw_isProbabilityMeasure (fun _ => K) (exact.map some)
        inferInstance (fun _ => hK.1) (fun _ => hK.2) (i + 1)
    apply MemLp.of_bound
      (measurable_retainedOptionWeight hweight).aestronglyMeasurable
      (Real.exp (1 / 2))
    filter_upwards [show ∀ᵐ result ∂endpoint,
        0 ≤ retainedOptionWeight weight result ∧
          retainedOptionWeight weight result ≤ Real.exp (1 / 2) by
      simpa [endpoint, exact, K, weight, s,
        scheduleValue_terminalPhaseSteps] using
        retainedOptionWeight_uniform_terminal_ae_bounds_iterated q I (i + 1)]
      with result hresult
    rw [Real.norm_eq_abs, abs_of_nonneg hresult.1]
    exact hresult.2
  have hidentity :=
    integral_iterated_retainedSumKernel_total_eq_sum_marginals_of_memLp
      K hK.1 hK.2 weight hweight hweight0 initial hinitial0 steps
      (by simpa [shadow, steps, initial, initialMap, K, weight, exact, s]
        using hshadowMem)
      hinitialMem hendpointMem
  have hinitialMean : (∫ state, state.1 ∂initial) =
      figureOneIdealPhaseMean q I .terminal := by
    rw [integral_map hinitialMap.aemeasurable
      measurable_fst.aestronglyMeasurable]
    simpa [exact, weight, s, initialMap, Function.comp_def,
      figureOneIdealPhaseMean] using
      uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)
  have hendpointLower : ∀ i, i < steps →
      figureOneIdealPhaseMean q I .terminal -
          Real.exp (1 / 2) * epsilon.toReal ≤
        ∫ state, retainedOptionWeight weight state
          ∂iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) (i + 1) := by
    intro i hi
    have hiCount : i + 1 ≤ count := by
      dsimp only [steps] at hi
      omega
    have herrorLe :
        2 * scheduledBalancedStationaryTargetError q +
            (i + 1) • figureOneCorrectedTransitionBudget q ≤ epsilon := by
      dsimp only [epsilon]
      apply add_le_add le_rfl
      rw [nsmul_eq_mul, nsmul_eq_mul]
      gcongr
    have hfinite : epsilon ≠ ⊤ := by simpa [epsilon] using hepsilonTop
    have hrealLe := ENNReal.toReal_mono hfinite herrorLe
    have hendpoint :=
      integral_iterated_retainedOption_uniform_terminal_abs_sub_ideal_le
        q I (i + 1)
    rw [hinitialState]
    have hlower := (abs_le.mp hendpoint).1
    have hmul := mul_le_mul_of_nonneg_left hrealLe
      (Real.exp_pos ((1 : ℝ) / 2)).le
    simpa [K, weight, exact, s, epsilon,
      scheduleValue_terminalPhaseSteps] using (show
        figureOneIdealPhaseMean q I .terminal -
            Real.exp (1 / 2) * epsilon.toReal ≤
          ∫ state, retainedOptionWeight
              (uniformRatioWeight (terminalVariance q)) state
            ∂iteratedKernelLaw
              (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
                (terminalVariance q))
              ((truncatedGaussianProbability q I (terminalVariance q)
                (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
                  some)
              (i + 1) by linarith)
  have hsumLower : (steps : ℝ) *
        (figureOneIdealPhaseMean q I .terminal -
          Real.exp (1 / 2) * epsilon.toReal) ≤
      ∑ i ∈ Finset.range steps,
        ∫ state, retainedOptionWeight weight state
          ∂iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) (i + 1) := by
    calc
      (steps : ℝ) * (figureOneIdealPhaseMean q I .terminal -
          Real.exp (1 / 2) * epsilon.toReal) =
          ∑ _i ∈ Finset.range steps,
            (figureOneIdealPhaseMean q I .terminal -
              Real.exp (1 / 2) * epsilon.toReal) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hendpointLower i (Finset.mem_range.mp hi)
  have hshadowLower : (count : ℝ) *
        (figureOneIdealPhaseMean q I .terminal -
          Real.exp (1 / 2) * epsilon.toReal) ≤
      ∫ state, state.1 ∂shadow := by
    rw [show count = steps + 1 by dsimp only [steps]; omega]
    push_cast
    rw [show (∫ state, state.1 ∂shadow) =
        (∫ state, state.1 ∂initial) +
          ∑ i ∈ Finset.range steps,
            ∫ state, retainedOptionWeight weight state
              ∂iteratedKernelLaw (fun _ => K)
                (initial.map retainedSumState) (i + 1) by
      simpa [shadow] using hidentity, hinitialMean]
    have hloss0 : 0 ≤ Real.exp (1 / 2) * epsilon.toReal := by positivity
    linarith
  have hshadowAverageLower :
      figureOneIdealPhaseMean q I .terminal -
          Real.exp (1 / 2) * epsilon.toReal ≤
        ∫ state, state.1 / (count : ℝ) ∂shadow := by
    rw [integral_div]
    apply (le_div_iff₀ hcountR).2
    simpa [mul_comm] using hshadowLower
  have htotal0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 := by
    apply iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight hweight0 initial hinitial0 steps
  have havgMem : MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) =>
        state.1 / (count : ℝ)) 2 shadow := by
    have h := (show MemLp
      (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2 shadow by
        simpa [shadow, steps, initial, initialMap, K, weight, exact, s]
          using hshadowMem).const_mul ((count : ℝ)⁻¹)
    simpa [div_eq_mul_inv, mul_comm] using h
  have hloss := integral_retainedLiveAverage_loss_le_sqrt
    shadow hcount htotal0 havgMem
  have hsqrtSecond :
      Real.sqrt (∫ state, (state.1 / (count : ℝ)) ^ 2 ∂shadow) ≤ A := by
    rw [Real.sqrt_le_iff]
    exact ⟨hA, by
      simpa [shadow, steps, initial, initialMap, K, weight, exact, s]
        using hshadowSecond⟩
  have hlossA :
      (∫ state, state.1 / (count : ℝ) ∂shadow) -
          ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow ≤
        A * Real.sqrt (shadow.real {state | state.2 = none}) :=
    hloss.trans <| mul_le_mul_of_nonneg_right hsqrtSecond (Real.sqrt_nonneg _)
  rw [show (∫ result, figureOneScheduledTraceLiveRawOutput result
      ∂figureOneScheduledTerminalPhaseTarget q I) =
      ∫ state, retainedLiveTotal state / (count : ℝ) ∂shadow by
    simpa [shadow, count, steps, initial, initialMap, K, weight, exact, s] using
      integral_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_shadow q I]
  simpa [shadow, count, steps, initial, initialMap, K, weight, exact, s,
    epsilon] using (sub_le_iff_le_add.mp <| hshadowAverageLower.trans <| by
      linarith [hlossA])

/-- Fully explicit terminal target lower mean: the internal shadow death
event is replaced by the scheduled stationary-target plus retry budget. -/
theorem integral_figureOneScheduledTerminalPhaseTarget_liveRaw_lower_explicit
    (q : VolumeParams) (I : VolumeInput q.n) {A : ℝ} (hA : 0 ≤ A)
    (hepsilonTop :
      2 * scheduledBalancedStationaryTargetError q +
          figureOneSampleCount q • figureOneCorrectedTransitionBudget q ≠ ⊤)
    (hshadowMem :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (terminalVariance q)
      let initial :=
        (truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
        (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)))
    (hshadowSecond :
      let count := figureOneSampleCount q
      let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
      let K := figureOneFinalScheduledRetainedOptionKernel q I
        (terminalVariance q)
      let initial :=
        (truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
            (fun x => (weight x, some x))
      (∫ state, (state.1 / (count : ℝ)) ^ 2
        ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
          initial (count - 1)) ≤ A ^ 2) :
    figureOneIdealPhaseMean q I .terminal -
        Real.exp (1 / 2) *
          (2 * scheduledBalancedStationaryTargetError q +
            figureOneSampleCount q •
              figureOneCorrectedTransitionBudget q).toReal -
        A * Real.sqrt
          ((scheduledBalancedStationaryTargetError q +
            (figureOneSampleCount q - 1) •
              figureOneCorrectedTransitionBudget q).toReal) ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledTerminalPhaseTarget q I := by
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (terminalVariance q)
  let initial :=
    (truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  have hbase := integral_figureOneScheduledTerminalPhaseTarget_liveRaw_lower
    q I hA hepsilonTop hshadowMem hshadowSecond
  have hdead : shadow.real {state | state.2 = none} ≤
      (scheduledBalancedStationaryTargetError q +
        (count - 1) • figureOneCorrectedTransitionBudget q).toReal := by
    simpa [shadow, count, weight, K, initial] using
      figureOneScheduledTerminalShadow_dead_real_le q I hepsilonTop
  have hsqrt := Real.sqrt_le_sqrt hdead
  have hmul := mul_le_mul_of_nonneg_left hsqrt hA
  simpa [shadow, count, weight, K, initial] using (show
    figureOneIdealPhaseMean q I .terminal -
        Real.exp (1 / 2) *
          (2 * scheduledBalancedStationaryTargetError q +
            count • figureOneCorrectedTransitionBudget q).toReal -
        A * Real.sqrt
          ((scheduledBalancedStationaryTargetError q +
            (count - 1) • figureOneCorrectedTransitionBudget q).toReal) ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledTerminalPhaseTarget q I by
      linarith)

#print axioms integral_initializedRetainedSampleHistory_average_eq_shadow
#print axioms figureOneScheduledTerminalPhaseTarget_eq_map_retainedSumKernel
#print axioms integral_map_balancedCooling_retainedSumOutput_liveRaw_eq
#print axioms
  integral_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_shadow
#print axioms
  integral_figureOneScheduledTerminalPhaseTarget_liveRaw_eq_shadow
#print axioms integral_initializedScheduledRetainedHistory_average_eq_shadow
#print axioms
  integral_initializedScheduledRetainedHistory_average_sub_target_le_death
#print axioms
  integral_initializedScheduledRetainedHistory_terminal_average_eq_shadow
#print axioms
  integral_initializedScheduledRetainedHistory_terminal_average_sub_target_le_death
#print axioms figureOneScheduledTerminalShadow_dead_real_le
#print axioms integral_figureOneScheduledTerminalPhaseTarget_liveRaw_lower
#print axioms
  integral_figureOneScheduledTerminalPhaseTarget_liveRaw_lower_explicit

end

end ArlibCommunity.Algorithms.CV18
