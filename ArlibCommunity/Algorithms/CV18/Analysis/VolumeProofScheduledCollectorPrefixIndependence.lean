/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorInitializedSampleHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorConditionedTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianEndpointMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorDependenceArithmetic

/-!
# Prefix independence for the scheduled initialized collector

This instantiates CV18 Lemma 7.17(b) for every tail coordinate of a phase
whose exact first sample is stored at coordinate zero.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- Asymmetric form of Lemma 7.17(b): conditioned and unconditional starts
may have different additive errors relative to their common target. -/
theorem approxIndepFun_history_next_of_state_warm_base_leUpTo
    {H S T : Type*} [MeasurableSpace H] [MeasurableSpace S]
    [MeasurableSpace T]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (state : H → S) (hstate : Measurable state)
    (K : S → Measure T) (hK : Measurable K)
    (hKprob : ∀ s, IsProbabilityMeasure (K s))
    (target : Measure T) [IsProbabilityMeasure target]
    {conditionedError baseError : ENNReal}
    (hconditionedTop : conditionedError ≠ ⊤)
    (hbaseTop : baseError ≠ ⊤)
    (hconditioned : ∀ mu : Measure S, IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu (rho.map state) →
      MeasureLeUpTo (mu.bind K) target conditionedError)
    (hbase : MeasureLeUpTo ((rho.map state).bind K) target baseError) :
    ApproxIndepFun (conditionedError + baseError).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho (K ∘ state)) := by
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
    rho (hK.comp hstate) (fun history => hKprob (state history))
      (ENNReal.add_ne_top.mpr ⟨hconditionedTop, hbaseTop⟩)
  intro A hA hhalf
  have hAposReal : 0 < rho.real A := lt_of_lt_of_le (by norm_num) hhalf
  have hA0 : rho A ≠ 0 := by
    intro hzero
    rw [measureReal_def, hzero] at hAposReal
    simp at hAposReal
  let hcondProb : IsProbabilityMeasure (Arlib.condOn rho A) :=
    Arlib.isProbabilityMeasure_condOn rho hA0 (measure_ne_top rho A)
  let _ : IsProbabilityMeasure (Arlib.condOn rho A) := hcondProb
  let _ : IsProbabilityMeasure
      ((Arlib.condOn rho A).bind (K ∘ state)) :=
    isProbabilityMeasure_bind (hK.comp hstate).aemeasurable
      (ae_of_all _ fun history => hKprob (state history))
  let _ : IsProbabilityMeasure (rho.bind (K ∘ state)) :=
    isProbabilityMeasure_bind (hK.comp hstate).aemeasurable
      (ae_of_all _ fun history => hKprob (state history))
  have hprojectedProb : IsProbabilityMeasure
      ((Arlib.condOn rho A).map state) :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hcond := hconditioned ((Arlib.condOn rho A).map state)
    hprojectedProb (isWarm_map (isWarm_condOn_two_of_half rho hA hhalf) hstate)
  rw [map_bind_eq_bind_comp_state (Arlib.condOn rho A) hstate hK] at hcond
  rw [map_bind_eq_bind_comp_state rho hstate hK] at hbase
  exact hcond.to_tvLe.trans hbase.to_tvLe.symm

/-- Conditioned one-step error at tail time `i`. -/
noncomputable def scheduledRetainedConditioningError
    (q : VolumeParams) (i : ℕ) : ENNReal :=
  figureOneCorrectedTransitionBudget q +
    2 * (scheduledBalancedStationaryTargetError q +
      i • figureOneCorrectedTransitionBudget q)

/-- Unconditional exact-start endpoint error after `i` transitions. -/
noncomputable def scheduledRetainedEndpointError
    (q : VolumeParams) (i : ℕ) : ENNReal :=
  2 * scheduledBalancedStationaryTargetError q +
    i • figureOneCorrectedTransitionBudget q

theorem scheduledRetainedConditioningError_ne_top
    (q : VolumeParams) (i : ℕ) :
    scheduledRetainedConditioningError q i ≠ ⊤ := by
  unfold scheduledRetainedConditioningError
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.ofReal_ne_top
  · apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top

theorem scheduledRetainedEndpointError_ne_top
    (q : VolumeParams) (i : ℕ) :
    scheduledRetainedEndpointError q i ≠ ⊤ := by
  unfold scheduledRetainedEndpointError
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top (by norm_num) <|
      ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
  · rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top

/-- The initialized coordinate-recording law for one scheduled phase. -/
noncomputable def initializedScheduledRetainedHistoryLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
  iteratedKernelLaw
    (fun i => retainedSampleHistoryKernel
      (figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)) (i + 1))
    ((truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
        retainedSampleHistoryWithFirst)
    tail

theorem initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    IsProbabilityMeasure
      (initializedScheduledRetainedHistoryLaw q I phase tail) := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let initial : Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
    exact.map retainedSampleHistoryWithFirst
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hinitial : IsProbabilityMeasure initial := by
    dsimp [initial]
    exact Measure.isProbabilityMeasure_map
      measurable_retainedSampleHistoryWithFirst.aemeasurable
  simpa [initializedScheduledRetainedHistoryLaw, exact, initial, K] using
    (iteratedKernelLaw_isProbabilityMeasure
      (fun i => retainedSampleHistoryKernel K (i + 1)) initial hinitial
      (fun i =>
        (retainedSampleHistoryKernel_measurable_and_probability
          K hK.1 hK.2 (i + 1)).1)
      (fun i history =>
        (retainedSampleHistoryKernel_measurable_and_probability
          K hK.1 hK.2 (i + 1)).2 history)
      tail)

/-- The retained state marginal at tail time `i` is exactly the killed chain
from the exact first sample after `i` transitions. -/
theorem map_initializedScheduledRetainedHistoryLaw_state
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    (initializedScheduledRetainedHistoryLaw q I phase i).map
        retainedSampleHistoryState =
      iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        i := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  rw [initializedScheduledRetainedHistoryLaw,
    map_iterated_initializedRetainedSampleHistoryKernel_state
      K hK.1 hK.2]
  rw [map_retainedSampleHistoryWithFirst_state]

/-- CV18 Lemma 7.17(b) for tail sample `i + 1`, transported to the final
history horizon. -/
theorem approxIndepFun_initializedScheduledRetainedHistory_prefix_next
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {i tail : ℕ} (hi : i < tail) :
    ApproxIndepFun
      (scheduledRetainedConditioningError q i +
        scheduledRetainedEndpointError q (i + 1)).toReal
      (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) (i + 1))
      (retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) (i + 1))
      (initializedScheduledRetainedHistoryLaw q I phase tail) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let exactSome : Measure (Option (AmbientSpace q.n)) := exact.map some
  let initial : Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
    exact.map retainedSampleHistoryWithFirst
  let rho := initializedScheduledRetainedHistoryLaw q I phase i
  let delta := scheduledRetainedConditioningError q i
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hrho : IsProbabilityMeasure rho := by
    simpa [rho] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase i
  have hexactSome : IsProbabilityMeasure exactSome := by
    dsimp [exactSome]
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let _ : IsProbabilityMeasure rho := hrho
  let _ : IsProbabilityMeasure exactSome := hexactSome
  have hbaseEndpoint : MeasureLeUpTo
      ((rho.map retainedSampleHistoryState).bind K) exactSome
      (scheduledRetainedEndpointError q (i + 1)) := by
    rw [map_initializedScheduledRetainedHistoryLaw_state q I phase i]
    rw [← iteratedKernelLaw_succ]
    simpa [K, exactSome, exact, scheduledRetainedEndpointError] using
      iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
        q I phase (i + 1)
  have hbase := approxIndepFun_history_next_of_state_warm_base_leUpTo
    rho retainedSampleHistoryState measurable_snd K hK.1 hK.2 exactSome
      (scheduledRetainedConditioningError_ne_top q i)
      (scheduledRetainedEndpointError_ne_top q (i + 1))
      (fun mu hmu hwarm => by
        let _ : IsProbabilityMeasure mu := hmu
        apply
          bind_figureOneFinalScheduledRetainedOptionKernel_leUpTo_of_warm_iterated_truncated
            q I phase i mu
        simpa [rho, K, exactSome, exact,
          map_initializedScheduledRetainedHistoryLaw_state q I phase i] using
          hwarm)
      hbaseEndpoint
  have hpair := hbase.comp
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1))) t) (i + 1))
    (measurable_retainedOptionWeight
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1))))
  apply initializedRetainedSampleHistory_approxIndep_prefix_next_final
    K hK.1 hK.2 weight
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1))) initial hi
  simpa only [rho, initial, exact, exactSome, K, weight, delta,
    initializedScheduledRetainedHistoryLaw, Function.comp_def] using hpair

/-- Uniform form of Lemma 7.17(b)/(c) for every coordinate of a complete
initialized collector.  Coordinate zero has a constant empty prefix; every
successor coordinate uses the conditioned transition estimate above. -/
theorem approxIndepFun_initializedScheduledRetainedHistory_all
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : count ≤ figureOneDependentMaxSampleCount q)
    (r : ℕ) (hr : r < count) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) r)
      (retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) r)
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1)) := by
  cases r with
  | zero =>
      let _ : IsProbabilityMeasure
          (initializedScheduledRetainedHistoryLaw q I phase (count - 1)) :=
        initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
          q I phase (count - 1)
      change ApproxIndepFun (figureOneDependentEpsilon q)
        (fun _ => (0 : ℝ))
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) 0)
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
      exact approxIndepFun_const_left_of_nonneg
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        (0 : ℝ)
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) 0)
        (figureOneDependentEpsilon_nonneg q)
  | succ i =>
      have hiTail : i < count - 1 := by omega
      have hpair :=
        approxIndepFun_initializedScheduledRetainedHistory_prefix_next
          q I phase hiTail
      apply hpair.mono
      simpa [scheduledRetainedConditioningError,
        scheduledRetainedEndpointError] using
        killedCollector_asymmetric_error_le_dependentEpsilon q
          (Nat.lt_trans (Nat.lt_succ_self i) hr) hcount

#print axioms scheduledRetainedConditioningError_ne_top
#print axioms scheduledRetainedEndpointError_ne_top
#print axioms approxIndepFun_history_next_of_state_warm_base_leUpTo
#print axioms initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
#print axioms map_initializedScheduledRetainedHistoryLaw_state
#print axioms
  approxIndepFun_initializedScheduledRetainedHistory_prefix_next
#print axioms approxIndepFun_initializedScheduledRetainedHistory_all

end ArlibCommunity.Algorithms.CV18
