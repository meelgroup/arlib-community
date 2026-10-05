/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetAverageSecond
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentProduct
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianPhaseMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPairedCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox

/-!
# Event-level transfer from a fixed-reset reference

An additive measure comparison does not control an unbounded second moment:
the residual mass may carry arbitrarily large values.  It does, however,
transfer every failure event with exactly its stated mass.  We therefore run
the target-centered Markov argument on the exact-coordinate reference and
only then transfer the resulting deviation event to the executable history.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- Target-centered Markov on a reference probability law, followed by an
honest one-sided event transfer to the executable law. -/
theorem MeasureLeUpTo.measure_relativeDeviation_le_of_reference_moments
    {Omega : Type*} [MeasurableSpace Omega]
    {actual reference : Measure Omega} [IsProbabilityMeasure reference]
    {error : ENNReal} (hcomparison : MeasureLeUpTo actual reference error)
    {X : Omega → ℝ} (hX : MemLp X 2 reference)
    {target eps eta delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hmeanLower : (1 - eta) * target ≤ ∫ omega, X omega ∂reference)
    (hsecond : (∫ omega, X omega ^ 2 ∂reference) ≤
      (1 + delta) * target ^ 2) :
    actual {omega | eps * target ≤ |X omega - target|} ≤
      ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) + error := by
  have href := measure_relativeDeviation_le_of_target_moments
    reference hX htarget heps heta hdelta hmeanLower hsecond
  calc
    actual {omega | eps * target ≤ |X omega - target|} ≤
        reference {omega | eps * target ≤ |X omega - target|} + error :=
      hcomparison.event_le _
    _ ≤ ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) + error := by
      gcongr

/-- Scheduled specialization of the event-level transfer.  The hypotheses
are precisely the reference-average facts supplied by the exact-coordinate
`L³` equation-(6) construction; no executable raw second moment is assumed.
-/
theorem initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcomparison : MeasureLeUpTo
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
      reference (scheduledResetReferenceError q (count - 1)))
    {target eps eta delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hmem : MemLp (fun history =>
      sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
        (count : ℝ)) 2 reference)
    (hmeanLower : (1 - eta) * target ≤
      ∫ history, sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ) ∂reference)
    (hsecond :
      (∫ history, (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + delta) * target ^ 2) :
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) - target|} ≤
      ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  exact hcomparison.measure_relativeDeviation_le_of_reference_moments
    hmem htarget heps heta hdelta hmeanLower hsecond

/-- Complete within-Gaussian-phase event adapter.  Exact coordinate moments
and the equation-(6) arithmetic are proved on one fixed-reset reference, and
only the resulting deviation event is transferred to the executable history.
-/
theorem initializedScheduledRetainedHistory_relativeDeviation_le_of_coordinate_moments
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {A factor delta eps : ℝ} (hA : 0 < A) (hdelta : 0 ≤ delta)
    (heps : 0 < eps)
    (hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2)
    (hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ A ^ 3)
    (hmomentBudget :
      (1 + (factor - 1) / (count : ℝ)) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2 +
        3 * (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
              (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * A ^ 2 ≤
        (1 + delta) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2) :
    let target :=
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) - target|} ≤
      ENNReal.ofReal (delta / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  dsimp only
  let mean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  have hmean : 0 < mean := by
    rw [show mean =
        gaussianIntegral (truncatedBody q I) (scheduleValue q (phase + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q phase) by
      simpa [mean] using
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (phase + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q phase))
  obtain ⟨reference, hprob, hcomparison, hmem, hrefMean, hrefSecond⟩ :=
    exists_scheduledRetainedResetReference_average_secondMoment
      q I phase count hcount hcountMax hA hmean.le (by
        exact le_rfl) (by simpa [mean] using hcoordinateSecond)
        hcoordinateThird
  let _ : IsProbabilityMeasure reference := hprob
  have hrefMean' :
      (∫ history, sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ) ∂reference) = mean := by
    simpa [mean] using hrefMean
  have hresult :=
    initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
      q I phase count reference hcomparison (target := mean) (eps := eps)
      (eta := 0) (delta := delta) hmean heps (by norm_num) hdelta hmem
      (by simpa [hrefMean'])
      (hrefSecond.trans (by simpa [mean] using hmomentBudget))
  simpa [mean] using hresult

/-- The initialized-history deviation event is exactly the corresponding
retained-sum shadow event.  This is a law identity, not an approximation. -/
theorem initializedScheduledRetainedHistory_deviation_eq_retainedSum
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) (target eps : ℝ) :
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum (retainedSampleObservation weight) count history /
              (count : ℝ) - target|} =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1))
        {state | eps * target ≤ |state.1 / (count : ℝ) - target|} := by
  dsimp only
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let toSum := retainedSampleHistoryToSum weight count
  let deviation : Set (ℝ × Option (AmbientSpace q.n)) :=
    {state | eps * target ≤ |state.1 / (count : ℝ) - target|}
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have htoSum : Measurable toSum := by
    simpa [toSum] using measurable_retainedSampleHistoryToSum hweight count
  have hdeviation : MeasurableSet deviation := by
    apply measurableSet_le measurable_const
    exact (((measurable_fst.div_const (count : ℝ)).sub_const target).abs)
  have hmap := map_iterated_initializedRetainedSampleHistoryKernel_sum
    K hK.1 hK.2 weight hweight exact (count - 1)
  have happly := congrArg
    (fun mu : Measure (ℝ × Option (AmbientSpace q.n)) => mu deviation) hmap
  rw [Measure.map_apply
    (measurable_retainedSampleHistoryToSum hweight ((count - 1) + 1))
    hdeviation] at happly
  have hcountEq : count - 1 + 1 = count := Nat.sub_add_cancel (by omega)
  simpa [initializedScheduledRetainedHistoryLaw, exact, K, weight, toSum,
    deviation, retainedSampleHistoryToSum, sequentialPrefixSum, hcountEq]
    using happly

/-- A completed collector can disagree with its raw accumulated average only
when the retained chain is dead.  This is the deterministic good/bad split
behind the paper's all-or-nothing phase coupling. -/
theorem retainedLiveAverage_deviation_subset_raw_union_dead
    {S : Type*} (count : ℕ) (target eps : ℝ) :
    {state : ℝ × Option S |
        eps * target ≤
          |retainedLiveTotal state / (count : ℝ) - target|} ⊆
      {state : ℝ × Option S |
        eps * target ≤ |state.1 / (count : ℝ) - target|} ∪
      {state : ℝ × Option S | state.2 = none} := by
  intro state hstate
  rcases state with ⟨total, result⟩
  cases result with
  | none =>
      exact Or.inr rfl
  | some point =>
      left
      simpa [retainedLiveTotal] using hstate

/-- Measure form of the completed/raw/dead split.  No moment of the
executable residual law is used. -/
theorem measure_retainedLiveAverage_deviation_le_raw_add_dead
    {S : Type*} [MeasurableSpace S] (mu : Measure (ℝ × Option S))
    (count : ℕ) (target eps : ℝ) :
    mu {state |
        eps * target ≤
          |retainedLiveTotal state / (count : ℝ) - target|} ≤
      mu {state | eps * target ≤
          |state.1 / (count : ℝ) - target|} +
        mu {state | state.2 = none} := by
  exact (measure_mono
    (retainedLiveAverage_deviation_subset_raw_union_dead
      count target eps)).trans (measure_union_le _ _)

/-- Scheduled collector form: any initialized-history raw-deviation bound
becomes a completed phase bound after adding only the collector's final death
mass. -/
theorem retainedSum_liveDeviation_le_of_initializedHistory
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) (target eps : ℝ) (bound : ENNReal)
    (hhistory :
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
          {history | eps * target ≤
            |sequentialPrefixSum
              (retainedSampleObservation
                (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                  (scheduleValue q (phase + 1)))) count history /
                (count : ℝ) - target|} ≤ bound) :
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
    shadow {state | eps * target ≤
        |retainedLiveTotal state / (count : ℝ) - target|} ≤
      bound + shadow {state | state.2 = none} := by
  dsimp only
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
  have hrawEq := initializedScheduledRetainedHistory_deviation_eq_retainedSum
    q I phase count hcount target eps
  have hsplit := measure_retainedLiveAverage_deviation_le_raw_add_dead
    shadow count target eps
  calc
    shadow {state | eps * target ≤
        |retainedLiveTotal state / (count : ℝ) - target|} ≤
      shadow {state | eps * target ≤
          |state.1 / (count : ℝ) - target|} +
        shadow {state | state.2 = none} := hsplit
    _ = (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
          {history | eps * target ≤
            |sequentialPrefixSum
              (retainedSampleObservation weight) count history /
                (count : ℝ) - target|} +
        shadow {state | state.2 = none} := by
      rw [hrawEq]
    _ ≤ bound + shadow {state | state.2 = none} := by
      gcongr

/-- The public Gaussian phase target's scalar-deviation event is exactly the
retained-sum shadow's live-average event. -/
theorem figureOneScheduledGaussianPhaseTarget_deviation_eq_retainedSum
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (target eps : ℝ) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    figureOneScheduledGaussianPhaseTarget q I phase
        {result | eps * target ≤
          |scheduledBalancedPhaseRatio result - target|} =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1))
        {state | eps * target ≤
          |retainedLiveTotal state / (count : ℝ) - target|} := by
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
  let deviation : Set (Option (ℝ × AmbientSpace q.n)) :=
    {result | eps * target ≤
      |scheduledBalancedPhaseRatio result - target|}
  have hdeviation : MeasurableSet deviation := by
    apply measurableSet_le measurable_const
    exact (measurable_scheduledBalancedPhaseRatio.sub_const target).abs
  rw [figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel]
  rw [Measure.map_apply
    ((measurable_balancedCoolingAverage count).comp
      measurable_retainedSumOutput) hdeviation]
  congr 1
  ext state
  rcases state with ⟨total, result⟩
  cases result <;>
    simp [deviation, count, Function.comp_def, retainedSumOutput,
      balancedCoolingAverage, scheduledBalancedPhaseRatio, retainedLiveTotal]

/-- Public phase-target deviation bound obtained from an initialized-history
bound plus the final collector death event. -/
theorem figureOneScheduledGaussianPhaseTarget_deviation_le_of_initializedHistory
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (target eps : ℝ) (bound : ENNReal)
    (hhistory :
      let count := figureOnePhaseSampleCount q (scheduleValue q phase)
      let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1))
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
          {history | eps * target ≤
            |sequentialPrefixSum (retainedSampleObservation weight) count history /
                (count : ℝ) - target|} ≤ bound) :
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
    figureOneScheduledGaussianPhaseTarget q I phase
        {result | eps * target ≤
          |scheduledBalancedPhaseRatio result - target|} ≤
      bound + shadow {state | state.2 = none} := by
  dsimp only at hhistory ⊢
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
  rw [figureOneScheduledGaussianPhaseTarget_deviation_eq_retainedSum]
  exact retainedSum_liveDeviation_le_of_initializedHistory
    q I phase count (figureOnePhaseSampleCount_pos q _)
      target eps bound hhistory

/-- On the public Gaussian phase target, the clamped raw-output projection
has the same law as the ordinary phase-ratio projection: retained totals are
nonnegative almost surely. -/
theorem map_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_ratio
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    (figureOneScheduledGaussianPhaseTarget q I phase).map
        figureOneScheduledTraceLiveRawOutput =
      (figureOneScheduledGaussianPhaseTarget q I phase).map
        scheduledBalancedPhaseRatio := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial :=
    (truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map initialMap
  let shadow := iteratedKernelLaw (fun _ => retainedSumKernel K weight)
    initial (count - 1)
  let output := balancedCoolingAverage count ∘
    (retainedSumOutput (S := AmbientSpace q.n))
  have hcount : 0 < count := figureOnePhaseSampleCount_pos q _
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hweight0 : ∀ x, 0 ≤ weight x :=
    gaussianRatioWeight_nonnegative _ _
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hinitialMap : Measurable initialMap :=
    hweight.prodMk measurable_some
  have hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1 := by
    apply (ae_map_iff hinitialMap.aemeasurable
      (measurableSet_le measurable_const measurable_fst)).2
    filter_upwards with x
    exact hweight0 x
  have hshadow0 : ∀ᵐ state ∂shadow, 0 ≤ state.1 :=
    iterated_retainedSumKernel_ae_total_nonnegative
      K hK.1 hK.2 weight hweight hweight0 initial hinitial0 (count - 1)
  have houtput : Measurable output :=
    (measurable_balancedCoolingAverage count).comp measurable_retainedSumOutput
  rw [figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel]
  rw [Measure.map_map
      measurable_figureOneScheduledTraceLiveRawOutput houtput,
    Measure.map_map measurable_scheduledBalancedPhaseRatio houtput]
  apply Measure.map_congr
  filter_upwards [hshadow0] with state hstate0
  rcases state with ⟨total, state⟩
  cases state with
  | none =>
      simp [output, Function.comp_def, retainedSumOutput,
        balancedCoolingAverage, figureOneScheduledTraceLiveRawOutput,
        scheduledBalancedPhaseRatio]
  | some point =>
      have havg0 : 0 ≤ total / (count : ℝ) :=
        div_nonneg hstate0 hcountReal.le
      simp [output, Function.comp_def, retainedSumOutput,
        balancedCoolingAverage, figureOneScheduledTraceLiveRawOutput,
        scheduledBalancedPhaseRatio, max_eq_right havg0]

/-- A noninitial public Gaussian phase-target deviation bound transports to
the corresponding coordinate of the final chronological trace, paying only
the already-budgeted live/dead prefix error. -/
theorem scheduledBalancedFinalTraceRawGaussianPhase_deviation_le_of_target
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase0 : 0 < phase) (hphase : phase < terminalPhaseSteps q)
    (target eps : ℝ) (bound : ENNReal)
    (htarget : figureOneScheduledGaussianPhaseTarget q I phase
      {result | eps * target ≤
        |scheduledBalancedPhaseRatio result - target|} ≤ bound) :
    (scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q))
      {trace | eps * target ≤
        |scheduledBalancedTracePhaseVariable q (phase + 1) trace - target|} ≤
      bound + (figureOneCorrectedTransitionBudget q +
        figureOneScheduledRetainedError q phase) := by
  let finalLaw := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let W := scheduledBalancedTracePhaseVariable q (phase + 1)
  let scalarDeviation : Set ℝ :=
    {value | eps * target ≤ |value - target|}
  have hset : MeasurableSet scalarDeviation := by
    apply measurableSet_le measurable_const
    exact (measurable_id.sub_const target).abs
  have hcomparison :=
    scheduledBalancedFinalTraceRawGaussianPhase_leUpTo_target
      q I phase hphase0 hphase
  have hevent := hcomparison.event_le scalarDeviation
  rw [Measure.map_apply
    (measurable_scheduledBalancedTracePhaseVariable q (phase + 1)) hset,
    map_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_ratio,
    Measure.map_apply measurable_scheduledBalancedPhaseRatio hset] at hevent
  have htarget' :
      (figureOneScheduledGaussianPhaseTarget q I phase)
          (scheduledBalancedPhaseRatio ⁻¹' scalarDeviation) ≤ bound := by
    simpa [scalarDeviation, Set.preimage] using htarget
  exact hevent.trans (by
    gcongr)

#print axioms
  MeasureLeUpTo.measure_relativeDeviation_le_of_reference_moments
#print axioms
  initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
#print axioms
  initializedScheduledRetainedHistory_relativeDeviation_le_of_coordinate_moments
#print axioms
  initializedScheduledRetainedHistory_deviation_eq_retainedSum
#print axioms retainedLiveAverage_deviation_subset_raw_union_dead
#print axioms measure_retainedLiveAverage_deviation_le_raw_add_dead
#print axioms retainedSum_liveDeviation_le_of_initializedHistory
#print axioms
  figureOneScheduledGaussianPhaseTarget_deviation_eq_retainedSum
#print axioms
  figureOneScheduledGaussianPhaseTarget_deviation_le_of_initializedHistory
#print axioms map_figureOneScheduledGaussianPhaseTarget_liveRaw_eq_ratio
#print axioms
  scheduledBalancedFinalTraceRawGaussianPhase_deviation_le_of_target

end ArlibCommunity.Algorithms.CV18
