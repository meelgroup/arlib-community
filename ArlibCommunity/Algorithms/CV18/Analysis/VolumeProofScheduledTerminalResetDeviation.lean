/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetAverageSecond
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalEndpointMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFixedThirdMoment

/-!
# Terminal equation-(6) on a fixed-reset reference

The Gaussian reset-reference construction is structural: it records exact
truncated-Gaussian coordinates while preserving the operational history.
This module specializes its independence and moment argument to the final
Gaussian-to-uniform weight, which is bounded by `exp (1/2)` on the terminal
body.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The initialized scheduled-history independence proof is independent of
the observable used to score retained states. -/
theorem approxIndepFun_initializedScheduledRetainedHistory_prefix_next_of_weight
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (weight : AmbientSpace q.n → ℝ) (hweight : Measurable weight)
    {i tail : ℕ} (hi : i < tail) :
    ApproxIndepFun
      (scheduledRetainedConditioningError q i +
        scheduledRetainedEndpointError q (i + 1)).toReal
      (sequentialPrefixSum (retainedSampleObservation weight) (i + 1))
      (retainedSampleObservation weight (i + 1))
      (initializedScheduledRetainedHistoryLaw q I phase tail) := by
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
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure q I phase i
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
      (fun t => measurable_retainedSampleObservation hweight t) (i + 1))
    (measurable_retainedOptionWeight hweight)
  apply initializedRetainedSampleHistory_approxIndep_prefix_next_final
    K hK.1 hK.2 weight hweight initial hi
  simpa only [rho, initial, exact, exactSome, K, delta,
    initializedScheduledRetainedHistoryLaw, Function.comp_def] using hpair

/-- Uniform-in-coordinate version for an arbitrary measurable retained
observable. -/
theorem approxIndepFun_initializedScheduledRetainedHistory_all_of_weight
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : count ≤ figureOneDependentMaxSampleCount q)
    (weight : AmbientSpace q.n → ℝ) (hweight : Measurable weight)
    (r : ℕ) (hr : r < count) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (sequentialPrefixSum (retainedSampleObservation weight) r)
      (retainedSampleObservation weight r)
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1)) := by
  cases r with
  | zero =>
      let _ : IsProbabilityMeasure
          (initializedScheduledRetainedHistoryLaw q I phase (count - 1)) :=
        initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
          q I phase (count - 1)
      change ApproxIndepFun (figureOneDependentEpsilon q)
        (fun _ => (0 : ℝ)) (retainedSampleObservation weight 0)
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
      exact approxIndepFun_const_left_of_nonneg
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        (0 : ℝ) (retainedSampleObservation weight 0)
        (figureOneDependentEpsilon_nonneg q)
  | succ i =>
      have hiTail : i < count - 1 := by omega
      have hpair :=
        approxIndepFun_initializedScheduledRetainedHistory_prefix_next_of_weight
          q I phase weight hweight hiTail
      apply hpair.mono
      simpa [scheduledRetainedConditioningError,
        scheduledRetainedEndpointError] using
        killedCollector_asymmetric_error_le_dependentEpsilon q
          (Nat.lt_trans (Nat.lt_succ_self i) hr) hcount

/-- A fixed-reset exact-coordinate reference carrying terminal uniform-weight
prefix independence. -/
theorem exists_terminalScheduledRetainedResetReference_all_approxIndep
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I
          (terminalPhaseSteps q) (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      (∀ j, j < count →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I (terminalPhaseSteps q)) ∧
      (∀ r, r < count →
        ApproxIndepFun
          (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal)
          (sequentialPrefixSum
            (retainedSampleObservation
              (uniformRatioWeight (n := q.n) (terminalVariance q))) r)
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q)) r)
          reference) := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, _hstate⟩ :=
    exists_scheduledRetainedResetReference_all q I
      (terminalPhaseSteps q) (count - 1)
  let actual := initializedScheduledRetainedHistoryLaw
    q I (terminalPhaseSteps q) (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I (terminalPhaseSteps q) (count - 1)
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  have hweight : Measurable weight :=
    measurable_uniformRatioWeight (terminalVariance q)
  refine ⟨reference, hreferenceProb, hmlu, ?_, ?_⟩
  · intro j hj
    exact hcoordinates j (by omega)
  · intro r hr
    have hprefix : Measurable
        (sequentialPrefixSum (retainedSampleObservation weight) r) :=
      measurable_sequentialPrefixSum
        (fun j => measurable_retainedSampleObservation hweight j) r
    have hobs : Measurable (retainedSampleObservation weight r) :=
      measurable_retainedSampleObservation hweight r
    have hactualIndep :=
      approxIndepFun_initializedScheduledRetainedHistory_all_of_weight
        q I (terminalPhaseSteps q) count hcountMax weight hweight r hr
    have htv : TVLe reference actual
        (scheduledResetReferenceError q (count - 1)) := hmlu.to_tvLe.symm
    simpa only [actual, weight] using
      (ApproxIndepFun.of_tvLe reference actual
        (scheduledResetReferenceError_ne_top q (count - 1))
        (sequentialPrefixSum (retainedSampleObservation weight) r)
        (retainedSampleObservation weight r) hprefix hobs htv hactualIndep)

/-- Every exact terminal coordinate of a reset reference has the bounded
uniform-ratio support used in the terminal equation-(6) argument. -/
theorem retainedSampleObservation_uniform_terminal_ae_bounds_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    ∀ᵐ history ∂reference,
      0 ≤ retainedSampleObservation
          (uniformRatioWeight (n := q.n) (terminalVariance q)) j history ∧
        retainedSampleObservation
          (uniformRatioWeight (n := q.n) (terminalVariance q)) j history ≤
            Real.exp (1 / 2) := by
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let coord : RetainedSampleHistory (AmbientSpace q.n) →
      Option (AmbientSpace q.n) := fun history => history.1 j
  let obs := retainedOptionWeight weight
  have hcoord : Measurable coord :=
    (measurable_pi_apply j).comp measurable_fst
  have hobs : Measurable obs :=
    measurable_retainedOptionWeight (measurable_uniformRatioWeight _)
  have hset : MeasurableSet {result | 0 ≤ obs result ∧
      obs result ≤ Real.exp (1 / 2)} :=
    (measurableSet_le measurable_const hobs).inter
      (measurableSet_le hobs measurable_const)
  apply (ae_map_iff hcoord.aemeasurable hset).1
  rw [hcoordinate]
  simpa [scheduledRetainedExactSome, scheduleValue_terminalPhaseSteps,
    coord, obs, weight] using
    retainedOptionWeight_uniform_terminal_ae_bounds_exactSome q I

/-- Exact terminal reference coordinates have the terminal ideal mean. -/
theorem integral_retainedSampleObservation_uniform_terminal_eq_ideal_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    (∫ history, retainedSampleObservation
        (uniformRatioWeight (n := q.n) (terminalVariance q)) j history
      ∂reference) = figureOneIdealPhaseMean q I .terminal := by
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let coord : RetainedSampleHistory (AmbientSpace q.n) →
      Option (AmbientSpace q.n) := fun history => history.1 j
  have hcoord : Measurable coord :=
    (measurable_pi_apply j).comp measurable_fst
  have hobs : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight (measurable_uniformRatioWeight _)
  calc
    (∫ history, retainedSampleObservation weight j history ∂reference) =
        ∫ result, retainedOptionWeight weight result
          ∂reference.map coord := by
      rw [integral_map hcoord.aemeasurable hobs.aestronglyMeasurable]
      rfl
    _ = ∫ result, retainedOptionWeight weight result
          ∂scheduledRetainedExactSome q I (terminalPhaseSteps q) := by
      rw [hcoordinate]
    _ = ∫ x, weight x
          ∂(truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n)) := by
      unfold scheduledRetainedExactSome
      rw [integral_map measurable_some.aemeasurable hobs.aestronglyMeasurable]
      simp [weight, retainedOptionWeight, scheduleValue_terminalPhaseSteps]
    _ = figureOneIdealPhaseMean q I .terminal := by
      simpa [weight, figureOneIdealPhaseMean] using
        uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)

/-- Exact terminal reference coordinates are bounded in `L³`. -/
theorem memLp_retainedSampleObservation_uniform_terminal_three_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsFiniteMeasure reference]
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    MemLp (retainedSampleObservation
      (uniformRatioWeight (n := q.n) (terminalVariance q)) j) 3 reference := by
  apply MemLp.of_bound
    (measurable_retainedSampleObservation
      (measurable_uniformRatioWeight (terminalVariance q)) j).aestronglyMeasurable
    (Real.exp (1 / 2))
  filter_upwards [
    retainedSampleObservation_uniform_terminal_ae_bounds_of_map_eq
      q I j reference hcoordinate] with history hhistory
  rw [Real.norm_eq_abs, abs_of_nonneg hhistory.1]
  exact hhistory.2

/-- Exact terminal reference coordinates have the sharp terminal second
moment factor. -/
theorem integral_retainedSampleObservation_uniform_terminal_sq_le_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    (∫ history, retainedSampleObservation
        (uniformRatioWeight (n := q.n) (terminalVariance q)) j history ^ 2
      ∂reference) ≤
      Real.exp (1 / 2) * (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let coord : RetainedSampleHistory (AmbientSpace q.n) →
      Option (AmbientSpace q.n) := fun history => history.1 j
  have hcoord : Measurable coord :=
    (measurable_pi_apply j).comp measurable_fst
  have hobs : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight (measurable_uniformRatioWeight _)
  have heq : (∫ history, retainedSampleObservation weight j history ^ 2
      ∂reference) =
      ∫ x, weight x ^ 2
        ∂(truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n)) := by
    calc
      _ = ∫ result, retainedOptionWeight weight result ^ 2
          ∂reference.map coord := by
        rw [integral_map hcoord.aemeasurable
          (hobs.pow_const 2).aestronglyMeasurable]
        rfl
      _ = ∫ result, retainedOptionWeight weight result ^ 2
          ∂scheduledRetainedExactSome q I (terminalPhaseSteps q) := by
        rw [hcoordinate]
      _ = _ := by
        unfold scheduledRetainedExactSome
        rw [integral_map measurable_some.aemeasurable
          (hobs.pow_const 2).aestronglyMeasurable]
        simp [weight, retainedOptionWeight, scheduleValue_terminalPhaseSteps]
  rw [heq]
  have hsecond := uniformRatioWeight_terminal_secondMoment_le q I
  have hmeanOne := uniformRatioWeight_terminal_mean_one_le q I
  have hmeanEq : (∫ x, weight x
      ∂(truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n))) =
      figureOneIdealPhaseMean q I .terminal := by
    simpa [weight, figureOneIdealPhaseMean] using
      uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)
  rw [hmeanEq] at hmeanOne
  have hmeanSq : figureOneIdealPhaseMean q I .terminal ≤
      (figureOneIdealPhaseMean q I .terminal) ^ 2 := by nlinarith
  rw [hmeanEq] at hsecond
  exact hsecond.trans <|
    mul_le_mul_of_nonneg_left hmeanSq (Real.exp_pos _).le

/-- A terminal exact coordinate has cube at most `exp (1/2)^3`. -/
theorem integral_retainedSampleObservation_uniform_terminal_cube_le_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    (∫ history, retainedSampleObservation
        (uniformRatioWeight (n := q.n) (terminalVariance q)) j history ^ 3
      ∂reference) ≤ (Real.exp (1 / 2)) ^ 3 := by
  let Y := retainedSampleObservation
    (uniformRatioWeight (n := q.n) (terminalVariance q)) j
  have hY3 : MemLp Y 3 reference := by
    simpa [Y] using
      memLp_retainedSampleObservation_uniform_terminal_three_of_map_eq
        q I j reference hcoordinate
  have hY0B :=
    retainedSampleObservation_uniform_terminal_ae_bounds_of_map_eq
      q I j reference hcoordinate
  have hcubeInt : Integrable (fun history => Y history ^ 3) reference :=
    hY3.integrable_norm_pow'.congr <| by
      filter_upwards [hY0B] with history hhistory
      rw [Real.norm_eq_abs, abs_of_nonneg hhistory.1]
  calc
    (∫ history, Y history ^ 3 ∂reference) ≤
        ∫ _history, (Real.exp (1 / 2)) ^ 3 ∂reference := by
      apply integral_mono_ae hcubeInt (integrable_const _)
      filter_upwards [hY0B] with history hhistory
      exact pow_le_pow_left₀ hhistory.1 hhistory.2 3
    _ = (Real.exp (1 / 2)) ^ 3 := by simp

/-- Bounded terminal coordinates give the prefix `L³` estimate needed by
the equation-(6) covariance recurrence. -/
theorem terminalExactShadowHistory_prefix_thirdMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcoordinates : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I (terminalPhaseSteps q)) :
    ∀ i, i ≤ count →
      MemLp (sequentialPrefixSum
        (retainedSampleObservation
          (uniformRatioWeight (n := q.n) (terminalVariance q))) i) 3
        reference ∧
      (∫ history, sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) i history ^ 3
        ∂reference) ≤ ((i : ℝ) * Real.exp (1 / 2)) ^ 3 := by
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let Y : ℕ → RetainedSampleHistory (AmbientSpace q.n) → ℝ :=
    retainedSampleObservation weight
  let B : ℝ := Real.exp (1 / 2)
  have hweight : Measurable weight := measurable_uniformRatioWeight _
  have hYmeas : ∀ j, Measurable (Y j) := fun j =>
    measurable_retainedSampleObservation hweight j
  have hY0 : ∀ j history, 0 ≤ Y j history := by
    intro j history
    unfold Y retainedSampleObservation retainedOptionWeight
    cases history.1 j <;> simp [weight, uniformRatioWeight_nonnegative]
  have hYbound : ∀ j, j < count → ∀ᵐ history ∂reference, Y j history ≤ B := by
    intro j hj
    simpa [Y, B, weight] using
      (retainedSampleObservation_uniform_terminal_ae_bounds_of_map_eq
        q I j reference (hcoordinates j hj)).mono fun _ h => h.2
  have hprefixBound : ∀ i, i ≤ count →
      ∀ᵐ history ∂reference,
        sequentialPrefixSum Y i history ≤ (i : ℝ) * B := by
    intro i hi
    induction i with
    | zero => simp [sequentialPrefixSum]
    | succ i ih =>
        have hiCount : i < count := by omega
        filter_upwards [ih (by omega), hYbound i hiCount] with history hp hYi
        rw [show sequentialPrefixSum Y (i + 1) history =
            sequentialPrefixSum Y i history + Y i history by
          simpa [sequentialPrefixSum, Nat.succ_eq_add_one] using
            Finset.sum_range_succ (fun j => Y j history) i]
        push_cast
        linarith
  intro i hi
  have hprefix0 : ∀ history, 0 ≤ sequentialPrefixSum Y i history := by
    intro history
    exact Finset.sum_nonneg fun j hj => hY0 j history
  have hprefixLp : MemLp (sequentialPrefixSum Y i) 3 reference := by
    apply MemLp.of_bound
      (measurable_sequentialPrefixSum hYmeas i).aestronglyMeasurable
      ((i : ℝ) * B)
    filter_upwards [hprefixBound i hi] with history hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (hprefix0 history)]
    exact hbound
  refine ⟨by simpa [Y, weight] using hprefixLp, ?_⟩
  have hcubeInt : Integrable
      (fun history => sequentialPrefixSum Y i history ^ 3) reference :=
    hprefixLp.integrable_norm_pow'.congr <| by
      filter_upwards with history
      rw [Real.norm_eq_abs, abs_of_nonneg (hprefix0 history)]
  calc
    (∫ history, sequentialPrefixSum Y i history ^ 3 ∂reference) ≤
        ∫ _history, ((i : ℝ) * B) ^ 3 ∂reference := by
      apply integral_mono_ae hcubeInt (integrable_const _)
      filter_upwards [hprefixBound i hi] with history hbound
      exact pow_le_pow_left₀ (hprefix0 history) hbound 3
    _ = ((i : ℝ) * B) ^ 3 := by simp

/-- Terminal equation (6) on one fixed-reset exact-coordinate reference. -/
theorem exists_terminalScheduledRetainedResetReference_average_secondMoment
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I
          (terminalPhaseSteps q) (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      MemLp (fun history =>
        sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ)) 2 reference ∧
      (∫ history, sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ) ∂reference) =
        figureOneIdealPhaseMean q I .terminal ∧
      (∫ history, (sequentialPrefixSum
          (retainedSampleObservation
            (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
          (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + (Real.exp (1 / 2) - 1) / (count : ℝ)) *
            (figureOneIdealPhaseMean q I .terminal) ^ 2 +
          3 * (figureOneDependentEpsilon q +
              3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
                (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * (Real.exp (1 / 2)) ^ 2 := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, hind⟩ :=
    exists_terminalScheduledRetainedResetReference_all_approxIndep
      q I count hcount hcountMax
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let Y : ℕ → RetainedSampleHistory (AmbientSpace q.n) → ℝ :=
    retainedSampleObservation weight
  let mean := figureOneIdealPhaseMean q I .terminal
  let B : ℝ := Real.exp (1 / 2)
  let epsilon := figureOneDependentEpsilon q +
    3 * (scheduledResetReferenceError q (count - 1)).toReal
  have hweight : Measurable weight := measurable_uniformRatioWeight _
  have hYmeas : ∀ j, Measurable (Y j) := fun j =>
    measurable_retainedSampleObservation hweight j
  have hY0 : ∀ j, j < count → ∀ history, 0 ≤ Y j history := by
    intro j hj history
    unfold Y retainedSampleObservation retainedOptionWeight
    cases history.1 j <;> simp [weight, uniformRatioWeight_nonnegative]
  have hY3 : ∀ j, j < count → MemLp (Y j) 3 reference := by
    intro j hj
    simpa [Y, weight] using
      memLp_retainedSampleObservation_uniform_terminal_three_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYmeanEq : ∀ j, j < count →
      (∫ history, Y j history ∂reference) = mean := by
    intro j hj
    simpa [Y, weight, mean] using
      integral_retainedSampleObservation_uniform_terminal_eq_ideal_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYsecond : ∀ j, j < count →
      (∫ history, Y j history ^ 2 ∂reference) ≤ B * mean ^ 2 := by
    intro j hj
    simpa [Y, weight, B, mean] using
      integral_retainedSampleObservation_uniform_terminal_sq_le_of_map_eq
        q I j reference (hcoordinates j hj)
  have hYcube : ∀ j, j < count →
      (∫ history, Y j history ^ 3 ∂reference) ≤ B ^ 3 := by
    intro j hj
    simpa [Y, weight, B] using
      integral_retainedSampleObservation_uniform_terminal_cube_le_of_map_eq
        q I j reference (hcoordinates j hj)
  have hprefix := terminalExactShadowHistory_prefix_thirdMoment_le
    q I count reference hcoordinates
  have hmean0 : 0 ≤ mean := (figureOneIdealPhaseMean_pos q I .terminal).le
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    have hdependent : 0 < figureOneDependentEpsilon q := by
      unfold figureOneDependentEpsilon
      have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
        exact_mod_cast figureOneDependentPhaseCount_pos q
      exact div_pos (sq_pos_of_pos q.heps.1)
        (mul_pos
          (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
    positivity
  have havg := sequentialAverage_secondMoment_le_of_approxIndepPrefix_thirdMoment
    reference hYmeas count hcount (Real.exp_pos ((1 : ℝ) / 2)) hmean0
      hepsilon hY0 hY3 (fun j hj => (hYmeanEq j hj).le) hYsecond
      (fun i hi => by simpa [Y, weight] using (hprefix i hi).1)
      (fun i hi => by simpa [Y, weight, B] using (hprefix i hi).2)
      hYcube (by simpa [epsilon, Y, weight] using hind)
  have hprefixLp := (hprefix count le_rfl).1
  have havgMem : MemLp (fun history =>
      sequentialPrefixSum Y count history / (count : ℝ)) 2 reference := by
    have h := (hprefixLp.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)).const_mul
      ((count : ℝ)⁻¹)
    simpa [div_eq_mul_inv, mul_comm] using h
  have havgMean : (∫ history,
      sequentialPrefixSum Y count history / (count : ℝ) ∂reference) = mean := by
    have hcountR : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
    rw [integral_div]
    unfold sequentialPrefixSum
    rw [integral_finsetSum (Finset.range count) (fun j hj =>
      (hY3 j (Finset.mem_range.mp hj)).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun j hj => hYmeanEq j (Finset.mem_range.mp hj))]
    simp [hcountR]
  refine ⟨reference, hreferenceProb, hmlu, ?_, ?_, ?_⟩
  · simpa [Y, weight] using havgMem
  · simpa [Y, weight, mean] using havgMean
  · simpa [epsilon, Y, weight, B, mean] using havg

/-- Executable terminal empirical-average deviation bound obtained by
proving equation (6) on the fixed-reset reference and transferring only the
deviation event. -/
theorem initializedScheduledRetainedHistory_terminal_relativeDeviation_le
    (q : VolumeParams) (I : VolumeInput q.n) (count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {delta eps : ℝ} (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hmomentBudget :
      (1 + (Real.exp (1 / 2) - 1) / (count : ℝ)) *
          (figureOneIdealPhaseMean q I .terminal) ^ 2 +
        3 * (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
              (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * (Real.exp (1 / 2)) ^ 2 ≤
        (1 + delta) * (figureOneIdealPhaseMean q I .terminal) ^ 2) :
    (initializedScheduledRetainedHistoryLaw q I
      (terminalPhaseSteps q) (count - 1))
        {history | eps * figureOneIdealPhaseMean q I .terminal ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
              (count : ℝ) - figureOneIdealPhaseMean q I .terminal|} ≤
      ENNReal.ofReal (delta / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  obtain ⟨reference, hprob, hcomparison, hmem, hmean, hsecond⟩ :=
    exists_terminalScheduledRetainedResetReference_average_secondMoment
      q I count hcount hcountMax
  let _ : IsProbabilityMeasure reference := hprob
  let X : RetainedSampleHistory (AmbientSpace q.n) → ℝ := fun history =>
    sequentialPrefixSum
      (retainedSampleObservation
        (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
      (count : ℝ)
  have href := measure_relativeDeviation_le_of_target_moments
    reference (by simpa [X] using hmem)
    (target := figureOneIdealPhaseMean q I .terminal) (eps := eps)
    (eta := 0) (delta := delta)
    (figureOneIdealPhaseMean_pos q I .terminal) heps (by norm_num) hdelta
    (by simpa [X, hmean]) (hsecond.trans hmomentBudget)
  have href' : reference
      {history | eps * figureOneIdealPhaseMean q I .terminal ≤
        |X history - figureOneIdealPhaseMean q I .terminal|} ≤
      ENNReal.ofReal (delta / eps ^ 2) := by
    simpa [X] using href
  calc
    (initializedScheduledRetainedHistoryLaw q I
      (terminalPhaseSteps q) (count - 1))
        {history | eps * figureOneIdealPhaseMean q I .terminal ≤
          |X history - figureOneIdealPhaseMean q I .terminal|} ≤
      reference {history | eps * figureOneIdealPhaseMean q I .terminal ≤
          |X history - figureOneIdealPhaseMean q I .terminal|} +
        scheduledResetReferenceError q (count - 1) :=
      hcomparison.event_le _
    _ ≤ ENNReal.ofReal (delta / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
      gcongr

/-- At any positive sample count, the transported reset-reference covariance
term for the bounded terminal weight fits one eighth of executable slack. -/
theorem figureOne_terminalResetReference_average_dependence_le_slack_div_eight
    (q : VolumeParams) {count : ℕ} (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    3 * (figureOneDependentEpsilon q +
          3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
            (1 / 3 : ℝ) *
        (1 - 1 / (count : ℝ)) * (Real.exp (1 / 2)) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 := by
  let epsilon := figureOneDependentEpsilon q +
    3 * (scheduledResetReferenceError q (count - 1)).toReal
  let finiteFactor := 1 - 1 / (count : ℝ)
  have hcountR : (1 : ℝ) ≤ count := by exact_mod_cast hcount
  have hcountPos : (0 : ℝ) < count := by exact_mod_cast hcount
  have hfinite0 : 0 ≤ finiteFactor := by
    dsimp [finiteFactor]
    rw [sub_nonneg, div_le_one hcountPos]
    exact hcountR
  have hfinite1 : finiteFactor ≤ 1 := by
    dsimp [finiteFactor]
    linarith [one_div_nonneg.mpr hcountPos.le]
  have hepsilon0 : 0 ≤ epsilon := by
    dsimp [epsilon]
    exact add_nonneg (figureOneDependentEpsilon_nonneg q)
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
  have htransport : epsilon ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
    simpa [epsilon] using
      scheduledResetReference_transportEpsilon_le q hcountMax
  have hcoeff :=
    figureOne_fixedThirdMoment_dependence_le_slack_div_eight_of_le_reset
      q hepsilon0 htransport
  have hexpTwo : Real.exp (1 / 2) ≤ (2 : ℝ) := by
    linarith [exp_half_sub_one_le_one]
  have hexpRat : Real.exp (1 / 2) ≤ (129 / 64 : ℝ) :=
    hexpTwo.trans (by norm_num)
  have hexpSq : (Real.exp (1 / 2)) ^ 2 ≤ (129 / 64 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexpRat 2
  have hbase0 : 0 ≤ 3 * epsilon ^ (1 / 3 : ℝ) := by positivity
  calc
    3 * epsilon ^ (1 / 3 : ℝ) * finiteFactor *
          (Real.exp (1 / 2)) ^ 2 =
        (3 * epsilon ^ (1 / 3 : ℝ) * (Real.exp (1 / 2)) ^ 2) *
          finiteFactor := by ring
    _ ≤ (3 * epsilon ^ (1 / 3 : ℝ) * (129 / 64 : ℝ) ^ 2) * 1 := by
      gcongr
    _ ≤ (figureOneExecutableMomentSlack q / 8) * 1 := by
      gcongr
    _ = figureOneExecutableMomentSlack q / 8 := by ring

/-- Final-count terminal equation-(6) deviation estimate with all reference
moment arithmetic discharged.  Only the chosen deviation threshold remains
as a parameter. -/
theorem initializedScheduledRetainedHistory_terminal_relativeDeviation_le_final
    (q : VolumeParams) (I : VolumeInput q.n) {eps : ℝ} (heps : 0 < eps) :
    let count := figureOneSampleCount q
    let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
      figureOneExecutableMomentSlack q / 8
    (initializedScheduledRetainedHistoryLaw q I
      (terminalPhaseSteps q) (count - 1))
        {history | eps * figureOneIdealPhaseMean q I .terminal ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (uniformRatioWeight (n := q.n) (terminalVariance q))) count history /
              (count : ℝ) - figureOneIdealPhaseMean q I .terminal|} ≤
      ENNReal.ofReal (delta / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  dsimp only
  let count := figureOneSampleCount q
  let mean := figureOneIdealPhaseMean q I .terminal
  let delta := (Real.exp (1 / 2) - 1) / (count : ℝ) +
    figureOneExecutableMomentSlack q / 8
  have hcount : 0 < count := figureOneSampleCount_pos q
  have hcountMax : count ≤ figureOneDependentMaxSampleCount q :=
    figureOneTerminalSampleCount_le_dependentMax q
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    have hexp : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
    exact add_nonneg
      (div_nonneg (sub_nonneg.mpr hexp) (Nat.cast_nonneg count))
      (div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num))
  apply initializedScheduledRetainedHistory_terminal_relativeDeviation_le
    q I count hcount hcountMax hdelta heps
  have hdependence :=
    figureOne_terminalResetReference_average_dependence_le_slack_div_eight
      q hcount hcountMax
  have hmeanOne : 1 ≤ mean := by
    simpa [mean] using figureOneIdealPhaseMean_one_le q I .terminal
  have hslack0 : 0 ≤ figureOneExecutableMomentSlack q / 8 :=
    div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  have hscaledSlack : figureOneExecutableMomentSlack q / 8 ≤
      figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by
    have hmeanSq : 1 ≤ mean ^ 2 := by nlinarith
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hmeanSq hslack0
  dsimp [delta, count, mean] at hdependence ⊢
  nlinarith

#print axioms
  approxIndepFun_initializedScheduledRetainedHistory_prefix_next_of_weight
#print axioms
  approxIndepFun_initializedScheduledRetainedHistory_all_of_weight
#print axioms
  exists_terminalScheduledRetainedResetReference_all_approxIndep
#print axioms
  retainedSampleObservation_uniform_terminal_ae_bounds_of_map_eq
#print axioms
  integral_retainedSampleObservation_uniform_terminal_eq_ideal_of_map_eq
#print axioms
  memLp_retainedSampleObservation_uniform_terminal_three_of_map_eq
#print axioms
  integral_retainedSampleObservation_uniform_terminal_sq_le_of_map_eq
#print axioms
  integral_retainedSampleObservation_uniform_terminal_cube_le_of_map_eq
#print axioms terminalExactShadowHistory_prefix_thirdMoment_le
#print axioms
  exists_terminalScheduledRetainedResetReference_average_secondMoment
#print axioms
  initializedScheduledRetainedHistory_terminal_relativeDeviation_le
#print axioms
  figureOne_terminalResetReference_average_dependence_le_slack_div_eight
#print axioms
  initializedScheduledRetainedHistory_terminal_relativeDeviation_le_final

end

end ArlibCommunity.Algorithms.CV18
