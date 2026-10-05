/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofHistoryPreservingSampleReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorPrefixIndependence

/-!
# An exact-shadow reference step for the scheduled collector

This file instantiates the history-preserving reset construction for one
tail sample of the scheduled retained collector.  The reference records an
exact truncated-Gaussian shadow at the new coordinate while preserving the
executable retained state used by the following walk block.

This is deliberately a one-coordinate statement.  Exact coordinate
marginals do not by themselves assert that all shadow coordinates are
independent.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The exact retained target for a Gaussian cooling sample. -/
noncomputable def scheduledRetainedExactSome
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (Option (AmbientSpace q.n)) :=
  (truncatedGaussianProbability q I (scheduleValue q phase)
    (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some

theorem scheduledRetainedExactSome_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (scheduledRetainedExactSome q I phase) := by
  unfold scheduledRetainedExactSome
  exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

/-- Updating one coordinate of the recorded part of a retained history is
measurable as a two-argument operation. -/
theorem measurable_uncurry_update_retainedHistoryCoordinate
    {S : Type*} [MeasurableSpace S] (i : ℕ) :
    Measurable (Function.uncurry fun history : ℕ → Option S =>
      Function.update history i) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hji : j = i
  · subst j
    simpa [Function.uncurry, Function.update] using
      (measurable_snd : Measurable fun value :
        (ℕ → Option S) × Option S => value.2)
  · simpa [Function.uncurry, Function.update, hji] using
      (show Measurable fun value : (ℕ → Option S) × Option S =>
          value.1 j from by
        convert (measurable_pi_apply j).comp measurable_fst using 1
        funext value
        rfl)

/-- The generic transition-then-record kernel is the collector's ordinary
coordinate-recording kernel. -/
theorem historyOperationalRecordKernel_update_eq_retainedSampleHistoryKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (i : ℕ) :
    historyOperationalRecordKernel K
        (fun history next => Function.update history i next) id =
      retainedSampleHistoryKernel K i := by
  funext history
  rfl

/-- Keep only the coordinates strictly before `limit`. -/
def retainedSampleHistoryPrefix {S : Type*} (limit : ℕ)
    (history : ℕ → Option S) : ℕ → Option S :=
  fun j => if j < limit then history j else none

theorem measurable_retainedSampleHistoryPrefix
    {S : Type*} [MeasurableSpace S] (limit : ℕ) :
    Measurable (retainedSampleHistoryPrefix (S := S) limit) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j < limit
  · simpa [retainedSampleHistoryPrefix, hj] using
      (measurable_pi_apply j :
        Measurable fun history : ℕ → Option S => history j)
  · simpa [retainedSampleHistoryPrefix, hj] using
      (measurable_const : Measurable fun _ : ℕ → Option S =>
        (none : Option S))

theorem retainedSampleHistoryPrefix_update_at_limit
    {S : Type*} (limit : ℕ) (history : ℕ → Option S)
    (next : Option S) :
    retainedSampleHistoryPrefix limit (Function.update history limit next) =
      retainedSampleHistoryPrefix limit history := by
  funext j
  by_cases hj : j < limit
  · have hne : j ≠ limit := Nat.ne_of_lt hj
    simp [retainedSampleHistoryPrefix, hj, Function.update, hne]
  · simp [retainedSampleHistoryPrefix, hj]

/-- Equality of truncated-prefix laws gives equality of every coordinate
strictly inside that prefix. -/
theorem map_retainedSampleHistory_coordinate_eq_of_prefix_eq
    {S : Type*} [MeasurableSpace S]
    (mu nu : Measure (RetainedSampleHistory S)) (limit j : ℕ)
    (hj : j < limit)
    (hprefix : mu.map
        (retainedSampleHistoryPrefix limit ∘ Prod.fst) =
      nu.map (retainedSampleHistoryPrefix limit ∘ Prod.fst)) :
    mu.map (fun history => history.1 j) =
      nu.map (fun history => history.1 j) := by
  have hprefixMeas : Measurable
      (retainedSampleHistoryPrefix (S := S) limit ∘
        (Prod.fst : RetainedSampleHistory S → (ℕ → Option S))) :=
    (measurable_retainedSampleHistoryPrefix limit).comp
      (measurable_fst : Measurable (Prod.fst :
        RetainedSampleHistory S → (ℕ → Option S)))
  have heval : Measurable fun history : ℕ → Option S => history j :=
    measurable_pi_apply j
  calc
    mu.map (fun history => history.1 j) =
        mu.map ((fun history : ℕ → Option S => history j) ∘
          (retainedSampleHistoryPrefix limit ∘ Prod.fst)) := by
      congr 1
      funext history
      simp [retainedSampleHistoryPrefix, hj]
    _ = (mu.map (retainedSampleHistoryPrefix limit ∘ Prod.fst)).map
          (fun history => history j) :=
      (Measure.map_map heval hprefixMeas).symm
    _ = (nu.map (retainedSampleHistoryPrefix limit ∘ Prod.fst)).map
          (fun history => history j) := by rw [hprefix]
    _ = nu.map ((fun history : ℕ → Option S => history j) ∘
          (retainedSampleHistoryPrefix limit ∘ Prod.fst)) :=
      Measure.map_map heval hprefixMeas
    _ = nu.map (fun history => history.1 j) := by
      congr 1
      funext history
      simp [retainedSampleHistoryPrefix, hj]

/-- Total event-transfer cost accumulated by recursively resetting every
tail coordinate to an exact shadow. -/
noncomputable def scheduledShadowReferenceError
    (q : VolumeParams) : ℕ → ENNReal
  | 0 => 0
  | i + 1 => scheduledShadowReferenceError q i +
      scheduledRetainedEndpointError q (i + 1)

theorem scheduledShadowReferenceError_ne_top
    (q : VolumeParams) : ∀ tail,
    scheduledShadowReferenceError q tail ≠ ⊤
  | 0 => by simp [scheduledShadowReferenceError]
  | i + 1 => by
      rw [scheduledShadowReferenceError]
      exact ENNReal.add_ne_top.mpr
        ⟨scheduledShadowReferenceError_ne_top q i,
          scheduledRetainedEndpointError_ne_top q (i + 1)⟩

/-- Fixed-cost exact-chance error when the reference operational state is
reset to the exact target after every recorded sample. -/
noncomputable def scheduledResetReferenceError
    (q : VolumeParams) : ℕ → ENNReal
  | 0 => 0
  | i + 1 => scheduledResetReferenceError q i +
      scheduledRetainedEndpointError q 1

theorem scheduledResetReferenceError_ne_top
    (q : VolumeParams) : ∀ tail,
    scheduledResetReferenceError q tail ≠ ⊤
  | 0 => by simp [scheduledResetReferenceError]
  | i + 1 => by
      rw [scheduledResetReferenceError]
      exact ENNReal.add_ne_top.mpr
        ⟨scheduledResetReferenceError_ne_top q i,
          scheduledRetainedEndpointError_ne_top q 1⟩

theorem scheduledResetReferenceError_eq_nsmul
    (q : VolumeParams) (tail : ℕ) :
    scheduledResetReferenceError q tail =
      tail • scheduledRetainedEndpointError q 1 := by
  induction tail with
  | zero => simp [scheduledResetReferenceError]
  | succ i ih =>
      rw [scheduledResetReferenceError, ih, succ_nsmul]

/-- Resetting from an exact target costs at most `3/2` of one transition
budget: one transition budget plus twice the reserved quarter-budget for
the stationary-target correction. -/
theorem scheduledRetainedEndpointError_one_toReal_le
    (q : VolumeParams) :
    (scheduledRetainedEndpointError q 1).toReal ≤
      (3 / 2 : ℝ) * figureOnePerSampleMixingError q := by
  let delta := figureOneCorrectedTransitionBudget q
  let stationary := scheduledBalancedStationaryTargetError q
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hdeltaTop : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have htargetTop : figureOneCorrectedTargetBudget q ≠ ⊤ :=
    ENNReal.div_ne_top hdeltaTop (by norm_num)
  have hstationaryTop : stationary ≠ ⊤ :=
    ne_top_of_le_ne_top htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
  have htwiceTop : 2 * stationary ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hstationaryTop
  have hstationaryReal : stationary.toReal ≤
      figureOnePerSampleMixingError q / 4 := by
    have hreal := ENNReal.toReal_mono htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
    simpa [stationary, figureOneCorrectedTargetBudget, delta,
      figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hnu.le] using hreal
  rw [scheduledRetainedEndpointError,
    ENNReal.toReal_add htwiceTop (by simpa using hdeltaTop),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  simp only [one_nsmul, delta, figureOneCorrectedTransitionBudget,
    ENNReal.toReal_ofReal hnu.le]
  nlinarith

/-- The exact-target reset recurrence is linear in the number of tail
samples, with an explicit real-valued `3/2` per-sample envelope. -/
theorem scheduledResetReferenceError_toReal_le
    (q : VolumeParams) (tail : ℕ) :
    (scheduledResetReferenceError q tail).toReal ≤
      (3 / 2 : ℝ) * (tail : ℝ) *
        figureOnePerSampleMixingError q := by
  rw [scheduledResetReferenceError_eq_nsmul, ENNReal.toReal_nsmul]
  have htail : 0 ≤ (tail : ℝ) := Nat.cast_nonneg tail
  have hone := scheduledRetainedEndpointError_one_toReal_le q
  simp only [nsmul_eq_mul]
  nlinarith

/-- Even after transporting the executable dependence estimate to the
fixed-cost reference, its coefficient grows by at most a factor `5/2`.
This uses the global sample/phase allocation from Lemma 7.17(c). -/
theorem scheduledResetReference_transportEpsilon_le
    (q : VolumeParams) {count : ℕ}
    (hcount : count ≤ figureOneDependentMaxSampleCount q) :
    figureOneDependentEpsilon q +
        3 * (scheduledResetReferenceError q (count - 1)).toReal ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have htailNat : count - 1 ≤ figureOneDependentMaxSampleCount q :=
    (Nat.sub_le count 1).trans hcount
  have htail : ((count - 1 : ℕ) : ℝ) ≤
      (figureOneDependentMaxSampleCount q : ℝ) := by
    exact_mod_cast htailNat
  have hreset := scheduledResetReferenceError_toReal_le q (count - 1)
  have hresetMax :
      (scheduledResetReferenceError q (count - 1)).toReal ≤
        (3 / 2 : ℝ) *
          (figureOneDependentMaxSampleCount q : ℝ) *
            figureOnePerSampleMixingError q := by
    exact hreset.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htail (by norm_num)) hnu.le)
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hk0 : 0 ≤ (figureOneDependentMaxSampleCount q : ℝ) := by
    positivity
  have hkm :
      (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q ≤
        (figureOneDependentMaxSampleCount q : ℝ) *
          (figureOneDependentPhaseCount q : ℝ) *
            figureOnePerSampleMixingError q := by
    have := mul_le_mul_of_nonneg_left hm hk0
    nlinarith
  have hbudget := figureOne_lemma717c_budget q
  nlinarith

/-- The one-step shadow reset may start from any reference prefix whose
operational-state marginal agrees with the executable prefix.  It preserves
all previously written coordinates, installs an exact new coordinate, and
keeps the next executable-state marginal. -/
theorem exists_initializedScheduledRetainedShadowReferenceStep
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (prefixLaw : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure prefixLaw]
    (hstate : prefixLaw.map retainedSampleHistoryState =
      (initializedScheduledRetainedHistoryLaw q I phase i).map
        retainedSampleHistoryState) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (prefixLaw.bind (retainedSampleHistoryKernel
          (figureOneFinalScheduledRetainedOptionKernel q I
            (scheduleValue q phase)) (i + 1)))
        reference (scheduledRetainedEndpointError q (i + 1)) ∧
      reference.map (fun history => history.1 (i + 1)) =
        scheduledRetainedExactSome q I phase ∧
      reference.map retainedSampleHistoryState =
        (initializedScheduledRetainedHistoryLaw q I phase (i + 1)).map
          retainedSampleHistoryState ∧
      reference.map
          (retainedSampleHistoryPrefix (i + 1) ∘ Prod.fst) =
        prefixLaw.map
          (retainedSampleHistoryPrefix (i + 1) ∘ Prod.fst) := by
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let target := scheduledRetainedExactSome q I phase
  let record : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) → ℕ → Option (AmbientSpace q.n) :=
    fun history next => Function.update history (i + 1) next
  let readNew : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) := fun history => history (i + 1)
  let projectOld := retainedSampleHistoryPrefix
    (S := AmbientSpace q.n) (i + 1)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  let _ : IsProbabilityMeasure target := by
    simpa [target] using
      scheduledRetainedExactSome_isProbabilityMeasure q I phase
  have hrecord : Measurable (Function.uncurry record) := by
    simpa [record] using
      (measurable_uncurry_update_retainedHistoryCoordinate
        (S := AmbientSpace q.n) (i + 1))
  have hreadNew : Measurable readNew := by
    simpa [readNew] using
      (measurable_pi_apply (i + 1) :
        Measurable fun history : ℕ → Option (AmbientSpace q.n) =>
          history (i + 1))
  have hprojectOld : Measurable projectOld := by
    simpa [projectOld] using
      measurable_retainedSampleHistoryPrefix
        (S := AmbientSpace q.n) (i + 1)
  have hnext : TVLe
      ((prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd)
      target (scheduledRetainedEndpointError q (i + 1)) := by
    rw [map_bind_historyRawNextWithCopyKernel_snd prefixLaw K hK.1 hK.2]
    change TVLe ((prefixLaw.map retainedSampleHistoryState).bind K) target
      (scheduledRetainedEndpointError q (i + 1))
    rw [hstate]
    rw [map_initializedScheduledRetainedHistoryLaw_state q I phase i]
    rw [← iteratedKernelLaw_succ]
    have htargetProb : IsProbabilityMeasure target := inferInstance
    have hiterProb : IsProbabilityMeasure
        (iteratedKernelLaw (fun _ => K) target (i + 1)) :=
      iteratedKernelLaw_isProbabilityMeasure (fun _ => K) target
        htargetProb (fun _ => hK.1) (fun _ => hK.2) (i + 1)
    let _ : IsProbabilityMeasure
        (iteratedKernelLaw (fun _ => K) target (i + 1)) := hiterProb
    have hendpoint : MeasureLeUpTo
        (iteratedKernelLaw (fun _ => K) target (i + 1)) target
        (scheduledRetainedEndpointError q (i + 1)) := by
      simpa [K, target, scheduledRetainedExactSome,
        scheduledRetainedEndpointError] using
        (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
          q I phase (i + 1))
    exact hendpoint.to_tvLe
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinate, hrefState,
      hprefix⟩ :=
    exists_shadowRecordedReference_of_nextMarginal_tvLe_preserving
      prefixLaw K record id target readNew projectOld hK.1 hK.2 hrecord
      measurable_id hreadNew hprojectOld (by
        intro history next
        simp [record, readNew]) (by
        intro history next
        exact retainedSampleHistoryPrefix_update_at_limit
          (i + 1) history next) hnext
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, ?_⟩
  · change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))) reference
      (scheduledRetainedEndpointError q (i + 1))
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))) reference
      (scheduledRetainedEndpointError q (i + 1)) at hmlu
    exact hmlu
  · rw [Measure.map_id] at hcoordinate
    change reference.map (fun history => history.1 (i + 1)) = target at hcoordinate
    simpa only [target] using hcoordinate
  · calc
      reference.map retainedSampleHistoryState =
          (prefixLaw.bind (historyOperationalRecordKernel K record id)).map
            Prod.snd := hrefState
      _ = (prefixLaw.map Prod.snd).bind K :=
        map_bind_historyOperationalRecordKernel_snd prefixLaw K record id
          hK.1 hK.2 hrecord measurable_id
      _ = ((initializedScheduledRetainedHistoryLaw q I phase i).map
          retainedSampleHistoryState).bind K := by
        change (prefixLaw.map retainedSampleHistoryState).bind K = _
        rw [hstate]
      _ = (initializedScheduledRetainedHistoryLaw q I phase (i + 1)).map
          retainedSampleHistoryState := by
        rw [map_initializedScheduledRetainedHistoryLaw_state q I phase i,
          map_initializedScheduledRetainedHistoryLaw_state q I phase (i + 1),
          iteratedKernelLaw_succ]
  · simpa only [projectOld] using hprefix

/-- Fixed-cost reset step for the exact-chance reference chain.  Its input
state marginal is exact, and its output state and newly recorded coordinate
are reset to that same exact marginal. -/
theorem exists_scheduledRetainedResetReferenceStep
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (prefixLaw : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure prefixLaw]
    (hstate : prefixLaw.map retainedSampleHistoryState =
      scheduledRetainedExactSome q I phase) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (prefixLaw.bind (retainedSampleHistoryKernel
          (figureOneFinalScheduledRetainedOptionKernel q I
            (scheduleValue q phase)) (i + 1)))
        reference (scheduledRetainedEndpointError q 1) ∧
      reference.map (fun history => history.1 (i + 1)) =
        scheduledRetainedExactSome q I phase ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I phase ∧
      reference.map
          (retainedSampleHistoryPrefix (i + 1) ∘ Prod.fst) =
        prefixLaw.map
          (retainedSampleHistoryPrefix (i + 1) ∘ Prod.fst) := by
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let target := scheduledRetainedExactSome q I phase
  let record : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) → ℕ → Option (AmbientSpace q.n) :=
    fun history next => Function.update history (i + 1) next
  let readNew : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) := fun history => history (i + 1)
  let projectOld := retainedSampleHistoryPrefix
    (S := AmbientSpace q.n) (i + 1)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  let _ : IsProbabilityMeasure target := by
    simpa [target] using
      scheduledRetainedExactSome_isProbabilityMeasure q I phase
  have hrecord : Measurable (Function.uncurry record) := by
    simpa [record] using
      (measurable_uncurry_update_retainedHistoryCoordinate
        (S := AmbientSpace q.n) (i + 1))
  have hreadNew : Measurable readNew := by
    simpa [readNew] using
      (measurable_pi_apply (i + 1) :
        Measurable fun history : ℕ → Option (AmbientSpace q.n) =>
          history (i + 1))
  have hprojectOld : Measurable projectOld := by
    simpa [projectOld] using
      measurable_retainedSampleHistoryPrefix
        (S := AmbientSpace q.n) (i + 1)
  have hnext : TVLe
      ((prefixLaw.bind (historyRawNextKernel K)).map Prod.snd)
      target (scheduledRetainedEndpointError q 1) := by
    rw [map_bind_historyRawNextKernel_snd prefixLaw K hK.1 hK.2]
    change TVLe ((prefixLaw.map retainedSampleHistoryState).bind K) target _
    rw [hstate]
    have hbindProb : IsProbabilityMeasure (target.bind K) :=
      isProbabilityMeasure_bind hK.1.aemeasurable (ae_of_all _ hK.2)
    let _ : IsProbabilityMeasure (target.bind K) := hbindProb
    have hendpoint : MeasureLeUpTo (target.bind K) target
        (scheduledRetainedEndpointError q 1) := by
      simpa [K, target, scheduledRetainedExactSome,
        scheduledRetainedEndpointError, iteratedKernelLaw_succ] using
        (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
          q I phase 1)
    exact hendpoint.to_tvLe
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinate, hrefState,
      hprefix⟩ :=
    exists_recordedResetReference_of_nextMarginal_tvLe_preserving
      prefixLaw K record id target readNew projectOld hK.1 hK.2 hrecord
      measurable_id hreadNew hprojectOld (by
        intro history next
        simp [record, readNew]) (by
        intro history next
        exact retainedSampleHistoryPrefix_update_at_limit
          (i + 1) history next) hnext
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, ?_⟩
  · change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))) reference
      (scheduledRetainedEndpointError q 1)
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))) reference
      (scheduledRetainedEndpointError q 1) at hmlu
    exact hmlu
  · rw [Measure.map_id] at hcoordinate
    change reference.map (fun history => history.1 (i + 1)) = target at hcoordinate
    simpa only [target] using hcoordinate
  · simpa only [target, retainedSampleHistoryState] using hrefState
  · simpa only [projectOld] using hprefix

/-- Paper-faithful per-sample exact-chance reference.  Every reference step
starts from and returns to the exact retained target, so the history-level
comparison accumulates only one fixed one-step error per tail sample. -/
theorem exists_scheduledRetainedResetReference_all
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase tail)
        reference (scheduledResetReferenceError q tail) ∧
      (∀ j, j ≤ tail →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I phase) ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I phase := by
  induction tail with
  | zero =>
      let reference := initializedScheduledRetainedHistoryLaw q I phase 0
      have hreferenceProb : IsProbabilityMeasure reference := by
        simpa [reference] using
          initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
            q I phase 0
      refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
      · simpa [scheduledResetReferenceError] using
          MeasureLeUpTo.refl reference
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        rw [show reference =
            (truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
                retainedSampleHistoryWithFirst by
          rfl]
        rw [Measure.map_map
          (show Measurable (fun history :
              RetainedSampleHistory (AmbientSpace q.n) => history.1 0) from
            (measurable_pi_apply 0).comp measurable_fst)
          measurable_retainedSampleHistoryWithFirst]
        change _ = scheduledRetainedExactSome q I phase
        unfold scheduledRetainedExactSome
        congr 1
      · simpa [reference, scheduledRetainedExactSome] using
          map_initializedScheduledRetainedHistoryLaw_state q I phase 0
  | succ i ih =>
      obtain ⟨oldReference, holdProb, holdMlu, holdCoordinates, holdState⟩ := ih
      let _ : IsProbabilityMeasure oldReference := holdProb
      obtain ⟨reference, hreferenceProb, hstep, hnewCoordinate, hstate,
          hprefix⟩ :=
        exists_scheduledRetainedResetReferenceStep
          q I phase i oldReference holdState
      have hhistoryKernel :=
        retainedSampleHistoryKernel_measurable_and_probability
          (figureOneFinalScheduledRetainedOptionKernel q I
            (scheduleValue q phase))
          (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
            q I (scheduleValue_pos q phase)).1
          (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
            q I (scheduleValue_pos q phase)).2 (i + 1)
      refine ⟨reference, hreferenceProb, ?_, ?_, hstate⟩
      · change MeasureLeUpTo
          ((initializedScheduledRetainedHistoryLaw q I phase i).bind
            (retainedSampleHistoryKernel
              (figureOneFinalScheduledRetainedOptionKernel q I
                (scheduleValue q phase)) (i + 1)))
          reference (scheduledResetReferenceError q (i + 1))
        have htotal := MeasureLeUpTo.bind_then_replace holdMlu
          (retainedSampleHistoryKernel
            (figureOneFinalScheduledRetainedOptionKernel q I
              (scheduleValue q phase)) (i + 1))
          hhistoryKernel.1 hhistoryKernel.2 hstep
        simpa only [scheduledResetReferenceError] using htotal
      · intro j hj
        by_cases hnew : j = i + 1
        · subst j
          exact hnewCoordinate
        · have hjold : j ≤ i := by omega
          calc
            reference.map (fun history => history.1 j) =
                oldReference.map (fun history => history.1 j) :=
              map_retainedSampleHistory_coordinate_eq_of_prefix_eq
                reference oldReference (i + 1) j (by omega) hprefix
            _ = scheduledRetainedExactSome q I phase :=
              holdCoordinates j hjold

/-- The fixed-cost exact-coordinate reference inherits the executable
prefix/next approximate-independence estimate.  Transport across the single
history-level comparison costs three times its total reset error. -/
theorem exists_scheduledRetainedResetReference_all_approxIndep_with_state
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      (∀ j, j < count →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I phase) ∧
      reference.map retainedSampleHistoryState =
        scheduledRetainedExactSome q I phase ∧
      (∀ r, r < count →
        ApproxIndepFun
          (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal)
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) r)
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) r)
          reference) := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, hstate⟩ :=
    exists_scheduledRetainedResetReference_all q I phase (count - 1)
  let actual := initializedScheduledRetainedHistoryLaw
    q I phase (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase (count - 1)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  refine ⟨reference, hreferenceProb, hmlu, ?_, hstate, ?_⟩
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
      approxIndepFun_initializedScheduledRetainedHistory_all
        q I phase count hcountMax r hr
    have htv : TVLe reference actual
        (scheduledResetReferenceError q (count - 1)) := by
      exact hmlu.to_tvLe.symm
    simpa only [actual, weight] using
      (ApproxIndepFun.of_tvLe reference actual
        (scheduledResetReferenceError_ne_top q (count - 1))
        (sequentialPrefixSum (retainedSampleObservation weight) r)
        (retainedSampleObservation weight r) hprefix hobs htv hactualIndep)

/-- Compatibility form of the fixed reset reference when the final retained
state marginal is not needed by the caller. -/
theorem exists_scheduledRetainedResetReference_all_approxIndep
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledResetReferenceError q (count - 1)) ∧
      (∀ j, j < count →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I phase) ∧
      (∀ r, r < count →
        ApproxIndepFun
          (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal)
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) r)
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) r)
          reference) := by
  obtain ⟨reference, hprob, hmlu, hcoordinates, _hstate, hind⟩ :=
    exists_scheduledRetainedResetReference_all_approxIndep_with_state
      q I phase count hcount0 hcountMax
  exact ⟨reference, hprob, hmlu, hcoordinates, hind⟩

/-- A single scheduled phase admits one reference history law on which all
recorded coordinates are exact truncated-Gaussian marginals.  The executable
history is dominated by this law with the sum of the successive endpoint
replacement errors. -/
theorem exists_initializedScheduledRetainedShadowReference_all
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase tail)
        reference (scheduledShadowReferenceError q tail) ∧
      (∀ j, j ≤ tail →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I phase) ∧
      reference.map retainedSampleHistoryState =
        (initializedScheduledRetainedHistoryLaw q I phase tail).map
          retainedSampleHistoryState := by
  induction tail with
  | zero =>
      let reference := initializedScheduledRetainedHistoryLaw q I phase 0
      have hreferenceProb : IsProbabilityMeasure reference := by
        simpa [reference] using
          initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
            q I phase 0
      refine ⟨reference, hreferenceProb, ?_, ?_, rfl⟩
      · simpa [scheduledShadowReferenceError] using
          MeasureLeUpTo.refl reference
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        rw [show reference =
            (truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
                retainedSampleHistoryWithFirst by
          rfl]
        rw [Measure.map_map
          (show Measurable (fun history :
              RetainedSampleHistory (AmbientSpace q.n) => history.1 0) from
            (measurable_pi_apply 0).comp measurable_fst)
          measurable_retainedSampleHistoryWithFirst]
        change _ = scheduledRetainedExactSome q I phase
        unfold scheduledRetainedExactSome
        congr 1
  | succ i ih =>
      obtain ⟨oldReference, holdProb, holdMlu, holdCoordinates, holdState⟩ := ih
      let _ : IsProbabilityMeasure oldReference := holdProb
      obtain ⟨reference, hreferenceProb, hstep, hnewCoordinate, hstate,
          hprefix⟩ :=
        exists_initializedScheduledRetainedShadowReferenceStep
          q I phase i oldReference holdState
      have hhistoryKernel :=
        retainedSampleHistoryKernel_measurable_and_probability
          (figureOneFinalScheduledRetainedOptionKernel q I
            (scheduleValue q phase))
          (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
            q I (scheduleValue_pos q phase)).1
          (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
            q I (scheduleValue_pos q phase)).2 (i + 1)
      refine ⟨reference, hreferenceProb, ?_, ?_, hstate⟩
      · change MeasureLeUpTo
          ((initializedScheduledRetainedHistoryLaw q I phase i).bind
            (retainedSampleHistoryKernel
              (figureOneFinalScheduledRetainedOptionKernel q I
                (scheduleValue q phase)) (i + 1)))
          reference (scheduledShadowReferenceError q (i + 1))
        have htotal := MeasureLeUpTo.bind_then_replace holdMlu
          (retainedSampleHistoryKernel
            (figureOneFinalScheduledRetainedOptionKernel q I
              (scheduleValue q phase)) (i + 1))
          hhistoryKernel.1 hhistoryKernel.2 hstep
        simpa only [scheduledShadowReferenceError] using htotal
      · intro j hj
        by_cases hnew : j = i + 1
        · subst j
          exact hnewCoordinate
        · have hjold : j ≤ i := by omega
          calc
            reference.map (fun history => history.1 j) =
                oldReference.map (fun history => history.1 j) :=
              map_retainedSampleHistory_coordinate_eq_of_prefix_eq
                reference oldReference (i + 1) j (by omega) hprefix
            _ = scheduledRetainedExactSome q I phase :=
              holdCoordinates j hjold

/-- The common exact-shadow reference inherits CV18 Lemma 7.17(b) from the
executable history by total-variation stability.  The explicit `3 * error`
term is the cost of transporting the joint rectangle and its two marginals.
-/
theorem exists_initializedScheduledRetainedShadowReference_all_approxIndep
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount0 : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledShadowReferenceError q (count - 1)) ∧
      (∀ j, j < count →
        reference.map (fun history => history.1 j) =
          scheduledRetainedExactSome q I phase) ∧
      (∀ r, r < count →
        ApproxIndepFun
          (figureOneDependentEpsilon q +
            3 * (scheduledShadowReferenceError q (count - 1)).toReal)
          (sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) r)
          (retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) r)
          reference) := by
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, _hstate⟩ :=
    exists_initializedScheduledRetainedShadowReference_all
      q I phase (count - 1)
  let actual := initializedScheduledRetainedHistoryLaw
    q I phase (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase (count - 1)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
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
      approxIndepFun_initializedScheduledRetainedHistory_all
        q I phase count hcountMax r hr
    have htv : TVLe reference actual
        (scheduledShadowReferenceError q (count - 1)) := by
      exact hmlu.to_tvLe.symm
    simpa only [actual, weight] using
      (ApproxIndepFun.of_tvLe reference actual
        (scheduledShadowReferenceError_ne_top q (count - 1))
        (sequentialPrefixSum (retainedSampleObservation weight) r)
        (retainedSampleObservation weight r) hprefix hobs htv hactualIndep)

/-- One executable scheduled tail step admits a reference law whose newly
recorded coordinate is exactly distributed as the truncated Gaussian while
the next operational retained-state marginal is unchanged. -/
theorem exists_initializedScheduledRetainedShadowReference
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (i + 1))
        reference (scheduledRetainedEndpointError q (i + 1)) ∧
      reference.map (fun history => history.1 (i + 1)) =
        scheduledRetainedExactSome q I phase ∧
      reference.map retainedSampleHistoryState =
        (initializedScheduledRetainedHistoryLaw q I phase (i + 1)).map
          retainedSampleHistoryState := by
  let prefixLaw := initializedScheduledRetainedHistoryLaw q I phase i
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let target := scheduledRetainedExactSome q I phase
  let record : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) → ℕ → Option (AmbientSpace q.n) :=
    fun history next => Function.update history (i + 1) next
  let readNew : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) := fun history => history (i + 1)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  let _ : IsProbabilityMeasure prefixLaw := by
    simpa [prefixLaw] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase i
  let _ : IsProbabilityMeasure target := by
    simpa [target] using
      scheduledRetainedExactSome_isProbabilityMeasure q I phase
  have hiterProb : IsProbabilityMeasure
      (iteratedKernelLaw (fun _ => K) target (i + 1)) := by
    exact iteratedKernelLaw_isProbabilityMeasure (fun _ => K) target
      (by infer_instance) (fun _ => hK.1) (fun _ => hK.2) (i + 1)
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw (fun _ => K) target (i + 1)) := hiterProb
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        (i + 1)) := by
    simpa [K, target, scheduledRetainedExactSome] using hiterProb
  have hrecord : Measurable (Function.uncurry record) := by
    simpa [record] using
      (measurable_uncurry_update_retainedHistoryCoordinate
        (S := AmbientSpace q.n) (i + 1))
  have hreadNew : Measurable readNew := by
    simpa [readNew] using
      (measurable_pi_apply (i + 1) :
        Measurable fun history : ℕ → Option (AmbientSpace q.n) =>
          history (i + 1))
  have hnext : TVLe
      ((prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd)
      target (scheduledRetainedEndpointError q (i + 1)) := by
    rw [map_bind_historyRawNextWithCopyKernel_snd prefixLaw K hK.1 hK.2]
    rw [show prefixLaw.map Prod.snd =
        iteratedKernelLaw (fun _ => K)
          (scheduledRetainedExactSome q I phase) i by
      simpa [prefixLaw, K, scheduledRetainedExactSome,
        retainedSampleHistoryState] using
        map_initializedScheduledRetainedHistoryLaw_state q I phase i]
    rw [← iteratedKernelLaw_succ]
    have hendpoint : MeasureLeUpTo
        (iteratedKernelLaw (fun _ => K) target (i + 1)) target
        (scheduledRetainedEndpointError q (i + 1)) := by
      simpa [K, target, scheduledRetainedExactSome,
        scheduledRetainedEndpointError] using
        (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
          q I phase (i + 1))
    exact hendpoint.to_tvLe
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinate, hstate⟩ :=
    exists_shadowRecordedReference_of_nextMarginal_tvLe
      prefixLaw K record id target readNew hK.1 hK.2 hrecord
      measurable_id hreadNew (by
        intro history next
        simp [record, readNew, Function.update]) hnext
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
  · rw [initializedScheduledRetainedHistoryLaw,
      iteratedKernelLaw_succ]
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1)))
      reference (scheduledRetainedEndpointError q (i + 1))
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1)))
      reference (scheduledRetainedEndpointError q (i + 1)) at hmlu
    exact hmlu
  · rw [Measure.map_id] at hcoordinate
    change reference.map (fun history => history.1 (i + 1)) = target at hcoordinate
    simpa only [target] using hcoordinate
  · rw [initializedScheduledRetainedHistoryLaw,
      iteratedKernelLaw_succ]
    change reference.map Prod.snd =
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))).map Prod.snd
    change reference.map Prod.snd =
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))).map Prod.snd
      at hstate
    exact hstate

#print axioms scheduledRetainedExactSome_isProbabilityMeasure
#print axioms measurable_uncurry_update_retainedHistoryCoordinate
#print axioms historyOperationalRecordKernel_update_eq_retainedSampleHistoryKernel
#print axioms measurable_retainedSampleHistoryPrefix
#print axioms retainedSampleHistoryPrefix_update_at_limit
#print axioms map_retainedSampleHistory_coordinate_eq_of_prefix_eq
#print axioms exists_initializedScheduledRetainedShadowReference_all
#print axioms scheduledShadowReferenceError_ne_top
#print axioms scheduledResetReferenceError_ne_top
#print axioms scheduledResetReferenceError_eq_nsmul
#print axioms scheduledRetainedEndpointError_one_toReal_le
#print axioms scheduledResetReferenceError_toReal_le
#print axioms scheduledResetReference_transportEpsilon_le
#print axioms exists_scheduledRetainedResetReferenceStep
#print axioms exists_scheduledRetainedResetReference_all
#print axioms
  exists_scheduledRetainedResetReference_all_approxIndep_with_state
#print axioms exists_scheduledRetainedResetReference_all_approxIndep
#print axioms
  exists_initializedScheduledRetainedShadowReference_all_approxIndep
#print axioms exists_initializedScheduledRetainedShadowReferenceStep
#print axioms exists_initializedScheduledRetainedShadowReference

end

end ArlibCommunity.Algorithms.CV18
