/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorSampleHistory

/-!
# Sample-history shadow including the exact first sample

The phase experiment in CV18 draws its first sample from the exact truncated
Gaussian and then runs `count - 1` retained transitions.  The base history
shadow records transition outputs starting at coordinate zero.  Here the
exact first sample is stored in coordinate zero and tail transition `i`
writes coordinate `i + 1`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- History initialized with the exact first retained sample in coordinate
zero. -/
def retainedSampleHistoryWithFirst {S : Type*} (x : S) :
    RetainedSampleHistory S :=
  (Function.update (fun _ => none) 0 (some x), some x)

theorem measurable_retainedSampleHistoryWithFirst
    {S : Type*} [MeasurableSpace S] :
    Measurable (retainedSampleHistoryWithFirst :
      S → RetainedSampleHistory S) := by
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j = 0
    · subst j
      simpa [retainedSampleHistoryWithFirst, Function.update] using
        (measurable_some : Measurable fun x : S => some x)
    · simpa [retainedSampleHistoryWithFirst, Function.update, hj] using
        (measurable_const : Measurable fun _ : S => (none : Option S))
  · exact measurable_some

@[simp] theorem retainedSampleHistoryWithFirst_state
    {S : Type*} (x : S) :
    retainedSampleHistoryState (retainedSampleHistoryWithFirst x) = some x :=
  rfl

@[simp] theorem retainedSampleHistoryWithFirst_observation_zero
    {S : Type*} (weight : S → ℝ) (x : S) :
    retainedSampleObservation weight 0 (retainedSampleHistoryWithFirst x) =
      weight x := by
  simp [retainedSampleObservation, retainedSampleHistoryWithFirst,
    retainedOptionWeight, Function.update]

@[simp] theorem retainedSampleHistoryWithFirst_toSum_one
    {S : Type*} (weight : S → ℝ) (x : S) :
    retainedSampleHistoryToSum weight 1 (retainedSampleHistoryWithFirst x) =
      (weight x, some x) := by
  apply Prod.ext
  · simp [retainedSampleHistoryToSum]
  · rfl

/-- Forgetting the initialized coordinate record gives the exact first-sample
law mapped into the retained optional state. -/
theorem map_retainedSampleHistoryWithFirst_state
    {S : Type*} [MeasurableSpace S] (initial : Measure S) :
    (initial.map retainedSampleHistoryWithFirst).map
        retainedSampleHistoryState =
      initial.map some := by
  change (initial.map retainedSampleHistoryWithFirst).map Prod.snd =
    initial.map some
  rw [Measure.map_map measurable_snd
    measurable_retainedSampleHistoryWithFirst]
  rfl

/-- Shifting the coordinate written at each step does not change the retained
optional-state chain. -/
theorem map_iterated_initializedRetainedSampleHistoryKernel_state
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (initial : Measure (RetainedSampleHistory S)) : ∀ tail,
    (iteratedKernelLaw
      (fun i => retainedSampleHistoryKernel K (i + 1))
      initial tail).map retainedSampleHistoryState =
      iteratedKernelLaw (fun _ => K)
        (initial.map retainedSampleHistoryState) tail := by
  intro tail
  induction tail with
  | zero => rfl
  | succ tail ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K (i + 1)) initial tail
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob (tail + 1)
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K (tail + 1) history).map
            retainedSampleHistoryState) =
          K ∘ retainedSampleHistoryState := by
        funext history
        unfold retainedSampleHistoryKernel retainedSampleHistoryState
        have hupdate : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate (tail + 1) history next :=
          (measurable_retainedSampleHistoryUpdate (tail + 1)).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map measurable_snd hupdate]
        simpa [retainedSampleHistoryUpdate, Function.comp_def]
      calc
        (old.bind (retainedSampleHistoryKernel K (tail + 1))).map
              retainedSampleHistoryState =
            old.bind fun history =>
              (retainedSampleHistoryKernel K (tail + 1) history).map
                retainedSampleHistoryState :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 measurable_snd
        _ = old.bind (K ∘ retainedSampleHistoryState) := by rw [hpoint]
        _ = (old.map retainedSampleHistoryState).bind K :=
          (map_bind_eq_bind_comp_state old measurable_snd hK).symm
        _ = (iteratedKernelLaw (fun _ => K)
            (initial.map retainedSampleHistoryState) tail).bind K := by rw [ih]

/-- The shifted history shadow and the retained-sum shadow have exactly the
same law.  This is the law identity needed for a phase containing an exact
first sample followed by `tail` executable samples. -/
theorem map_iterated_initializedRetainedSampleHistoryKernel_sum
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure S) : ∀ tail,
    (iteratedKernelLaw
      (fun i => retainedSampleHistoryKernel K (i + 1))
      (initial.map retainedSampleHistoryWithFirst) tail).map
        (retainedSampleHistoryToSum weight (tail + 1)) =
      iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        (initial.map fun x => (weight x, some x)) tail := by
  intro tail
  induction tail with
  | zero =>
      simp only [iteratedKernelLaw_zero, zero_add]
      rw [Measure.map_map
        (measurable_retainedSampleHistoryToSum hweight 1)
        measurable_retainedSampleHistoryWithFirst]
      apply Measure.map_congr
      filter_upwards with x
      exact retainedSampleHistoryWithFirst_toSum_one weight x
  | succ tail ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K (i + 1))
        (initial.map retainedSampleHistoryWithFirst) tail
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob (tail + 1)
      have hsum := retainedSumKernel_measurable_and_probability
        K hK hKprob weight hweight
      have htoOld :=
        measurable_retainedSampleHistoryToSum hweight (tail + 1)
      have htoNew :=
        measurable_retainedSampleHistoryToSum hweight (tail + 1 + 1)
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K (tail + 1) history).map
            (retainedSampleHistoryToSum weight (tail + 1 + 1))) =
          (fun history => retainedSumKernel K weight
            (retainedSampleHistoryToSum weight (tail + 1) history)) := by
        funext history
        unfold retainedSampleHistoryKernel retainedSumKernel
        have hupdateHistory : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate (tail + 1) history next :=
          (measurable_retainedSampleHistoryUpdate (tail + 1)).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map htoNew hupdateHistory]
        apply Measure.map_congr
        filter_upwards with next
        apply Prod.ext
        · exact retainedSampleHistory_prefixSum_update weight
            (tail + 1) history next
        · rfl
      calc
        (old.bind (retainedSampleHistoryKernel K (tail + 1))).map
              (retainedSampleHistoryToSum weight (tail + 1 + 1)) =
            old.bind fun history =>
              (retainedSampleHistoryKernel K (tail + 1) history).map
                (retainedSampleHistoryToSum weight (tail + 1 + 1)) :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 htoNew
        _ = old.bind fun history => retainedSumKernel K weight
              (retainedSampleHistoryToSum weight (tail + 1) history) := by
          rw [hpoint]
        _ = (old.map
              (retainedSampleHistoryToSum weight (tail + 1))).bind
              (retainedSumKernel K weight) :=
          (map_bind_eq_bind_comp_state old htoOld hsum.1).symm
        _ = (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
            (initial.map fun x => (weight x, some x)) tail).bind
              (retainedSumKernel K weight) := by rw [ih]

/-- Tail step `i` creates coordinate `i + 1`; its preceding prefix includes
the exact first sample and all earlier tail samples. -/
theorem map_initializedRetainedSample_prefix_next_succ_eq_sequentialPairLaw
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) (i : ℕ) :
    (iteratedKernelLaw
      (fun j => retainedSampleHistoryKernel K (j + 1))
      initial (i + 1)).map (fun history =>
        (sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
            history,
          retainedSampleObservation weight (i + 1) history)) =
      (sequentialPairLaw
        (iteratedKernelLaw
          (fun j => retainedSampleHistoryKernel K (j + 1)) initial i)
        (K ∘ retainedSampleHistoryState)).map (fun pair =>
          (sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
              pair.1,
            retainedOptionWeight weight pair.2)) := by
  let rho := iteratedKernelLaw
    (fun j => retainedSampleHistoryKernel K (j + 1)) initial i
  let pref : RetainedSampleHistory S → ℝ :=
    sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
  let observe : RetainedSampleHistory S → ℝ :=
    retainedSampleObservation weight (i + 1)
  have hpref : Measurable pref := measurable_sequentialPrefixSum
    (fun t => measurable_retainedSampleObservation hweight t) (i + 1)
  have hobserve : Measurable observe :=
    measurable_retainedSampleObservation hweight (i + 1)
  have hoptionWeight : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hhistoryKernel := retainedSampleHistoryKernel_measurable_and_probability
    K hK hKprob (i + 1)
  have hpairKernel : Measurable fun history : RetainedSampleHistory S =>
      ((K ∘ retainedSampleHistoryState) history).map
        (fun next => (history, next)) :=
    measurable_sequentialPairKernel (rho := rho)
      (hK.comp measurable_snd) (fun history => hKprob history.2)
  have hleft :
      (rho.bind (retainedSampleHistoryKernel K (i + 1))).map
          (fun history => (pref history, observe history)) =
        rho.bind fun history => (K history.2).map fun next =>
          (pref history, retainedOptionWeight weight next) := by
    rw [map_bind_eq_bind_map_of_measurable rho hhistoryKernel.1
      (hpref.prodMk hobserve)]
    apply Measure.bind_congr_right
    filter_upwards with history
    unfold retainedSampleHistoryKernel
    have hupdate : Measurable fun next : Option S =>
        retainedSampleHistoryUpdate (i + 1) history next :=
      (measurable_retainedSampleHistoryUpdate (i + 1)).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_map (hpref.prodMk hobserve) hupdate]
    apply Measure.map_congr
    filter_upwards with next
    apply Prod.ext
    · exact retainedSampleHistory_prefixSum_update_same
        weight (i + 1) history next
    · exact retainedSampleObservation_update_same
        weight (i + 1) history next
  have hright :
      (sequentialPairLaw rho (K ∘ retainedSampleHistoryState)).map
          (fun pair =>
            (pref pair.1, retainedOptionWeight weight pair.2)) =
        rho.bind fun history => (K history.2).map fun next =>
          (pref history, retainedOptionWeight weight next) := by
    unfold sequentialPairLaw
    let transform : RetainedSampleHistory S × Option S → ℝ × ℝ :=
      fun pair => (pref pair.1, retainedOptionWeight weight pair.2)
    have htransform : Measurable transform :=
      (hpref.comp measurable_fst).prodMk
        (hoptionWeight.comp measurable_snd)
    calc
      (rho.bind fun history => (K history.2).map
          fun next => (history, next)).map transform =
          rho.bind fun history =>
            ((K history.2).map fun next => (history, next)).map transform :=
        map_bind_eq_bind_map_of_measurable rho hpairKernel htransform
      _ = rho.bind fun history => (K history.2).map fun next =>
          (pref history, retainedOptionWeight weight next) := by
        apply Measure.bind_congr_right
        filter_upwards with history
        have hpair : Measurable fun next : Option S => (history, next) :=
          measurable_const.prodMk measurable_id
        calc
          ((K history.2).map fun next => (history, next)).map transform =
              (K history.2).map
                (transform ∘ fun next => (history, next)) :=
            Measure.map_map htransform hpair
          _ = (K history.2).map fun next =>
              (pref history, retainedOptionWeight weight next) := by rfl
  rw [iteratedKernelLaw_succ]
  exact hleft.trans hright.symm

/-- A written initialized-history coordinate and its preceding prefix are
unchanged by all later shifted tail transitions. -/
theorem map_initializedRetainedSample_prefix_next_eq_of_le
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) (i start stop : ℕ)
    (hi : i < start) (hstart : start ≤ stop) :
    (iteratedKernelLaw
      (fun j => retainedSampleHistoryKernel K (j + 1)) initial stop).map
        (fun history =>
          (sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
              history,
            retainedSampleObservation weight (i + 1) history)) =
      (iteratedKernelLaw
        (fun j => retainedSampleHistoryKernel K (j + 1)) initial start).map
          (fun history =>
            (sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
                history,
              retainedSampleObservation weight (i + 1) history)) := by
  let X : RetainedSampleHistory S → ℝ :=
    sequentialPrefixSum (retainedSampleObservation weight) (i + 1)
  let Y : RetainedSampleHistory S → ℝ :=
    retainedSampleObservation weight (i + 1)
  have hX : Measurable X := measurable_sequentialPrefixSum
    (fun t => measurable_retainedSampleObservation hweight t) (i + 1)
  have hY : Measurable Y :=
    measurable_retainedSampleObservation hweight (i + 1)
  induction stop, hstart using Nat.le_induction with
  | base => rfl
  | succ stop hstartStop ih =>
      rw [iteratedKernelLaw_succ]
      calc
        ((iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K (j + 1))
              initial stop).bind
            (retainedSampleHistoryKernel K (stop + 1))).map
              (fun history => (X history, Y history)) =
            (iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K (j + 1))
              initial stop).map (fun history => (X history, Y history)) := by
          apply Measure.map_pair_bind_eq_of_ae_eq
            (iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K (j + 1)) initial stop)
            (retainedSampleHistoryKernel K (stop + 1))
            (retainedSampleHistoryKernel_measurable_and_probability
              K hK hKprob (stop + 1)).1
            (retainedSampleHistoryKernel_measurable_and_probability
              K hK hKprob (stop + 1)).2 X Y X Y hX hY hX hY
          filter_upwards with history
          unfold retainedSampleHistoryKernel
          have hupdate : Measurable fun next : Option S =>
              retainedSampleHistoryUpdate (stop + 1) history next :=
            (measurable_retainedSampleHistoryUpdate (stop + 1)).comp
              (measurable_const.prodMk measurable_id)
          apply (ae_map_iff hupdate.aemeasurable
            ((measurableSet_eq_fun hX measurable_const).inter
              (measurableSet_eq_fun hY measurable_const))).2
          filter_upwards with next
          exact retainedSampleHistory_prefix_next_update_of_lt weight
            (by omega : i + 1 < stop + 1) history next
        _ = _ := ih

/-- Creation-time approximate independence for tail coordinate `i + 1`
persists to the final shifted history horizon. -/
theorem initializedRetainedSampleHistory_approxIndep_prefix_next_final
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    {epsilon : ℝ} {i tail : ℕ} (hi : i < tail)
    (hpair : ApproxIndepFun epsilon
      (fun pair => sequentialPrefixSum
        (retainedSampleObservation weight) (i + 1) pair.1)
      (fun pair => retainedOptionWeight weight pair.2)
      (sequentialPairLaw
        (iteratedKernelLaw
          (fun j => retainedSampleHistoryKernel K (j + 1)) initial i)
        (K ∘ retainedSampleHistoryState))) :
    ApproxIndepFun epsilon
      (sequentialPrefixSum (retainedSampleObservation weight) (i + 1))
      (retainedSampleObservation weight (i + 1))
      (iteratedKernelLaw
        (fun j => retainedSampleHistoryKernel K (j + 1))
        initial tail) := by
  apply ApproxIndepFun.of_map_pair_eq
    ((measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t)
      (i + 1)).comp measurable_fst)
    ((measurable_retainedOptionWeight hweight).comp measurable_snd)
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t) (i + 1))
    (measurable_retainedSampleObservation hweight (i + 1)) ?_ hpair
  rw [map_initializedRetainedSample_prefix_next_eq_of_le
    K hK hKprob weight hweight initial i (i + 1) tail (by omega) (by omega)]
  exact (map_initializedRetainedSample_prefix_next_succ_eq_sequentialPairLaw
    K hK hKprob weight hweight initial i).symm

#print axioms measurable_retainedSampleHistoryWithFirst
#print axioms map_retainedSampleHistoryWithFirst_state
#print axioms map_iterated_initializedRetainedSampleHistoryKernel_state
#print axioms map_iterated_initializedRetainedSampleHistoryKernel_sum
#print axioms
  map_initializedRetainedSample_prefix_next_succ_eq_sequentialPairLaw
#print axioms map_initializedRetainedSample_prefix_next_eq_of_le
#print axioms
  initializedRetainedSampleHistory_approxIndep_prefix_next_final

end ArlibCommunity.Algorithms.CV18
