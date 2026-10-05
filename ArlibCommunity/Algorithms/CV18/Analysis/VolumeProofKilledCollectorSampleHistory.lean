/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentAverage
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceTransport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov

/-!
# Sample-history shadow for a killed collector

The executable retry collector retains only its accumulated total.  To use
the sequential approximate-independence calculation one needs all individual
observations on one probability space.  This module augments the retained
optional-state chain by an infinite, initially empty coordinate record.  The
`i`-th transition writes exactly its returned optional state in coordinate
`i`; after death the usual absorbing optional kernel therefore records zero
observations.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A coordinate record together with the current retained optional state. -/
abbrev RetainedSampleHistory (S : Type*) := (ℕ → Option S) × Option S

/-- Write the next retained state into coordinate `i` and carry it forward. -/
def retainedSampleHistoryUpdate {S : Type*} (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    RetainedSampleHistory S :=
  (Function.update history.1 i next, next)

theorem measurable_retainedSampleHistoryUpdate
    {S : Type*} [MeasurableSpace S] (i : ℕ) :
    Measurable fun value : RetainedSampleHistory S × Option S =>
      retainedSampleHistoryUpdate i value.1 value.2 := by
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun j => ?_
    by_cases hji : j = i
    · subst j
      simpa [retainedSampleHistoryUpdate] using
        (measurable_snd : Measurable fun value :
          RetainedSampleHistory S × Option S => value.2)
    · convert ((measurable_pi_apply j).comp
        (measurable_fst.comp measurable_fst) :
          Measurable fun value : RetainedSampleHistory S × Option S =>
            value.1.1 j) using 1
      funext value
      simp [retainedSampleHistoryUpdate, Function.update, hji]
  · exact measurable_snd

/-- One step of the coordinate-recording shadow. -/
noncomputable def retainedSampleHistoryKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (i : ℕ) :
    RetainedSampleHistory S → Measure (RetainedSampleHistory S) :=
  fun history => (K history.2).map
    (retainedSampleHistoryUpdate i history)

theorem retainedSampleHistoryKernel_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state)) (i : ℕ) :
    Measurable (retainedSampleHistoryKernel K i) ∧
      ∀ history, IsProbabilityMeasure
        (retainedSampleHistoryKernel K i history) := by
  have hupdate : Measurable fun value :
      RetainedSampleHistory S × Option S =>
        retainedSampleHistoryUpdate i value.1 value.2 :=
    measurable_retainedSampleHistoryUpdate i
  constructor
  · unfold retainedSampleHistoryKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun history => hKprob history.2) hupdate
  · intro history
    unfold retainedSampleHistoryKernel
    let _ : IsProbabilityMeasure (K history.2) := hKprob history.2
    exact Measure.isProbabilityMeasure_map
      (hupdate.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Forget the coordinate record and keep the retained optional state. -/
def retainedSampleHistoryState {S : Type*} :
    RetainedSampleHistory S → Option S := Prod.snd

/-- Recording sample coordinates does not alter the retained optional-state
chain at any finite horizon. -/
theorem map_iterated_retainedSampleHistoryKernel_state
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (initial : Measure (RetainedSampleHistory S)) : ∀ steps,
    (iteratedKernelLaw (fun i => retainedSampleHistoryKernel K i)
      initial steps).map retainedSampleHistoryState =
    iteratedKernelLaw (fun _ => K)
      (initial.map retainedSampleHistoryState) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K i) initial steps
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob steps
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K steps history).map
            retainedSampleHistoryState) =
          K ∘ retainedSampleHistoryState := by
        funext history
        unfold retainedSampleHistoryKernel retainedSampleHistoryState
        have hupdate : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate steps history next :=
          (measurable_retainedSampleHistoryUpdate steps).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map measurable_snd hupdate]
        change Measure.map id (K history.2) = K history.2
        exact Measure.map_id
      calc
        (old.bind (retainedSampleHistoryKernel K steps)).map
              retainedSampleHistoryState =
            old.bind fun history =>
              (retainedSampleHistoryKernel K steps history).map
                retainedSampleHistoryState :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 measurable_snd
        _ = old.bind (K ∘ retainedSampleHistoryState) := by rw [hpoint]
        _ = (old.map retainedSampleHistoryState).bind K :=
          (map_bind_eq_bind_comp_state old measurable_snd hK).symm
        _ = (iteratedKernelLaw (fun _ => K)
            (initial.map retainedSampleHistoryState) steps).bind K := by rw [ih]

/-- The observation stored in coordinate `i`, assigning zero to death. -/
def retainedSampleObservation {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) : ℝ :=
  retainedOptionWeight weight (history.1 i)

theorem measurable_retainedSampleObservation
    {S : Type*} [MeasurableSpace S] {weight : S → ℝ}
    (hweight : Measurable weight) (i : ℕ) :
    Measurable (retainedSampleObservation weight i) := by
  exact (measurable_retainedOptionWeight hweight).comp <|
    (measurable_pi_apply i).comp measurable_fst

/-- Project a coordinate history to its accumulated prefix total and current
retained state. -/
def retainedSampleHistoryToSum {S : Type*} (weight : S → ℝ) (steps : ℕ)
    (history : RetainedSampleHistory S) : ℝ × Option S :=
  (∑ i ∈ Finset.range steps, retainedSampleObservation weight i history,
    history.2)

theorem measurable_retainedSampleHistoryToSum
    {S : Type*} [MeasurableSpace S] {weight : S → ℝ}
    (hweight : Measurable weight) (steps : ℕ) :
    Measurable (retainedSampleHistoryToSum weight steps) := by
  exact ((Finset.range steps).measurable_fun_sum fun i _ =>
    measurable_retainedSampleObservation hweight i).prodMk measurable_snd

/-- The newly written observation is precisely the zero-filled weight of the
new retained state. -/
@[simp] theorem retainedSampleObservation_update_same
    {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    retainedSampleObservation weight i
        (retainedSampleHistoryUpdate i history next) =
      retainedOptionWeight weight next := by
  change retainedOptionWeight weight
      (Function.update history.1 i next i) = retainedOptionWeight weight next
  simp [Function.update]

/-- Writing coordinate `i` leaves every earlier coordinate unchanged. -/
@[simp] theorem retainedSampleObservation_update_of_lt
    {S : Type*} (weight : S → ℝ) {j i : ℕ} (hji : j < i)
    (history : RetainedSampleHistory S) (next : Option S) :
    retainedSampleObservation weight j
        (retainedSampleHistoryUpdate i history next) =
      retainedSampleObservation weight j history := by
  change retainedOptionWeight weight
      (Function.update history.1 i next j) =
    retainedOptionWeight weight (history.1 j)
  simp [Function.update, hji.ne]

/-- Updating coordinate `i` extends the recorded prefix sum by exactly the
new zero-filled observation. -/
theorem retainedSampleHistory_prefixSum_update
    {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    (∑ j ∈ Finset.range (i + 1),
        retainedSampleObservation weight j
          (retainedSampleHistoryUpdate i history next)) =
      (∑ j ∈ Finset.range i,
        retainedSampleObservation weight j history) +
        retainedOptionWeight weight next := by
  rw [Finset.sum_range_succ, retainedSampleObservation_update_same]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact retainedSampleObservation_update_of_lt weight
    (Finset.mem_range.mp hj) history next

/-- Once coordinate `i` has been written, later coordinate updates preserve
both its preceding prefix sum and its value. -/
theorem retainedSampleHistory_prefix_next_update_of_lt
    {S : Type*} (weight : S → ℝ) {i j : ℕ} (hij : i < j)
    (history : RetainedSampleHistory S) (next : Option S) :
    sequentialPrefixSum (retainedSampleObservation weight) i
          (retainedSampleHistoryUpdate j history next) =
        sequentialPrefixSum (retainedSampleObservation weight) i history ∧
      retainedSampleObservation weight i
          (retainedSampleHistoryUpdate j history next) =
        retainedSampleObservation weight i history := by
  constructor
  · unfold sequentialPrefixSum
    apply Finset.sum_congr rfl
    intro t ht
    exact retainedSampleObservation_update_of_lt weight
      (lt_trans (Finset.mem_range.mp ht) hij) history next
  · exact retainedSampleObservation_update_of_lt weight hij history next

/-- Writing coordinate `i` does not alter the prefix strictly before it. -/
theorem retainedSampleHistory_prefixSum_update_same
    {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    sequentialPrefixSum (retainedSampleObservation weight) i
        (retainedSampleHistoryUpdate i history next) =
      sequentialPrefixSum (retainedSampleObservation weight) i history := by
  unfold sequentialPrefixSum
  apply Finset.sum_congr rfl
  intro t ht
  exact retainedSampleObservation_update_of_lt weight
    (Finset.mem_range.mp ht) history next

/-- Creating coordinate `i` is exactly the usual sequential pair experiment:
draw the old history, run the retained kernel from its current state, and
record the old prefix together with the new zero-filled weight. -/
theorem map_retainedSample_prefix_next_succ_eq_sequentialPairLaw
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) (i : ℕ) :
    (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
      initial (i + 1)).map (fun history =>
        (sequentialPrefixSum (retainedSampleObservation weight) i history,
          retainedSampleObservation weight i history)) =
    (sequentialPairLaw
      (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial i)
      (K ∘ retainedSampleHistoryState)).map (fun pair =>
        (sequentialPrefixSum (retainedSampleObservation weight) i pair.1,
          retainedOptionWeight weight pair.2)) := by
  let rho := iteratedKernelLaw
    (fun j => retainedSampleHistoryKernel K j) initial i
  let pref : RetainedSampleHistory S → ℝ :=
    sequentialPrefixSum (retainedSampleObservation weight) i
  let observe : RetainedSampleHistory S → ℝ :=
    retainedSampleObservation weight i
  have hpref : Measurable pref := measurable_sequentialPrefixSum
    (fun t => measurable_retainedSampleObservation hweight t) i
  have hobserve : Measurable observe :=
    measurable_retainedSampleObservation hweight i
  have hoptionWeight : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hhistoryKernel := retainedSampleHistoryKernel_measurable_and_probability
    K hK hKprob i
  have hpairKernel : Measurable fun history : RetainedSampleHistory S =>
      ((K ∘ retainedSampleHistoryState) history).map
        (fun next => (history, next)) :=
    measurable_sequentialPairKernel (rho := rho)
      (hK.comp measurable_snd) (fun history => hKprob history.2)
  have hleft :
      (rho.bind (retainedSampleHistoryKernel K i)).map
          (fun history => (pref history, observe history)) =
        rho.bind fun history => (K history.2).map fun next =>
          (pref history, retainedOptionWeight weight next) := by
    rw [map_bind_eq_bind_map_of_measurable rho hhistoryKernel.1
      (hpref.prodMk hobserve)]
    apply Measure.bind_congr_right
    filter_upwards with history
    unfold retainedSampleHistoryKernel
    have hupdate : Measurable fun next : Option S =>
        retainedSampleHistoryUpdate i history next :=
      (measurable_retainedSampleHistoryUpdate i).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_map (hpref.prodMk hobserve) hupdate]
    apply Measure.map_congr
    filter_upwards with next
    apply Prod.ext
    · exact retainedSampleHistory_prefixSum_update_same
        weight i history next
    · exact retainedSampleObservation_update_same weight i history next
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

/-- Sequential-pair approximate independence is therefore exactly the
prefix/coordinate independence needed by the empirical-average recurrence
at the step when coordinate `i` is written. -/
theorem retainedSampleHistory_approxIndep_prefix_next_of_sequentialPair
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    {epsilon : ℝ} (i : ℕ)
    (hpair : ApproxIndepFun epsilon
      (fun pair => sequentialPrefixSum
        (retainedSampleObservation weight) i pair.1)
      (fun pair => retainedOptionWeight weight pair.2)
      (sequentialPairLaw
        (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial i)
        (K ∘ retainedSampleHistoryState))) :
    ApproxIndepFun epsilon
      (sequentialPrefixSum (retainedSampleObservation weight) i)
      (retainedSampleObservation weight i)
      (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial (i + 1)) := by
  apply ApproxIndepFun.of_map_pair_eq
    ((measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t) i).comp
        measurable_fst)
    ((measurable_retainedOptionWeight hweight).comp measurable_snd)
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t) i)
    (measurable_retainedSampleObservation hweight i) ?_ hpair
  exact (map_retainedSample_prefix_next_succ_eq_sequentialPairLaw
    K hK hKprob weight hweight initial i).symm

/-- The joint law of a written coordinate and its preceding prefix sum is
unchanged by every later transition.  This lets Lemma 7.17(b) be proved at
the moment the sample is created and then reused at the collector's final
horizon. -/
theorem map_retainedSample_prefix_next_iteratedKernelLaw_eq_of_le
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) (i start stop : ℕ)
    (hi : i < start) (hstart : start ≤ stop) :
    (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
      initial stop).map (fun history =>
        (sequentialPrefixSum (retainedSampleObservation weight) i history,
          retainedSampleObservation weight i history)) =
    (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
      initial start).map (fun history =>
        (sequentialPrefixSum (retainedSampleObservation weight) i history,
          retainedSampleObservation weight i history)) := by
  let X : RetainedSampleHistory S → ℝ :=
    sequentialPrefixSum (retainedSampleObservation weight) i
  let Y : RetainedSampleHistory S → ℝ :=
    retainedSampleObservation weight i
  have hX : Measurable X := measurable_sequentialPrefixSum
    (fun t => measurable_retainedSampleObservation hweight t) i
  have hY : Measurable Y := measurable_retainedSampleObservation hweight i
  induction stop, hstart using Nat.le_induction with
  | base => rfl
  | succ stop hstartStop ih =>
      rw [iteratedKernelLaw_succ]
      calc
        ((iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K j) initial stop).bind
            (retainedSampleHistoryKernel K stop)).map
              (fun history => (X history, Y history)) =
            (iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K j) initial stop).map
                (fun history => (X history, Y history)) := by
          apply Measure.map_pair_bind_eq_of_ae_eq
            (iteratedKernelLaw
              (fun j => retainedSampleHistoryKernel K j) initial stop)
            (retainedSampleHistoryKernel K stop)
            (retainedSampleHistoryKernel_measurable_and_probability
              K hK hKprob stop).1
            (retainedSampleHistoryKernel_measurable_and_probability
              K hK hKprob stop).2 X Y X Y hX hY hX hY
          filter_upwards with history
          unfold retainedSampleHistoryKernel
          have hupdate : Measurable fun next : Option S =>
              retainedSampleHistoryUpdate stop history next :=
            (measurable_retainedSampleHistoryUpdate stop).comp
              (measurable_const.prodMk measurable_id)
          apply (ae_map_iff hupdate.aemeasurable
            ((measurableSet_eq_fun hX measurable_const).inter
              (measurableSet_eq_fun hY measurable_const))).2
          filter_upwards with next
          exact retainedSampleHistory_prefix_next_update_of_lt weight
            (lt_of_lt_of_le hi hstartStop) history next
        _ = _ := ih

/-- Approximate prefix/next independence established at time `i+1` remains
valid under the final history law, because subsequent transitions cannot
alter either observable. -/
theorem retainedSampleHistory_approxIndep_prefix_next_of_step
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    {epsilon : ℝ} {i k : ℕ} (hik : i < k)
    (hstep : ApproxIndepFun epsilon
      (sequentialPrefixSum (retainedSampleObservation weight) i)
      (retainedSampleObservation weight i)
      (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial (i + 1))) :
    ApproxIndepFun epsilon
      (sequentialPrefixSum (retainedSampleObservation weight) i)
      (retainedSampleObservation weight i)
      (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial k) := by
  apply ApproxIndepFun.of_map_pair_eq
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t) i)
    (measurable_retainedSampleObservation hweight i)
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation hweight t) i)
    (measurable_retainedSampleObservation hweight i) ?_ hstep
  exact (map_retainedSample_prefix_next_iteratedKernelLaw_eq_of_le
    K hK hKprob weight hweight initial i (i + 1) k (by omega) (by omega)).symm

/-- Combined creation-time and future-preservation bridge.  This is the
direct adapter from CV18 Lemma 7.17(b)/(c), stated on `sequentialPairLaw`, to
the `hind` premise of the executable killed-collector moment bound. -/
theorem retainedSampleHistory_approxIndep_prefix_next_of_sequentialPair_final
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    {epsilon : ℝ} {i k : ℕ} (hik : i < k)
    (hpair : ApproxIndepFun epsilon
      (fun pair => sequentialPrefixSum
        (retainedSampleObservation weight) i pair.1)
      (fun pair => retainedOptionWeight weight pair.2)
      (sequentialPairLaw
        (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial i)
        (K ∘ retainedSampleHistoryState))) :
    ApproxIndepFun epsilon
      (sequentialPrefixSum (retainedSampleObservation weight) i)
      (retainedSampleObservation weight i)
      (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial k) := by
  apply retainedSampleHistory_approxIndep_prefix_next_of_step
    K hK hKprob weight hweight initial hik
  exact retainedSampleHistory_approxIndep_prefix_next_of_sequentialPair
    K hK hKprob weight hweight initial i hpair

/-- At every horizon, projecting the coordinate-recording shadow to its
prefix sum gives exactly the retained-sum shadow.  Thus the individual
coordinates used by the approximate-independence calculation represent the
same executable collector total, rather than an auxiliary estimator. -/
theorem map_iterated_retainedSampleHistoryKernel_sum
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) : ∀ steps,
    (iteratedKernelLaw (fun i => retainedSampleHistoryKernel K i)
      initial steps).map (retainedSampleHistoryToSum weight steps) =
    iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      (initial.map (retainedSampleHistoryToSum weight 0)) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K i) initial steps
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob steps
      have hsum := retainedSumKernel_measurable_and_probability
        K hK hKprob weight hweight
      have htoOld := measurable_retainedSampleHistoryToSum hweight steps
      have htoNew := measurable_retainedSampleHistoryToSum hweight (steps + 1)
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K steps history).map
            (retainedSampleHistoryToSum weight (steps + 1))) =
          (fun history => retainedSumKernel K weight
            (retainedSampleHistoryToSum weight steps history)) := by
        funext history
        unfold retainedSampleHistoryKernel retainedSumKernel
        have hupdateHistory : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate steps history next :=
          (measurable_retainedSampleHistoryUpdate steps).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map htoNew hupdateHistory]
        apply Measure.map_congr
        filter_upwards with next
        apply Prod.ext
        · exact retainedSampleHistory_prefixSum_update weight steps history next
        · rfl
      calc
        (old.bind (retainedSampleHistoryKernel K steps)).map
              (retainedSampleHistoryToSum weight (steps + 1)) =
            old.bind fun history =>
              (retainedSampleHistoryKernel K steps history).map
                (retainedSampleHistoryToSum weight (steps + 1)) :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 htoNew
        _ = old.bind fun history => retainedSumKernel K weight
              (retainedSampleHistoryToSum weight steps history) := by
          rw [hpoint]
        _ = (old.map (retainedSampleHistoryToSum weight steps)).bind
              (retainedSumKernel K weight) :=
          (map_bind_eq_bind_comp_state old htoOld hsum.1).symm
        _ = (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
            (initial.map (retainedSampleHistoryToSum weight 0)) steps).bind
              (retainedSumKernel K weight) := by rw [ih]

/-- The CV18 equation-(6) calculation applies directly to the individual
coordinates recorded by the killed-collector history.  This is the common
probability-space form; the next theorem transports it to the retained-sum
law used by the executable semantics. -/
theorem retainedSampleHistory_average_secondMoment_le_of_approxIndepPrefix
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    (hinitial : IsProbabilityMeasure initial)
    (k : ℕ) (hk : 0 < k) {B mean factor epsilon : ℝ}
    (hB0 : 0 ≤ B) (hmean0 : 0 ≤ mean) (hepsilon0 : 0 ≤ epsilon)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (hweightB : ∀ state, weight state ≤ B)
    (hmean : ∀ i, i < k →
      (∫ history, retainedSampleObservation weight i history
        ∂iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k) ≤ mean)
    (hsecond : ∀ i, i < k →
      (∫ history, retainedSampleObservation weight i history ^ 2
        ∂iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k) ≤ factor * mean ^ 2)
    (hind : ∀ i, i < k →
      ApproxIndepFun epsilon
        (sequentialPrefixSum (retainedSampleObservation weight) i)
        (retainedSampleObservation weight i)
        (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k)) :
    (∫ history,
        (retainedSampleHistoryToSum weight k history).1 ^ 2 /
          (k : ℝ) ^ 2
      ∂iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
        initial k) ≤
      (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
        epsilon * (1 - 1 / (k : ℝ)) * B ^ 2 := by
  let mu := iteratedKernelLaw
    (fun j => retainedSampleHistoryKernel K j) initial k
  have hkernel : ∀ j, Measurable (retainedSampleHistoryKernel K j) :=
    fun j => (retainedSampleHistoryKernel_measurable_and_probability
      K hK hKprob j).1
  have hkernelProb : ∀ j history,
      IsProbabilityMeasure (retainedSampleHistoryKernel K j history) :=
    fun j history => (retainedSampleHistoryKernel_measurable_and_probability
      K hK hKprob j).2 history
  let _ : IsProbabilityMeasure mu :=
    iteratedKernelLaw_isProbabilityMeasure _ initial hinitial
      hkernel hkernelProb k
  have hY0 : ∀ i, i < k → ∀ history,
      0 ≤ retainedSampleObservation weight i history := by
    intro i hi history
    unfold retainedSampleObservation
    cases history.1 i with
    | none => simp [retainedOptionWeight]
    | some state => simpa [retainedOptionWeight] using hweight0 state
  have hYB : ∀ i, i < k → ∀ history,
      retainedSampleObservation weight i history ≤ B := by
    intro i hi history
    unfold retainedSampleObservation
    cases history.1 i with
    | none => simpa [retainedOptionWeight] using hB0
    | some state => simpa [retainedOptionWeight] using hweightB state
  have havg := sequentialAverage_secondMoment_le_of_approxIndepPrefix
    mu (fun i => measurable_retainedSampleObservation hweight i)
    k hk hB0 hmean0 hepsilon0 hY0 hYB hmean hsecond hind
  simpa [mu, sequentialPrefixSum, retainedSampleHistoryToSum, div_pow] using havg

/-- Transport the coordinate-history second-moment estimate to the
retained-sum shadow.  The latter is exactly the law already identified with
the executable retry collector. -/
theorem iterated_retainedSumKernel_average_secondMoment_le_of_approxIndepPrefix
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S))
    (hinitial : IsProbabilityMeasure initial)
    (k : ℕ) (hk : 0 < k) {B mean factor epsilon : ℝ}
    (hB0 : 0 ≤ B) (hmean0 : 0 ≤ mean) (hepsilon0 : 0 ≤ epsilon)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (hweightB : ∀ state, weight state ≤ B)
    (hmean : ∀ i, i < k →
      (∫ history, retainedSampleObservation weight i history
        ∂iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k) ≤ mean)
    (hsecond : ∀ i, i < k →
      (∫ history, retainedSampleObservation weight i history ^ 2
        ∂iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k) ≤ factor * mean ^ 2)
    (hind : ∀ i, i < k →
      ApproxIndepFun epsilon
        (sequentialPrefixSum (retainedSampleObservation weight) i)
        (retainedSampleObservation weight i)
        (iteratedKernelLaw (fun j => retainedSampleHistoryKernel K j)
          initial k)) :
    (∫ state, (state.1 / (k : ℝ)) ^ 2
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        (initial.map (retainedSampleHistoryToSum weight 0)) k) ≤
      (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
        epsilon * (1 - 1 / (k : ℝ)) * B ^ 2 := by
  have hhistory :=
    retainedSampleHistory_average_secondMoment_le_of_approxIndepPrefix
      K hK hKprob weight hweight initial hinitial k hk hB0 hmean0
        hepsilon0 hweight0 hweightB hmean hsecond hind
  rw [← map_iterated_retainedSampleHistoryKernel_sum
    K hK hKprob weight hweight initial k]
  rw [integral_map
    (measurable_retainedSampleHistoryToSum hweight k).aemeasurable
    ((measurable_fst.div_const (k : ℝ)).pow_const 2).aestronglyMeasurable]
  simpa [retainedSampleHistoryToSum, div_pow] using hhistory

#print axioms retainedSampleHistoryKernel_measurable_and_probability
#print axioms map_iterated_retainedSampleHistoryKernel_state
#print axioms retainedSampleHistory_prefixSum_update
#print axioms map_retainedSample_prefix_next_succ_eq_sequentialPairLaw
#print axioms
  retainedSampleHistory_approxIndep_prefix_next_of_sequentialPair_final
#print axioms map_retainedSample_prefix_next_iteratedKernelLaw_eq_of_le
#print axioms retainedSampleHistory_approxIndep_prefix_next_of_step
#print axioms map_iterated_retainedSampleHistoryKernel_sum
#print axioms retainedSampleHistory_average_secondMoment_le_of_approxIndepPrefix
#print axioms iterated_retainedSumKernel_average_secondMoment_le_of_approxIndepPrefix

end ArlibCommunity.Algorithms.CV18
