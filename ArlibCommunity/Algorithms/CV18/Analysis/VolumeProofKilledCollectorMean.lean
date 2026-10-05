/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorEndpoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedMean

/-!
# Marginal means of a killed retained collector

The executable phase collector discards its accumulated total if a later
retry fails.  For first-moment comparisons it is useful to retain that total
in a shadow state and kill it only in the final observation.  This module
constructs that shadow without changing the retained optional-state chain.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A weight on a retained optional state, with a dead state contributing
zero. -/
def retainedOptionWeight (weight : S → ℝ) : Option S → ℝ
  | none => 0
  | some state => weight state

theorem measurable_retainedOptionWeight {S : Type*} [MeasurableSpace S]
    {weight : S → ℝ} (hweight : Measurable weight) :
    Measurable (retainedOptionWeight weight) := by
  unfold retainedOptionWeight
  convert Measurable.optionElim (0 : ℝ) hweight using 1
  funext state
  cases state <;> rfl

/-- Shadow one-step kernel.  Unlike the public optional collector, a killed
state retains the total accumulated before death. -/
noncomputable def retainedSumKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (weight : S → ℝ) :
    (ℝ × Option S) → Measure (ℝ × Option S) := fun state =>
  (K state.2).map fun next =>
    (state.1 + retainedOptionWeight weight next, next)

theorem retainedSumKernel_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight) :
    Measurable (retainedSumKernel K weight) ∧
      ∀ state, IsProbabilityMeasure (retainedSumKernel K weight state) := by
  have hwopt : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hout : Measurable fun value : (ℝ × Option S) × Option S =>
      (value.1.1 + retainedOptionWeight weight value.2, value.2) :=
    ((measurable_fst.comp measurable_fst).add
      (hwopt.comp measurable_snd)).prodMk measurable_snd
  constructor
  · unfold retainedSumKernel
    apply measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2)
    convert hout using 1
  · intro state
    unfold retainedSumKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      ((measurable_const.add hwopt).prodMk measurable_id).aemeasurable

/-- Forget the shadow total. -/
def retainedSumState {S : Type*} : ℝ × Option S → Option S := Prod.snd

/-- Expose the accumulated total only if the retained chain is still live. -/
def retainedLiveTotal {S : Type*} : ℝ × Option S → ℝ
  | (_total, none) => 0
  | (total, some _) => total

/-- Convert a shadow state back to the public optional collector output. -/
def retainedSumOutput {S : Type*} : ℝ × Option S → Option (ℝ × S)
  | (_, none) => none
  | (total, some state) => some (total, state)

theorem measurable_retainedLiveTotal {S : Type*} [MeasurableSpace S] :
    Measurable (retainedLiveTotal (S := S)) := by
  let noneValue : ℝ → ℝ := fun _ => 0
  let someValue : ℝ × S → ℝ := fun value => value.1
  have hnone : Measurable noneValue := measurable_const
  have hsome : Measurable someValue := measurable_fst
  convert Measurable.optionElimParam hnone hsome using 1
  funext state
  rcases state with ⟨_total, state⟩
  cases state <;> rfl

theorem measurable_retainedSumOutput {S : Type*} [MeasurableSpace S] :
    Measurable (retainedSumOutput (S := S)) := by
  let noneValue : ℝ → Option (ℝ × S) := fun _ => none
  let someValue : ℝ × S → Option (ℝ × S) := fun value => some value
  have hnone : Measurable noneValue := measurable_const
  have hsome : Measurable someValue := measurable_some
  convert Measurable.optionElimParam hnone hsome using 1
  funext state
  rcases state with ⟨total, state⟩
  cases state <;> rfl

@[simp] theorem scheduledBalancedPhaseRatio_retainedSumOutput
    {S : Type*} (state : ℝ × Option S) :
    (match retainedSumOutput state with
      | none => 0
      | some result => result.1) = retainedLiveTotal state := by
  rcases state with ⟨total, state⟩
  cases state <;> rfl

/-- The shadow construction does not alter the optional retained-state
chain at any finite horizon. -/
theorem map_iterated_retainedSumKernel_state
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (ℝ × Option S)) : ∀ steps,
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial steps).map retainedSumState =
    iteratedKernelLaw (fun _ => K)
      (initial.map retainedSumState) steps := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun _ => retainedSumKernel K weight) initial steps
      have hpoint : (fun state : ℝ × Option S =>
          (retainedSumKernel K weight state).map retainedSumState) =
          K ∘ retainedSumState := by
        funext state
        unfold retainedSumKernel retainedSumState
        have hout : Measurable fun next : Option S =>
            (state.1 + retainedOptionWeight weight next, next) :=
          (measurable_const.add
            (measurable_retainedOptionWeight hweight)).prodMk measurable_id
        simpa [Function.comp_def] using
          (Measure.map_map (μ := K state.2) measurable_snd hout)
      calc
        (old.bind (retainedSumKernel K weight)).map retainedSumState =
            old.bind fun state =>
              (retainedSumKernel K weight state).map retainedSumState :=
          map_bind_eq_bind_map_of_measurable old hsum.1 measurable_snd
        _ = old.bind (K ∘ retainedSumState) := by rw [hpoint]
        _ = (old.map retainedSumState).bind K :=
          (map_bind_eq_bind_comp_state old measurable_snd hK).symm
        _ = (iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) steps).bind K := by rw [ih]

set_option maxHeartbeats 1000000 in
/-- Nonnegative initial totals and nonnegative retained weights keep every
shadow accumulated total nonnegative. -/
theorem iterated_retainedSumKernel_ae_total_nonnegative
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (initial : Measure (ℝ × Option S))
    (hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1) : ∀ steps,
    ∀ᵐ state ∂iteratedKernelLaw
      (fun _ => retainedSumKernel K weight) initial steps,
      0 ≤ state.1 := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  intro steps
  induction steps with
  | zero => exact hinitial0
  | succ steps ih =>
      rw [iteratedKernelLaw_succ]
      let R : Kernel (ℝ × Option S) (ℝ × Option S) :=
        ⟨retainedSumKernel K weight, hsum.1⟩
      letI : IsMarkovKernel R := ⟨hsum.2⟩
      change ∀ᵐ state ∂R ∘ₘ iteratedKernelLaw
        (fun _ => retainedSumKernel K weight) initial steps, 0 ≤ state.1
      apply Measure.ae_comp_of_ae_ae (κ := R)
        (measurableSet_le measurable_const measurable_fst)
      filter_upwards [ih] with state hstate0
      change ∀ᵐ next ∂retainedSumKernel K weight state, 0 ≤ next.1
      unfold retainedSumKernel
      have hout : Measurable fun next : Option S =>
          (state.1 + retainedOptionWeight weight next, next) :=
        (measurable_const.add
          (measurable_retainedOptionWeight hweight)).prodMk measurable_id
      apply (ae_map_iff hout.aemeasurable
        (measurableSet_le measurable_const measurable_fst)).2
      filter_upwards with next
      cases next with
      | none => simpa [retainedOptionWeight] using hstate0
      | some next =>
          exact add_nonneg hstate0 (hweight0 next)

set_option maxHeartbeats 1000000 in
/-- A uniform retained-weight bound gives the expected linear deterministic
bound on the shadow total. -/
theorem iterated_retainedSumKernel_ae_total_le
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    {B C : ℝ} (hB : 0 ≤ B) (hweightB : ∀ state, weight state ≤ B)
    (initial : Measure (ℝ × Option S))
    (hinitialC : ∀ᵐ state ∂initial, state.1 ≤ C) : ∀ (steps : ℕ),
    ∀ᵐ state ∂iteratedKernelLaw
      (fun _ => retainedSumKernel K weight) initial steps,
      state.1 ≤ C + (steps : ℝ) * B := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  intro steps
  induction steps with
  | zero => simpa using hinitialC
  | succ steps ih =>
      rw [iteratedKernelLaw_succ]
      let R : Kernel (ℝ × Option S) (ℝ × Option S) :=
        ⟨retainedSumKernel K weight, hsum.1⟩
      letI : IsMarkovKernel R := ⟨hsum.2⟩
      change ∀ᵐ state ∂R ∘ₘ iteratedKernelLaw
        (fun _ => retainedSumKernel K weight) initial steps,
        state.1 ≤ C + ((steps + 1 : ℕ) : ℝ) * B
      apply Measure.ae_comp_of_ae_ae (κ := R)
        (measurableSet_le measurable_fst measurable_const)
      filter_upwards [ih] with state hstate
      change ∀ᵐ next ∂retainedSumKernel K weight state,
        next.1 ≤ C + ((steps + 1 : ℕ) : ℝ) * B
      unfold retainedSumKernel
      have hout : Measurable fun next : Option S =>
          (state.1 + retainedOptionWeight weight next, next) :=
        (measurable_const.add
          (measurable_retainedOptionWeight hweight)).prodMk measurable_id
      apply (ae_map_iff hout.aemeasurable
        (measurableSet_le measurable_fst measurable_const)).2
      filter_upwards with next
      have hnext : retainedOptionWeight weight next ≤ B := by
        cases next with
        | none =>
            simp only [retainedOptionWeight]
            exact hB
        | some next => exact hweightB next
      change state.1 + retainedOptionWeight weight next ≤ _
      push_cast
      nlinarith

/-- The shadow expected total is exactly the initial expected total plus the
sum of the zero-filled retained-state marginal means.  This is the finite
endpoint-marginal identity needed for CV18's killed phase collector. -/
theorem lintegral_iterated_retainedSumKernel_total_eq_sum_marginals
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (initial : Measure (ℝ × Option S))
    (hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1) : ∀ steps,
    (∫⁻ state, ENNReal.ofReal state.1
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial steps) =
      (∫⁻ state, ENNReal.ofReal state.1 ∂initial) +
        ∑ i ∈ Finset.range steps,
          ∫⁻ state, ENNReal.ofReal (retainedOptionWeight weight state)
            ∂iteratedKernelLaw (fun _ => K)
              (initial.map retainedSumState) (i + 1) := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  have htotalMeas : Measurable fun state : ℝ × Option S =>
      ENNReal.ofReal state.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have hweightOpt : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hweightENN : Measurable fun state : Option S =>
      ENNReal.ofReal (retainedOptionWeight weight state) :=
    ENNReal.measurable_ofReal.comp hweightOpt
  have hweightOpt0 : ∀ state : Option S,
      0 ≤ retainedOptionWeight weight state := by
    intro state
    cases state with
    | none => rfl
    | some state => exact hweight0 state
  intro steps
  induction steps with
  | zero => simp
  | succ steps ih =>
      let old := iteratedKernelLaw
        (fun _ => retainedSumKernel K weight) initial steps
      have hold0 : ∀ᵐ state ∂old, 0 ≤ state.1 :=
        iterated_retainedSumKernel_ae_total_nonnegative
          K hK hKprob weight hweight hweight0 initial hinitial0 steps
      let nextMean : ℝ × Option S → ENNReal := fun state =>
        ∫⁻ next, ENNReal.ofReal (retainedOptionWeight weight next) ∂K state.2
      have hnextMean : Measurable nextMean := by
        exact (Measure.measurable_lintegral hweightENN).comp
          (hK.comp measurable_snd)
      have hinner : ∀ᵐ state ∂old,
          (∫⁻ nextState, ENNReal.ofReal nextState.1
            ∂retainedSumKernel K weight state) =
          ENNReal.ofReal state.1 + nextMean state := by
        filter_upwards [hold0] with state hstate0
        unfold retainedSumKernel nextMean
        have hout : Measurable fun next : Option S =>
            (state.1 + retainedOptionWeight weight next, next) :=
          (measurable_const.add hweightOpt).prodMk measurable_id
        rw [lintegral_map' htotalMeas.aemeasurable hout.aemeasurable]
        simp_rw [ENNReal.ofReal_add hstate0 (hweightOpt0 _)]
        rw [lintegral_add_left measurable_const]
        let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
        simp
      have hnextEq : (∫⁻ state, nextMean state ∂old) =
          ∫⁻ state, ENNReal.ofReal (retainedOptionWeight weight state)
            ∂iteratedKernelLaw (fun _ => K)
              (initial.map retainedSumState) (steps + 1) := by
        have hlaw : old.bind (K ∘ retainedSumState) =
            iteratedKernelLaw (fun _ => K)
              (initial.map retainedSumState) (steps + 1) := by
          calc
            old.bind (K ∘ retainedSumState) =
                (old.map retainedSumState).bind K :=
              (map_bind_eq_bind_comp_state old measurable_snd hK).symm
            _ = (iteratedKernelLaw (fun _ => K)
                (initial.map retainedSumState) steps).bind K := by
              rw [map_iterated_retainedSumKernel_state
                K hK hKprob weight hweight initial steps]
            _ = _ := rfl
        calc
          (∫⁻ state, nextMean state ∂old) =
              ∫⁻ next, ENNReal.ofReal (retainedOptionWeight weight next)
                ∂old.bind (K ∘ retainedSumState) := by
            simpa [nextMean, retainedSumState, Function.comp_def] using
              (Measure.lintegral_bind
                (m := old) (μ := K ∘ retainedSumState)
                (f := fun next => ENNReal.ofReal
                  (retainedOptionWeight weight next))
                (hK.comp measurable_snd).aemeasurable
                hweightENN.aemeasurable).symm
          _ = _ := by rw [hlaw]
      rw [iteratedKernelLaw_succ,
        Measure.lintegral_bind hsum.1.aemeasurable htotalMeas.aemeasurable]
      rw [lintegral_congr_ae hinner, lintegral_add_left htotalMeas]
      rw [ih, Finset.sum_range_succ, hnextEq]
      ac_rfl

/-- Real-integral form of the endpoint-marginal identity for uniformly
bounded nonnegative weights and totals. -/
theorem integral_iterated_retainedSumKernel_total_eq_sum_marginals
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hweight0 : ∀ state, 0 ≤ weight state)
    (hweightB : ∀ state, weight state ≤ B)
    (initial : Measure (ℝ × Option S)) [IsProbabilityMeasure initial]
    (hinitial0 : ∀ᵐ state ∂initial, 0 ≤ state.1)
    (hinitialC : ∀ᵐ state ∂initial, state.1 ≤ C)
    (steps : ℕ) :
    (∫ state, state.1
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial steps) =
      (∫ state, state.1 ∂initial) +
        ∑ i ∈ Finset.range steps,
          ∫ state, retainedOptionWeight weight state
            ∂iteratedKernelLaw (fun _ => K)
              (initial.map retainedSumState) (i + 1) := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  have hweightOpt : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hweightOpt0 : ∀ state : Option S,
      0 ≤ retainedOptionWeight weight state := by
    intro state
    cases state with
    | none => rfl
    | some state => exact hweight0 state
  have hweightOptB : ∀ state : Option S,
      retainedOptionWeight weight state ≤ B := by
    intro state
    cases state with
    | none => simpa [retainedOptionWeight] using hB
    | some state => exact hweightB state
  have hshadow0 := iterated_retainedSumKernel_ae_total_nonnegative
    K hK hKprob weight hweight hweight0 initial hinitial0 steps
  have hshadowC := iterated_retainedSumKernel_ae_total_le
    K hK hKprob weight hweight hB hweightB initial hinitialC steps
  let shadow := iteratedKernelLaw
    (fun _ => retainedSumKernel K weight) initial steps
  let endpoint : ℕ → Measure (Option S) := fun i =>
    iteratedKernelLaw (fun _ => K) (initial.map retainedSumState) (i + 1)
  let _ : IsProbabilityMeasure shadow :=
    iteratedKernelLaw_isProbabilityMeasure
      (fun _ => retainedSumKernel K weight) initial inferInstance
      (fun _ => hsum.1) (fun _ => hsum.2) steps
  have hshadowInt : Integrable (fun state : ℝ × Option S => state.1)
      shadow := by
    apply Integrable.of_bound measurable_fst.aestronglyMeasurable
      (C + (steps : ℝ) * B)
    filter_upwards [hshadow0, hshadowC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hinitialInt : Integrable
      (fun state : ℝ × Option S => state.1) initial := by
    apply Integrable.of_bound measurable_fst.aestronglyMeasurable C
    filter_upwards [hinitial0, hinitialC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hendpointProb : ∀ i, IsProbabilityMeasure (endpoint i) := by
    intro i
    dsimp only [endpoint]
    exact iteratedKernelLaw_isProbabilityMeasure
      (fun _ => K) (initial.map retainedSumState)
      (Measure.isProbabilityMeasure_map measurable_snd.aemeasurable)
      (fun _ => hK) (fun _ => hKprob) (i + 1)
  have hendpointInt : ∀ i,
      Integrable (retainedOptionWeight weight) (endpoint i) := by
    intro i
    let _ : IsProbabilityMeasure (endpoint i) := hendpointProb i
    apply Integrable.of_bound hweightOpt.aestronglyMeasurable B
    filter_upwards with state
    rw [Real.norm_eq_abs, abs_of_nonneg (hweightOpt0 state)]
    exact hweightOptB state
  have hshadowNN : 0 ≤ ∫ state, state.1 ∂shadow :=
    integral_nonneg_of_ae hshadow0
  have hinitialNN : 0 ≤ ∫ state, state.1 ∂initial :=
    integral_nonneg_of_ae hinitial0
  have hendpointNN : ∀ i, 0 ≤
      ∫ state, retainedOptionWeight weight state ∂endpoint i := by
    intro i
    exact integral_nonneg fun state => hweightOpt0 state
  have hlin := lintegral_iterated_retainedSumKernel_total_eq_sum_marginals
    K hK hKprob weight hweight hweight0 initial hinitial0 steps
  have hshadowConv : ENNReal.ofReal (∫ state, state.1 ∂shadow) =
      ∫⁻ state, ENNReal.ofReal state.1 ∂shadow :=
    ofReal_integral_eq_lintegral_ofReal hshadowInt hshadow0
  have hinitialConv : ENNReal.ofReal (∫ state, state.1 ∂initial) =
      ∫⁻ state, ENNReal.ofReal state.1 ∂initial :=
    ofReal_integral_eq_lintegral_ofReal hinitialInt hinitial0
  have hendpointConv : ∀ i,
      ENNReal.ofReal
          (∫ state, retainedOptionWeight weight state ∂endpoint i) =
        ∫⁻ state, ENNReal.ofReal (retainedOptionWeight weight state)
          ∂endpoint i := by
    intro i
    exact ofReal_integral_eq_lintegral_ofReal (hendpointInt i)
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
        exact (hendpointConv i).symm
      _ = _ := by
        have hsumNN : 0 ≤ ∑ i ∈ Finset.range steps,
            ∫ state, retainedOptionWeight weight state ∂endpoint i :=
          Finset.sum_nonneg fun i _ => hendpointNN i
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hendpointNN i),
          ← ENNReal.ofReal_add hinitialNN hsumNN]
  exact (ENNReal.ofReal_eq_ofReal_iff hshadowNN
    (add_nonneg hinitialNN <| Finset.sum_nonneg fun i _ => hendpointNN i)).mp
      hENN

/-! ## Exact relation with the executable scheduled collector -/

/-- An absorbing dead retained state stays dead in the shadow construction,
while preserving its invisible accumulated total. -/
theorem iterated_retainedSumKernel_dirac_none
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (hnone : K none = Measure.dirac none)
    (weight : S → ℝ) (hweight : Measurable weight)
    (total : ℝ) : ∀ steps,
    iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        (Measure.dirac (total, none)) steps =
      Measure.dirac (total, none) := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, ih, Measure.dirac_bind hsum.1]
      unfold retainedSumKernel
      rw [hnone]
      let F : Option S → ℝ × Option S := fun next =>
        ((total, (none : Option S)).1 + retainedOptionWeight weight next, next)
      have hF : Measurable F :=
        (measurable_const.add
          (measurable_retainedOptionWeight hweight)).prodMk measurable_id
      calc
        (Measure.dirac none).map F = Measure.dirac (F none) :=
          Measure.map_dirac' hF none
        _ = Measure.dirac (total, none) := by
          simp [F, retainedOptionWeight]

set_option maxHeartbeats 1000000 in
/-- A scheduled recursive collector is exactly the shadow retained-state
iteration, with the accumulated total exposed only when the last state is
live. -/
theorem scheduledBalancedTransitionCollectLaw_eq_map_retainedSumKernel
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) : ∀ samples total current,
    scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples total
          (accuracyScaleFactor q • current) =
      (iteratedKernelLaw
        (fun _ => retainedSumKernel
          (scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
            properStride retryLimit) weight)
        (Measure.dirac (total, some current)) samples).map
          retainedSumOutput := by
  let K := scheduledBalancedRetainedOptionKernel q I sigma2 proposalCap
    properStride retryLimit
  have hK : Measurable K :=
    scheduledBalancedRetainedOptionKernel_measurable q I hsigma2 _ _ _
  have hKprob : ∀ state, IsProbabilityMeasure (K state) := by
    intro state
    cases state with
    | none =>
        change IsProbabilityMeasure (Measure.dirac none)
        infer_instance
    | some state =>
        exact (scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
          q I hsigma2 proposalCap properStride retryLimit).2 _
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  have hout : Measurable (retainedSumOutput
      (S := AmbientSpace q.n)) := measurable_retainedSumOutput
  intro samples
  induction samples with
  | zero =>
      intro total current
      simp only [scheduledBalancedTransitionCollectLaw,
        iteratedKernelLaw_zero]
      rw [Measure.map_dirac' hout]
      congr 3
      exact inv_smul_smul₀ (accuracyScaleFactor_pos q).ne' current
  | succ samples ih =>
      intro total current
      let R := retainedSumKernel K weight
      let update : (ℝ × Option (AmbientSpace q.n)) ×
          Option (AmbientSpace q.n) →
          ℝ × Option (AmbientSpace q.n) := fun value =>
        (value.1.1 + retainedOptionWeight weight value.2, value.2)
      have hupdate : Measurable update := by
        exact ((measurable_fst.comp measurable_fst).add
          ((measurable_retainedOptionWeight hweight).comp measurable_snd)).prodMk
            measurable_snd
      have hfront := iteratedKernelLaw_const_succ_eq_bind
        R hsum.1 (Measure.dirac (total, some current)) samples
      have hmix := bind_iteratedKernelLaw_dirac_eq_iteratedKernelLaw_map
        (fun _ => R) (fun _ => hsum.1) (fun _ _ => hsum.2 _)
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride retryLimit (accuracyScaleFactor q • current))
        (fun next => update ((total, some current), next))
        (hupdate.comp (measurable_const.prodMk measurable_id)) samples
      rw [scheduledBalancedTransitionCollectLaw]
      change _ = (iteratedKernelLaw (fun _ => R)
        (Measure.dirac (total, some current)) (samples + 1)).map
          retainedSumOutput
      rw [hfront, Measure.dirac_bind
        (measurable_iteratedKernelLaw_const_from_kernel R hsum.1 samples)]
      change _ = (iteratedKernelLaw (fun _ => R)
        (R (total, some current)) samples).map retainedSumOutput
      have hRstart : R (total, some current) =
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit (accuracyScaleFactor q • current)).map
              (fun next => update ((total, some current), next)) := by rfl
      rw [hRstart, ← hmix]
      let T := scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit (accuracyScaleFactor q • current)
      let F : Option (AmbientSpace q.n) →
          Measure (ℝ × Option (AmbientSpace q.n)) := fun next =>
        iteratedKernelLaw (fun _ => R)
          (Measure.dirac (update ((total, some current), next))) samples
      have hF : Measurable F :=
        (iteratedKernelLaw_dirac_measurable_and_probability
          (fun _ => R) (fun _ => hsum.1) (fun _ _ => hsum.2 _) samples).1.comp
            (hupdate.comp (measurable_const.prodMk measurable_id))
      change T.bind (fun result => match result with
          | none => Measure.dirac none
          | some target =>
              scheduledBalancedTransitionCollectLaw q I sigma2 weight
                proposalCap properStride retryLimit samples
                (total + weight target) (accuracyScaleFactor q • target)) =
        (T.bind F).map retainedSumOutput
      calc
        _ = T.bind (fun next => (F next).map retainedSumOutput) := by
          apply Measure.bind_congr_right
          filter_upwards with next
          cases next with
          | none =>
              have hdead := iterated_retainedSumKernel_dirac_none
                K hK hKprob rfl weight hweight total samples
              dsimp [F, update, retainedOptionWeight]
              rw [add_zero]
              change Measure.dirac none =
                (iteratedKernelLaw (fun _ => R)
                  (Measure.dirac (total, none)) samples).map retainedSumOutput
              rw [hdead, Measure.map_dirac' hout]
              rfl
          | some next =>
              simpa [F, update, retainedOptionWeight, K, R] using
                ih (total + weight next) next
        _ = _ := (map_bind_eq_bind_map_of_measurable T hF hout).symm

/-- Pointwise, one shadow step increments the total by exactly the weight of
the new retained state (zero after death). -/
theorem retainedSumKernel_total_eq
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (weight : S → ℝ)
    (hweight : Measurable weight)
    (state : ℝ × Option S) :
    (retainedSumKernel K weight state).map Prod.fst =
      (K state.2).map
        (fun next => state.1 + retainedOptionWeight weight next) := by
  unfold retainedSumKernel
  have hout : Measurable fun next : Option S =>
      (state.1 + retainedOptionWeight weight next, next) :=
    (measurable_const.add
      (measurable_retainedOptionWeight hweight)).prodMk measurable_id
  simpa [Function.comp_def] using
    (Measure.map_map (μ := K state.2) measurable_fst hout)

/-! ## Loss from killing the accumulated sum -/

/-- Killing the shadow total only on dead outcomes loses at most the
deterministic total bound times the final death probability. -/
theorem integral_retainedLiveTotal_loss_le
    {S : Type*} [MeasurableSpace S]
    (mu : Measure (ℝ × Option S)) [IsProbabilityMeasure mu]
    {C : ℝ} (hC : 0 ≤ C)
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1)
    (htotalC : ∀ᵐ state ∂mu, state.1 ≤ C) :
    0 ≤ (∫ state, state.1 ∂mu) -
        ∫ state, retainedLiveTotal state ∂mu ∧
      (∫ state, state.1 ∂mu) -
          ∫ state, retainedLiveTotal state ∂mu ≤
        C * mu.real {state | state.2 = none} := by
  let dead : Set (ℝ × Option S) := {state | state.2 = none}
  have hdead : MeasurableSet dead :=
    measurable_snd measurableSet_option_none
  have hfstInt : Integrable (fun state : ℝ × Option S => state.1) mu := by
    apply Integrable.of_bound measurable_fst.aestronglyMeasurable C
    filter_upwards [htotal0, htotalC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hlive0 : ∀ᵐ state ∂mu, 0 ≤ retainedLiveTotal state := by
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, hstate0]
  have hliveC : ∀ᵐ state ∂mu, retainedLiveTotal state ≤ C := by
    filter_upwards [htotalC] with state hstateC
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, hC, hstateC]
  have hliveInt : Integrable (retainedLiveTotal (S := S)) mu := by
    apply Integrable.of_bound
      measurable_retainedLiveTotal.aestronglyMeasurable C
    filter_upwards [hlive0, hliveC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hindInt : Integrable (dead.indicator (fun _ => C)) mu := by
    apply Integrable.of_bound
      (measurable_const.indicator hdead).aestronglyMeasurable C
    filter_upwards with state
    by_cases hstate : state ∈ dead
    · simp [Set.indicator_of_mem hstate, Real.norm_eq_abs, abs_of_nonneg hC]
    · simpa [Set.indicator, hstate] using hC
  have hliveLe : ∫ state, retainedLiveTotal state ∂mu ≤
      ∫ state, state.1 ∂mu :=
    integral_mono_ae hliveInt hfstInt <| by
      filter_upwards [htotal0] with state hstate0
      rcases state with ⟨total, state⟩
      cases state <;> simp [retainedLiveTotal, hstate0]
  constructor
  · linarith
  · rw [← integral_sub hfstInt hliveInt]
    calc
      (∫ state, state.1 - retainedLiveTotal state ∂mu) ≤
          ∫ state, dead.indicator (fun _ => C) state ∂mu := by
        apply integral_mono_ae (hfstInt.sub hliveInt) hindInt
        filter_upwards [htotal0, htotalC] with state hstate0 hstateC
        rcases state with ⟨total, state⟩
        cases state with
        | none => simpa [dead, retainedLiveTotal] using hstateC
        | some value => simp [dead, retainedLiveTotal]
      _ = mu.real dead * C := integral_indicator_const C hdead
      _ = C * mu.real {state | state.2 = none} := by
        rw [mul_comm]

/-! ## Scheduled Gaussian endpoint marginals -/

/-- Starting the retained within-phase chain from the exact truncated
Gaussian law, every finite endpoint is close to the scheduled accepted
target.  This is the marginal (rather than joint-history) replacement used
in the first-moment argument. -/
theorem iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ) :
    MeasureLeUpTo
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        samples)
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      (scheduledBalancedStationaryTargetError q +
        samples • figureOneCorrectedTransitionBudget q) := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let target : Measure (AmbientSpace q.n) :=
    figureOneScheduledAcceptedTargetAt q I phase
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
  have htv : Arlib.TVLe target exact
      (scheduledBalancedStationaryTargetError q) := by
    simpa [target, exact, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
        scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
          q I (scheduleValue_pos q phase)
  have hinitial : MeasureLeUpTo (exact.map some) (target.map some)
      (scheduledBalancedStationaryTargetError q) :=
    (MeasureLeUpTo.of_tvLe htv.symm).map measurable_some
  simpa [exact, target, figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt] using
    (iterated_figureOneFinalScheduledRetainedOptionKernel_leUpTo
      q I (scheduleValue_pos q phase) (exact.map some) hinitial samples)

/-- The same marginal comparison bounds the absorbing failure mass, since
the accepted target has no `none` outcome. -/
theorem iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase samples : ℕ) :
    (iteratedKernelLaw
      (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase))
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
      samples) {none} ≤
      scheduledBalancedStationaryTargetError q +
        samples • figureOneCorrectedTransitionBudget q := by
  have h :=
    (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_leUpTo
      q I phase samples).event_le {none}
  have hnone : ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      {none} = 0 := by
    rw [Measure.map_apply measurable_some measurableSet_option_none]
    have hpre : (some : AmbientSpace q.n → Option (AmbientSpace q.n)) ⁻¹'
        ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
      ext point
      simp
    rw [hpre, measure_empty]
  rw [hnone, zero_add] at h
  exact h

#print axioms retainedSumKernel_measurable_and_probability
#print axioms map_iterated_retainedSumKernel_state
#print axioms iterated_retainedSumKernel_ae_total_le
#print axioms lintegral_iterated_retainedSumKernel_total_eq_sum_marginals
#print axioms integral_iterated_retainedSumKernel_total_eq_sum_marginals
#print axioms scheduledBalancedTransitionCollectLaw_eq_map_retainedSumKernel
#print axioms integral_retainedLiveTotal_loss_le
#print axioms
  iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_leUpTo
#print axioms
  iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_none_le

end ArlibCommunity.Algorithms.CV18
