/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset

/-!
# History-preserving reset before recording a sample

The finite-walk replacement in CV18 must not first append a score and then
try to replace its source sample.  The correct order is:

1. run the operational next-state kernel;
2. reset only the new-state marginal, preserving the old recorded history;
3. append the observable of the reset state.

This file isolates the measure-theoretic bookkeeping for that order.  The
actual reset construction is deliberately an input: a coupling theorem may
produce it from a TV estimate on the new-state marginal.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Run one operational transition but do not yet record its observable. -/
noncomputable def historyRawNextKernel
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) : H × X → Measure (H × X) :=
  fun state => (K state.2).map (Prod.mk state.1)

theorem historyRawNextKernel_measurable_and_probability
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    Measurable (historyRawNextKernel (H := H) K) ∧
      ∀ state, IsProbabilityMeasure (historyRawNextKernel (H := H) K state) := by
  have hpair : Measurable fun value : (H × X) × X =>
      (value.1.1, value.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  constructor
  · unfold historyRawNextKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hpair
  · intro state
    unfold historyRawNextKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable

/-- A raw transition preserves every measurable observable of the old
recorded history. -/
theorem map_bind_historyRawNextKernel_old
    {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (projectOld : H → Z)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hprojectOld : Measurable projectOld) :
    (prefixLaw.bind (historyRawNextKernel K)).map
        (projectOld ∘ Prod.fst) =
      prefixLaw.map (projectOld ∘ Prod.fst) := by
  have hraw := historyRawNextKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hout : Measurable (projectOld ∘ Prod.fst : H × X → Z) :=
    hprojectOld.comp measurable_fst
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hout]
  calc
    prefixLaw.bind (fun state =>
        (historyRawNextKernel K state).map (projectOld ∘ Prod.fst)) =
        prefixLaw.bind (fun state => Measure.dirac (projectOld state.1)) := by
      apply Measure.bind_congr_right
      filter_upwards with state
      unfold historyRawNextKernel
      let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
      have hpair : Measurable fun next : X => (state.1, next) :=
        measurable_const.prodMk measurable_id
      calc
        ((K state.2).map fun next => (state.1, next)).map
              (projectOld ∘ Prod.fst) =
            (K state.2).map
              ((projectOld ∘ Prod.fst) ∘ (fun next => (state.1, next))) :=
          Measure.map_map hout hpair
        _ = (K state.2).map (fun _ => projectOld state.1) := by rfl
        _ = Measure.dirac (projectOld state.1) := by
          rw [Measure.map_const, measure_univ, one_smul]
    _ = prefixLaw.map (projectOld ∘ Prod.fst) :=
      Measure.bind_dirac_eq_map prefixLaw (hprojectOld.comp measurable_fst)

/-- The state coordinate of the raw law is the ordinary operational
next-state marginal. -/
theorem map_bind_historyRawNextKernel_snd
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    (prefixLaw.bind (historyRawNextKernel K)).map Prod.snd =
      (prefixLaw.map Prod.snd).bind K := by
  have hraw := historyRawNextKernel_measurable_and_probability
    (H := H) K hK hKprob
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 measurable_snd]
  rw [map_bind_eq_bind_comp_state prefixLaw measurable_snd hK]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextKernel
  have hpair : Measurable fun next : X => (state.1, next) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map measurable_snd hpair]
  change Measure.map id (K state.2) = K state.2
  exact Measure.map_id

/-- Append the observable of a reset state, retaining that reset state as the
operational state for the following step. -/
def historyRecordResetState
    {H X Y : Type*}
    (record : H → Y → H) (observe : X → Y) : H × X → H × X :=
  fun state => (record state.1 (observe state.2), state.2)

theorem measurable_historyRecordResetState
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyRecordResetState record observe) := by
  exact (hrecord.comp
      (measurable_fst.prodMk (hobserve.comp measurable_snd))).prodMk
    measurable_snd

/-- The executable one-step kernel, written directly as transition followed
by recording. -/
noncomputable def historyOperationalRecordKernel
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y) :
    H × X → Measure (H × X) :=
  fun state => (K state.2).map fun next =>
    (record state.1 (observe next), next)

theorem historyOperationalRecordKernel_measurable_and_probability
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyOperationalRecordKernel K record observe) ∧
      ∀ state, IsProbabilityMeasure
        (historyOperationalRecordKernel K record observe state) := by
  have hupdate : Measurable fun value : (H × X) × X =>
      (record value.1.1 (observe value.2), value.2) :=
    (hrecord.comp ((measurable_fst.comp measurable_fst).prodMk
      (hobserve.comp measurable_snd))).prodMk measurable_snd
  constructor
  · unfold historyOperationalRecordKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hupdate
  · intro state
    unfold historyOperationalRecordKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (hupdate.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Recording an observation does not change the operational next-state
marginal. -/
theorem map_bind_historyOperationalRecordKernel_snd
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    (prefixLaw.bind
        (historyOperationalRecordKernel K record observe)).map Prod.snd =
      (prefixLaw.map Prod.snd).bind K := by
  have hstep := historyOperationalRecordKernel_measurable_and_probability
    K record observe hK hKprob hrecord hobserve
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hstep.1 measurable_snd]
  rw [map_bind_eq_bind_comp_state prefixLaw measurable_snd hK]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyOperationalRecordKernel
  have hnext : Measurable fun next : X =>
      (record state.1 (observe next), next) :=
    (hrecord.comp (measurable_const.prodMk hobserve)).prodMk measurable_id
  rw [Measure.map_map measurable_snd hnext]
  change Measure.map id (K state.2) = K state.2
  exact Measure.map_id

/-- Running the operational transition and then recording is exactly the
direct executable recording kernel. -/
theorem bind_historyRawNextKernel_map_record_eq
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    (prefixLaw.bind (historyRawNextKernel K)).map
        (historyRecordResetState record observe) =
      prefixLaw.bind (historyOperationalRecordKernel K record observe) := by
  have hraw := historyRawNextKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hrecordState := measurable_historyRecordResetState
    record observe hrecord hobserve
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hrecordState]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextKernel historyOperationalRecordKernel
  calc
    ((K state.2).map (Prod.mk state.1)).map
          (historyRecordResetState record observe) =
        (K state.2).map
          (historyRecordResetState record observe ∘ Prod.mk state.1) :=
      Measure.map_map hrecordState
        (measurable_const.prodMk measurable_id)
    _ = (K state.2).map (fun next =>
        (record state.1 (observe next), next)) := by rfl

/-- A history-preserving reset of the raw next-state law can be pushed
through recording without increasing its additive comparison error. -/
theorem MeasureLeUpTo.historyOperationalRecord_of_rawReset
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw reset : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) {epsilon : ENNReal}
    (hreset : MeasureLeUpTo
      (prefixLaw.bind (historyRawNextKernel K)) reset epsilon) :
    MeasureLeUpTo
      (prefixLaw.bind (historyOperationalRecordKernel K record observe))
      (reset.map (historyRecordResetState record observe)) epsilon := by
  rw [← bind_historyRawNextKernel_map_record_eq prefixLaw K record observe
    hK hKprob hrecord hobserve]
  exact hreset.map
    (measurable_historyRecordResetState record observe hrecord hobserve)

/-- If `readNew` reads the freshly appended coordinate, the reference law
obtained by reset-before-recording gives that coordinate exactly the target
observable marginal. -/
theorem map_recorded_newCoordinate_eq_of_reset_marginal
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (reset : Measure (H × X)) (target : Measure X)
    (record : H → Y → H) (observe : X → Y) (readNew : H → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hmarginal : reset.map Prod.snd = target) :
    (reset.map (historyRecordResetState record observe)).map
        (readNew ∘ Prod.fst) = target.map observe := by
  have hrecordState := measurable_historyRecordResetState
    record observe hrecord hobserve
  rw [Measure.map_map (hreadNew.comp measurable_fst) hrecordState]
  have heq : (readNew ∘ Prod.fst) ∘
      historyRecordResetState record observe = observe ∘ Prod.snd := by
    funext state
    exact hreadRecord state.1 state.2
  rw [heq, ← Measure.map_map hobserve measurable_snd, hmarginal]

/-- Construct the per-sample exact reference used by the CV18 exact-chance
induction.  Unlike the shadow-copy construction below, this resets the
operational state of the *reference* chain itself.  Consequently its next
step again starts from the exact target marginal, while the executable chain
is related to it by additive domination. -/
theorem exists_recordedResetReference_of_nextMarginal_tvLe_preserving
    {H X Y Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (prefixLaw : Measure (H × X)) [IsProbabilityMeasure prefixLaw]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (target : Measure X) [IsProbabilityMeasure target]
    (readNew : H → Y) (projectOld : H → Z)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hprojectOld : Measurable projectOld)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hprojectRecord : ∀ history x,
      projectOld (record history (observe x)) = projectOld history)
    {epsilon : ENNReal}
    (hnext : Arlib.TVLe
      ((prefixLaw.bind (historyRawNextKernel K)).map Prod.snd)
      target epsilon) :
    ∃ reference : Measure (H × X),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (prefixLaw.bind (historyOperationalRecordKernel K record observe))
        reference epsilon ∧
      reference.map (readNew ∘ Prod.fst) = target.map observe ∧
      reference.map Prod.snd = target ∧
      reference.map (projectOld ∘ Prod.fst) =
        prefixLaw.map (projectOld ∘ Prod.fst) := by
  let raw := prefixLaw.bind (historyRawNextKernel K)
  have hrawKernel := historyRawNextKernel_measurable_and_probability
    (H := H) K hK hKprob
  let _ : IsProbabilityMeasure raw :=
    isProbabilityMeasure_bind hrawKernel.1.aemeasurable
      (ae_of_all _ hrawKernel.2)
  obtain ⟨reset, hresetProb, hresetHistory, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  let reference := reset.map (historyRecordResetState record observe)
  have hrecordState := measurable_historyRecordResetState
    record observe hrecord hobserve
  have hreferenceProb : IsProbabilityMeasure reference :=
    Measure.isProbabilityMeasure_map hrecordState.aemeasurable
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, ?_⟩
  · have hresetMlu : MeasureLeUpTo raw reset epsilon :=
      MeasureLeUpTo.of_tvLe hresetTV
    simpa only [raw, reference] using
      (MeasureLeUpTo.historyOperationalRecord_of_rawReset
        prefixLaw reset K record observe hK hKprob hrecord hobserve
        hresetMlu)
  · simpa only [reference] using
      map_recorded_newCoordinate_eq_of_reset_marginal
        reset target record observe readNew hrecord hobserve hreadNew
        hreadRecord hresetTarget
  · calc
      reference.map Prod.snd =
          reset.map (Prod.snd ∘ historyRecordResetState record observe) :=
        Measure.map_map measurable_snd hrecordState
      _ = reset.map Prod.snd := by rfl
      _ = target := hresetTarget
  · have hprojectFunction :
        (projectOld ∘ Prod.fst) ∘ historyRecordResetState record observe =
          projectOld ∘ Prod.fst := by
      funext state
      exact hprojectRecord state.1 state.2
    calc
      reference.map (projectOld ∘ Prod.fst) =
          reset.map ((projectOld ∘ Prod.fst) ∘
            historyRecordResetState record observe) :=
        Measure.map_map (hprojectOld.comp measurable_fst) hrecordState
      _ = reset.map (projectOld ∘ Prod.fst) := by rw [hprojectFunction]
      _ = (reset.map Prod.fst).map projectOld :=
        (Measure.map_map hprojectOld measurable_fst).symm
      _ = (raw.map Prod.fst).map projectOld := by rw [hresetHistory]
      _ = raw.map (projectOld ∘ Prod.fst) :=
        Measure.map_map hprojectOld measurable_fst
      _ = prefixLaw.map (projectOld ∘ Prod.fst) := by
        simpa only [raw] using map_bind_historyRawNextKernel_old
          prefixLaw K projectOld hK hKprob hprojectOld

/-! ## Shadow reset that preserves the operational state

For the executable collector the reset sample is only a shadow used for the
recorded score.  The actual next state must remain available for the next
walk block.  We therefore duplicate the raw next state, preserve the first
copy together with the history, and reset only the second copy.
-/

/-- Run the operational transition and retain both an operational and a
shadow copy of the raw next state. -/
noncomputable def historyRawNextWithCopyKernel
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) : H × X → Measure ((H × X) × X) :=
  fun state => (K state.2).map fun next => ((state.1, next), next)

theorem historyRawNextWithCopyKernel_measurable_and_probability
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    Measurable (historyRawNextWithCopyKernel (H := H) K) ∧
      ∀ state, IsProbabilityMeasure
        (historyRawNextWithCopyKernel (H := H) K state) := by
  have hcopy : Measurable fun value : (H × X) × X =>
      ((value.1.1, value.2), value.2) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      measurable_snd
  constructor
  · unfold historyRawNextWithCopyKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hcopy
  · intro state
    unfold historyRawNextWithCopyKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (((measurable_const.prodMk measurable_id).prodMk
        measurable_id)).aemeasurable

/-- The shadow copy before reset has exactly the ordinary operational
next-state marginal. -/
theorem map_bind_historyRawNextWithCopyKernel_snd
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    (prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd =
      (prefixLaw.map Prod.snd).bind K := by
  have hraw := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 measurable_snd]
  rw [map_bind_eq_bind_comp_state prefixLaw measurable_snd hK]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextWithCopyKernel
  calc
    ((K state.2).map (fun next => ((state.1, next), next))).map Prod.snd =
        (K state.2).map
          (Prod.snd ∘ fun next => ((state.1, next), next)) :=
      Measure.map_map measurable_snd
        ((measurable_const.prodMk measurable_id).prodMk measurable_id)
    _ = K state.2 := by
      change Measure.map id (K state.2) = K state.2
      exact Measure.map_id

/-- A raw copied transition preserves every measurable observable of the
old recorded history. -/
theorem map_bind_historyRawNextWithCopyKernel_old
    {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (projectOld : H → Z)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hprojectOld : Measurable projectOld) :
    (prefixLaw.bind (historyRawNextWithCopyKernel K)).map
        (projectOld ∘ Prod.fst ∘ Prod.fst) =
      prefixLaw.map (projectOld ∘ Prod.fst) := by
  have hraw := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hout : Measurable (projectOld ∘ Prod.fst ∘ Prod.fst :
      ((H × X) × X) → Z) :=
    hprojectOld.comp (measurable_fst.comp measurable_fst)
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hout]
  calc
    prefixLaw.bind (fun state =>
        (historyRawNextWithCopyKernel K state).map
          (projectOld ∘ Prod.fst ∘ Prod.fst)) =
        prefixLaw.bind (fun state => Measure.dirac (projectOld state.1)) := by
      apply Measure.bind_congr_right
      filter_upwards with state
      unfold historyRawNextWithCopyKernel
      let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
      have hcopy : Measurable fun next : X => ((state.1, next), next) :=
        (measurable_const.prodMk measurable_id).prodMk measurable_id
      calc
        ((K state.2).map (fun next => ((state.1, next), next))).map
            (projectOld ∘ Prod.fst ∘ Prod.fst) =
            (K state.2).map
              ((projectOld ∘ Prod.fst ∘ Prod.fst) ∘
                (fun next => ((state.1, next), next))) :=
          Measure.map_map hout hcopy
        _ = (K state.2).map (fun _ => projectOld state.1) := by rfl
        _ = Measure.dirac (projectOld state.1) := by
          rw [Measure.map_const, measure_univ, one_smul]
    _ = prefixLaw.map (projectOld ∘ Prod.fst) :=
      Measure.bind_dirac_eq_map prefixLaw (hprojectOld.comp measurable_fst)

/-- Record the observable of the reset shadow, while carrying the untouched
operational copy into the next executable step. -/
def historyRecordShadowState
    {H X Y : Type*}
    (record : H → Y → H) (observe : X → Y) : ((H × X) × X) → H × X :=
  fun state => (record state.1.1 (observe state.2), state.1.2)

theorem measurable_historyRecordShadowState
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyRecordShadowState record observe) := by
  exact (hrecord.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (hobserve.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_fst)

/-- Before reset the two copies coincide, so recording the shadow copy is
exactly the executable transition-and-record kernel. -/
theorem bind_historyRawNextWithCopy_map_recordShadow_eq
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    (prefixLaw.bind (historyRawNextWithCopyKernel K)).map
        (historyRecordShadowState record observe) =
      prefixLaw.bind (historyOperationalRecordKernel K record observe) := by
  have hraw := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hrecordShadow]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextWithCopyKernel historyOperationalRecordKernel
  calc
    ((K state.2).map (fun next => ((state.1, next), next))).map
          (historyRecordShadowState record observe) =
        (K state.2).map
          (historyRecordShadowState record observe ∘
            fun next => ((state.1, next), next)) :=
      Measure.map_map hrecordShadow
        ((measurable_const.prodMk measurable_id).prodMk measurable_id)
    _ = (K state.2).map (fun next =>
        (record state.1 (observe next), next)) := by rfl

/-- The paper-faithful one-sample replacement: reset only the shadow copy,
then record its score.  The operational next state is untouched. -/
theorem MeasureLeUpTo.historyOperationalRecord_of_shadowReset
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X)) (reset : Measure ((H × X) × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) {epsilon : ENNReal}
    (hreset : MeasureLeUpTo
      (prefixLaw.bind (historyRawNextWithCopyKernel K)) reset epsilon) :
    MeasureLeUpTo
      (prefixLaw.bind (historyOperationalRecordKernel K record observe))
      (reset.map (historyRecordShadowState record observe)) epsilon := by
  rw [← bind_historyRawNextWithCopy_map_recordShadow_eq
    prefixLaw K record observe hK hKprob hrecord hobserve]
  exact hreset.map
    (measurable_historyRecordShadowState record observe hrecord hobserve)

/-- An exact reset shadow gives the freshly recorded score exactly the
target observable marginal. -/
theorem map_shadowRecorded_newCoordinate_eq_of_reset_marginal
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (reset : Measure ((H × X) × X)) (target : Measure X)
    (record : H → Y → H) (observe : X → Y) (readNew : H → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hmarginal : reset.map Prod.snd = target) :
    (reset.map (historyRecordShadowState record observe)).map
        (readNew ∘ Prod.fst) = target.map observe := by
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [Measure.map_map (hreadNew.comp measurable_fst) hrecordShadow]
  have heq : (readNew ∘ Prod.fst) ∘
      historyRecordShadowState record observe = observe ∘ Prod.snd := by
    funext state
    exact hreadRecord state.1.1 state.2
  rw [heq, ← Measure.map_map hobserve measurable_snd, hmarginal]

/-- Preserving the raw `(history, operationalNext)` coordinate in the reset
preserves the next operational-state marginal after the shadow score is
recorded. -/
theorem map_shadowRecorded_operationalState_eq_of_reset_history
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (raw reset : Measure ((H × X) × X))
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe)
    (hhistory : reset.map Prod.fst = raw.map Prod.fst) :
    (reset.map (historyRecordShadowState record observe)).map Prod.snd =
      (raw.map (historyRecordShadowState record observe)).map Prod.snd := by
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [Measure.map_map measurable_snd hrecordShadow,
    Measure.map_map measurable_snd hrecordShadow]
  have heq : Prod.snd ∘ historyRecordShadowState record observe =
      Prod.snd ∘ Prod.fst := by rfl
  rw [heq, ← Measure.map_map measurable_snd measurable_fst,
    ← Measure.map_map measurable_snd measurable_fst, hhistory]

/-- Any measurable moment of a freshly recorded exact shadow is exactly the
corresponding target moment.  In particular, use `moment y = y` or
`moment y = y ^ 2` to obtain the coordinate premises of CV18 equation (6)
without transferring an unbounded score through TV. -/
theorem integral_shadowRecorded_newCoordinate_eq_target
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (reference : Measure (H × X)) (target : Measure X)
    (observe : X → Y) (readNew : H → Y) (moment : Y → ℝ)
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hmoment : Measurable moment)
    (hcoordinate : reference.map (readNew ∘ Prod.fst) =
      target.map observe) :
    (∫ state, moment (readNew state.1) ∂reference) =
      ∫ x, moment (observe x) ∂target := by
  calc
    (∫ state, moment (readNew state.1) ∂reference) =
        ∫ y, moment y ∂reference.map (readNew ∘ Prod.fst) := by
      simpa [Function.comp_apply] using
        (integral_map (hreadNew.comp measurable_fst).aemeasurable
          hmoment.aestronglyMeasurable).symm
    _ = ∫ y, moment y ∂target.map observe := by rw [hcoordinate]
    _ = ∫ x, moment (observe x) ∂target := by
      exact integral_map hobserve.aemeasurable hmoment.aestronglyMeasurable

/-- A state-marginal TV estimate constructs the paper-faithful next
reference law: its new score is computed from an exact target shadow, while
its operational next state is exactly the executable one. -/
theorem exists_shadowRecordedReference_of_nextMarginal_tvLe
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X)) [IsProbabilityMeasure prefixLaw]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (target : Measure X) [IsProbabilityMeasure target]
    (readNew : H → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    {epsilon : ENNReal}
    (hnext : Arlib.TVLe
      ((prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd)
      target epsilon) :
    ∃ reference : Measure (H × X),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (prefixLaw.bind (historyOperationalRecordKernel K record observe))
        reference epsilon ∧
      reference.map (readNew ∘ Prod.fst) = target.map observe ∧
      reference.map Prod.snd =
        (prefixLaw.bind
          (historyOperationalRecordKernel K record observe)).map Prod.snd := by
  let raw := prefixLaw.bind (historyRawNextWithCopyKernel K)
  have hrawKernel := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  let _ : IsProbabilityMeasure raw :=
    isProbabilityMeasure_bind hrawKernel.1.aemeasurable
      (ae_of_all _ hrawKernel.2)
  obtain ⟨reset, hresetProb, hresetHistory, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  let reference := reset.map (historyRecordShadowState record observe)
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  have hreferenceProb : IsProbabilityMeasure reference := by
    exact Measure.isProbabilityMeasure_map hrecordShadow.aemeasurable
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
  · have hresetMlu : MeasureLeUpTo raw reset epsilon :=
      MeasureLeUpTo.of_tvLe hresetTV
    simpa only [raw, reference] using
      (MeasureLeUpTo.historyOperationalRecord_of_shadowReset
        prefixLaw reset K record observe hK hKprob hrecord hobserve
        hresetMlu)
  · simpa only [reference] using
      map_shadowRecorded_newCoordinate_eq_of_reset_marginal
        reset target record observe readNew hrecord hobserve hreadNew
        hreadRecord hresetTarget
  · have hop := map_shadowRecorded_operationalState_eq_of_reset_history
      raw reset record observe hrecord hobserve hresetHistory
    rw [bind_historyRawNextWithCopy_map_recordShadow_eq
      prefixLaw K record observe hK hKprob hrecord hobserve] at hop
    simpa only [reference] using hop

/-- Strengthened one-sample reset that also exposes preservation of any
measurable old-history projection left unchanged by recording.  This is the
induction interface for constructing a single reference law with many exact
shadow coordinates. -/
theorem exists_shadowRecordedReference_of_nextMarginal_tvLe_preserving
    {H X Y Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (prefixLaw : Measure (H × X)) [IsProbabilityMeasure prefixLaw]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (target : Measure X) [IsProbabilityMeasure target]
    (readNew : H → Y) (projectOld : H → Z)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hprojectOld : Measurable projectOld)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hprojectRecord : ∀ history x,
      projectOld (record history (observe x)) = projectOld history)
    {epsilon : ENNReal}
    (hnext : Arlib.TVLe
      ((prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd)
      target epsilon) :
    ∃ reference : Measure (H × X),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (prefixLaw.bind (historyOperationalRecordKernel K record observe))
        reference epsilon ∧
      reference.map (readNew ∘ Prod.fst) = target.map observe ∧
      reference.map Prod.snd =
        (prefixLaw.bind
          (historyOperationalRecordKernel K record observe)).map Prod.snd ∧
      reference.map (projectOld ∘ Prod.fst) =
        prefixLaw.map (projectOld ∘ Prod.fst) := by
  let raw := prefixLaw.bind (historyRawNextWithCopyKernel K)
  have hrawKernel := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  let _ : IsProbabilityMeasure raw :=
    isProbabilityMeasure_bind hrawKernel.1.aemeasurable
      (ae_of_all _ hrawKernel.2)
  obtain ⟨reset, hresetProb, hresetHistory, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  let reference := reset.map (historyRecordShadowState record observe)
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  have hreferenceProb : IsProbabilityMeasure reference :=
    Measure.isProbabilityMeasure_map hrecordShadow.aemeasurable
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, ?_⟩
  · have hresetMlu : MeasureLeUpTo raw reset epsilon :=
      MeasureLeUpTo.of_tvLe hresetTV
    simpa only [raw, reference] using
      (MeasureLeUpTo.historyOperationalRecord_of_shadowReset
        prefixLaw reset K record observe hK hKprob hrecord hobserve
        hresetMlu)
  · simpa only [reference] using
      map_shadowRecorded_newCoordinate_eq_of_reset_marginal
        reset target record observe readNew hrecord hobserve hreadNew
        hreadRecord hresetTarget
  · have hop := map_shadowRecorded_operationalState_eq_of_reset_history
      raw reset record observe hrecord hobserve hresetHistory
    rw [bind_historyRawNextWithCopy_map_recordShadow_eq
      prefixLaw K record observe hK hKprob hrecord hobserve] at hop
    simpa only [reference] using hop
  · have hprojectFunction :
        (projectOld ∘ Prod.fst) ∘
            historyRecordShadowState record observe =
          (projectOld ∘ Prod.fst) ∘ Prod.fst := by
      funext state
      exact hprojectRecord state.1.1 state.2
    calc
      reference.map (projectOld ∘ Prod.fst) =
          reset.map ((projectOld ∘ Prod.fst) ∘
            historyRecordShadowState record observe) :=
        Measure.map_map (hprojectOld.comp measurable_fst) hrecordShadow
      _ = reset.map ((projectOld ∘ Prod.fst) ∘ Prod.fst) := by
        rw [hprojectFunction]
      _ = (reset.map Prod.fst).map (projectOld ∘ Prod.fst) :=
        (Measure.map_map (hprojectOld.comp measurable_fst)
          measurable_fst).symm
      _ = (raw.map Prod.fst).map (projectOld ∘ Prod.fst) := by
        rw [hresetHistory]
      _ = raw.map ((projectOld ∘ Prod.fst) ∘ Prod.fst) :=
        Measure.map_map (hprojectOld.comp measurable_fst) measurable_fst
      _ = prefixLaw.map (projectOld ∘ Prod.fst) := by
        simpa only [raw, Function.comp_def] using
          map_bind_historyRawNextWithCopyKernel_old
            prefixLaw K projectOld hK hKprob hprojectOld

#print axioms historyRawNextKernel_measurable_and_probability
#print axioms map_bind_historyRawNextKernel_old
#print axioms map_bind_historyRawNextKernel_snd
#print axioms historyOperationalRecordKernel_measurable_and_probability
#print axioms map_bind_historyOperationalRecordKernel_snd
#print axioms bind_historyRawNextKernel_map_record_eq
#print axioms MeasureLeUpTo.historyOperationalRecord_of_rawReset
#print axioms map_recorded_newCoordinate_eq_of_reset_marginal
#print axioms exists_recordedResetReference_of_nextMarginal_tvLe_preserving
#print axioms historyRawNextWithCopyKernel_measurable_and_probability
#print axioms map_bind_historyRawNextWithCopyKernel_snd
#print axioms map_bind_historyRawNextWithCopyKernel_old
#print axioms bind_historyRawNextWithCopy_map_recordShadow_eq
#print axioms MeasureLeUpTo.historyOperationalRecord_of_shadowReset
#print axioms map_shadowRecorded_newCoordinate_eq_of_reset_marginal
#print axioms map_shadowRecorded_operationalState_eq_of_reset_history
#print axioms integral_shadowRecorded_newCoordinate_eq_target
#print axioms exists_shadowRecordedReference_of_nextMarginal_tvLe
#print axioms exists_shadowRecordedReference_of_nextMarginal_tvLe_preserving

end

end ArlibCommunity.Algorithms.CV18
