/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectSemantics
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov

/-!
# History-preserving reset after a recorded kernel step

A phase kernel may return both an observable and its next operational state.
This module runs such a kernel, resets the complete returned result to a
nearby reference marginal while preserving the entire past, and only then
records the observable.  It is the outer-phase analogue of the per-sample
reset used in the CV18 exact-chance construction.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Run `K` on the operational state and retain the old history beside the
complete result. -/
noncomputable def historyRawOutputLaw
    {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z]
    (sourceLaw : Measure (H × X)) (K : X → Measure Z) : Measure (H × Z) :=
  sourceLaw.bind fun state => (K state.2).map fun result => (state.1, result)

/-- Record the observable returned by one phase and retain its next state. -/
noncomputable def historyRecordedOutputLaw
    {H X Y Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (sourceLaw : Measure (H × X)) (K : X → Measure Z)
    (record : H → Y → H) (observe : Z → Y) (nextState : Z → X) :
    Measure (H × X) :=
  (historyRawOutputLaw sourceLaw K).map fun state =>
    (record state.1 (observe state.2), nextState state.2)

theorem historyRawOutputLaw_measurable_and_probability
    {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z]
    (sourceLaw : Measure (H × X)) [IsProbabilityMeasure sourceLaw]
    (K : X → Measure Z) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    IsProbabilityMeasure (historyRawOutputLaw sourceLaw K) := by
  let lift : (H × X) → Measure (H × Z) := fun state =>
    (K state.2).map fun result => (state.1, result)
  have hlift : Measurable lift := by
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2)
      (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)
  have hliftProb : ∀ state, IsProbabilityMeasure (lift state) := by
    intro state
    exact Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable
  exact isProbabilityMeasure_bind hlift.aemeasurable (ae_of_all _ hliftProb)

/-- The output coordinate of the raw history law depends only on the
operational-state marginal of its source.  This is the rewrite used by the
outer CV18 recurrence once the previous reset has made that marginal exact. -/
theorem map_historyRawOutputLaw_snd
    {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z]
    (sourceLaw : Measure (H × X)) (K : X → Measure Z)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    (historyRawOutputLaw sourceLaw K).map Prod.snd =
      (sourceLaw.map Prod.snd).bind K := by
  let lift : (H × X) → Measure (H × Z) := fun state =>
    (K state.2).map fun result => (state.1, result)
  have hlift : Measurable lift := by
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2)
      (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)
  change (sourceLaw.bind lift).map Prod.snd =
    (sourceLaw.map Prod.snd).bind K
  rw [map_bind_eq_bind_map_of_measurable sourceLaw hlift measurable_snd]
  rw [map_bind_eq_bind_comp_state sourceLaw measurable_snd hK]
  apply Measure.bind_congr_right
  filter_upwards with state
  have hpair : Measurable fun result : Z => (state.1, result) :=
    measurable_const.prodMk measurable_id
  calc
    ((K state.2).map fun result : Z => (state.1, result)).map Prod.snd =
        (K state.2).map (Prod.snd ∘ fun result : Z => (state.1, result)) :=
      Measure.map_map measurable_snd hpair
    _ = (K state.2).map id := by rfl
    _ = K state.2 := Measure.map_id

/-- A one-step exact-chance reset for a phase result.  The target is a joint
law of the phase observable and retained next state, so one reset supplies
both the desired moment marginal and the exact operational marginal.  The
old-history projection is preserved exactly. -/
theorem exists_historyRecordedOutputReset_of_tvLe
    {H X Y Z P : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace P]
    (sourceLaw : Measure (H × X)) [IsProbabilityMeasure sourceLaw]
    (K : X → Measure Z) (target : Measure Z)
    [IsProbabilityMeasure target]
    (record : H → Y → H) (observe : Z → Y) (nextState : Z → X)
    (readNew : H → Y) (projectOld : H → P)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hnextState : Measurable nextState)
    (hreadNew : Measurable readNew) (hprojectOld : Measurable projectOld)
    (hreadRecord : ∀ history result,
      readNew (record history (observe result)) = observe result)
    (hprojectRecord : ∀ history result,
      projectOld (record history (observe result)) = projectOld history)
    {epsilon : ENNReal}
    (hnext : Arlib.TVLe
      ((historyRawOutputLaw sourceLaw K).map Prod.snd) target epsilon) :
    ∃ reference : Measure (H × X),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (historyRecordedOutputLaw sourceLaw K record observe nextState)
        reference epsilon ∧
      reference.map (readNew ∘ Prod.fst) = target.map observe ∧
      reference.map Prod.snd = target.map nextState ∧
      reference.map (projectOld ∘ Prod.fst) =
        sourceLaw.map (projectOld ∘ Prod.fst) := by
  let raw := historyRawOutputLaw sourceLaw K
  let _ : IsProbabilityMeasure raw :=
    historyRawOutputLaw_measurable_and_probability sourceLaw K hK hKprob
  obtain ⟨reset, hresetProb, hresetHistory, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  let update : H × Z → H × X := fun state =>
    (record state.1 (observe state.2), nextState state.2)
  have hupdate : Measurable update := by
    exact (hrecord.comp (measurable_fst.prodMk
      (hobserve.comp measurable_snd))).prodMk
        (hnextState.comp measurable_snd)
  let reference := reset.map update
  have hreferenceProb : IsProbabilityMeasure reference :=
    Measure.isProbabilityMeasure_map hupdate.aemeasurable
  let actual := historyRecordedOutputLaw sourceLaw K record observe nextState
  let _ : IsProbabilityMeasure actual := by
    dsimp only [actual, historyRecordedOutputLaw]
    exact Measure.isProbabilityMeasure_map hupdate.aemeasurable
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_, ?_⟩
  · change MeasureLeUpTo actual reference epsilon
    exact MeasureLeUpTo.of_tvLe (by
      simpa only [actual, historyRecordedOutputLaw, raw, reference] using
        hresetTV.map hupdate)
  · calc
      reference.map (readNew ∘ Prod.fst) =
          reset.map ((readNew ∘ Prod.fst) ∘ update) :=
        Measure.map_map (hreadNew.comp measurable_fst) hupdate
      _ = reset.map (observe ∘ Prod.snd) := by
        apply Measure.map_congr
        filter_upwards with state
        exact hreadRecord state.1 state.2
      _ = (reset.map Prod.snd).map observe :=
        (Measure.map_map hobserve measurable_snd).symm
      _ = target.map observe := by rw [hresetTarget]
  · calc
      reference.map Prod.snd =
          reset.map (nextState ∘ Prod.snd) :=
        Measure.map_map measurable_snd hupdate
      _ = (reset.map Prod.snd).map nextState :=
        (Measure.map_map hnextState measurable_snd).symm
      _ = target.map nextState := by rw [hresetTarget]
  · calc
      reference.map (projectOld ∘ Prod.fst) =
          reset.map ((projectOld ∘ Prod.fst) ∘ update) :=
        Measure.map_map (hprojectOld.comp measurable_fst) hupdate
      _ = reset.map (projectOld ∘ Prod.fst) := by
        apply Measure.map_congr
        filter_upwards with state
        exact hprojectRecord state.1 state.2
      _ = (reset.map Prod.fst).map projectOld :=
        (Measure.map_map hprojectOld measurable_fst).symm
      _ = (raw.map Prod.fst).map projectOld := by rw [hresetHistory]
      _ = raw.map (projectOld ∘ Prod.fst) :=
        Measure.map_map hprojectOld measurable_fst
      _ = sourceLaw.map (projectOld ∘ Prod.fst) := by
        unfold raw historyRawOutputLaw
        have hlift : Measurable fun state : H × X =>
            (K state.2).map fun result : Z => (state.1, result) := by
          exact measurable_measure_map_param_variable
            (hK.comp measurable_snd) (fun state => hKprob state.2)
            (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)
        have hout : Measurable (projectOld ∘ Prod.fst : H × Z → P) :=
          hprojectOld.comp measurable_fst
        rw [map_bind_eq_bind_map_of_measurable sourceLaw hlift hout]
        calc
          sourceLaw.bind (fun state =>
              ((K state.2).map fun result : Z => (state.1, result)).map
                (projectOld ∘ Prod.fst)) =
              sourceLaw.bind (fun state =>
                Measure.dirac (projectOld state.1)) := by
            apply Measure.bind_congr_right
            filter_upwards with state
            let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
            have hpair : Measurable fun result : Z => (state.1, result) :=
              measurable_const.prodMk measurable_id
            calc
              ((K state.2).map fun result : Z => (state.1, result)).map
                    (projectOld ∘ Prod.fst) =
                  (K state.2).map ((projectOld ∘ Prod.fst) ∘
                    fun result : Z => (state.1, result)) :=
                Measure.map_map hout hpair
              _ = (K state.2).map (fun _ => projectOld state.1) := by rfl
              _ = Measure.dirac (projectOld state.1) := by
                rw [Measure.map_const, measure_univ, one_smul]
          _ = sourceLaw.map (projectOld ∘ Prod.fst) :=
            Measure.bind_dirac_eq_map sourceLaw
              (hprojectOld.comp measurable_fst)

#print axioms historyRawOutputLaw_measurable_and_probability
#print axioms map_historyRawOutputLaw_snd
#print axioms exists_historyRecordedOutputReset_of_tvLe

end

end ArlibCommunity.Algorithms.CV18
