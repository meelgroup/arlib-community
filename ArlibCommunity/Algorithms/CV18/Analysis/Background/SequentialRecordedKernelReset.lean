/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependencePerturbation

/-!
# Recorded-output resets for state-dependent sequential kernels

This is the direct-state variant of `RecordedKernelReset`.  The source law is
already a law on the complete operational/recorded state `H`, and the next
kernel may inspect all of that state.  A maximal-coupling reset replaces the
new kernel output by a prescribed target while retaining the old state.  The
result is then recorded back into `H`.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Apply the returned value of a state-dependent kernel to the state. -/
noncomputable def sequentialRecordedOutputLaw
    {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (source : Measure H) (K : H → Measure Z) (update : H → Z → H) :
    Measure H :=
  (sequentialPairLaw source K).map (Function.uncurry update)

/-- The old-state marginal of a sequential pair law is exactly its source. -/
theorem map_sequentialPairLaw_fst
    {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (source : Measure H) (K : H → Measure Z)
    (hK : Measurable K) (hKprob : ∀ state, IsProbabilityMeasure (K state)) :
    (sequentialPairLaw source K).map Prod.fst = source := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  exact sequentialPairLaw_fst source hK hKprob hA

/-- Direct state-dependent recorded-output reset, including the sharp
`3δ` perturbation of an old-statistic/new-output independence estimate. -/
theorem exists_sequentialRecordedOutputReset_of_tvLe_with_approxIndep
    {H Z Y P S : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace S]
    (source : Measure H) [IsProbabilityMeasure source]
    (K : H → Measure Z) (target : Measure Z)
    [IsProbabilityMeasure target]
    (update : H → Z → H) (observe : Z → Y)
    (readNew : H → Y) (projectOld : H → P)
    (oldStatistic : H → S)
    (hK : Measurable K) (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (hupdate : Measurable (Function.uncurry update))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hprojectOld : Measurable projectOld)
    (holdStatistic : Measurable oldStatistic)
    (hreadUpdate : ∀ state result,
      readNew (update state result) = observe result)
    (hprojectUpdate : ∀ state result,
      projectOld (update state result) = projectOld state)
    (holdUpdate : ∀ state result,
      oldStatistic (update state result) = oldStatistic state)
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hnext : Arlib.TVLe
      ((sequentialPairLaw source K).map Prod.snd) target delta)
    {eta : ℝ}
    (hind : ApproxIndepFun eta
      (oldStatistic ∘ Prod.fst) (observe ∘ Prod.snd)
      (sequentialPairLaw source K)) :
    ∃ reference : Measure H,
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo (sequentialRecordedOutputLaw source K update)
        reference delta ∧
      reference.map readNew = target.map observe ∧
      reference.map projectOld = source.map projectOld ∧
      ApproxIndepFun (eta + 3 * delta.toReal)
        oldStatistic readNew reference := by
  let raw := sequentialPairLaw source K
  have hrawProb : IsProbabilityMeasure raw :=
    sequentialPairLaw_isProbabilityMeasure source hK hKprob
  let _ : IsProbabilityMeasure raw := hrawProb
  obtain ⟨reset, hresetProb, hresetOld, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  let applyUpdate : H × Z → H := Function.uncurry update
  let actual := sequentialRecordedOutputLaw source K update
  let reference := reset.map applyUpdate
  have hactualProb : IsProbabilityMeasure actual := by
    dsimp only [actual, sequentialRecordedOutputLaw]
    exact Measure.isProbabilityMeasure_map hupdate.aemeasurable
  let _ : IsProbabilityMeasure actual := hactualProb
  have hreferenceProb : IsProbabilityMeasure reference :=
    Measure.isProbabilityMeasure_map hupdate.aemeasurable
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hresetMapped : Arlib.TVLe actual reference delta := by
    simpa only [actual, reference, raw, applyUpdate,
      sequentialRecordedOutputLaw] using hresetTV.map hupdate
  have hdom : MeasureLeUpTo actual reference delta :=
    MeasureLeUpTo.of_tvLe hresetMapped
  have hnew : reference.map readNew = target.map observe := by
    calc
      reference.map readNew = reset.map (readNew ∘ applyUpdate) :=
        Measure.map_map hreadNew hupdate
      _ = reset.map (observe ∘ Prod.snd) := by
        apply Measure.map_congr
        filter_upwards with state
        exact hreadUpdate state.1 state.2
      _ = (reset.map Prod.snd).map observe :=
        (Measure.map_map hobserve measurable_snd).symm
      _ = target.map observe := by rw [hresetTarget]
  have hold : reference.map projectOld = source.map projectOld := by
    calc
      reference.map projectOld = reset.map (projectOld ∘ applyUpdate) :=
        Measure.map_map hprojectOld hupdate
      _ = reset.map (projectOld ∘ Prod.fst) := by
        apply Measure.map_congr
        filter_upwards with state
        exact hprojectUpdate state.1 state.2
      _ = (reset.map Prod.fst).map projectOld :=
        (Measure.map_map hprojectOld measurable_fst).symm
      _ = (raw.map Prod.fst).map projectOld := by rw [hresetOld]
      _ = source.map projectOld := by
        rw [show raw.map Prod.fst = source by
          dsimp only [raw]
          exact map_sequentialPairLaw_fst source K hK hKprob]
  have hindActual : ApproxIndepFun eta oldStatistic readNew actual := by
    apply ApproxIndepFun.map applyUpdate hupdate oldStatistic readNew
      holdStatistic hreadNew
    have holdFun : oldStatistic ∘ applyUpdate = oldStatistic ∘ Prod.fst := by
      funext state
      exact holdUpdate state.1 state.2
    have hnewFun : readNew ∘ applyUpdate = observe ∘ Prod.snd := by
      funext state
      exact hreadUpdate state.1 state.2
    rw [holdFun, hnewFun]
    simpa only [raw] using hind
  have hindReference : ApproxIndepFun (eta + 3 * delta.toReal)
      oldStatistic readNew reference :=
    ApproxIndepFun.of_tvLe reference actual hdelta
      oldStatistic readNew holdStatistic hreadNew hresetMapped.symm hindActual
  exact ⟨reference, hreferenceProb, hdom, hnew, hold, hindReference⟩

#print axioms map_sequentialPairLaw_fst
#print axioms exists_sequentialRecordedOutputReset_of_tvLe_with_approxIndep

end

end ArlibCommunity.Algorithms.CV18
