/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.RecordedKernelReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependencePerturbation

/-!
# Approximate independence after a recorded-output reset

The outer chronological construction resets one joint phase output while
preserving all old coordinates.  Total-variation perturbation changes the
strong-mixing coefficient by at most three times the reset error.  This file
packages that transport with `exists_historyRecordedOutputReset_of_tvLe` so
the global recurrence can use the same existential witness.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Symmetric use of additive domination: an independence estimate on the
dominated law transfers to the dominating reset reference at cost `3δ`. -/
theorem ApproxIndepFun.of_measureLeUpTo_symm
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (actual reference : Measure Omega)
    [IsProbabilityMeasure actual] [IsProbabilityMeasure reference]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    {eta : ℝ} (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hreset : MeasureLeUpTo actual reference delta)
    (hind : ApproxIndepFun eta X Y actual) :
    ApproxIndepFun (eta + 3 * delta.toReal) X Y reference :=
  ApproxIndepFun.of_tvLe reference actual hdelta X Y hX hY
    hreset.to_tvLe.symm hind

/-- The history-preserving recorded-output reset together with the inherited
old-history/new-score approximate-independence estimate.  The returned
reference is exactly the witness from
`exists_historyRecordedOutputReset_of_tvLe`; all its marginal identities are
retained. -/
theorem exists_historyRecordedOutputReset_of_tvLe_with_approxIndep
    {H X Y Z P S : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace P]
    [MeasurableSpace S]
    (sourceLaw : Measure (H × X)) [IsProbabilityMeasure sourceLaw]
    (K : X → Measure Z) (target : Measure Z)
    [IsProbabilityMeasure target]
    (record : H → Y → H) (observe : Z → Y) (nextState : Z → X)
    (readNew : H → Y) (projectOld : H → P)
    (oldStatistic : H × X → S)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hnextState : Measurable nextState)
    (hreadNew : Measurable readNew) (hprojectOld : Measurable projectOld)
    (holdStatistic : Measurable oldStatistic)
    (hreadRecord : ∀ history result,
      readNew (record history (observe result)) = observe result)
    (hprojectRecord : ∀ history result,
      projectOld (record history (observe result)) = projectOld history)
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hnext : Arlib.TVLe
      ((historyRawOutputLaw sourceLaw K).map Prod.snd) target delta)
    {eta : ℝ}
    (hind : ApproxIndepFun eta oldStatistic (readNew ∘ Prod.fst)
      (historyRecordedOutputLaw sourceLaw K record observe nextState)) :
    ∃ reference : Measure (H × X),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (historyRecordedOutputLaw sourceLaw K record observe nextState)
        reference delta ∧
      reference.map (readNew ∘ Prod.fst) = target.map observe ∧
      reference.map Prod.snd = target.map nextState ∧
      reference.map (projectOld ∘ Prod.fst) =
        sourceLaw.map (projectOld ∘ Prod.fst) ∧
      ApproxIndepFun (eta + 3 * delta.toReal)
        oldStatistic (readNew ∘ Prod.fst) reference := by
  obtain ⟨reference, hreferenceProb, hreset, hnew, hstate, hold⟩ :=
    exists_historyRecordedOutputReset_of_tvLe
      sourceLaw K target record observe nextState readNew projectOld
      hK hKprob hrecord hobserve hnextState hreadNew hprojectOld
      hreadRecord hprojectRecord hnext
  let raw := historyRawOutputLaw sourceLaw K
  let update : H × Z → H × X := fun state =>
    (record state.1 (observe state.2), nextState state.2)
  let actual := historyRecordedOutputLaw sourceLaw K record observe nextState
  have hrawProb : IsProbabilityMeasure raw :=
    historyRawOutputLaw_measurable_and_probability sourceLaw K hK hKprob
  let _ : IsProbabilityMeasure raw := hrawProb
  have hupdate : Measurable update :=
    (hrecord.comp (measurable_fst.prodMk
      (hobserve.comp measurable_snd))).prodMk
        (hnextState.comp measurable_snd)
  have hactualProb : IsProbabilityMeasure actual := by
    dsimp only [actual, historyRecordedOutputLaw]
    exact Measure.isProbabilityMeasure_map hupdate.aemeasurable
  let _ : IsProbabilityMeasure actual := hactualProb
  let _ : IsProbabilityMeasure reference := hreferenceProb
  refine ⟨reference, hreferenceProb, hreset, hnew, hstate, hold, ?_⟩
  exact ApproxIndepFun.of_measureLeUpTo_symm actual reference hdelta
    oldStatistic (readNew ∘ Prod.fst) holdStatistic
      (hreadNew.comp measurable_fst) hreset (by simpa [actual] using hind)

#print axioms ApproxIndepFun.of_measureLeUpTo_symm
#print axioms
  exists_historyRecordedOutputReset_of_tvLe_with_approxIndep

end

end ArlibCommunity.Algorithms.CV18
