/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.SequentialRecordedKernelReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceTransport

/-!
# Structural invariants preserved by a sequential recorded reset

The maximal-coupling reset preserves the old-state marginal before its
output is recorded.  These lemmas turn almost-sure preservation by the
recording update into exact laws for old projections and coordinates.  Exact
coordinate laws immediately retain `L²` membership, means, second moments,
and all previous approximate-independence statements.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

noncomputable section

/-- Old/new almost-sure facts can be combined on a joint reset law from its
two exact marginals. -/
theorem ae_fst_and_snd_of_map_eq
    {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (reset : Measure (H × Z)) (source : Measure H) (target : Measure Z)
    (OldGood : H → Prop) (NewGood : Z → Prop)
    (hOldMeas : MeasurableSet {state | OldGood state})
    (hNewMeas : MeasurableSet {result | NewGood result})
    (hfst : reset.map Prod.fst = source)
    (hsnd : reset.map Prod.snd = target)
    (hOld : ∀ᵐ state ∂source, OldGood state)
    (hNew : ∀ᵐ result ∂target, NewGood result) :
    ∀ᵐ state ∂reset, OldGood state.1 ∧ NewGood state.2 := by
  have hOld' : ∀ᵐ state ∂reset, OldGood state.1 := by
    have hmapped : ∀ᵐ state ∂reset.map Prod.fst, OldGood state := by
      rw [hfst]
      exact hOld
    exact (ae_map_iff measurable_fst.aemeasurable hOldMeas).1 hmapped
  have hNew' : ∀ᵐ state ∂reset, NewGood state.2 := by
    have hmapped : ∀ᵐ result ∂reset.map Prod.snd, NewGood result := by
      rw [hsnd]
      exact hNew
    exact (ae_map_iff measurable_snd.aemeasurable hNewMeas).1 hmapped
  filter_upwards [hOld', hNew'] with state hold hnew
  exact ⟨hold, hnew⟩

/-- A structural predicate established almost surely after applying the
recording update holds almost surely under the mapped reference law. -/
theorem ae_map_uncurry_update
    {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (reset : Measure (H × Z)) (update : H → Z → H)
    (hupdate : Measurable (Function.uncurry update))
    (Good : H → Prop) (hGoodMeas : MeasurableSet {state | Good state})
    (hGood : ∀ᵐ state ∂reset, Good (update state.1 state.2)) :
    ∀ᵐ state ∂reset.map (Function.uncurry update), Good state := by
  exact (ae_map_iff hupdate.aemeasurable hGoodMeas).2 hGood

/-- An old projection unchanged almost surely by the update has exactly its
source pushforward law after reset and recording. -/
theorem map_map_uncurry_update_eq_source_of_ae
    {H Z P : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace P]
    (reset : Measure (H × Z)) (source : Measure H)
    (update : H → Z → H) (project : H → P)
    (hupdate : Measurable (Function.uncurry update))
    (hproject : Measurable project)
    (hfst : reset.map Prod.fst = source)
    (hpreserve : ∀ᵐ state ∂reset,
      project (update state.1 state.2) = project state.1) :
    (reset.map (Function.uncurry update)).map project = source.map project := by
  calc
    (reset.map (Function.uncurry update)).map project =
        reset.map (project ∘ Function.uncurry update) :=
      Measure.map_map hproject hupdate
    _ = reset.map (project ∘ Prod.fst) := by
      apply Measure.map_congr
      exact hpreserve
    _ = (reset.map Prod.fst).map project :=
      (Measure.map_map hproject measurable_fst).symm
    _ = source.map project := by rw [hfst]

/-- Two old observables retain their complete joint law. -/
theorem map_pair_map_uncurry_update_eq_source_of_ae
    {H Z S T : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace T]
    (reset : Measure (H × Z)) (source : Measure H)
    (update : H → Z → H) (X : H → S) (Y : H → T)
    (hupdate : Measurable (Function.uncurry update))
    (hX : Measurable X) (hY : Measurable Y)
    (hfst : reset.map Prod.fst = source)
    (hpreserve : ∀ᵐ state ∂reset,
      X (update state.1 state.2) = X state.1 ∧
        Y (update state.1 state.2) = Y state.1) :
    (reset.map (Function.uncurry update)).map (fun state => (X state, Y state)) =
      source.map (fun state => (X state, Y state)) := by
  have hpair : Measurable fun state : H => (X state, Y state) :=
    hX.prodMk hY
  calc
    (reset.map (Function.uncurry update)).map
          (fun state => (X state, Y state)) =
        reset.map ((fun state => (X state, Y state)) ∘
          Function.uncurry update) :=
      Measure.map_map hpair hupdate
    _ = reset.map ((fun state => (X state, Y state)) ∘ Prod.fst) := by
      apply Measure.map_congr
      filter_upwards [hpreserve] with state hstate
      exact Prod.ext hstate.1 hstate.2
    _ = (reset.map Prod.fst).map (fun state => (X state, Y state)) :=
      (Measure.map_map hpair measurable_fst).symm
    _ = source.map (fun state => (X state, Y state)) := by rw [hfst]

/-- Exact equality of one real coordinate law preserves `L²`, its mean,
and its second moment. -/
theorem coordinate_moments_of_map_eq
    {H H' : Type*} [MeasurableSpace H] [MeasurableSpace H']
    (source : Measure H) (reference : Measure H')
    (X : H → ℝ) (X' : H' → ℝ)
    (hX : Measurable X) (hX' : Measurable X')
    (hlaw : reference.map X' = source.map X)
    (hmem : MemLp X 2 source) :
    MemLp X' 2 reference ∧
      (∫ state, X' state ∂reference) = ∫ state, X state ∂source ∧
      (∫ state, X' state ^ 2 ∂reference) =
        ∫ state, X state ^ 2 ∂source := by
  have hmemId : MemLp id 2 (source.map X) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      hX.aemeasurable).2
    simpa only [Function.id_comp] using hmem
  have hmemId' : MemLp id 2 (reference.map X') := by
    rw [hlaw]
    exact hmemId
  have hmem' : MemLp X' 2 reference := by
    have := (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      hX'.aemeasurable).1 hmemId'
    simpa only [Function.id_comp] using this
  refine ⟨hmem', ?_, ?_⟩
  · calc
      (∫ state, X' state ∂reference) =
          ∫ value, value ∂reference.map X' :=
        (integral_map hX'.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ value, value ∂source.map X := by rw [hlaw]
      _ = ∫ state, X state ∂source :=
        integral_map hX.aemeasurable measurable_id.aestronglyMeasurable
  · calc
      (∫ state, X' state ^ 2 ∂reference) =
          ∫ value, value ^ 2 ∂reference.map X' :=
        (integral_map hX'.aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable).symm
      _ = ∫ value, value ^ 2 ∂source.map X := by rw [hlaw]
      _ = ∫ state, X state ^ 2 ∂source :=
        integral_map hX.aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable

/-- Any previous approximate-independence statement transports unchanged
when the two old observables are almost surely preserved by the update. -/
theorem ApproxIndepFun.map_uncurry_update_of_ae_preserved
    {H Z S T : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace S] [MeasurableSpace T]
    (reset : Measure (H × Z)) (source : Measure H)
    (update : H → Z → H) (X : H → S) (Y : H → T)
    (hupdate : Measurable (Function.uncurry update))
    (hX : Measurable X) (hY : Measurable Y)
    (hfst : reset.map Prod.fst = source)
    (hpreserve : ∀ᵐ state ∂reset,
      X (update state.1 state.2) = X state.1 ∧
        Y (update state.1 state.2) = Y state.1)
    {epsilon : ℝ} (hind : ApproxIndepFun epsilon X Y source) :
    ApproxIndepFun epsilon X Y
      (reset.map (Function.uncurry update)) := by
  apply ApproxIndepFun.of_map_pair_eq hX hY hX hY _ hind
  exact (map_pair_map_uncurry_update_eq_source_of_ae reset source update
    X Y hupdate hX hY hfst hpreserve).symm

/-- The direct recorded-output reset with update identities that need only
hold on a product of an almost-sure old-state invariant and an almost-sure
output invariant.  The output invariant is required under both the raw output
marginal and the reset target.  This is the form used by trace append
operations: the old trace is valid almost surely and both raw and reset scores
are nonnegative/live almost surely, but none of these facts is pointwise true
on the ambient types. -/
theorem exists_sequentialRecordedOutputReset_of_tvLe_with_approxIndep_ae
    {H Z Y P S : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace S]
    (source : Measure H) [IsProbabilityMeasure source]
    (K : H → Measure Z) (target : Measure Z)
    [IsProbabilityMeasure target]
    (update : H → Z → H) (observe : Z → Y)
    (readNew : H → Y) (projectOld : H → P)
    (oldStatistic : H → S)
    (OldGood : H → Prop) (NewGood : Z → Prop) (Good : H → Prop)
    (hK : Measurable K) (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (hupdate : Measurable (Function.uncurry update))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hprojectOld : Measurable projectOld)
    (holdStatistic : Measurable oldStatistic)
    (hOldMeas : MeasurableSet {state | OldGood state})
    (hNewMeas : MeasurableSet {result | NewGood result})
    (hGoodMeas : MeasurableSet {state | Good state})
    (hOld : ∀ᵐ state ∂source, OldGood state)
    (hNewRaw : ∀ᵐ result
      ∂((sequentialPairLaw source K).map Prod.snd), NewGood result)
    (hNew : ∀ᵐ result ∂target, NewGood result)
    (hreadUpdate : ∀ state result, OldGood state → NewGood result →
      readNew (update state result) = observe result)
    (hprojectUpdate : ∀ state result, OldGood state → NewGood result →
      projectOld (update state result) = projectOld state)
    (holdUpdate : ∀ state result, OldGood state → NewGood result →
      oldStatistic (update state result) = oldStatistic state)
    (hGoodUpdate : ∀ state result, OldGood state → NewGood result →
      Good (update state result))
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
        oldStatistic readNew reference ∧
      ∀ᵐ state ∂reference, Good state := by
  let raw := sequentialPairLaw source K
  have hrawProb : IsProbabilityMeasure raw :=
    sequentialPairLaw_isProbabilityMeasure source hK hKprob
  let _ : IsProbabilityMeasure raw := hrawProb
  obtain ⟨reset, hresetProb, hresetOld, hresetTarget, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe raw target (by
      simpa only [raw] using hnext)
  let _ : IsProbabilityMeasure reset := hresetProb
  have hrawFst : raw.map Prod.fst = source := by
    dsimp only [raw]
    exact map_sequentialPairLaw_fst source K hK hKprob
  have hresetFst : reset.map Prod.fst = source := hresetOld.trans hrawFst
  have hrawGood : ∀ᵐ state ∂raw,
      OldGood state.1 ∧ NewGood state.2 :=
    ae_fst_and_snd_of_map_eq raw source (raw.map Prod.snd)
      OldGood NewGood hOldMeas hNewMeas hrawFst rfl hOld (by
        simpa only [raw] using hNewRaw)
  have hresetGood : ∀ᵐ state ∂reset,
      OldGood state.1 ∧ NewGood state.2 :=
    ae_fst_and_snd_of_map_eq reset source target OldGood NewGood
      hOldMeas hNewMeas hresetFst hresetTarget hOld hNew
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
        filter_upwards [hresetGood] with state hstate
        exact hreadUpdate state.1 state.2 hstate.1 hstate.2
      _ = (reset.map Prod.snd).map observe :=
        (Measure.map_map hobserve measurable_snd).symm
      _ = target.map observe := by rw [hresetTarget]
  have hold : reference.map projectOld = source.map projectOld := by
    calc
      reference.map projectOld = reset.map (projectOld ∘ applyUpdate) :=
        Measure.map_map hprojectOld hupdate
      _ = reset.map (projectOld ∘ Prod.fst) := by
        apply Measure.map_congr
        filter_upwards [hresetGood] with state hstate
        exact hprojectUpdate state.1 state.2 hstate.1 hstate.2
      _ = (reset.map Prod.fst).map projectOld :=
        (Measure.map_map hprojectOld measurable_fst).symm
      _ = source.map projectOld := by rw [hresetFst]
  have hindActual : ApproxIndepFun eta oldStatistic readNew actual := by
    apply ApproxIndepFun.of_map_pair_eq
      (holdStatistic.comp measurable_fst) (hobserve.comp measurable_snd)
      holdStatistic hreadNew _ hind
    calc
      raw.map (fun state =>
          (oldStatistic state.1, observe state.2)) =
          raw.map ((fun state =>
            (oldStatistic state, readNew state)) ∘ applyUpdate) := by
        apply Measure.map_congr
        filter_upwards [hrawGood] with state hstate
        exact Prod.ext
          (holdUpdate state.1 state.2 hstate.1 hstate.2).symm
          (hreadUpdate state.1 state.2 hstate.1 hstate.2).symm
      _ = actual.map (fun state =>
          (oldStatistic state, readNew state)) := by
        rw [show actual = raw.map applyUpdate by rfl]
        exact (Measure.map_map
          (holdStatistic.prodMk hreadNew) hupdate).symm
  have hindReference : ApproxIndepFun (eta + 3 * delta.toReal)
      oldStatistic readNew reference :=
    ApproxIndepFun.of_tvLe reference actual hdelta
      oldStatistic readNew holdStatistic hreadNew hresetMapped.symm hindActual
  have hGoodReference : ∀ᵐ state ∂reference, Good state := by
    apply ae_map_uncurry_update reset update hupdate Good hGoodMeas
    filter_upwards [hresetGood] with state hstate
    exact hGoodUpdate state.1 state.2 hstate.1 hstate.2
  exact ⟨reference, hreferenceProb, hdom, hnew, hold,
    hindReference, hGoodReference⟩

#print axioms map_map_uncurry_update_eq_source_of_ae
#print axioms map_pair_map_uncurry_update_eq_source_of_ae
#print axioms coordinate_moments_of_map_eq
#print axioms ApproxIndepFun.map_uncurry_update_of_ae_preserved
#print axioms exists_sequentialRecordedOutputReset_of_tvLe_with_approxIndep_ae

end

end ArlibCommunity.Algorithms.CV18
