/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

/-!
# Sequential laws and CV18 approximate independence

The paper's Lemma 7.17 is applied to a Markov experiment in which a previous
history `h` is drawn from `rho`, then the next block is drawn from `K h`.  This
module exposes that joint law and reduces its strong-mixing coefficient to TV
mixing from conditionally restricted previous laws.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Set

variable {H T : Type*} [MeasurableSpace H] [MeasurableSpace T]

/-- Measurable postprocessing preserves warmness with the same coefficient. -/
theorem isWarm_map {S : Type*} [MeasurableSpace S]
    {M : ENNReal} {mu nu : Measure H} (h : Arlib.IsWarm M mu nu)
    {f : H -> S} (hf : Measurable f) :
    Arlib.IsWarm M (mu.map f) (nu.map f) := by
  intro A hA
  rw [Measure.map_apply hf hA, Measure.map_apply hf hA]
  exact h (f ⁻¹' A) (hf hA)

/-- Mapping a state projection before a kernel agrees with composing that
kernel with the projection. -/
theorem map_bind_eq_bind_comp_state
    {S : Type*} [MeasurableSpace S]
    (mu : Measure H) {state : H -> S} (hstate : Measurable state)
    {K : S -> Measure T} (hK : Measurable K) :
    (mu.map state).bind K = mu.bind (K ∘ state) := by
  ext A hA
  rw [Measure.bind_apply hA hK.aemeasurable,
    Measure.bind_apply hA (hK.comp hstate).aemeasurable]
  have hm : AEMeasurable (fun s => K s A) (mu.map state) :=
    ((Measure.measurable_coe hA).comp hK).aemeasurable
  rw [lintegral_map' hm hstate.aemeasurable]
  rfl

/-- Joint law of a previous history and the output of the next sequential
kernel. -/
noncomputable def sequentialPairLaw (rho : Measure H) (K : H -> Measure T) :
    Measure (H × T) :=
  rho.bind fun h => (K h).map fun t => (h, t)

/-- The pointwise pair kernel is measurable. -/
theorem measurable_sequentialPairKernel {rho : Measure H} {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h)) :
    Measurable fun h => (K h).map fun t => (h, t) := by
  exact measurable_measure_map_param_variable hK hKprob
    (measurable_fst.prodMk measurable_snd)

/-- A sequential pair law is a probability law. -/
theorem sequentialPairLaw_isProbabilityMeasure
    (rho : Measure H) [IsProbabilityMeasure rho] {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h)) :
    IsProbabilityMeasure (sequentialPairLaw rho K) := by
  unfold sequentialPairLaw
  have hpair := measurable_sequentialPairKernel (rho := rho) hK hKprob
  exact isProbabilityMeasure_bind hpair.aemeasurable <|
    ae_of_all rho fun h => Measure.isProbabilityMeasure_map (by fun_prop)

/-- A measurable rectangle in the sequential pair law is the next kernel
integrated over the restricted previous law. -/
theorem sequentialPairLaw_rectangle
    (rho : Measure H) {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    {A : Set H} (hA : MeasurableSet A) {B : Set T} (hB : MeasurableSet B) :
    sequentialPairLaw rho K (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B) =
      (rho.restrict A).bind K B := by
  unfold sequentialPairLaw
  have hpair := measurable_sequentialPairKernel (rho := rho) hK hKprob
  rw [Measure.bind_apply (hA.preimage measurable_fst |>.inter
      (hB.preimage measurable_snd)) hpair.aemeasurable,
    Measure.bind_apply hB (hK.aemeasurable.mono_measure Measure.restrict_le_self)]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro h
  have hmap : Measurable (fun t : T => (h, t)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_apply hmap
    (hA.preimage measurable_fst |>.inter (hB.preimage measurable_snd))]
  by_cases hh : h ∈ A
  · rw [show (fun t : T => (h, t)) ⁻¹'
        (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B) = B by
      ext t
      simp [hh], indicator_of_mem hh]
  · rw [show (fun t : T => (h, t)) ⁻¹'
        (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B) = ∅ by
      ext t
      simp [hh], indicator_of_notMem hh, measure_empty]

/-- The first marginal of the sequential pair law is the previous law. -/
theorem sequentialPairLaw_fst
    (rho : Measure H) {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    {A : Set H} (hA : MeasurableSet A) :
    sequentialPairLaw rho K (Prod.fst ⁻¹' A) = rho A := by
  have hrect := sequentialPairLaw_rectangle rho hK hKprob hA MeasurableSet.univ
  rw [measure_bind_apply_univ (rho.restrict A) hK hKprob,
    Measure.restrict_apply_univ] at hrect
  simpa using hrect

/-- The second marginal of the sequential pair law is `rho.bind K`. -/
theorem sequentialPairLaw_snd
    (rho : Measure H) {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    {B : Set T} (hB : MeasurableSet B) :
    sequentialPairLaw rho K (Prod.snd ⁻¹' B) = rho.bind K B := by
  have hrect := sequentialPairLaw_rectangle rho hK hKprob MeasurableSet.univ hB
  simpa using hrect

/-- Restricting the previous law and then binding is its event probability
times binding from the conditional previous law. -/
theorem real_restrict_bind_eq_mul_condOn_bind
    (rho : Measure H) [IsProbabilityMeasure rho] {K : H -> Measure T}
    (hK : Measurable K) {A : Set H} (hA : MeasurableSet A)
    (hA0 : rho A ≠ 0) {B : Set T} (hB : MeasurableSet B) :
    ((rho.restrict A).bind K).real B =
      rho.real A * ((Arlib.condOn rho A).bind K).real B := by
  have hAtop : rho A ≠ ⊤ := measure_ne_top rho A
  have hbind : (Arlib.condOn rho A).bind K =
      (rho A)⁻¹ • ((rho.restrict A).bind K) := by
    rw [Arlib.condOn_def, Measure.bind_smul]
  have hENN : rho A * ((Arlib.condOn rho A).bind K B) =
      (rho.restrict A).bind K B := by
    rw [hbind, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
  have hreal := congrArg ENNReal.toReal hENN
  simpa [measureReal_def, ENNReal.toReal_mul] using hreal.symm

/-- Conditioning a probability measure on an event of probability at least
one half produces a `2`-warm measure.  This is the warm-start observation used
in the proof of CV18 Lemma 7.17(b). -/
theorem isWarm_condOn_two_of_half
    (rho : Measure H) [IsProbabilityMeasure rho]
    {A : Set H} (hA : MeasurableSet A)
    (hhalf : 1 / 2 <= rho.real A) :
    Arlib.IsWarm 2 (Arlib.condOn rho A) rho := by
  have hhalfENN : (2 : ENNReal)⁻¹ <= rho A := by
    apply (ENNReal.toReal_le_toReal (by norm_num)
      (measure_ne_top rho A)).mp
    simpa [measureReal_def] using hhalf
  have hinv : (rho A)⁻¹ <= (2 : ENNReal) := by
    exact ENNReal.inv_le_iff_inv_le.mpr (by simpa using hhalfENN)
  intro S hS
  rw [Arlib.condOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS]
  calc
    (rho A)⁻¹ * rho (S ∩ A) <= (rho A)⁻¹ * rho S := by
      exact mul_le_mul le_rfl (measure_mono Set.inter_subset_left)
        (by simp) (by simp)
    _ <= 2 * rho S := mul_le_mul hinv le_rfl (by simp) (by simp)

/-- Sequential form of CV18 Lemma 7.17(b).  If conditioning on every
half-mass previous event leaves the next-output law within `epsilon` of its
unconditional law, then the complete previous history and next output are
`epsilon`-independent. -/
theorem approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
    (rho : Measure H) [IsProbabilityMeasure rho] {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    {epsilon : ENNReal} (hepsilon : epsilon ≠ ⊤)
    (hcond : forall A : Set H, MeasurableSet A ->
      1 / 2 <= rho.real A ->
      Arlib.TVLe ((Arlib.condOn rho A).bind K) (rho.bind K) epsilon) :
    ApproxIndepFun epsilon.toReal Prod.fst Prod.snd
      (sequentialPairLaw rho K) := by
  let pairLaw := sequentialPairLaw rho K
  let _ : IsProbabilityMeasure pairLaw :=
    sequentialPairLaw_isProbabilityMeasure rho hK hKprob
  apply ApproxIndepFun.of_large_left pairLaw measurable_fst measurable_snd
  intro A hA hhalf B hB
  have hfirst : pairLaw.real (Prod.fst ⁻¹' A) = rho.real A := by
    rw [measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (sequentialPairLaw_fst rho hK hKprob hA)
  have hsecond : pairLaw.real (Prod.snd ⁻¹' B) = (rho.bind K).real B := by
    rw [measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (sequentialPairLaw_snd rho hK hKprob hB)
  have hrectangle : pairLaw.real
      (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B) =
      ((rho.restrict A).bind K).real B := by
    rw [measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal
      (sequentialPairLaw_rectangle rho hK hKprob hA hB)
  have hhalfRho : 1 / 2 <= rho.real A := by simpa [hfirst] using hhalf
  have hAposReal : 0 < rho.real A := lt_of_lt_of_le (by norm_num) hhalfRho
  have hA0 : rho A ≠ 0 := by
    intro hzero
    rw [measureReal_def, hzero] at hAposReal
    simp at hAposReal
  let _ : IsProbabilityMeasure (Arlib.condOn rho A) :=
    Arlib.isProbabilityMeasure_condOn rho hA0 (measure_ne_top rho A)
  let _ : IsProbabilityMeasure ((Arlib.condOn rho A).bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  have htv := (hcond A hA hhalfRho).abs_measureReal_sub_le hepsilon hB
  have hscale := real_restrict_bind_eq_mul_condOn_bind rho hK hA hA0 hB
  rw [hrectangle, hfirst, hsecond, hscale]
  have hp0 : 0 <= rho.real A := measureReal_nonneg
  have hp1 : rho.real A <= 1 := by
    simpa only [probReal_univ] using
      measureReal_mono (subset_univ A) (measure_ne_top rho Set.univ)
  calc
    |rho.real A * ((Arlib.condOn rho A).bind K).real B -
        rho.real A * (rho.bind K).real B| =
        rho.real A * |((Arlib.condOn rho A).bind K).real B -
          (rho.bind K).real B| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hp0]
    _ <= rho.real A * epsilon.toReal :=
      mul_le_mul_of_nonneg_left htv hp0
    _ <= epsilon.toReal := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hp1 ENNReal.toReal_nonneg

/-- CV18 Lemma 7.17(b) in the form used by the executable proof.  It is
enough that every `2`-warm start is additively dominated by one common target
law: conditioning on a half-mass history event gives such a start, and the
two comparisons with the common target give the required conditional TV
bound. -/
theorem approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
    (rho : Measure H) [IsProbabilityMeasure rho] {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    (target : Measure T) [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (happrox : forall mu : Measure H, IsProbabilityMeasure mu ->
      Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo (mu.bind K) target delta) :
    ApproxIndepFun (delta + delta).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho K) := by
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
    rho hK hKprob (ENNReal.add_ne_top.mpr ⟨hdelta, hdelta⟩)
  intro A hA hhalf
  have hAposReal : 0 < rho.real A :=
    lt_of_lt_of_le (by norm_num) hhalf
  have hA0 : rho A ≠ 0 := by
    intro hzero
    rw [measureReal_def, hzero] at hAposReal
    simp at hAposReal
  let hcondProb : IsProbabilityMeasure (Arlib.condOn rho A) :=
    Arlib.isProbabilityMeasure_condOn rho hA0 (measure_ne_top rho A)
  let _ : IsProbabilityMeasure (Arlib.condOn rho A) := hcondProb
  let _ : IsProbabilityMeasure ((Arlib.condOn rho A).bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  have hconditioned := happrox (Arlib.condOn rho A) hcondProb
    (isWarm_condOn_two_of_half rho hA hhalf)
  have hunconditioned := happrox rho (inferInstance : IsProbabilityMeasure rho)
    ((Arlib.IsWarm.refl rho).mono (by norm_num))
  exact hconditioned.to_tvLe.trans hunconditioned.to_tvLe.symm

/-- CV18 Lemma 7.17(c), in its model-independent form.  Once the complete
past history and the next phase block satisfy Lemma 7.17(b), taking the
accumulated product of the past and the estimator of the next block is only
measurable postprocessing.  The final premise records the paper's deliberately
coarser `3 k m nu` budget. -/
theorem approxIndepFun_accumulatedProduct_nextEstimator_of_warm_leUpTo
    (rho : Measure H) [IsProbabilityMeasure rho] {K : H -> Measure T}
    (hK : Measurable K) (hKprob : forall h, IsProbabilityMeasure (K h))
    (target : Measure T) [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (happrox : forall mu : Measure H, IsProbabilityMeasure mu ->
      Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo (mu.bind K) target delta)
    (pastProduct : H -> ℝ) (nextEstimator : T -> ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget : (delta + delta).toReal <=
      3 * (k : ℝ) * (m : ℝ) * nu) :
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw rho K) := by
  have hhistory :=
    approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
      rho hK hKprob target hdelta happrox
  exact (hhistory.comp hpastProduct hnextEstimator).mono hbudget

/-- Lemma 7.17(b) when the sequential kernel sees only a retained measurable
state rather than the whole history.  A `2`-warm conditioning of the history
projects to a `2`-warm conditioning of its retained-state marginal. -/
theorem approxIndepFun_history_next_of_state_warm_leUpTo
    {S : Type*} [MeasurableSpace S]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (state : H -> S) (hstate : Measurable state)
    {K : S -> Measure T}
    (hK : Measurable K) (hKprob : forall s, IsProbabilityMeasure (K s))
    (target : Measure T) [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (happrox : forall mu : Measure S, IsProbabilityMeasure mu ->
      Arlib.IsWarm 2 mu (rho.map state) ->
      MeasureLeUpTo (mu.bind K) target delta) :
    ApproxIndepFun (delta + delta).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho (K ∘ state)) := by
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
    rho (hK.comp hstate) (fun h => hKprob (state h)) target hdelta
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  let hmuMapProb : IsProbabilityMeasure (mu.map state) :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hprojected := happrox (mu.map state) hmuMapProb
    (isWarm_map hwarm hstate)
  rw [map_bind_eq_bind_comp_state mu hstate hK] at hprojected
  exact hprojected

/-- CV18 Lemma 7.17(c) for a complete history with a retained Markov state.
The accumulated past product and next-block estimator inherit the paper's
`3 k m nu` dependence budget. -/
theorem approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo
    {S : Type*} [MeasurableSpace S]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (state : H -> S) (hstate : Measurable state)
    {K : S -> Measure T}
    (hK : Measurable K) (hKprob : forall s, IsProbabilityMeasure (K s))
    (target : Measure T) [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (happrox : forall mu : Measure S, IsProbabilityMeasure mu ->
      Arlib.IsWarm 2 mu (rho.map state) ->
      MeasureLeUpTo (mu.bind K) target delta)
    (pastProduct : H -> ℝ) (nextEstimator : T -> ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget : (delta + delta).toReal <=
      3 * (k : ℝ) * (m : ℝ) * nu) :
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw rho (K ∘ state)) := by
  have hhistory := approxIndepFun_history_next_of_state_warm_leUpTo
    rho state hstate hK hKprob target hdelta happrox
  exact (hhistory.comp hpastProduct hnextEstimator).mono hbudget

#print axioms approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
#print axioms approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
#print axioms approxIndepFun_accumulatedProduct_nextEstimator_of_warm_leUpTo
#print axioms approxIndepFun_history_next_of_state_warm_leUpTo
#print axioms approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo

end ArlibCommunity.Algorithms.CV18
