/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ContinuousProgramSemantics

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped Classical

/-!
# Measure-valued interpreter laws

The public program syntax now contains genuine continuous draws. Probability
is therefore expressed by `Measure`, while membership-query complexity remains
a structural property of the program tree.
-/

/-- Measurability obligations for the estimate-only interpreter. -/
def MembershipOracleProgram.EstimateMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Prop
  | .pure _ => True
  | .query point next => EstimateMeasurable oracle (next (oracle point))
  | .randomNat law next =>
      AEMeasurable (fun seed => runEstimate oracle (next seed)) law.toMeasure ∧
        ∀ᵐ seed ∂law.toMeasure, EstimateMeasurable oracle (next seed)
  | .randomPoint law _ next =>
      AEMeasurable (fun point => runEstimate oracle (next point)) law ∧
        ∀ᵐ point ∂law, EstimateMeasurable oracle (next point)
  | .randomReal law _ next =>
      AEMeasurable (fun value => runEstimate oracle (next value)) law ∧
        ∀ᵐ value ∂law, EstimateMeasurable oracle (next value)

/-- A pointwise version used for compositional interpreter laws. -/
def MembershipOracleProgram.StronglyMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Prop
  | .pure _ => True
  | .query point next => StronglyMeasurable oracle (next (oracle point))
  | .randomNat _ next =>
      Measurable (fun seed => runEstimate oracle (next seed)) ∧
        ∀ seed, StronglyMeasurable oracle (next seed)
  | .randomPoint _ _ next =>
      Measurable (fun point => runEstimate oracle (next point)) ∧
        ∀ point, StronglyMeasurable oracle (next point)
  | .randomReal _ _ next =>
      Measurable (fun value => runEstimate oracle (next value)) ∧
        ∀ value, StronglyMeasurable oracle (next value)

theorem MembershipOracleProgram.StronglyMeasurable.estimateMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {oracle : AmbientSpace n → Bool} {program : MembershipOracleProgram n Result}
    (h : program.StronglyMeasurable oracle) :
    program.EstimateMeasurable oracle := by
  induction program with
  | pure => trivial
  | query point next ih => exact ih (oracle point) h
  | randomNat law next ih =>
      exact ⟨h.1.aemeasurable, Filter.Eventually.of_forall fun seed => ih seed (h.2 seed)⟩
  | randomPoint law hprob next ih =>
      exact ⟨h.1.aemeasurable, Filter.Eventually.of_forall fun point => ih point (h.2 point)⟩
  | randomReal law hprob next ih =>
      exact ⟨h.1.aemeasurable, Filter.Eventually.of_forall fun value => ih value (h.2 value)⟩

/-- Interpreting syntactic bind is Giry bind when both sides are measurable. -/
theorem MembershipOracleProgram.runEstimate_bind
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool) (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (hprogram : program.StronglyMeasurable oracle)
    (_hnext : ∀ result, (next result).StronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).runEstimate oracle) :
    (program.bind next).runEstimate oracle =
      (program.runEstimate oracle).bind fun result =>
        (next result).runEstimate oracle := by
  induction program with
  | pure result =>
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.runEstimate]
      rw [Measure.dirac_bind hnextRun]
  | query point branch ih =>
      exact ih (oracle point) hprogram
  | randomNat law branch ih =>
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.runEstimate]
      rw [show (fun seed => ((branch seed).bind next).runEstimate oracle) =
          (fun seed => ((branch seed).runEstimate oracle).bind fun result =>
            (next result).runEstimate oracle) by
        funext seed
        exact ih seed (hprogram.2 seed)]
      exact (Measure.bind_bind hprogram.1.aemeasurable hnextRun.aemeasurable).symm
  | randomPoint law hprob branch ih =>
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.runEstimate]
      rw [show (fun point => ((branch point).bind next).runEstimate oracle) =
          (fun point => ((branch point).runEstimate oracle).bind fun result =>
            (next result).runEstimate oracle) by
        funext point
        exact ih point (hprogram.2 point)]
      exact (Measure.bind_bind hprogram.1.aemeasurable hnextRun.aemeasurable).symm
  | randomReal law hprob branch ih =>
      simp only [MembershipOracleProgram.bind, MembershipOracleProgram.runEstimate]
      rw [show (fun value => ((branch value).bind next).runEstimate oracle) =
          (fun value => ((branch value).runEstimate oracle).bind fun result =>
            (next result).runEstimate oracle) by
        funext value
        exact ih value (hprogram.2 value)]
      exact (Measure.bind_bind hprogram.1.aemeasurable hnextRun.aemeasurable).symm

theorem MembershipOracleProgram.StronglyMeasurable.bind
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {oracle : AmbientSpace n → Bool} {program : MembershipOracleProgram n A}
    {next : A → MembershipOracleProgram n B}
    (hprogram : program.StronglyMeasurable oracle)
    (hnext : ∀ result, (next result).StronglyMeasurable oracle)
    (hnextRun : Measurable fun result => (next result).runEstimate oracle) :
    (program.bind next).StronglyMeasurable oracle := by
  induction program with
  | pure result =>
      simpa [MembershipOracleProgram.bind] using hnext result
  | query point branch ih =>
      exact ih (oracle point) hprogram
  | randomNat law branch ih =>
      constructor
      · rw [show (fun seed => ((branch seed).bind next).runEstimate oracle) =
            (fun seed => ((branch seed).runEstimate oracle).bind fun result =>
              (next result).runEstimate oracle) by
          funext seed
          exact MembershipOracleProgram.runEstimate_bind oracle (branch seed) next
            (hprogram.2 seed) hnext hnextRun]
        exact (Measure.measurable_bind' hnextRun).comp hprogram.1
      · exact fun seed => ih seed (hprogram.2 seed)
  | randomPoint law hprob branch ih =>
      constructor
      · rw [show (fun point => ((branch point).bind next).runEstimate oracle) =
            (fun point => ((branch point).runEstimate oracle).bind fun result =>
              (next result).runEstimate oracle) by
          funext point
          exact MembershipOracleProgram.runEstimate_bind oracle (branch point) next
            (hprogram.2 point) hnext hnextRun]
        exact (Measure.measurable_bind' hnextRun).comp hprogram.1
      · exact fun point => ih point (hprogram.2 point)
  | randomReal law hprob branch ih =>
      constructor
      · rw [show (fun value => ((branch value).bind next).runEstimate oracle) =
            (fun value => ((branch value).runEstimate oracle).bind fun result =>
              (next result).runEstimate oracle) by
          funext value
          exact MembershipOracleProgram.runEstimate_bind oracle (branch value) next
            (hprogram.2 value) hnext hnextRun]
        exact (Measure.measurable_bind' hnextRun).comp hprogram.1
      · exact fun value => ih value (hprogram.2 value)
theorem MembershipOracleProgram.runEstimate_isProbabilityMeasure
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) (program : MembershipOracleProgram n Result)
    (hmeas : program.EstimateMeasurable oracle) :
    IsProbabilityMeasure (program.runEstimate oracle) := by
  induction program with
  | pure result =>
      rw [MembershipOracleProgram.runEstimate]
      infer_instance
  | query point next ih =>
      change EstimateMeasurable oracle (next (oracle point)) at hmeas
      exact ih (oracle point) hmeas
  | randomNat law next ih =>
      simp only [EstimateMeasurable] at hmeas
      simp only [MembershipOracleProgram.runEstimate]
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with seed hseed
      exact ih seed hseed
  | randomPoint law hprob next ih =>
      simp only [EstimateMeasurable] at hmeas
      simp only [MembershipOracleProgram.runEstimate]
      let _ : IsProbabilityMeasure law := hprob
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with point hpoint
      exact ih point hpoint
  | randomReal law hprob next ih =>
      simp only [EstimateMeasurable] at hmeas
      simp only [MembershipOracleProgram.runEstimate]
      let _ : IsProbabilityMeasure law := hprob
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with value hvalue
      exact ih value hvalue

/-- A worst-case query bound may always be weakened. -/
theorem MembershipOracleProgram.QueryBound.mono
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {first second : ℕ} (hprogram : program.QueryBound first)
    (hle : first ≤ second) : program.QueryBound second := by
  induction hprogram generalizing second with
  | pure result budget => exact .pure result second
  | query point branch budget hbranch ih =>
      have hbudget : budget ≤ second - 1 := by omega
      have hsecond : second = (second - 1) + 1 := by omega
      rw [hsecond]
      exact .query point _ _ fun answer => ih answer hbudget
  | randomNat law branch budget hbranch ih =>
      exact .randomNat law _ _ fun seed => ih seed hle
  | randomPoint law hprob branch budget hbranch ih =>
      exact .randomPoint law hprob _ _ fun point => ih point hle
  | randomReal law hprob branch budget hbranch ih =>
      exact .randomReal law hprob _ _ fun value => ih value hle

/-- Sequential composition adds worst-case syntax-level query bounds. -/
theorem MembershipOracleProgram.QueryBound.bind
    {n : ℕ} {A B : Type}
    {program : MembershipOracleProgram n A}
    {next : A → MembershipOracleProgram n B} {first second : ℕ}
    (hprogram : program.QueryBound first)
    (hnext : ∀ result, (next result).QueryBound second) :
    (program.bind next).QueryBound (first + second) := by
  induction hprogram with
  | pure result budget =>
      simpa [MembershipOracleProgram.bind] using
        (hnext result).mono (Nat.le_add_left second budget)
  | query point branch count hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      rw [Nat.add_assoc, Nat.add_comm 1 second, ← Nat.add_assoc]
      exact .query point _ _ fun answer => ih answer
  | randomNat law branch count hbranch ih =>
      exact .randomNat law _ _ fun seed => ih seed
  | randomPoint law hprob branch count hbranch ih =>
      exact .randomPoint law hprob _ _ fun point => ih point
  | randomReal law hprob branch count hbranch ih =>
      exact .randomReal law hprob _ _ fun value => ih value

theorem repeatVolumeCooling_queryBound
    (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) {budget : ℕ}
    (hbase : (baseVolumeCooling P S q).QueryBound budget) :
    ∀ repetitions : ℕ,
      (repeatVolumeCooling P S q repetitions).QueryBound (repetitions * budget) := by
  intro repetitions
  induction repetitions with
  | zero => simpa [repeatVolumeCooling] using
      (MembershipOracleProgram.QueryBound.pure (Result := Fin 0 → ℝ) Fin.elim0 0)
  | succ repetitions ih =>
      rw [repeatVolumeCooling]
      have htail : ∀ estimate : ℝ,
          ((repeatVolumeCooling P S q repetitions).bind fun tail =>
            .pure (Fin.cons estimate tail : Fin (repetitions + 1) → ℝ)).QueryBound
              (repetitions * budget) := by
        intro estimate
        simpa using ih.bind (fun tail => MembershipOracleProgram.QueryBound.pure _ 0)
      have h := hbase.bind htail
      simpa [Nat.succ_mul, Nat.add_comm] using h

theorem volumeCoolingAlgorithm_queryBound
    (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) {budget : ℕ}
    (hbase : (baseVolumeCooling P S q).QueryBound budget) :
    (volumeCoolingAlgorithm P S q).QueryBound
      (confidenceRepetitions q * budget) := by
  unfold volumeCoolingAlgorithm
  simpa using (repeatVolumeCooling_queryBound P S q hbase (confidenceRepetitions q)).bind
    (fun estimates => MembershipOracleProgram.QueryBound.pure _ 0)

/-- Independent repetition of an arbitrary real-valued probability measure. -/
noncomputable def repeatEstimateMeasure (μ : Measure ℝ) :
    (repetitions : ℕ) → Measure (Fin repetitions → ℝ)
  | 0 => Measure.dirac Fin.elim0
  | repetitions + 1 =>
      μ.bind fun estimate =>
        (repeatEstimateMeasure μ repetitions).map fun tail => Fin.cons estimate tail

theorem measurable_finCons (repetitions : ℕ) :
    Measurable fun p : ℝ × (Fin repetitions → ℝ) =>
      (Fin.cons p.1 p.2 : Fin (repetitions + 1) → ℝ) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · change Measurable fun p : ℝ × (Fin repetitions → ℝ) => p.2 j
    fun_prop

theorem measurable_countInSet {m : ℕ} {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable fun v : Fin m → ℝ =>
      (Finset.univ.filter fun i => v i ∈ S).card := by
  classical
  have hsum : Measurable fun v : Fin m → ℝ =>
      ∑ i ∈ Finset.univ, if v i ∈ S then 1 else 0 := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact Measurable.ite ((measurable_pi_apply i) hS) measurable_const measurable_const
  simpa only [Finset.card_filter] using hsum

theorem measurable_medianOf (m : ℕ) :
    Measurable (Arlib.Probability.medianOf : (Fin m → ℝ) → ℝ) := by
  classical
  by_cases hm : 0 < m
  · unfold Arlib.Probability.medianOf
    simp only [dif_pos hm]
    apply measurable_of_Iic
    intro a
    let k : Fin m := ⟨m / 2, Nat.div_lt_self hm one_lt_two⟩
    have hpreimage :
        (fun v : Fin m → ℝ => v (Tuple.sort v k)) ⁻¹' Set.Iic a =
          {v | (k : ℕ) < (Finset.univ.filter fun i => v i ∈ Set.Iic a).card} := by
      ext v
      have hcard :
          (Finset.univ.filter fun i => (v ∘ Tuple.sort v) i ≤ a).card =
            (Finset.univ.filter fun i => v i ≤ a).card := by
        apply Finset.card_equiv (Tuple.sort v)
        intro i
        simp [Function.comp_apply]
      have hsorted := Tuple.lt_card_le_iff_apply_le_of_monotone
        (j := k) (a := a) (Tuple.monotone_sort v)
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
      rw [← hcard]
      simpa only [Function.comp_apply] using hsorted.symm
    rw [hpreimage]
    exact measurableSet_lt measurable_const
      (measurable_countInSet measurableSet_Iic)
  · have hm0 : m = 0 := by omega
    subst m
    unfold Arlib.Probability.medianOf
    simp only [lt_self_iff_false, ↓reduceDIte]
    exact measurable_const

theorem repeatEstimateMeasure_isProbabilityMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∀ repetitions : ℕ,
    IsProbabilityMeasure (repeatEstimateMeasure μ repetitions) := by
  intro repetitions
  induction repetitions with
  | zero =>
      rw [repeatEstimateMeasure]
      infer_instance
  | succ repetitions ih =>
      rw [repeatEstimateMeasure]
      apply MeasureTheory.isProbabilityMeasure_bind
        (measurable_measure_map_param (repeatEstimateMeasure μ repetitions)
          (measurable_finCons repetitions)).aemeasurable
      filter_upwards with estimate
      exact Measure.isProbabilityMeasure_map
        ((measurable_finCons repetitions).comp
          (measurable_const.prodMk measurable_id)).aemeasurable

theorem repeatVolumeCooling_semantics
    (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool)
    (hbase : (baseVolumeCooling P S q).StronglyMeasurable oracle) :
    ∀ repetitions : ℕ,
      (repeatVolumeCooling P S q repetitions).StronglyMeasurable oracle ∧
      (repeatVolumeCooling P S q repetitions).runEstimate oracle =
        repeatEstimateMeasure
          ((baseVolumeCooling P S q).runEstimate oracle) repetitions := by
  let _ : IsProbabilityMeasure ((baseVolumeCooling P S q).runEstimate oracle) :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle _
      hbase.estimateMeasurable
  intro repetitions
  induction repetitions with
  | zero =>
      constructor
      · trivial
      · rfl
  | succ repetitions ih =>
      let _ : IsProbabilityMeasure
          (repeatEstimateMeasure
            ((baseVolumeCooling P S q).runEstimate oracle) repetitions) :=
        repeatEstimateMeasure_isProbabilityMeasure _ repetitions
      let base := baseVolumeCooling P S q
      let tail := repeatVolumeCooling P S q repetitions
      have hpureStrong (estimate : ℝ) : ∀ tailValues : Fin repetitions → ℝ,
          (MembershipOracleProgram.pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).StronglyMeasurable
              oracle := fun _ => trivial
      have hpureRun (estimate : ℝ) : Measurable fun tailValues : Fin repetitions → ℝ =>
          (MembershipOracleProgram.pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle := by
        simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          ((measurable_finCons repetitions).comp
            ((measurable_const : Measurable fun _ : (Fin repetitions → ℝ) => estimate).prodMk
              measurable_id))
      have hinnerStrong (estimate : ℝ) :
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).StronglyMeasurable
              oracle := ih.1.bind (hpureStrong estimate) (hpureRun estimate)
      have hinnerLaw (estimate : ℝ) :
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle =
          (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
            fun tailValues =>
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ) := by
        rw [MembershipOracleProgram.runEstimate_bind oracle tail _ ih.1
          (hpureStrong estimate) (hpureRun estimate)]
        rw [ih.2]
        exact Measure.bind_dirac_eq_map _
          ((measurable_finCons repetitions).comp
            ((measurable_const : Measurable fun _ : (Fin repetitions → ℝ) => estimate).prodMk
              measurable_id))
      have hinnerRun : Measurable fun estimate : ℝ =>
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle := by
        rw [show (fun estimate =>
            (tail.bind fun tailValues => .pure
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle) =
            (fun estimate =>
              (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
                fun tailValues =>
                  (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)) by
          funext estimate
          exact hinnerLaw estimate]
        exact measurable_measure_map_param _ (measurable_finCons repetitions)
      rw [repeatVolumeCooling]
      constructor
      · exact hbase.bind hinnerStrong hinnerRun
      · rw [MembershipOracleProgram.runEstimate_bind oracle base _ hbase
          hinnerStrong hinnerRun]
        rw [show (fun estimate =>
            (tail.bind fun tailValues => .pure
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle) =
            (fun estimate =>
              (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
                fun tailValues =>
                  (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)) by
          funext estimate
          exact hinnerLaw estimate]
        rfl

theorem volumeCoolingAlgorithm_semantics
    (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool)
    (hbase : (baseVolumeCooling P S q).StronglyMeasurable oracle) :
    (volumeCoolingAlgorithm P S q).StronglyMeasurable oracle ∧
      (volumeCoolingAlgorithm P S q).runEstimate oracle =
        (repeatEstimateMeasure
          ((baseVolumeCooling P S q).runEstimate oracle)
          (confidenceRepetitions q)).map Arlib.Probability.medianOf := by
  have hrepeat := repeatVolumeCooling_semantics P S q oracle hbase
    (confidenceRepetitions q)
  have hpureStrong : ∀ estimates : Fin (confidenceRepetitions q) → ℝ,
      (MembershipOracleProgram.pure
        (Arlib.Probability.medianOf estimates)).StronglyMeasurable oracle :=
    fun _ => trivial
  have hpureRun : Measurable fun estimates : Fin (confidenceRepetitions q) → ℝ =>
      (MembershipOracleProgram.pure
        (Arlib.Probability.medianOf estimates)).runEstimate oracle := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp (measurable_medianOf _)
  unfold volumeCoolingAlgorithm
  constructor
  · exact hrepeat.1.bind hpureStrong hpureRun
  · rw [MembershipOracleProgram.runEstimate_bind oracle _ _ hrepeat.1
      hpureStrong hpureRun]
    rw [hrepeat.2]
    exact Measure.bind_dirac_eq_map _ (measurable_medianOf _)

/-- The estimate-accuracy event is a Borel interval. -/
theorem accurateOutcome_measurable (q : VolumeParams) (I : VolumeInput q.n) :
    MeasurableSet (accurateOutcome q I) := by
  unfold accurateOutcome RelativeApprox Arlib.relErr
  exact measurableSet_Icc

/-- On the measurable accuracy event, `outcomeProbability` is ordinary measure. -/
theorem outcomeProbability_eq_measure
    (μ : Measure ℝ) (q : VolumeParams) (I : VolumeInput q.n) :
    outcomeProbability μ (accurateOutcome q I) =
      (μ (accurateOutcome q I)).toReal := by
  unfold outcomeProbability
  rw [Measure.toOuterMeasure_apply μ]

end ArlibCommunity.Algorithms.CV18
