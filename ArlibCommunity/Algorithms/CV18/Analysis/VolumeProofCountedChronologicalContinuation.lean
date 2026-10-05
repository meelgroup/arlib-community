/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedMarginalCompletion
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectSemantics

/-! # Marginal and cost laws for chronological counted continuations -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Query-free return is a right identity for the oracle-program syntax. -/
theorem MembershipOracleProgram.bind_pure_right_cv18
    {n : ℕ} {A : Type} (program : MembershipOracleProgram n A) :
    program.bind MembershipOracleProgram.pure = program := by
  induction program with
  | pure value => rfl
  | query point branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext answer
      exact ih answer
  | randomNat law branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext seed
      exact ih seed
  | randomPoint law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext point
      exact ih point
  | randomReal law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext value
      exact ih value

/-- Associativity of oracle-program bind, available to the counted
chronological assembly without importing later estimator modules. -/
theorem MembershipOracleProgram.bind_assoc_counted_cv18
    {n : ℕ} {A B C : Type}
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (last : B → MembershipOracleProgram n C) :
    (program.bind next).bind last =
      program.bind (fun value => (next value).bind last) := by
  induction program with
  | pure value => rfl
  | query point branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext answer
      exact ih answer
  | randomNat law branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext seed
      exact ih seed
  | randomPoint law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext point
      exact ih point
  | randomReal law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext value
      exact ih value

/-- Forgetting the accumulated count after a counted continuation gives the
ordinary estimate kernel, independently of the incoming count. -/
theorem MembershipOracleProgram.countedContinuation_fst
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (next : A → MembershipOracleProgram n B)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (first : A × ℕ) :
    (countedContinuation oracle next first).fst =
      (next first.1).runEstimate oracle := by
  unfold Measure.fst countedContinuation
  rw [Measure.map_map measurable_fst (by fun_prop)]
  rw [(next first.1).runEstimate_eq_map_fst_run oracle
    (hnext first.1).executionMeasurable]
  congr 1

/-- The endpoint marginal of applying a counted continuation depends only on
the endpoint marginal of the incoming counted law. -/
theorem MembershipOracleProgram.fst_bind_countedContinuation
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ))
    (next : A → MembershipOracleProgram n B)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle) :
    (rho.bind (countedContinuation oracle next)).fst =
      rho.fst.bind fun result => (next result).runEstimate oracle := by
  have hcont : Measurable (countedContinuation oracle next) :=
    measurable_countedContinuation oracle next hnextRun hnext
  have hestimate : Measurable fun result => (next result).runEstimate oracle := by
    rw [show (fun result => (next result).runEstimate oracle) =
        fun result => ((next result).run oracle).map Prod.fst by
      funext result
      exact (next result).runEstimate_eq_map_fst_run oracle
        (hnext result).executionMeasurable]
    exact (Measure.measurable_map _ measurable_fst).comp hnextRun
  unfold Measure.fst
  rw [map_bind_eq_bind_map_of_measurable rho hcont measurable_fst]
  rw [Measure.map_bind_eq_bind_comp rho measurable_fst hestimate]
  apply Measure.bind_congr_right
  filter_upwards with first
  exact MembershipOracleProgram.countedContinuation_fst oracle next hnext first

/-- Exact expected-count law for applying a counted continuation to an
arbitrary incoming joint law.  This is the measure-level counterpart of
`countedQueryCost_bind_eq_add`; it applies to the artificial reference laws
used by chronological completion. -/
theorem MembershipOracleProgram.countedQueryCost_bind_countedContinuation
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ))
    (next : A → MembershipOracleProgram n B)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle) :
    countedQueryCost (rho.bind (countedContinuation oracle next)) =
      countedQueryCost rho +
        ∫⁻ result, countedQueryCost ((next result).run oracle) ∂rho.fst := by
  have hcont : Measurable (countedContinuation oracle next) :=
    measurable_countedContinuation oracle next hnextRun hnext
  have hphaseCost : Measurable fun result =>
      countedQueryCost ((next result).run oracle) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hnextRun
  unfold countedQueryCost
  rw [Measure.lintegral_bind hcont.aemeasurable
    measurable_countedQueryCost_integrand.aemeasurable]
  have hpoint : (∫⁻ first, ∫⁻ outcome, (outcome.2 : ENNReal)
        ∂countedContinuation oracle next first ∂rho) =
      ∫⁻ first, (first.2 : ENNReal) +
        countedQueryCost ((next first.1).run oracle) ∂rho := by
    apply lintegral_congr
    intro first
    exact lintegral_countedContinuation_queryCount oracle next hnext first
  rw [hpoint, lintegral_add_left measurable_countedQueryCost_integrand]
  congr 1
  unfold Measure.fst
  rw [lintegral_map]
  · rfl
  · exact hphaseCost
  · fun_prop

/-- A phase endpoint approximation and an ideal-marginal phase cost bound
give precisely the uniform reference-prefix premise required by
`exists_countedReference_iteratedKernelLaw`. -/
theorem MembershipOracleProgram.countedContinuation_step
    {n : ℕ} {A : Type} [MeasurableSpace A]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ)) (ideal nextIdeal : Measure A)
    (program : A → MembershipOracleProgram n A)
    (hprogramRun : Measurable fun result => (program result).run oracle)
    (hprogram : ∀ result, (program result).CountedStronglyMeasurable oracle)
    {delta phaseCost : ENNReal} (hmarginal : rho.fst = ideal)
    (hendpoint : MeasureLeUpTo
      (ideal.bind fun state => (program state).runEstimate oracle)
      nextIdeal delta)
    (hcost : (∫⁻ state, countedQueryCost ((program state).run oracle) ∂ideal) ≤
      phaseCost) :
    MeasureLeUpTo
        ((rho.bind (countedContinuation oracle program)).fst)
        nextIdeal delta ∧
      countedQueryCost (rho.bind (countedContinuation oracle program)) ≤
        countedQueryCost rho + phaseCost := by
  constructor
  · rw [MembershipOracleProgram.fst_bind_countedContinuation oracle rho
      program hprogramRun hprogram, hmarginal]
    exact hendpoint
  · rw [MembershipOracleProgram.countedQueryCost_bind_countedContinuation
      oracle rho program hprogramRun hprogram, hmarginal]
    gcongr

/-- A measurable query-free output map preserves the full counted execution
law up to applying the same map to the result coordinate. -/
theorem MembershipOracleProgram.run_bind_pure_eq_map
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (f : A → B) (hf : Measurable f)
    (hprogram : program.CountedStronglyMeasurable oracle) :
    (program.bind fun result => .pure (f result)).run oracle =
      (program.run oracle).map fun outcome => (f outcome.1, outcome.2) := by
  let next : A → MembershipOracleProgram n B := fun result => .pure (f result)
  have hnext : ∀ result, (next result).CountedStronglyMeasurable oracle := by
    intro result
    trivial
  have hnextRun : Measurable fun result => (next result).run oracle := by
    simp only [next, MembershipOracleProgram.run]
    exact Measure.measurable_dirac.comp (hf.prodMk measurable_const)
  rw [MembershipOracleProgram.run_bind_counted oracle program next
    hprogram hnext hnextRun]
  unfold countedContinuation next
  simp only [MembershipOracleProgram.run]
  have hkernel : (fun first : A × ℕ =>
      (Measure.dirac (f first.1, 0)).map fun second : B × ℕ =>
        (second.1, first.2 + second.2)) =
      fun first => Measure.dirac (f first.1, first.2) := by
    funext first
    rw [Measure.map_dirac']
    · simp
    · fun_prop
  rw [hkernel]
  rw [Measure.bind_dirac_eq_map]
  exact hf.comp measurable_fst |>.prodMk measurable_snd

/-- In particular, query-free postprocessing leaves the entire distribution
of the interpreter-counted query total unchanged. -/
theorem MembershipOracleProgram.map_snd_run_bind_pure
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n A)
    (f : A → B) (hf : Measurable f)
    (hprogram : program.CountedStronglyMeasurable oracle) :
    ((program.bind fun result => .pure (f result)).run oracle).map Prod.snd =
      (program.run oracle).map Prod.snd := by
  rw [MembershipOracleProgram.run_bind_pure_eq_map oracle program f hf hprogram]
  rw [Measure.map_map (μ := program.run oracle)
    (f := fun outcome : A × ℕ => (f outcome.1, outcome.2))
    (g := Prod.snd) measurable_snd
      ((hf.comp measurable_fst).prodMk measurable_snd)]
  congr 1

/-- Counted-law simulation is compositional through dependent continuations.
Both the intermediate and final result maps preserve the accumulated query
coordinate. -/
theorem MembershipOracleProgram.map_bind_countedContinuation_simulation
    {n : ℕ} {A B C D : Type}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (oracle : AmbientSpace n → Bool) (rho : Measure (A × ℕ))
    (f : A → B) (hf : Measurable f) (g : C → D) (hg : Measurable g)
    (actualNext : A → MembershipOracleProgram n C)
    (mappedNext : B → MembershipOracleProgram n D)
    (hactualRun : Measurable fun result => (actualNext result).run oracle)
    (hactual : ∀ result, (actualNext result).CountedStronglyMeasurable oracle)
    (hmappedRun : Measurable fun result => (mappedNext result).run oracle)
    (hmapped : ∀ result, (mappedNext result).CountedStronglyMeasurable oracle)
    (hsim : ∀ result,
      (mappedNext (f result)).run oracle =
        ((actualNext result).run oracle).map fun outcome =>
          (g outcome.1, outcome.2)) :
    ((rho.map fun outcome => (f outcome.1, outcome.2)).bind
        (countedContinuation oracle mappedNext)) =
      (rho.bind (countedContinuation oracle actualNext)).map fun outcome =>
        (g outcome.1, outcome.2) := by
  let liftF : A × ℕ → B × ℕ := fun outcome =>
    (f outcome.1, outcome.2)
  let liftG : C × ℕ → D × ℕ := fun outcome =>
    (g outcome.1, outcome.2)
  have hliftF : Measurable liftF :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hliftG : Measurable liftG :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hactualCont : Measurable (countedContinuation oracle actualNext) :=
    measurable_countedContinuation oracle actualNext hactualRun hactual
  have hmappedCont : Measurable (countedContinuation oracle mappedNext) :=
    measurable_countedContinuation oracle mappedNext hmappedRun hmapped
  rw [show (fun outcome : A × ℕ => (f outcome.1, outcome.2)) = liftF by rfl]
  rw [show (fun outcome : C × ℕ => (g outcome.1, outcome.2)) = liftG by rfl]
  rw [Measure.map_bind_eq_bind_comp rho hliftF hmappedCont]
  rw [map_bind_eq_bind_map_of_measurable rho hactualCont hliftG]
  apply Measure.bind_congr_right
  filter_upwards with first
  unfold countedContinuation liftF liftG
  rw [hsim first.1, Measure.map_map, Measure.map_map]
  · congr 1
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

/-- A result-map simulation can be weakened to equality of the final query
count distribution.  This form also composes when the two continuations have
different result types and agree only after forgetting those results. -/
theorem MembershipOracleProgram.map_snd_bind_countedContinuation_eq
    {n : ℕ} {A B C D : Type}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (oracle : AmbientSpace n → Bool) (rho : Measure (A × ℕ))
    (f : A → B) (hf : Measurable f)
    (actualNext : A → MembershipOracleProgram n C)
    (mappedNext : B → MembershipOracleProgram n D)
    (hactualRun : Measurable fun result => (actualNext result).run oracle)
    (hactual : ∀ result, (actualNext result).CountedStronglyMeasurable oracle)
    (hmappedRun : Measurable fun result => (mappedNext result).run oracle)
    (hmapped : ∀ result, (mappedNext result).CountedStronglyMeasurable oracle)
    (hsim : ∀ result,
      ((mappedNext (f result)).run oracle).map Prod.snd =
        ((actualNext result).run oracle).map Prod.snd) :
    (((rho.map fun outcome => (f outcome.1, outcome.2)).bind
        (countedContinuation oracle mappedNext)).map Prod.snd) =
      (rho.bind (countedContinuation oracle actualNext)).map Prod.snd := by
  let liftF : A × ℕ → B × ℕ := fun outcome =>
    (f outcome.1, outcome.2)
  have hliftF : Measurable liftF :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hactualCont : Measurable (countedContinuation oracle actualNext) :=
    measurable_countedContinuation oracle actualNext hactualRun hactual
  have hmappedCont : Measurable (countedContinuation oracle mappedNext) :=
    measurable_countedContinuation oracle mappedNext hmappedRun hmapped
  have hactualCount : Measurable fun first =>
      (countedContinuation oracle actualNext first).map Prod.snd :=
    (Measure.measurable_map _ measurable_snd).comp hactualCont
  have hmappedCount : Measurable fun first =>
      (countedContinuation oracle mappedNext first).map Prod.snd :=
    (Measure.measurable_map _ measurable_snd).comp hmappedCont
  rw [show (fun outcome : A × ℕ => (f outcome.1, outcome.2)) = liftF by rfl]
  rw [map_bind_eq_bind_map_of_measurable (rho.map liftF) hmappedCont
    measurable_snd]
  rw [Measure.map_bind_eq_bind_comp rho hliftF hmappedCount]
  rw [map_bind_eq_bind_map_of_measurable rho hactualCont measurable_snd]
  apply Measure.bind_congr_right
  filter_upwards with first
  unfold countedContinuation liftF
  rw [Measure.map_map, Measure.map_map]
  · let addCount : ℕ → ℕ := fun count => first.2 + count
    calc
      ((mappedNext (f first.1)).run oracle).map
          (fun second => first.2 + second.2) =
          (((mappedNext (f first.1)).run oracle).map Prod.snd).map
            addCount := by
        rw [Measure.map_map]
        · congr 1
        · fun_prop
        · exact measurable_snd
      _ = (((actualNext first.1).run oracle).map Prod.snd).map
            addCount := by rw [hsim first.1]
      _ = ((actualNext first.1).run oracle).map
          (fun second => first.2 + second.2) := by
        rw [Measure.map_map]
        · congr 1
        · fun_prop
        · exact measurable_snd
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

#print axioms MembershipOracleProgram.countedContinuation_fst
#print axioms MembershipOracleProgram.bind_pure_right_cv18
#print axioms MembershipOracleProgram.bind_assoc_counted_cv18
#print axioms MembershipOracleProgram.fst_bind_countedContinuation
#print axioms MembershipOracleProgram.countedQueryCost_bind_countedContinuation
#print axioms MembershipOracleProgram.countedContinuation_step
#print axioms MembershipOracleProgram.run_bind_pure_eq_map
#print axioms MembershipOracleProgram.map_snd_run_bind_pure
#print axioms
  MembershipOracleProgram.map_bind_countedContinuation_simulation
#print axioms
  MembershipOracleProgram.map_snd_bind_countedContinuation_eq

end ArlibCommunity.Algorithms.CV18
