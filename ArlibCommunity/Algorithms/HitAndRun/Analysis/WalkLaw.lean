/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeAlgorithm
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Kernel

/-!
# The sampler's law is the iterate of its step kernel

`stepKernel w member` is the law of one step of the sampler from each point, with fresh
random numbers (`Tape.step`).  The sampler's output law from a start drawn from `σ` is
that kernel iterated `w.steps` times from `σ` (`walkLaw_eq_iterate`): the random tape gives
each step fresh randomness (`Analysis/TapeLaw.lean`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)
open TapeProgram

variable {n : ℕ} {member : State n → Bool}

/-- **The step kernel of the sampler**: from `x`, the law of one step `Tape.step w x`. -/
noncomputable def stepKernel (w : WalkParams) (member : State n → Bool)
    (hm : Measurable member) : Kernel (State n) (State n) where
  toFun x := law member (Tape.step w x)
  measurable' := measurable_law member (Tape.step w) (Tape.step_meas hm w).fst

theorem stepKernel_apply (w : WalkParams) (hm : Measurable member) (x : State n) :
    stepKernel w member hm x = law member (Tape.step w x) := rfl

instance stepKernel_isMarkovKernel (w : WalkParams) (hm : Measurable member) :
    IsMarkovKernel (stepKernel w member hm) :=
  ⟨fun _ => isProbabilityMeasure_law member _
    ((Tape.step_meas hm w).fst.comp (measurable_const.prodMk measurable_id))⟩

/-- Stepping first and then iterating is iterating one step more. -/
theorem iterate_step_eq {Ω : Type*} [MeasurableSpace Ω] (P : Kernel Ω Ω) (μ : Measure Ω) :
    ∀ m : ℕ, iterate P (ArlibCommunity.Foundations.MarkovChainTheory.step P μ) m = iterate P μ (m + 1)
  | 0 => rfl
  | m + 1 => by
      change ArlibCommunity.Foundations.MarkovChainTheory.step P (iterate P (ArlibCommunity.Foundations.MarkovChainTheory.step P μ) m) = ArlibCommunity.Foundations.MarkovChainTheory.step P (iterate P μ (m + 1))
      rw [iterate_step_eq P μ m]

/-- The law of `m` steps from each point, averaged over `μ`, is the step kernel iterated
`m` times from `μ`. -/
theorem bind_law_walk (w : WalkParams) (hm : Measurable member) :
    ∀ (m : ℕ) (μ : Measure (State n)),
      μ.bind (fun x => law member (Tape.walk w m x)) = iterate (stepKernel w member hm) μ m
  | 0, μ => Measure.bind_dirac
  | m + 1, μ => by
      have hwalk := Tape.walk_meas hm w m
      have hlaw : ∀ x, law member (Tape.walk w (m + 1) x) =
          (stepKernel w member hm x).bind fun y => law member (Tape.walk w m y) := by
        intro x
        exact law_bind member (Tape.step w x) (Tape.walk w m)
          (Measurable.comp (Tape.step_meas hm w)
            (measurable_const.prodMk measurable_id : Measurable fun t : Tape n => (x, t)))
          hwalk.fst
      simp_rw [hlaw]
      rw [← Measure.bind_bind (stepKernel w member hm).measurable.aemeasurable
        (measurable_law member _ hwalk.fst).aemeasurable, bind_law_walk w hm m]
      exact iterate_step_eq _ μ m

/-- The final point of one execution is the result of the tape program `Tape.walk`. -/
theorem execution_val (w : WalkParams) (x₀ : State n) (t : Tape n) :
    (execution w member x₀ t).val = (exec member (Tape.walk w w.steps x₀) t).1 := by
  show ((Program.walk w w.steps x₀).run (Oracle.ofTape member t)).val.1 = _
  rw [← Tape.walk_interp, interp_run_val]

/-- **The sampler's law is the iterate of its step kernel.** -/
theorem walkLaw_eq_iterate (w : WalkParams) {p : Problem n} (oracle : MembershipOracle p)
    (hm : Measurable oracle.query) (σ : Measure (State n)) :
    walkLaw w oracle σ = iterate (stepKernel w oracle.query hm) σ w.steps := by
  have hwalk := Tape.walk_meas hm w w.steps
  unfold walkLaw
  simp_rw [execution_val]
  rw [← bind_law_walk w hm]
  congr 1
  funext x₀
  exact tapeLaw_map_exec _ _ (hwalk.fst.comp (measurable_const.prodMk measurable_id))

end ArlibCommunity.Algorithms.HitAndRun
