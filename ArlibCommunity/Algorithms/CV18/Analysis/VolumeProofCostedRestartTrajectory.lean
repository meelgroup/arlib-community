/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperStoppedTrajectory
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Finite independently restarted costed Markov executions

A costed step kernel returns both a nonnegative cost increment and the next state.  Restarting
that experiment independently at every Markov step is itself a Markov chain on
`ENNReal × state`; the first coordinate is the latest increment.  The full path retains all
increments, so a finite sum is an honest total-cost random variable.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- Generic transport of a finite Markov iterate through a measurable intertwining map. -/
theorem map_iterate_of_map_kernel_general {f : S → T} (hf : Measurable f)
    {Q : Kernel S S} {P : Kernel T T} [IsMarkovKernel Q] [IsMarkovKernel P]
    (h : ∀ x, Measure.map f (Q x) = P (f x)) (μ : Measure S) (t : ℕ) :
    Measure.map f (iterate Q μ t) = iterate P (Measure.map f μ) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterate_succ, iterate_succ, ← ih]
      ext A hA
      rw [Measure.map_apply hf hA, step_apply Q _ (hA.preimage hf), step_apply P _ hA,
        lintegral_map (Kernel.measurable_coe P hA) hf]
      refine lintegral_congr fun x => ?_
      rw [← Measure.map_apply hf hA, h x]

/-- Every coordinate marginal of `pathMeasure` is the corresponding finite iterate. -/
theorem map_eval_pathMeasure_eq_iterate (P : Kernel S S) [IsMarkovKernel P]
    (μ : Measure S) [IsProbabilityMeasure μ] (t : ℕ) :
    (pathMeasure P μ).map (fun ω => ω t) = iterate P μ t := by
  induction t with
  | zero => exact map_eval_pathMeasure_zero P μ
  | succ t ih =>
      rw [map_eval_pathMeasure_succ, ih, iterate_succ]
      rfl

/-- Forget the previous increment and run a fresh costed experiment from the current state. -/
noncomputable def restartedCostKernel (Q : Kernel S (ℝ≥0∞ × S)) :
    Kernel (ℝ≥0∞ × S) (ℝ≥0∞ × S) :=
  Kernel.comap Q Prod.snd measurable_snd

instance (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q] :
    IsMarkovKernel (restartedCostKernel Q) := by
  rw [restartedCostKernel]
  infer_instance

/-- Initial extended-state law, with zero cost and state law `μ`. -/
noncomputable def zeroCostLaw (μ : Measure S) : Measure (ℝ≥0∞ × S) :=
  μ.map (fun x => (0, x))

instance (μ : Measure S) [IsProbabilityMeasure μ] : IsProbabilityMeasure (zeroCostLaw μ) := by
  unfold zeroCostLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Infinite path law of independently restarted costed experiments.  Consumers use only a
finite prefix, indexed by their requested number of steps. -/
noncomputable def restartedCostExecution (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q]
    (μ : Measure S) : Measure (ℕ → ℝ≥0∞ × S) :=
  pathMeasure (restartedCostKernel Q) (zeroCostLaw μ)

/-- Total realized cost of the first `t` independently restarted steps. -/
noncomputable def restartedTotalCost (t : ℕ) (ω : ℕ → ℝ≥0∞ × S) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (ω (i + 1)).1

theorem measurable_restartedTotalCost (t : ℕ) :
    Measurable (restartedTotalCost (S := S) t) := by
  unfold restartedTotalCost
  fun_prop

/-- The state output after `t` costed restarts has exactly the `t`-step law of the state
kernel obtained by forgetting costs. -/
theorem map_restartedCostExecution_output
    (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q]
    (P : Kernel S S) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x)
    (μ : Measure S) [IsProbabilityMeasure μ] (t : ℕ) :
    (restartedCostExecution Q μ).map (fun ω => (ω t).2) = iterate P μ t := by
  let R := restartedCostKernel Q
  have hR : ∀ z : ℝ≥0∞ × S, Measure.map Prod.snd (R z) = P z.2 := by
    intro z
    exact hforget z.2
  have hzero : (zeroCostLaw μ).map Prod.snd = μ := by
    unfold zeroCostLaw
    rw [Measure.map_map (μ := μ) (f := fun x : S => (0, x)) (g := Prod.snd)
      measurable_snd (by fun_prop)]
    simp [Function.comp_def]
  rw [show (fun ω : ℕ → ℝ≥0∞ × S => (ω t).2) =
      Prod.snd ∘ (fun ω => ω t) from rfl,
    ← Measure.map_map (μ := restartedCostExecution Q μ)
      (f := fun ω : ℕ → ℝ≥0∞ × S => ω t) (g := Prod.snd)
      measurable_snd (measurable_pi_apply t),
    restartedCostExecution, map_eval_pathMeasure_eq_iterate,
    map_iterate_of_map_kernel_general measurable_snd hR, hzero]

/-- The expectation of the realized total cost is the sum of the expectations of the
increment coordinate at the successive extended-state marginals. -/
theorem lintegral_restartedTotalCost
    (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q]
    (μ : Measure S) [IsProbabilityMeasure μ] (t : ℕ) :
    ∫⁻ ω, restartedTotalCost t ω ∂(restartedCostExecution Q μ) =
      ∑ i ∈ Finset.range t,
        ∫⁻ z, z.1 ∂(iterate (restartedCostKernel Q) (zeroCostLaw μ) (i + 1)) := by
  simp only [restartedTotalCost]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← lintegral_map measurable_fst (measurable_pi_apply (i + 1)),
      restartedCostExecution, map_eval_pathMeasure_eq_iterate]
  · intro i hi
    exact measurable_fst.comp (measurable_pi_apply (i + 1))

/-- One increment marginal is the current-state average of the one-step cost mean. -/
theorem lintegral_increment_iterate_eq
    (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q]
    (P : Kernel S S) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x)
    (μ : Measure S) [IsProbabilityMeasure μ] (i : ℕ) :
    ∫⁻ z, z.1 ∂(iterate (restartedCostKernel Q) (zeroCostLaw μ) (i + 1)) =
      ∫⁻ x, (∫⁻ y, y.1 ∂Q x) ∂(iterate P μ i) := by
  let R := restartedCostKernel Q
  have hR : ∀ z : ℝ≥0∞ × S, Measure.map Prod.snd (R z) = P z.2 := by
    intro z
    exact hforget z.2
  have hzero : (zeroCostLaw μ).map Prod.snd = μ := by
    unfold zeroCostLaw
    rw [Measure.map_map (μ := μ) (f := fun x : S => (0, x)) (g := Prod.snd)
      measurable_snd (by fun_prop)]
    simp [Function.comp_def]
  have hmarg : Measure.map Prod.snd (iterate R (zeroCostLaw μ) i) = iterate P μ i := by
    rw [map_iterate_of_map_kernel_general measurable_snd hR, hzero]
  rw [iterate_succ]
  change ∫⁻ z, z.1 ∂(iterate R (zeroCostLaw μ) i).bind R = _
  rw [Measure.lintegral_bind (Kernel.measurable R).aemeasurable measurable_fst.aemeasurable]
  rw [← hmarg, lintegral_map]
  · rfl
  · exact Measurable.lintegral_kernel_prod_right (κ := Q) measurable_snd.fst
  · exact measurable_snd

/-- Final composition theorem: expected realized cost is exactly the sum of the per-state
one-step expected costs along the intended state-chain marginals. -/
theorem lintegral_restartedTotalCost_eq_sum_stateMeans
    (Q : Kernel S (ℝ≥0∞ × S)) [IsMarkovKernel Q]
    (P : Kernel S S) [IsMarkovKernel P]
    (hforget : ∀ x, Measure.map Prod.snd (Q x) = P x)
    (μ : Measure S) [IsProbabilityMeasure μ] (t : ℕ) :
    ∫⁻ ω, restartedTotalCost t ω ∂(restartedCostExecution Q μ) =
      ∑ i ∈ Finset.range t, ∫⁻ x, (∫⁻ y, y.1 ∂Q x) ∂(iterate P μ i) := by
  rw [lintegral_restartedTotalCost]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_increment_iterate_eq Q P hforget μ i

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.map_restartedCostExecution_output
#print axioms Arlib.MarkovChains.lintegral_restartedTotalCost_eq_sum_stateMeans
