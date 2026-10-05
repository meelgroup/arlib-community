/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Pseudocode

/-!
# Proofs that the pseudocode denotes hit-and-run

This file proves the semantic facts exposed beside the headline theorem: the
direction/chord formula, the Markov property, stationarity, and equivalence of
the finite-facet implementation.
-/

namespace ArlibCommunity.Algorithms.HitAndRun.PseudocodeProof

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem proposal_apply {n : ℕ} {K : Body n} (hK : MeasurableSet K)
    (u : State n) {A : Set (State n)} (hA : MeasurableSet A) :
    proposal K u A =
      ∫⁻ theta, Arlib.uniformOn (volume : Measure ℝ)
        (Arlib.MarkovChains.chordSet K u (theta : State n))
        {t : ℝ | u + t • (theta : State n) ∈ A}
        ∂(Arlib.MarkovChains.unifSphere n) := by
  simpa [proposal] using
    Arlib.MarkovChains.hitAndRunProposal_apply_uniformOn hK u hA

theorem step_isMarkovKernel {n : ℕ} (K : Body n) :
    IsMarkovKernel (step K) := by
  unfold step
  infer_instance

theorem target_invariant {n : ℕ} [NeZero n] {K : Body n} (hK : MeasurableSet K) :
    Kernel.Invariant (step K) (target K) := by
  simpa [step, target] using Arlib.MarkovChains.invariant_hitAndRun hK

theorem finiteFacetStep_eq_step {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → State n) (b : ι → ℝ)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) [NeZero n] :
    finiteFacetStep A b = step (Arlib.Polytope.body A b) := by
  simpa [finiteFacetStep, step] using
    Arlib.MarkovChains.PolytopeHitAndRunExecution.finiteFacetHitAndRun_eq_hitAndRun A b hK

end ArlibCommunity.Algorithms.HitAndRun.PseudocodeProof
