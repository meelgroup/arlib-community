/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Prelude
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunMixingUncond
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PolytopeHitAndRunExecution

/-!
# Hit-and-run pseudocode

One proposal draws a uniform direction on the unit sphere, then a uniform line
parameter on the chord cut out by the body, and moves to that point.  `step`
completes the proposal to a Markov kernel, `lazyStep` stays put with probability
`1/2`, and `run` iterates that lazy kernel.

For a finite-facet polytope, `finiteFacetStep` computes the two chord endpoints
by scanning the facets.  Its equality with the denotational kernel is proved in
`Analysis/PseudocodeProof.lean`.
-/

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory ProbabilityTheory

/-- The direction-then-chord proposal of one hit-and-run step.  Its measurable
completion is `step`. -/
noncomputable def proposal {n : ℕ} (K : Body n) : State n → Measure (State n) :=
  Arlib.MarkovChains.hitAndRunProposal K

/-- The completed hit-and-run Markov kernel. -/
noncomputable def step {n : ℕ} (K : Body n) : Kernel (State n) (State n) :=
  Arlib.MarkovChains.hitAndRun K

/-- The lazy walk used by the mixing theorem. -/
noncomputable def lazyStep {n : ℕ} (K : Body n) : Kernel (State n) (State n) :=
  Arlib.MarkovChains.lazy (step K)

/-- The target distribution: normalized Lebesgue measure on the body. -/
noncomputable def target {n : ℕ} (K : Body n) : Measure (State n) :=
  Arlib.uniformOn volume K

/-- The law after `m` lazy hit-and-run steps from `sigma`. -/
noncomputable def run {n : ℕ} (K : Body n) (sigma : Measure (State n))
    (m : ℕ) : Measure (State n) :=
  Arlib.MarkovChains.iterate (lazyStep K) sigma m

/-- An implementation-oriented kernel for a polytope `A i • x ≤ b i`, using a
finite scan to compute both chord endpoints. -/
noncomputable def finiteFacetStep {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → State n) (b : ι → ℝ) : Kernel (State n) (State n) :=
  Arlib.MarkovChains.PolytopeHitAndRunExecution.finiteFacetHitAndRun A b

end ArlibCommunity.Algorithms.HitAndRun
