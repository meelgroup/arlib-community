/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Model.ProblemSetting
import ArlibCommunity.Algorithms.KV97.Model.Pseudocode
import ArlibCommunity.Algorithms.KV97.Analysis.TheoremProof

/-!
# Kannan–Vempala, *Sampling Lattice Points*, Theorem 2

Every lattice point of the polytope is returned with probability within a factor of
uniform: between `(1−ε)(1−e^{−c²/2})/V` and `(1+ε)/V`, where `V` is the normaliser of the
sampler on the inflated polytope.

Two deviations from the paper's statement, both explained in `Analysis/HitProbability.lean`:
the sampler's density is assumed close to uniform pointwise, not merely in total
variation; and the loss is `e^{−c²/2}`, not `2e^{−c²}`, because the paper's inflation
`κ = c + √(2 log r)` supports only the former.
-/

namespace ArlibCommunity.Algorithms.KV97

open MeasureTheory

/-- **Kannan–Vempala Theorem 2.**  Run the program with a sampler that is pointwise
`(1 ± ε)`-uniform on the inflated polytope.  Then every lattice point `x` of the polytope is
returned with probability in `[(1−ε)(1−e^{−c²/2})/V, (1+ε)/V]`. -/
theorem latticePoint_probability {n : ℕ} {ι : Type*} [Fintype ι] (p : Problem n ι)
    {sampler : Measure (State n)} {V ε : ℝ} (hV : 0 < V) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : AlmostUniformSampler sampler p.inflatedBody V ε)
    {x : LatticePoint n} (hx : toState x ∈ p.body) :
    (1 - ε) * (1 - Real.exp (-p.c ^ 2 / 2)) / V ≤ (output sampler {x}).toReal ∧
      (output sampler {x}).toReal ≤ (1 + ε) / V :=
  TheoremProof.latticePoint_probability p hV hε0 hε1 hs hx

end ArlibCommunity.Algorithms.KV97
