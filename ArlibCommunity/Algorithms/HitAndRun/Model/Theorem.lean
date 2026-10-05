/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.ProblemSetting
import ArlibCommunity.Algorithms.HitAndRun.Model.Pseudocode
import ArlibCommunity.Algorithms.HitAndRun.Analysis.PseudocodeProof
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TheoremProof

/-!
# Hit-and-run: audited statements

The first three statements pin the formal kernel to the paper's pseudocode and
to a finite-facet implementation.  The last is the fully discharged mixing
theorem.

The paper [Lov99] prints a substantially smaller coefficient.  Its proof of
Lemma 8 uses incompatible cap-volume and chord-length constants, so this file
does not assert that unsupported numeral.  The proved replacement keeps the
same `n² D² log(M/ε²)` dependence with explicit coefficient `2^64`.
-/

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A proposal is exactly a uniform sphere direction followed by a uniform
point on the resulting chord. -/
theorem proposal_apply {n : ℕ} {K : Body n} (hK : MeasurableSet K)
    (u : State n) {A : Set (State n)} (hA : MeasurableSet A) :
    proposal K u A =
      ∫⁻ theta, Arlib.uniformOn (volume : Measure ℝ)
        (Arlib.MarkovChains.chordSet K u (theta : State n))
        {t : ℝ | u + t • (theta : State n) ∈ A}
        ∂(Arlib.MarkovChains.unifSphere n) :=
  PseudocodeProof.proposal_apply hK u hA

/-- The uniform distribution on the body is stationary. -/
theorem target_invariant {n : ℕ} [NeZero n] {K : Body n} (hK : MeasurableSet K) :
    Kernel.Invariant (step K) (target K) :=
  PseudocodeProof.target_invariant hK

/-- Scanning a bounded polytope's facets computes exactly the same kernel as
the denotational direction/chord definition. -/
theorem finiteFacetStep_eq_step {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → State n) (b : ι → ℝ)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) [NeZero n] :
    finiteFacetStep A b = step (Arlib.Polytope.body A b) :=
  PseudocodeProof.finiteFacetStep_eq_step A b hK

/-- The unconditional corrected hit-and-run mixing theorem.

For `n ≥ 21`, after at least `deadline n D M eps` lazy steps on a rounded
convex body of diameter at most `D`, an `(M,S)`-warm probability law is within
`eps` total variation of uniform measure.  There are no assumed overlap,
isoperimetry, conductance, or mixing lemmas among the binders. -/
theorem hitAndRun_mixes {n : ℕ} (hn : 21 ≤ n) (p : Problem n)
    {sigma : Measure (State n)} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (State n)} (hWarm : WarmStart p.body sigma M eps S)
    {m : ℕ} (hm : deadline n p.diameter M eps ≤ (m : ℝ)) :
    Arlib.TVLe (run p.body sigma m) (target p.body) (ENNReal.ofReal eps) :=
  TheoremProof.hitAndRun_mixes hn p hM heps0 heps1 hWarm hm

end ArlibCommunity.Algorithms.HitAndRun
