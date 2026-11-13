/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceExists

/-!
# CV18 Theorem 1.1

This is the headline audit surface.  The statement below mentions only
objects defined under `Model/`: the input promise, oracle-program semantics,
success event, the concrete algorithm `cv18Program` (`Pseudocode.lean`),
and the exact parameter-only query rate.  Its proof is developed under
`Analysis/`.

The exact displayed rate retains all protected logarithmic factors.  Removing
them gives the paper's `O*(roundness * n^3 / eps^2)` notation; for a
well-rounded body with universal `roundness`, this is `O*(n^3 / eps^2)`.
The deterministic cooling schedule is part of the algorithm's definition and
is not a parameter of the public theorem statement.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- The explicit constant in front of the query rate. -/
noncomputable def volumeQueryConstant : ℝ := 9 * (64 * 10 ^ 30 + 1)

/-- Accuracy and worst-case membership-query guarantee for one uniform
volume algorithm at a specified model-level rate, with the explicit constant
`volumeQueryConstant`.  The membership cost is computed from the program by
`Arlib.Computation.Charged`, using the roster carrier's membership
operation. -/
def VolumeGuarantee (algorithm : VolumeAlgorithm)
    (rate : VolumeParams → ℝ) : Prop :=
  ∀ (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I), WellRounded q I →
      1 - q.p ≤ outcomeProbability
        (volumeAlgorithmLaw algorithm q I oracle) (accurateOutcome q I) ∧
      (algorithm q).MembershipCostBound
        (Nat.ceil (volumeQueryConstant * rate q))

/-- Cousins--Vempala 2018, Theorem 1.1, for the concrete membership-oracle
program `cv18Program`: it succeeds with probability at least `1-p`, with the
exact polylogarithmic refinement of the paper's `O*` query bound.

The program is fixed before the body and its membership oracle are
quantified, and its rate is a model-level function only of the public
parameters. -/
theorem cv18TheoremOneOne :
    VolumeGuarantee cv18Program volumeTheoremOneOneRate := by
  intro q I oracle hrounded
  obtain ⟨haccuracy, calls, hcalls, hle⟩ :=
    volumeTheorem_finalScheduled q I oracle hrounded
  have hconst : figureOneFinalScheduledQueryConstant = volumeQueryConstant := by
    norm_num [figureOneFinalScheduledQueryConstant,
      figureOneFinalScheduledExpectedCostConstant, volumeQueryConstant]
  rw [hconst] at hle
  refine ⟨haccuracy, fun oracle' choices => ?_⟩
  exact (hcalls.toMembershipCostBound oracle' choices).trans hle

#modelClosureOfType cv18TheoremOneOne
#print axioms cv18TheoremOneOne

end ArlibCommunity.Algorithms.CV18
