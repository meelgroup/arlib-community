/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import ArlibCommunity.Algorithms.CV18.Analysis.PseudocodeBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceExists

/-!
# CV18 Theorem 1.1

The statement mentions only objects defined under `Model/`: the input promise
and parameters (`Prelude.lean`), the program `cv18Program` and its cost model
`queryCost` (`Pseudocode.lean`), and the explicit query rate
`queryRate`, constant included (`Prelude.lean`).  The proof is developed under `Analysis/`.

The rate keeps every logarithmic factor.  Dropping them gives the paper's
`O*(roundness · n³ / ε²)`; for a well-rounded body with constant `roundness`
this is `O*(n³ / ε²)`.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- What Theorem 1.1 asserts about a volume algorithm, at query rate `rate`:
for every admissible parameter choice and every well-rounded body with a
correct membership oracle,

* **accuracy**: the estimate is within `1 ± ε` of the volume with probability
  at least `1 - p`, and
* **cost**: every execution makes at most `⌈rate q⌉` membership calls. -/
def VolumeGuarantee (algorithm : VolumeAlgorithm)
    (rate : VolumeParams → ℝ) : Prop :=
  ∀ (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I), WellRounded q I →
      1 - q.p ≤ outcomeProbability
        (volumeAlgorithmLaw algorithm q I oracle) (accurateOutcome q I) ∧
      (algorithm q).queryCost ≤ Nat.ceil (rate q)

/-- **Cousins–Vempala 2018, Theorem 1.1**, for the program `cv18Program`. -/
theorem cv18TheoremOneOne :
    VolumeGuarantee cv18Program queryRate := by
  intro q I oracle hrounded
  rw [cv18Program_eq]
  obtain ⟨haccuracy, calls, hcalls, hle⟩ :=
    volumeTheorem_finalScheduled q I oracle hrounded
  have hconst : figureOneFinalScheduledQueryConstant = queryConstant := by
    norm_num [figureOneFinalScheduledQueryConstant,
      runCostConstant, queryConstant]
  rw [hconst, ← mul_assoc] at hle
  exact ⟨haccuracy, hcalls.queryCost_le.trans (by exact_mod_cast hle)⟩

#modelClosureOfType cv18TheoremOneOne
#print axioms cv18TheoremOneOne

end ArlibCommunity.Algorithms.CV18
