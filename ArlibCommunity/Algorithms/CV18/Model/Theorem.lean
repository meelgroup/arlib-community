/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Prelude
import ArlibCommunity.Algorithms.CV18.Model.Operations
import ArlibCommunity.Algorithms.CV18.Model.Program
import ArlibCommunity.Algorithms.CV18.Model.Run
import ArlibCommunity.Algorithms.CV18.Meta.ModelClosure
import ArlibCommunity.Algorithms.CV18.Analysis.TapeBridge

/-!
# Theorem 1.1 of [CV18]

> For any convex body `K` in `ℝⁿ` given by a membership oracle, with `B ⊆ K` and
> `E_K ‖X‖² = O(n)`, and any `ε, p > 0`, the algorithm outputs `V` with
> `(1 - ε) vol(K) ≤ V ≤ (1 + ε) vol(K)` with probability at least `1 - p`, using
> `O*(n³)` membership queries.

Stated about the **explicit** algorithm: `execution q member t` is `Program.estimator q`
(`Model/Program.lean`) run on the oracle that answers membership by `member` and reads
the random tape `t` (`Model/Run.lean`).  The program never mentions the body; it reads it
only through the charged operations of `Model/Operations.lean`.  Proving the claim for
this one algorithm is stronger than "there is an algorithm".

Two claims, split as the paper splits them:

* `cv18_correct` — **accuracy**, the only claim that can fail: under the output law
  `estimate q I oracle`, `Pr[V ∈ (1 ± ε) vol(K)] ≥ 1 - p`.
* `cv18_queries` — **query bound**, sure: on *every* tape, and whatever answers
  membership, `queryCount (Charged.cost (execution q member t)) ≤ ⌈queryRate q⌉`.
  `queryCount` counts every membership call once and random draws zero.  The rate keeps
  every logarithmic factor; dropping them gives the paper's `O*(roundness · n³ / ε²)`,
  which is `O*(n³ / ε²)` for constant `roundness`.

`cv18TheoremOneOne` is the conjunction.

**Hypotheses** are the paper's: the parameters `q` (`n ≥ 3`, `ε, p ∈ (0, 1)`), a convex
body `I` containing the unit ball, a correct membership oracle, and well-roundedness.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18

open Arlib.Computation
open ArlibCommunity.Algorithms.CV18.Model.Operations

/-- **Accuracy** (Theorem 1.1): on a well-rounded body with a correct membership oracle,
with probability at least `1 - p` over the random tape, the estimate is within a factor
`1 ± ε` of the volume. -/
theorem cv18_correct (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I) :
    1 - q.p ≤ outcomeProbability (estimate q I oracle) (accurateOutcome q I) := by
  rw [estimate_eq]
  exact (cv18Program_volumeGuarantee q I oracle hrounded).1

/-- **Query bound** (Theorem 1.1): every execution, on every tape and whatever answers
membership, makes at most `⌈queryRate q⌉` membership calls. -/
theorem cv18_queries (q : VolumeParams) (member : AmbientSpace q.n → Bool) (t : Tape q.n) :
    queryCount (Charged.cost (execution q member t)) ≤ Nat.ceil (queryRate q) :=
  execution_queryCount_le q member t

/-- **Cousins–Vempala 2018, Theorem 1.1**, for the explicit algorithm `Program.estimator`:
for every admissible parameter choice and every well-rounded body with a correct
membership oracle, (1) the estimate is within `1 ± ε` of the volume with probability at
least `1 - p`; (2) every execution makes at most `⌈queryRate q⌉` membership calls. -/
theorem cv18TheoremOneOne :
    ∀ (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I),
      WellRounded q I →
        1 - q.p ≤ outcomeProbability (estimate q I oracle) (accurateOutcome q I) ∧
        ∀ t : Tape q.n,
          queryCount (Charged.cost (execution q oracle.query t)) ≤ Nat.ceil (queryRate q) :=
  fun q I oracle hrounded =>
    ⟨cv18_correct q I oracle hrounded, cv18_queries q oracle.query⟩

end ArlibCommunity.Algorithms.CV18

#modelClosureOfType ArlibCommunity.Algorithms.CV18.cv18TheoremOneOne
#print axioms ArlibCommunity.Algorithms.CV18.cv18TheoremOneOne
-- The `*_ofTape` lemmas are the analysis's only view of the sealed oracle: they unfold
-- the private fields, so they must live in `Operations.lean` beside them.
#surplusIn ArlibCommunity.Algorithms.CV18.Model from ArlibCommunity.Algorithms.CV18.cv18TheoremOneOne
  ArlibCommunity.Algorithms.CV18.cv18_correct ArlibCommunity.Algorithms.CV18.cv18_queries
  ArlibCommunity.Algorithms.CV18.Model.Operations.ask_ofTape
  ArlibCommunity.Algorithms.CV18.Model.Operations.drawBall_ofTape
  ArlibCommunity.Algorithms.CV18.Model.Operations.drawGaussian_ofTape
  ArlibCommunity.Algorithms.CV18.Model.Operations.drawUnit_ofTape
