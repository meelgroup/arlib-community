/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Prelude
import ArlibCommunity.Algorithms.HitAndRun.Model.ProblemSetting
import ArlibCommunity.Algorithms.HitAndRun.Model.Operations
import ArlibCommunity.Algorithms.HitAndRun.Model.Program
import ArlibCommunity.Algorithms.HitAndRun.Model.Run
import ArlibCommunity.Algorithms.HitAndRun.Meta.ModelClosure
import ArlibCommunity.Algorithms.HitAndRun.Analysis.QueryCount
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Accuracy

/-!
# Hit-and-run mixes fast, with a membership oracle

> [Lov99] For a convex body `K` with `B ⊆ K` and diameter at most `D`, the lazy
> hit-and-run walk from an `M`-warm start is within total variation `ε` of the uniform
> distribution on `K` after `O(n² D² log(M/ε))` steps.

Stated about the **explicit** sampler: `walkLaw w oracle σ` is `Program.sampler w`
(`Model/Program.lean`) run on the random tape of `Model/Run.lean`, from a start drawn from
`σ`, on a convex body accessed only through a membership oracle.  The program never
mentions the body; it reads it only through the charged operations of
`Model/Operations.lean`.

Two claims:

* `hitAndRun_correct` — **accuracy**: with the parameters `walkParams n D M ε m`, after
  `m ≥ deadline n D M (ε/2)` steps from a warm start, the output law is within total
  variation `ε` of uniform on the body.  The walk's own mixing gives `ε/2`
  (`hitAndRun_mixes` at `ε/2`); the warm start's exceptional set and the capped chord
  sampling (**Deviation**, `Model/Program.lean`) give at most `ε/4` each.
* `hitAndRun_queries` — **query bound**, sure: on every tape and whatever answers
  membership, at most `steps · (2 · bisectionSteps + rejectionTries)` membership calls.

**Hypotheses** are the paper's, at `ε/2`: `n ≥ 21`, the body convex, closed, bounded,
containing a unit ball and of diameter at most `D`, `M ≥ 1`, `0 < ε ≤ 1`, and a start that
is `M`-warm outside a set of mass at most `ε/4`.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory
open Arlib.Computation
open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

/-- **Accuracy**: after `m ≥ deadline n D M (ε/2)` steps from an `M`-warm start, the
sampler's output law is within total variation `ε` of the uniform law on the body. -/
theorem hitAndRun_correct {n : ℕ} (hn : 21 ≤ n) (p : Problem n) (oracle : MembershipOracle p)
    {σ : Measure (State n)} [IsProbabilityMeasure σ]
    {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {S : Set (State n)} (hWarm : WarmStart p.body σ M (ε / 2) S)
    {m : ℕ} (hm : deadline n p.diameter M (ε / 2) ≤ (m : ℝ)) :
    TVLe (walkLaw (walkParams n p.diameter M ε m) oracle σ) (target p.body)
      (ENNReal.ofReal ε) :=
  hitAndRun_correct_proof hn p oracle hM hε0 hε1 hWarm hm

/-- **Query bound**: on every tape, and whatever answers membership, the sampler makes at
most `steps · (2 · bisectionSteps + rejectionTries)` membership calls. -/
theorem hitAndRun_queries {n : ℕ} (w : WalkParams) (member : State n → Bool)
    (x₀ : State n) (t : Tape n) :
    queryCount (Charged.cost (execution w member x₀ t)) ≤
      w.steps * (2 * w.bisectionSteps + w.rejectionTries) :=
  execution_queryCount_le w member x₀ t

end ArlibCommunity.Algorithms.HitAndRun

#modelClosureOfType ArlibCommunity.Algorithms.HitAndRun.hitAndRun_correct
#modelClosureOfType ArlibCommunity.Algorithms.HitAndRun.hitAndRun_queries
#print axioms ArlibCommunity.Algorithms.HitAndRun.hitAndRun_correct
#print axioms ArlibCommunity.Algorithms.HitAndRun.hitAndRun_queries
#surplusIn ArlibCommunity.Algorithms.HitAndRun.Model from
  ArlibCommunity.Algorithms.HitAndRun.hitAndRun_correct
  ArlibCommunity.Algorithms.HitAndRun.hitAndRun_queries
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.ask_ofTape
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.drawGaussian_ofTape
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.drawUnit_ofTape
