/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.ProblemSetting
import ArlibCommunity.Algorithms.HitAndRun.Model.Program
import Mathlib.Probability.ProductMeasure

/-!
# Run: the law of the random tape, and the sampler's output law

`Program.sampler w x₀` takes its randomness as the argument `o : Oracle n`.  This file
says how that oracle is built when the sampler runs on a body, and is noncomputable
throughout.

* `roundLaw n` — one round of the tape: a standard Gaussian vector and a uniform number in
  `[0, 1]`, independent.
* `tapeLaw n` — the tape: independent rounds, one for every `i : ℕ`.
* `execution w member x₀ t` — **the sampler on one tape**: `Program.sampler w x₀` run on
  the oracle that answers membership by `member` and reads the tape `t`.  `Charged.val`
  is the final point, `Charged.cost` the tally of its operations.
* `walkLaw w oracle σ` — **its output law** on the body of `oracle`, from a starting
  point drawn from `σ`: for each start, the tape law pushed through the final point,
  averaged over `σ`.

## Why this is the oracle model

Membership answers are the body's, exactly (`MembershipOracle.correct`).  Each draw
consumes one fresh round and the rounds are independent, so each random number the
program reads is distributed as its law, independently of everything it has seen.  The
starting point is an input of the program, as in the paper; the theorem averages over a
warm law of it.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory
open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

/-- **One round of the tape**: a standard Gaussian vector and a uniform number in
`[0, 1]`, independent. -/
noncomputable def roundLaw (n : ℕ) : Measure (Round n) :=
  (standardGaussian n).prod uniformUnit

instance roundLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (roundLaw n) := by
  unfold roundLaw
  infer_instance

/-- **The tape law**: independent rounds, one for every `i : ℕ`. -/
noncomputable def tapeLaw (n : ℕ) : Measure (Tape n) :=
  Measure.infinitePi fun _ : ℕ => roundLaw n

/-- **The sampler on one tape**: `Program.sampler w x₀` on the oracle that answers
membership by `member` and reads the tape `t`. -/
noncomputable def execution {n : ℕ} (w : WalkParams) (member : State n → Bool)
    (x₀ : State n) (t : Tape n) : Prog (State n) :=
  Program.sampler w x₀ (Oracle.ofTape member t)

/-- **The output law** of the sampler on the body of `oracle`, from a starting point drawn
from `σ`. -/
noncomputable def walkLaw {n : ℕ} (w : WalkParams) {p : Problem n}
    (oracle : MembershipOracle p) (σ : Measure (State n)) : Measure (State n) :=
  σ.bind fun x₀ => (tapeLaw n).map fun t => (execution w oracle.query x₀ t).val

end ArlibCommunity.Algorithms.HitAndRun
