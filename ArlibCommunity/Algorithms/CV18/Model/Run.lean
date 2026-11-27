/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Program
import Mathlib.Probability.ProductMeasure

/-!
# Run: the law of the random tape, and the algorithm's output law

`Program.estimator q` takes its randomness as the argument `o : Oracle q.n`.  This file
says how that oracle is built when the algorithm runs on a body, and is noncomputable
throughout.

* `roundLaw n` — one round of the tape: a uniform point of the closed unit ball
  (`centeredBall n 1`), a standard Gaussian vector (`standardGaussian n`) and a uniform
  number in `[0, 1]` (`uniformUnit`), independent.
* `tapeLaw n` — the tape: independent rounds, one for every `i : ℕ` (Mathlib's
  `Measure.infinitePi`).
* `execution q member t` — **the algorithm on one tape**: `Program.estimator q` run on
  the oracle that answers membership by `member` and reads the tape `t`.  A charged
  computation: `Charged.val` is the estimate, and `Charged.cost` the tally of its
  operations.
* `estimate q I oracle` — **its output law** on the body `I`: the tape law pushed
  through the estimate of `execution q oracle.query`.

## Why this is the oracle model

Membership answers are the body's, exactly (`MembershipOracle.correct`).  Each draw
consumes one fresh round and the rounds are independent, so conditional on everything
the program has seen, each random number it reads is distributed as its law.  Rounds the
program never reads are drawn and ignored.  `Analysis/TapeLaw.lean` proves that the
output law of a program on this tape is the law of the same program with its random
numbers drawn one at a time.

The tape is infinite, so it never runs out and there is no length to choose.

## Correspondence

| paper | Lean |
|---|---|
| a uniform proposal in a ball (Figure 1) | `x + r • u`, `u` the round's unit-ball point |
| a point of `N(0, σ₀²I)` | `√σ₀² • g`, `g` the round's Gaussian vector |
| a Metropolis or rejection coin | the round's uniform number |
| independent randomness per draw | `tapeLaw` (independent rounds) |
| running the algorithm on `K` | `execution q oracle.query` on a tape drawn from `tapeLaw` |
| the output | `estimate q I oracle` |
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open ArlibCommunity.Algorithms.CV18.Model.Operations

/-- **One round of the tape**: a uniform point of the closed unit ball, a standard
Gaussian vector and a uniform number in `[0, 1]`, independent. -/
noncomputable def roundLaw (n : ℕ) : Measure (Round n) :=
  (centeredBall n 1).prod ((standardGaussian n).prod uniformUnit)

instance roundLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (roundLaw n) := by
  unfold roundLaw
  infer_instance

/-- **The tape law**: independent rounds, one for every `i : ℕ`. -/
noncomputable def tapeLaw (n : ℕ) : Measure (Tape n) :=
  Measure.infinitePi fun _ : ℕ => roundLaw n

/-- **The algorithm on one tape**: `Program.estimator q` on the oracle that answers
membership by `member` and reads the tape `t`.  `Charged.val` of the result is the
estimate, and `Charged.cost` the tally of its operations. -/
noncomputable def execution (q : VolumeParams) (member : AmbientSpace q.n → Bool)
    (t : Tape q.n) : Prog ℝ :=
  Program.estimator q (Oracle.ofTape member t)

/-- **The output law** of the algorithm on the body `I`: the tape law pushed through the
estimate. -/
noncomputable def estimate (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Measure ℝ :=
  (tapeLaw q.n).map fun t => (execution q oracle.query t).val

end ArlibCommunity.Algorithms.CV18
