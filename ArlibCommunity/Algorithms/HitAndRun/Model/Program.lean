/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Operations
import ArlibCommunity.Algorithms.HitAndRun.Meta.CostSeal
import ArlibCommunity.Algorithms.HitAndRun.Meta.ModelClosure

/-!
# Program: the lazy hit-and-run walk, with a membership oracle

The transcription of the algorithm: `m` steps of lazy hit-and-run [Lov99] from a starting
point `x₀`, on a convex body given only by a membership oracle.

## Shape

Every procedure is a computation in the monad `M n`, which threads the sealed oracle
`o : Oracle n` of `Model/Operations.lean`.  It reads the oracle only through `isMember`,
`gaussianVector` and `unitNumber`, which call the charged operations `ask`,
`drawGaussian` and `drawUnit`: one `query` per membership call, one `draw` per random
number.  Arithmetic is on real numbers and free.  The algorithm never mentions the body.

## One step

From the current point `x`:

```
coin ← uniform in [0, 1];  if coin ≤ 1/2, stay at x                   (laziness)
g ← standard Gaussian vector;  θ ← g / ‖g‖                            (direction)
on each side of x along θ, bisect k times between 0 and 2D            (bracket)
    to an outer distance: x + outer · θ is not in the body
try at most r times: t uniform on the bracket [-lo, hi],              (chord point)
    move to x + t · θ if it is in the body
if no try succeeds, stay at x
```

This is the implementation of [Vem05, §2] and [Rud13, §3.4]: bracket the chord by
bisection, then sample the bracket by rejection.  A point of the body at distance `2D`
from `x` would contradict the diameter bound, so `x ± 2D·θ` is outside and each side's
bisection starts with a valid bracket.  An accepted point is exactly uniform on the chord.

## Where the program differs from the paper

**Deviation: capped chord sampling.**  The literature runs the bisection to a precision
and the rejection loop until it succeeds, so its number of membership calls is random
and unbounded.  Here both are capped (`bisectionSteps`, `rejectionTries`), and a step whose
tries all miss stays put.  Every execution then makes at most
`steps · (2 · bisectionSteps + rejectionTries)` membership calls; the price is a small
probability that a step gives up, which `walkParams` makes at most `ε/4`.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.HitAndRun.Program

open ArlibCommunity.Algorithms.HitAndRun
open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

/-! ## The monad and its primitives -/

/-- **The program's monad**: a computation threads the sealed oracle.  Its charged
operations are tallied by `Prog`. -/
abbrev M (n : ℕ) := StateT (Oracle n) Prog

/-- **One membership call**: is `x` in the body?  One `query`. -/
def isMember {n : ℕ} (x : State n) : M n Bool := do
  let o ← get
  let (answer, o) ← (ask x o : Prog _)
  set o
  pure answer

/-- **A standard Gaussian vector.**  One `draw`. -/
def gaussianVector {n : ℕ} : M n (State n) := do
  let o ← get
  let (g, o) ← (drawGaussian o : Prog _)
  set o
  pure g

/-- **A uniform number in `[0, 1]`.**  One `draw`. -/
def unitNumber {n : ℕ} : M n ℝ := do
  let o ← get
  let (v, o) ← (drawUnit o : Prog _)
  set o
  pure v

/-! ## One step -/

/-- **Bisection along one side of a chord.**  `x + inner · θ` is in the body and
`x + outer · θ` is not; halve the gap `k` times, keeping that invariant, and return the
final `outer`.  `k` membership calls. -/
noncomputable def bisect {n : ℕ} (x θ : State n) : (k : ℕ) → (inner outer : ℝ) → M n ℝ
  | 0, _, outer => pure outer
  | k + 1, inner, outer => do
      let mid := (inner + outer) / 2
      let inside ← isMember (x + mid • θ)
      if inside then bisect x θ k mid outer else bisect x θ k inner mid

/-- **A point of the chord, by rejection.**  At most `r` tries: a uniform point
`x + t · θ` of the bracket `t ∈ [-lo, hi]`, kept if it is in the body.  If every try
misses, stay at `x`.  One `query` per try. -/
noncomputable def chordPoint {n : ℕ} (x θ : State n) (lo hi : ℝ) : (r : ℕ) → M n (State n)
  | 0 => pure x
  | r + 1 => do
      let u ← unitNumber
      let y := x + (-lo + u * (lo + hi)) • θ
      let inside ← isMember y
      if inside then pure y else chordPoint x θ lo hi r

/-- **One lazy hit-and-run step** from `x`: stay with probability `1/2`; otherwise pick a
uniform direction `θ = g/‖g‖`, bracket the chord through `x` along `θ` by bisection on
both sides, and move to a uniform point of the chord by rejection (**Deviation**: capped;
see the module docstring). -/
noncomputable def step {n : ℕ} (w : WalkParams) (x : State n) : M n (State n) := do
  let coin ← unitNumber
  if coin ≤ 1 / 2 then pure x else do
    let g ← gaussianVector
    let θ := ‖g‖⁻¹ • g
    let hi ← bisect x θ w.bisectionSteps 0 (2 * w.D)
    let lo ← bisect x (-θ) w.bisectionSteps 0 (2 * w.D)
    chordPoint x θ lo hi w.rejectionTries

/-- `m` steps of the walk from `x`. -/
noncomputable def walk {n : ℕ} (w : WalkParams) : (m : ℕ) → State n → M n (State n)
  | 0, x => pure x
  | m + 1, x => do
      let y ← step w x
      walk w m y

/-- **The hit-and-run sampler**: `w.steps` lazy hit-and-run steps from `x₀`, on the
oracle `o`.  This is the program the theorems are about; `Model/Run.lean` runs it on a
random tape. -/
noncomputable def sampler {n : ℕ} (w : WalkParams) (x₀ : State n) (o : Oracle n) :
    Prog (State n) := do
  let (y, _) ← (walk w w.steps x₀).run o
  pure y

end ArlibCommunity.Algorithms.HitAndRun.Program

#programSeal ArlibCommunity.Algorithms.HitAndRun.Program
#executableModule ArlibCommunity.Algorithms.HitAndRun.Model.Program
#modelClosure ArlibCommunity.Algorithms.HitAndRun.Program.sampler
#surplusIn ArlibCommunity.Algorithms.HitAndRun.Model.Program from
  ArlibCommunity.Algorithms.HitAndRun.Program.sampler
