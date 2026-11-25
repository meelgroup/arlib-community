/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Probability.Median
import ArlibCommunity.Algorithms.CV18.Model.Operations
import ArlibCommunity.Algorithms.CV18.Meta.ProgramSeal
import ArlibCommunity.Algorithms.CV18.Meta.ModelClosure

/-!
# Program: CV18 Figure 1, with the median of independent runs

The transcription of the algorithm of Theorem 1.1: Figure 1 of [CV18], run
`confidenceRepetitions q` times, with the median of the estimates.  Every numeric
parameter it uses is defined in `Model/Prelude.lean`.

## Shape

Every procedure is a computation in the monad `M n`.  A computation threads a state,
the sealed oracle `o : Oracle n` of `Model/Operations.lean` together with the number of
membership calls still allowed, and may stop early (`failure`) when that number runs
out.  It reads the oracle only through `isMember`, `ballPoint`, `gaussianVector` and
`unitNumber`, which call the charged operations `ask`, `drawBall`, `drawGaussian` and
`drawUnit`: one `query` per membership call, one `draw` per random number.  Arithmetic
is on real numbers and free.  The algorithm never mentions the body: it is
parameterised by `q : VolumeParams` and the oracle, so "given membership access" holds
structurally.

## Figure 1

Writing `f_σ²(x) = exp(-‖x‖²/(2σ²))` and `C²n = terminalVariance q`, one run of
Figure 1 is:

```
x ← a point of N(0, σ₀²I) restricted to K                     initialSample
σ² ← σ₀²
while σ² < C²n:                                                coolingPhases
    τ² ← σ²·(1 + 1/n)          if σ² ≤ 1                       nextVariance
         σ²·(1 + σ²/(2C²n))    otherwise   (capped at C²n)
    draw k samples X₁ … X_k of N(0, σ²I) restricted to K       collectSamples
        by the ball walk, each walk starting where the last one stopped
    W ← (1/k) Σⱼ f_τ²(Xⱼ) / f_σ²(Xⱼ)                           coolingPhase
    σ² ← τ²
draw k samples of N(0, C²n·I) restricted to K
U ← (1/k) Σⱼ 1 / f_C²n(Xⱼ)                                    uniformPhase
return (2πσ₀²)^{n/2} · Π W · U                                 figureOneRun
```

Theorem 1.1 then takes the median of `confidenceRepetitions q = ⌈8 log(1/p)⌉`
independent runs (`estimator`).

## Random points from random numbers

The program draws two kinds of random point, each from the random numbers of the tape:

* a ball-walk proposal around `x` of radius `r` is `x + r · u`, for `u` a uniform point
  of the closed unit ball (`ballPoint`);
* the starting point is `√σ₀² · g`, for `g` a standard Gaussian vector
  (`gaussianVector`).

## Where the program differs from the paper

It differs from Figure 1 in three places, each marked **Deviation** where it occurs:

1. **Walk length counted in proper steps** (`properWalk`).  A walk ends after
   `walkSteps q σ²` *proper* proposals (inside the body and inside the truncation
   radius), and gives up after a fixed number of proposals in all.  It makes one extra
   membership call at its endpoint.
2. **Speedy-to-target rejection** (`rejectionAttempt`).  The walk runs on the body
   enlarged by `c = scaleFactor q`; each walk sample is shrunk back by `1/c` and kept by
   a rejection test.  A sample may be retried at most `maxRetries q` times.
3. **Global query budget** (`cappedRun`).  A run that would make more than
   `queryBudget q` membership calls is stopped and reports `0`.

Two smaller differences: the starting variance is `σ₀² = ε/(64n)` rather than `1/(4n)`,
and any run that fails (initial point outside the body, a walk or a sample collection
giving up) reports `0`.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18.Program

open ArlibCommunity.Algorithms.CV18
open ArlibCommunity.Algorithms.CV18.Model.Operations

/-! ## The monad and its primitives -/

/-- **The program's monad.**  A computation threads the number of membership calls
still allowed and the sealed oracle, and may stop early (`failure`), keeping the state
it stopped in.  Its charged operations are tallied by `Prog`. -/
abbrev M (n : ℕ) := OptionT (StateT (ℕ × Oracle n) Prog)

/-- **One membership call**: is `x` in the body?  One `query`.  A call with no calls
left stops the computation instead (`failure`), without asking. -/
def isMember {n : ℕ} (x : AmbientSpace n) : M n Bool := do
  let (budget, o) ← get
  match budget with
  | 0 => failure
  | budget + 1 =>
      let (answer, o) ← (ask x o : Prog _)
      set (budget, o)
      pure answer

/-- **A uniform point of the closed unit ball.**  One `draw`. -/
def ballPoint {n : ℕ} : M n (AmbientSpace n) := do
  let (budget, o) ← get
  let (u, o) ← (drawBall o : Prog _)
  set (budget, o)
  pure u

/-- **A standard Gaussian vector.**  One `draw`. -/
def gaussianVector {n : ℕ} : M n (AmbientSpace n) := do
  let (budget, o) ← get
  let (g, o) ← (drawGaussian o : Prog _)
  set (budget, o)
  pure g

/-- **A uniform number in `[0, 1]`.**  One `draw`. -/
def unitNumber {n : ℕ} : M n ℝ := do
  let (budget, o) ← get
  let (v, o) ← (drawUnit o : Prog _)
  set (budget, o)
  pure v

/-! ## The algorithm -/

variable (q : VolumeParams)

/-! ### The ball walk -/

/-- **One ball-walk step** toward `N(0, σ²I)` restricted to `K`.  Propose a uniform
point `y` of the ball of radius `proposalRadius q σ²` around `x` and query it.  If `y`
is proper (inside the body and inside the truncation radii), move to `y` with the lazy
Metropolis probability; otherwise stay at `x`.  The flag reports whether `y` was
proper. -/
noncomputable def ballWalkStep (sigma2 : ℝ) (x : AmbientSpace q.n) :
    M q.n (Bool × AmbientSpace q.n) := do
  let u ← ballPoint
  let y := x + proposalRadius q sigma2 • u
  let inside ← isMember y
  let coin ← unitNumber
  if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖y‖ ≤ phaseRadius q sigma2 then
    pure (true, if coin ≤ lazyAcceptance sigma2 x y then y else x)
  else
    pure (false, x)

/-- **Deviation 1: walk length counted in proper steps.**  Take ball-walk steps from
`x` until `steps` proper proposals have been made, and return the final point.  Give up
(`none`) once `cap` proposals have been made in total.  On success one more membership
call is made at the shrunk endpoint; its answer is not used. -/
noncomputable def properWalk (sigma2 : ℝ) :
    (cap steps : ℕ) → AmbientSpace q.n → M q.n (Option (AmbientSpace q.n))
  | 0, _, _ => pure none
  | _ + 1, 0, x => do
      let _ ← isMember ((scaleFactor q)⁻¹ • x)
      pure (some x)
  | cap + 1, steps + 1, x => do
      let (proper, y) ← ballWalkStep q sigma2 x
      properWalk sigma2 cap (if proper then steps else steps + 1) y

/-! ### Drawing the samples of one phase -/

/-- **Deviation 2: speedy-to-target rejection.**  One attempt at turning the walk point
`x` (on the body enlarged by `c`) into a sample of `N(0, σ²I)` restricted to `K`: shrink
it to `y = x / c`, query `y`, and accept with probability `½ · f_σ²(y) / f_{σ²/c²}(y)`. -/
noncomputable def rejectionAttempt (sigma2 : ℝ) (x : AmbientSpace q.n) :
    M q.n (Bool × AmbientSpace q.n) := do
  let c := scaleFactor q
  let y := c⁻¹ • x
  let inside ← isMember y
  let coin ← unitNumber
  if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖y‖ ≤ phaseRadius q sigma2 ∧
      ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ * gaussianScaleAcceptance sigma2 c y then
    pure (true, y)
  else
    pure (false, y)

/-- **Draw `samplesLeft` samples and add up `weight` over them** (Figure 1: "draw k
samples X₁ … X_k").  Each sample is a proper-step walk from the current point followed
by one rejection attempt.  On acceptance, add `weight y` to `total` and reset the retry
budget.  On rejection, walk again from where the walk stopped, at most `retries` times
for one sample.  Running out of retries, or a walk giving up, abandons the phase
(`none`).  Returns the total and the last walk point. -/
noncomputable def collectSamples (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (cap steps retries : ℕ) :
    (retriesLeft samplesLeft : ℕ) → (total : ℝ) → AmbientSpace q.n →
      M q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, x => pure (some (total, x))
  | 0, _ + 1, _, _ => pure none
  | retriesLeft + 1, samplesLeft + 1, total, x => do
      let some y ← properWalk q sigma2 (cap + 1) steps x | pure none
      let (accepted, z) ← rejectionAttempt q sigma2 y
      if accepted then
        collectSamples sigma2 weight cap steps retries retries samplesLeft
          (total + weight z) y
      else
        collectSamples sigma2 weight cap steps retries retriesLeft
          (samplesLeft + 1) total y
termination_by retriesLeft samplesLeft => (samplesLeft, retriesLeft)

/-! ### The phases -/

/-- **One cooling phase** from variance `σ²` to `τ²`: draw `k = phaseSampleCount q σ²`
samples and return the ratio estimate `W = (1/k) Σⱼ f_τ²(Xⱼ) / f_σ²(Xⱼ)`, together with
the point the next phase starts from.  The walk runs on the body enlarged by `c`, so the
starting point is scaled by `c` and the final point by `1/c`. -/
noncomputable def coolingPhase (sigma2 tau2 : ℝ) (x : AmbientSpace q.n) :
    M q.n (Option (ℝ × AmbientSpace q.n)) := do
  let c := scaleFactor q
  let k := phaseSampleCount q sigma2
  let some (total, y) ← collectSamples q sigma2 (gaussianRatioWeight sigma2 tau2)
      (maxProposals q sigma2) (walkSteps q sigma2)
      (maxRetries q) (maxRetries q) k 0 (c • x)
    | pure none
  pure (some (total / k, c⁻¹ • y))

/-- **The final Gaussian-to-uniform phase** at variance `σ²`: draw `k = sampleCount q`
samples and return `U = (1/k) Σⱼ 1 / f_σ²(Xⱼ)`. -/
noncomputable def uniformPhase (sigma2 : ℝ) (x : AmbientSpace q.n) :
    M q.n (Option ℝ) := do
  let c := scaleFactor q
  let k := sampleCount q
  let some (total, _) ← collectSamples q sigma2 (uniformRatioWeight sigma2)
      (maxProposals q sigma2) (walkSteps q sigma2)
      (maxRetries q) (maxRetries q) k 0 (c • x)
    | pure none
  pure (some (total / k))

/-- **The starting point**: `√σ₀² · g` for a standard Gaussian vector `g`, a point of
`N(0, σ₀²I)`, and one membership call.  The run is abandoned (`none`) if the point is
outside the body or outside the truncation radius. -/
noncomputable def initialSample : M q.n (Option (AmbientSpace q.n)) := do
  let g ← gaussianVector
  let x := Real.sqrt (initialVariance q) • g
  let inside ← isMember x
  pure (if inside = true ∧ ‖x‖ ≤ Real.sqrt (terminalVariance q) then some x else none)

/-- **The cooling loop**: run `coolingPhase` for each consecutive pair of variances in
the list, each phase starting where the previous one stopped, and multiply the ratio
estimates. -/
noncomputable def coolingPhases :
    List ℝ → AmbientSpace q.n → M q.n (Option (ℝ × AmbientSpace q.n))
  | sigma2 :: tau2 :: rest, x => do
      let some (W, y) ← coolingPhase q sigma2 tau2 x | pure none
      let some (product, z) ← coolingPhases (tau2 :: rest) y | pure none
      pure (some (W * product, z))
  | _, x => pure (some (1, x))

/-! ### One run, and the median of independent runs -/

/-- **One run of Figure 1**: starting point, the cooling phases along the schedule
`coolingSchedule q`, the final Gaussian-to-uniform phase, and the product with the known
Gaussian integral `(2πσ₀²)^{n/2}`.  A failed step makes the run report `0`. -/
noncomputable def figureOneRun : M q.n ℝ := do
  let some x₀ ← initialSample q | pure 0
  let some (product, x) ← coolingPhases q (coolingSchedule q) x₀ | pure 0
  let some U ← uniformPhase q (terminalVariance q) x | pure 0
  pure (initialGaussianIntegral q * product * U)

/-- **Deviation 3: global query budget.**  One run of Figure 1 with `queryBudget q`
membership calls allowed; a run that would make more is stopped and reports `0`. -/
noncomputable def cappedRun : M q.n ℝ := do
  let (_, o) ← get
  set (queryBudget q, o)
  figureOneRun q <|> pure 0

/-- `m` independent runs of `run`, in order. -/
noncomputable def repeatIndependently {n : ℕ} (run : M n ℝ) :
    (m : ℕ) → M n (Fin m → ℝ)
  | 0 => pure Fin.elim0
  | m + 1 => do
      let first ← run
      let rest ← repeatIndependently run m
      pure (Fin.cons first rest)

/-- The median of `confidenceRepetitions q` independent capped runs of Figure 1. -/
noncomputable def medianOfRuns : M q.n ℝ := do
  let estimates ← repeatIndependently (cappedRun q) (confidenceRepetitions q)
  pure (Arlib.Probability.medianOf estimates)

/-- **The CV18 volume algorithm** (Theorem 1.1): on the oracle `o`, the median of
`confidenceRepetitions q` independent capped runs of Figure 1.  This is the program
Theorem 1.1 is about; `Model/Run.lean` runs it on a random tape. -/
noncomputable def estimator (o : Oracle q.n) : Prog ℝ := do
  let (estimate, _) ← ((medianOfRuns q).run).run (0, o)
  pure (estimate.getD 0)

end ArlibCommunity.Algorithms.CV18.Program

#programSeal ArlibCommunity.Algorithms.CV18.Program
#executableModule ArlibCommunity.Algorithms.CV18.Model.Program
#modelClosure ArlibCommunity.Algorithms.CV18.Program.estimator
#surplusIn ArlibCommunity.Algorithms.CV18.Model.Program from
  ArlibCommunity.Algorithms.CV18.Program.estimator
