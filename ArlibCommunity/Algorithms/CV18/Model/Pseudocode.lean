/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Probability.Median
import Arlib.Computation.Std
import ArlibCommunity.Algorithms.CV18.Model.Prelude

/-!
# Accelerated Gaussian-cooling pseudocode for ordinary volume

This file models Figure 1 all the way to the uniform endpoint. Ratio estimators
are membership-oracle programs, not arbitrary laws with access to the complete
set, and query counts are produced by the interpreter.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-! ## Operational semantics -/

/-- Sequential composition of membership-oracle programs. -/
def MembershipOracleProgram.bind {n : ℕ} {A B : Type}
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B) : MembershipOracleProgram n B :=
  match program with
  | .pure result => next result
  | .query point branch => .query point (fun answer => (branch answer).bind next)
  | .randomNat law branch => .randomNat law (fun seed => (branch seed).bind next)
  | .randomPoint law hprob branch =>
      .randomPoint law hprob (fun point => (branch point).bind next)
  | .randomReal law hprob branch =>
      .randomReal law hprob (fun value => (branch value).bind next)

/-- Execute a program against an oracle. The second component is the actual
number of `query` nodes traversed by that execution. -/
noncomputable def MembershipOracleProgram.run {n : ℕ} {Result : Type}
    [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Measure (Result × ℕ)
  | .pure result => Measure.dirac (result, 0)
  | .query point next =>
      (run oracle (next (oracle point))).map fun outcome =>
        (outcome.1, outcome.2 + 1)
  | .randomNat law next => law.toMeasure.bind fun seed => run oracle (next seed)
  | .randomPoint law _ next => law.bind fun point => run oracle (next point)
  | .randomReal law _ next => law.bind fun value => run oracle (next value)

/-- The estimate marginal of an oracle program. Keeping costs at the syntax
level avoids treating the topological support of a non-atomic measure as if it
were the atom support of a `PMF`. -/
noncomputable def MembershipOracleProgram.runEstimate {n : ℕ} {Result : Type}
    [MeasurableSpace Result] (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Measure Result
  | .pure result => Measure.dirac result
  | .query point next => runEstimate oracle (next (oracle point))
  | .randomNat law next => law.toMeasure.bind fun seed => runEstimate oracle (next seed)
  | .randomPoint law _ next => law.bind fun point => runEstimate oracle (next point)
  | .randomReal law _ next => law.bind fun value => runEstimate oracle (next value)

/-- A syntax-level worst-case membership-query bound. Continuous draws do not
hide a cost field: every possible continuation must satisfy the same bound. -/
inductive MembershipOracleProgram.QueryBound {n : ℕ} {Result : Type} :
    MembershipOracleProgram n Result → ℕ → Prop where
  | pure (result : Result) (budget : ℕ) : QueryBound (.pure result) budget
  | query (point : AmbientSpace n) (next : Bool → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ answer, QueryBound (next answer) budget) :
      QueryBound (.query point next) (budget + 1)
  | randomNat (law : PMF ℕ) (next : ℕ → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ seed, QueryBound (next seed) budget) :
      QueryBound (.randomNat law next) budget
  | randomPoint (law : Measure (AmbientSpace n)) (hprob : IsProbabilityMeasure law)
      (next : AmbientSpace n → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ point, QueryBound (next point) budget) :
      QueryBound (.randomPoint law hprob next) budget
  | randomReal (law : Measure ℝ) (hprob : IsProbabilityMeasure law)
      (next : ℝ → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ value, QueryBound (next value) budget) :
      QueryBound (.randomReal law hprob next) budget

/-! ## Cost derived from `Arlib.Computation`

The theorem reports membership-oracle cost, not a separately asserted counter.
An execution below is a `Charged` computation in Arlib's standard currency.
Every oracle query performs exactly the membership operation exported by the
sealed `Roster` carrier, namely `StdOp.roster RosterOp.mem`; resolving random
nodes performs no charged operation because randomness is outside the resource
being reported here.

`MembershipCostChoices` resolves the random nodes only to expose an individual
execution path.  `MembershipCostBound` quantifies over every such resolution
and every Boolean oracle, so its bound is worst-case rather than probabilistic.
-/

/-- A resolution of all random nodes along one execution. -/
structure MembershipOracleProgram.MembershipCostChoices (n : ℕ) where
  randomNat : ℕ → PMF ℕ → ℕ
  randomPoint : ℕ → Measure (AmbientSpace n) → AmbientSpace n
  randomReal : ℕ → Measure ℝ → ℝ

/-- One execution, from a specified random-draw index, interpreted in Arlib's
charged carrier.  A membership query is the roster carrier's canonical
membership operation. -/
def MembershipOracleProgram.chargedMembershipRunFrom
    {n : ℕ} {Result : Type}
    (oracle : AmbientSpace n → Bool) (choices : MembershipCostChoices n) : ℕ →
      MembershipOracleProgram n Result →
      Arlib.Computation.Charged Arlib.Computation.StdOp
        Arlib.Computation.Cell Result
  | _, .pure result => Arlib.Computation.Charged.pure result
  | drawIndex, .query point next =>
      Arlib.Computation.Charged.op
          (Arlib.Computation.StdOp.roster Arlib.Computation.RosterOp.mem)
          (oracle point) >>= fun answer =>
        chargedMembershipRunFrom oracle choices drawIndex (next answer)
  | drawIndex, .randomNat law next =>
      chargedMembershipRunFrom oracle choices (drawIndex + 1)
        (next (choices.randomNat drawIndex law))
  | drawIndex, .randomPoint law _ next =>
      chargedMembershipRunFrom oracle choices (drawIndex + 1)
        (next (choices.randomPoint drawIndex law))
  | drawIndex, .randomReal law _ next =>
      chargedMembershipRunFrom oracle choices (drawIndex + 1)
        (next (choices.randomReal drawIndex law))

/-- One complete execution interpreted in Arlib's charged carrier. -/
def MembershipOracleProgram.chargedMembershipRun
    {n : ℕ} {Result : Type} (program : MembershipOracleProgram n Result)
    (oracle : AmbientSpace n → Bool) (choices : MembershipCostChoices n) :=
  chargedMembershipRunFrom oracle choices 0 program

/-- Worst-case membership cost computed from the program through
`Arlib.Computation.Charged`.  Unit pricing makes one roster-membership operation
one membership-oracle call. -/
def MembershipOracleProgram.MembershipCostBound
    {n : ℕ} {Result : Type} (program : MembershipOracleProgram n Result)
    (budget : ℕ) : Prop :=
  ∀ (oracle : AmbientSpace n → Bool) (choices : MembershipCostChoices n),
    Arlib.Computation.Charged.steps
      (Arlib.Computation.Rate.unit Arlib.Computation.StdOp)
      (program.chargedMembershipRun oracle choices) ≤ budget

/-- The syntax-directed bound controls the charged cost from every draw index. -/
theorem MembershipOracleProgram.QueryBound.toMembershipCostBoundFrom
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {budget : ℕ} (h : program.QueryBound budget) :
    ∀ (drawIndex : ℕ) (oracle : AmbientSpace n → Bool)
      (choices : MembershipCostChoices n),
      Arlib.Computation.Charged.steps
        (Arlib.Computation.Rate.unit Arlib.Computation.StdOp)
        (chargedMembershipRunFrom oracle choices drawIndex program) ≤ budget := by
  induction h with
  | pure result budget =>
      intro drawIndex oracle choices
      change 0 ≤ budget
      exact Nat.zero_le budget
  | query point next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom, Arlib.Computation.Charged.steps_bind,
        Arlib.Computation.Charged.steps_op, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Rate.unit_cost]
      have htail := ih (oracle point) drawIndex oracle choices
      omega
  | randomNat law next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomNat drawIndex law) (drawIndex + 1) oracle choices
  | randomPoint law hprob next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomPoint drawIndex law) (drawIndex + 1) oracle choices
  | randomReal law hprob next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomReal drawIndex law) (drawIndex + 1) oracle choices

/-- The existing syntax-directed bound is a certificate for the cost derived
from Arlib's charged roster-membership operation. -/
theorem MembershipOracleProgram.QueryBound.toMembershipCostBound
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {budget : ℕ} (h : program.QueryBound budget) :
    program.MembershipCostBound budget := by
  intro oracle choices
  exact h.toMembershipCostBoundFrom 0 oracle choices

/-- The estimate law of a program.  Membership cost is exposed separately by
`MembershipCostBound`, through `Arlib.Computation.Charged`. -/
noncomputable def volumeAlgorithmLaw (A : VolumeAlgorithm) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) : Measure ℝ :=
  (A q).runEstimate oracle.query

/-! ## Figure 1 schedule -/

/-- The all-epsilon replacement for Figure 1's `1/(4n)`. -/
noncomputable def initialVariance (q : VolumeParams) : ℝ :=
  q.eps / (64 * (q.n : ℝ))

/-- The known full-space integral of the initial unnormalised Gaussian. -/
noncomputable def initialGaussianIntegral (q : VolumeParams) : ℝ :=
  Real.rpow (2 * Real.pi * initialVariance q) ((q.n : ℝ) / 2)

/-- The truncation/terminal variance `C²n`. From the second-moment promise
`E_K‖X‖² ≤ roundness*n`, the paper takes a truncation radius proportional
to `sqrt(roundness*n) * log(1/eps)`. -/
noncomputable def terminalVariance (q : VolumeParams) : ℝ :=
  volumeTerminalScale q

/-- The high-probability truncation of `K` used to turn the second-moment
promise into the outer-radius hypothesis required by Figure 1. -/
noncomputable def truncatedBody (q : VolumeParams) (I : VolumeInput q.n) :
    Set (AmbientSpace q.n) :=
  (I.body : Set (AmbientSpace q.n)) ∩ Metric.closedBall 0 (Real.sqrt (terminalVariance q))

/-- Figure 1's two-rate multiplier: `1+1/n` through variance one, followed by
the accelerated rate `1+σ²/(2C²n)`. -/
noncomputable def coolingRate (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  if sigma2 ≤ 1 then 1 + 1 / (q.n : ℝ)
  else 1 + sigma2 / (2 * terminalVariance q)

/-- One Gaussian-to-Gaussian schedule step, shortened at the terminal
variance so the following phase can jump exactly to the uniform density. -/
noncomputable def nextVariance (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (terminalVariance q) (sigma2 * coolingRate q sigma2)

/-- The deterministic variance after `k` cooling transitions.  This is the
model-level counterpart of the loop variable in Figure 1. -/
noncomputable def modelScheduleValue (q : VolumeParams) (k : ℕ) : ℝ :=
  (nextVariance q)^[k] (initialVariance q)

/-- The first point at which Figure 1's deterministic cooling schedule reaches
the terminal variance.  The analysis proves that the defining set is nonempty;
using its infimum here keeps the public query rate a function of the input
parameters, rather than exposing a schedule witness in Theorem 1.1. -/
noncomputable def modelTerminalPhaseSteps (q : VolumeParams) : ℕ :=
  sInf {k | modelScheduleValue q k = terminalVariance q}

/-- A finite schedule witnessing the loop in Figure 1.

Existence and quantitative bounds for this schedule are analysis obligations;
they are deliberately not hidden inside an unconstrained estimator. -/
structure VolumeCoolingSchedule (q : VolumeParams) where
  variances : List ℝ
  nonempty : variances ≠ []
  start : variances.head? = some (initialVariance q)
  step : variances.IsChain (fun sigma2 tau2 => tau2 = nextVariance q sigma2)
  positive : ∀ sigma2 ∈ variances, 0 < sigma2
  finish : variances.getLast? = some (terminalVariance q)

/-- Primitive ratio-estimation programs used by the transcription.

Unlike the previous interface, these fields receive neither `VolumeInput` nor
an oracle law. They can learn membership only when their returned program is
interpreted and traverses a `query` node. -/
structure VolumeCoolingPrimitives where
  /-- Produce the first point at the starting variance.  The unit-ball promise
  is what makes rejection from the concentrated full Gaussian possible. -/
  initialSample :
    (q : VolumeParams) → MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  ratioEstimate :
    (q : VolumeParams) → (sigma2 tau2 : ℝ) →
      AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  uniformRatioEstimate :
    (q : VolumeParams) → (sigma2 : ℝ) →
      AmbientSpace q.n → MembershipOracleProgram q.n (Option ℝ)

/-- Multiply estimates for every adjacent pair while threading the last walk
point into the next phase.  This state is the warm start used in Figure 1 and
is essential for the amortized cubic query bound. -/
noncomputable def coolingProduct (P : VolumeCoolingPrimitives)
    (q : VolumeParams) :
    List ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | [], point => .pure (some (1, point))
  | [_], point => .pure (some (1, point))
  | sigma2 :: tau2 :: rest, point =>
      (P.ratioEstimate q sigma2 tau2 point).bind fun phase =>
        match phase with
        | none => .pure none
        | some (ratio, nextPoint) =>
            (coolingProduct P q (tau2 :: rest) nextPoint).bind fun tail =>
              .pure <| match tail with
                | some (product, lastPoint) => some (ratio * product, lastPoint)
                | none => none
termination_by variances => variances.length

/-- One run of Figure 1: Gaussian cooling, the final Gaussian-to-uniform ratio,
and multiplication by the known initial integral. Aborted capped subroutines
return estimate zero, while the interpreter retains their actual query count. -/
noncomputable def baseVolumeCooling (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  (P.initialSample q).bind fun initialPoint =>
    match initialPoint with
    | none => .pure 0
    | some point =>
        (coolingProduct P q (S q).variances point).bind fun product =>
          match product with
          | none => .pure 0
          | some (gaussianProduct, lastPoint) =>
              (P.uniformRatioEstimate q (terminalVariance q) lastPoint).bind fun finalRatio =>
                .pure <| match finalRatio with
                  | some uniformRatio =>
                      initialGaussianIntegral q * gaussianProduct * uniformRatio
                  | none => 0

/-- Repeat a program independently in the `PMF` semantics. -/
noncomputable def repeatVolumeCooling (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) : (m : ℕ) → MembershipOracleProgram q.n (Fin m → ℝ)
  | 0 => .pure Fin.elim0
  | m + 1 =>
      (baseVolumeCooling P S q).bind fun estimate =>
        (repeatVolumeCooling P S q m).bind fun tail =>
          .pure (Fin.cons estimate tail)

/-- Confidence amplification count. -/
noncomputable def confidenceRepetitions (q : VolumeParams) : ℕ :=
  Nat.ceil (8 * protectedLog (1 / q.p))

/-- The concrete shape of the paper's volume algorithm: repeated accelerated
cooling runs followed by their median. -/
noncomputable def volumeCoolingAlgorithm (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q) : VolumeAlgorithm :=
  fun q =>
    (repeatVolumeCooling P S q (confidenceRepetitions q)).bind fun estimates =>
      .pure (Arlib.Probability.medianOf estimates)

/-- Successful complete runs. -/
def accurateOutcome (q : VolumeParams) (I : VolumeInput q.n) : Set ℝ :=
  {estimate | RelativeApprox q.eps (euclideanVolume I) estimate}

/-- Probability assigned to an event of complete executions. -/
noncomputable def outcomeProbability (mu : Measure ℝ) (S : Set ℝ) : ℝ :=
  (mu.toOuterMeasure S).toReal

/-! ## Exact rate exposed by the verified scheduled implementation -/

/-- Exact query rate for Theorem 1.1, including confidence amplification.

The local bindings expose the concrete logarithmic factors used by the proof
without adding auxiliary rate declarations to the model's public audit
surface.  These factors are suppressed by the paper's `O*` notation. -/
noncomputable def volumeTheoremOneOneRate (q : VolumeParams) : ℝ :=
  let sampleCount : ℕ :=
    Nat.ceil (512 * protectedLog (terminalVariance q) / q.eps ^ 2)
  let fixedSampleCount : ℕ :=
    Nat.ceil (4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)
  let phaseCount : ℕ := modelTerminalPhaseSteps q + 1
  let maxSampleCount : ℕ := max fixedSampleCount sampleCount
  let alpha : ℝ := 1024 * (phaseCount : ℝ) / q.eps ^ 2
  let dependenceBudget : ℝ :=
    q.eps ^ 2 / (4096 * alpha ^ 4 * (phaseCount : ℝ))
  let perSampleError : ℝ :=
    dependenceBudget / (3 * (maxSampleCount : ℝ) * (phaseCount : ℝ))
  let retryCount : ℕ :=
    Nat.ceil (128 * protectedLog (4 / perSampleError))
  let accuracyLog : ℝ :=
    max
      (protectedLog ((q.n : ℝ) / (perSampleError / 768)))
      (protectedLog ((q.n : ℝ) / (perSampleError / 8)))
  volumeBaseComplexityRate q * accuracyLog *
    protectedLog
      (1 / (perSampleError /
        (4 * (((retryCount - 1 : ℕ) : ℝ) + 1)))) ^ 2 *
    protectedLog (1 / q.p)

#modelClosure volumeCoolingAlgorithm
#modelClosure volumeTheoremOneOneRate

end ArlibCommunity.Algorithms.CV18
