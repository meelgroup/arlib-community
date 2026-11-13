/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Probability.Median
import Arlib.Computation.Std
import ArlibCommunity.Algorithms.CV18.Model.Prelude
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Accelerated Gaussian-cooling pseudocode for ordinary volume

This file models Figure 1 all the way to the uniform endpoint, and ends with
`cv18Program`, the concrete algorithm Theorem 1.1 is stated for. Ratio estimators
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

/-- Figure 1's two-rate multiplier: `1+1/n` through variance one, followed by
the accelerated rate `1+σ²/(2C²n)`. -/
noncomputable def coolingRate (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  if sigma2 ≤ 1 then 1 + 1 / (q.n : ℝ)
  else 1 + sigma2 / (2 * terminalVariance q)

/-- One Gaussian-to-Gaussian schedule step, shortened at the terminal
variance so the following phase can jump exactly to the uniform density. -/
noncomputable def nextVariance (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (terminalVariance q) (sigma2 * coolingRate q sigma2)

/-- The deterministic variance after `k` cooling transitions: the loop
variable of Figure 1. -/
noncomputable def scheduleValue (q : VolumeParams) (k : ℕ) : ℝ :=
  (nextVariance q)^[k] (initialVariance q)

/-- The first index at which Figure 1's deterministic cooling schedule reaches
the terminal variance.  The analysis proves that the defining set is nonempty
(`scheduleValue_terminalPhaseSteps`); stopping at the least such index matters
for the runtime, since afterwards `nextVariance` is stationary. -/
noncomputable def terminalPhaseSteps (q : VolumeParams) : ℕ :=
  sInf {k | scheduleValue q k = terminalVariance q}

/-- The variances visited by Figure 1, from `initialVariance q` up to and
including the terminal variance. -/
noncomputable def explicitScheduleVariances (q : VolumeParams) : List ℝ :=
  List.ofFn fun i : Fin (terminalPhaseSteps q + 1) => scheduleValue q i

/-- Primitive ratio-estimation programs used by the transcription.  The
concrete primitives of the certified algorithm are
`scheduledBalancedAbortCoolingPrimitives` below.

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

/-- One run of Figure 1 along an explicit list of variances: Gaussian cooling,
the final Gaussian-to-uniform ratio, and multiplication by the known initial
integral. Aborted capped subroutines return estimate zero, while the
interpreter retains their actual query count. -/
noncomputable def baseVolumeCoolingOn (P : VolumeCoolingPrimitives)
    (q : VolumeParams) (variances : List ℝ) : MembershipOracleProgram q.n ℝ :=
  (P.initialSample q).bind fun initialPoint =>
    match initialPoint with
    | none => .pure 0
    | some point =>
        (coolingProduct P q variances point).bind fun product =>
          match product with
          | none => .pure 0
          | some (gaussianProduct, lastPoint) =>
              (P.uniformRatioEstimate q (terminalVariance q) lastPoint).bind fun finalRatio =>
                .pure <| match finalRatio with
                  | some uniformRatio =>
                      initialGaussianIntegral q * gaussianProduct * uniformRatio
                  | none => 0

/-- Confidence amplification count. -/
noncomputable def confidenceRepetitions (q : VolumeParams) : ℕ :=
  Nat.ceil (8 * protectedLog (1 / q.p))

/-- Successful complete runs. -/
def accurateOutcome (q : VolumeParams) (I : VolumeInput q.n) : Set ℝ :=
  {estimate | RelativeApprox q.eps (euclideanVolume I) estimate}

/-- Probability assigned to an event of complete executions. -/
noncomputable def outcomeProbability (mu : Measure ℝ) (S : Set ℝ) : ℝ :=
  (mu.toOuterMeasure S).toReal


/-!
## The certified CV18 program

The sections above give the shape of Figure 1 with its three sampling
subroutines left abstract.  The rest of this file fills them in: it defines,
as membership-oracle programs, exactly the algorithm `cv18Program` that
Theorem 1.1 (`Model/Theorem.lean`) is proved for.

Reading order:

1. *Sampling laws*: the only continuous randomness the program draws (uniform
   ball proposals, `[0,1]` coins, and the initial Gaussian), each with the
   probability-measure fact its `randomPoint`/`randomReal` node requires.
2. *Acceptance probabilities and estimator weights*.
3. *Sample counts, error budget, walk geometry, query budget*: every numeric
   parameter of the run, as an explicit function of `VolumeParams`.
4. *Programs*: the lazy Metropolis ball walk with a proper-step clock, the
   speedy-to-target rejection, the per-phase sample collector, the aborting
   initial sample, one base run along the schedule, the global query cap, and
   median amplification.

Compared with the paper's Figure 1, the program (a) counts *proper* walk steps
and caps raw proposals, (b) converts speedy-walk samples to target samples by
a homothetic rejection with bounded retries, and (c) guards each base run with
one global query budget whose exhaustion returns the estimate `0`.  The
analysis under `Analysis/` justifies each change; see `Analysis/README.md`.

The proofs here are only the side conditions needed for the definitions to
type-check (each random draw is a probability measure); nothing about the
algorithm's behaviour is proved here.
-/

end ArlibCommunity.Algorithms.CV18

namespace Arlib.MarkovChains

open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-- The **unnormalised Gaussian weight** `e^{-‖x‖²/(2s)}`, as a real number. -/
noncomputable def gaussianWeightReal (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (2 * s))

/-- The **Gaussian weight** `e^{-‖x‖²/(2s)}` as an element of `ℝ≥0∞`.  It is the density,
with respect to Lebesgue measure, of the unnormalised measure whose restriction to a body
`K` is the Cousins-Vempala target `∝ 1_K(x)·e^{-‖x‖²/(2s)}`. -/
noncomputable def gaussianWeight (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianWeightReal s x)

/-- Acceptance probability used after scaling the core back to `K`. -/
noncomputable def gaussianScaleAcceptance (variance c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  gaussianWeight variance x / gaussianWeight (variance / c ^ 2) x

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal

/-! ### Sampling laws -/

/-- Lebesgue measure on the centered proposal ball, with its finiteness proof. -/
noncomputable def centeredClosedBallFiniteMeasure (n : ℕ) (radius : ℝ) :
    FiniteMeasure (AmbientSpace n) :=
  ⟨volume.restrict (Metric.closedBall 0 radius), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top⟩⟩

/-- Normalized Lebesgue measure on the proposal ball centered at zero. -/
noncomputable def centeredClosedBallMeasure (n : ℕ) (radius : ℝ) :
    Measure (AmbientSpace n) :=
  (centeredClosedBallFiniteMeasure n radius).normalize

instance centeredClosedBallMeasure_isProbabilityMeasure (n : ℕ) (radius : ℝ) :
    IsProbabilityMeasure (centeredClosedBallMeasure n radius) := by
  unfold centeredClosedBallMeasure
  infer_instance

/-- Uniform proposal measure on a ball, written as a translated centered law.
This presentation makes dependence on the current point measurably explicit. -/
noncomputable def uniformClosedBallMeasure (n : ℕ) (center : AmbientSpace n)
    (radius : ℝ) : Measure (AmbientSpace n) :=
  (centeredClosedBallMeasure n radius).map fun offset => center + offset

instance uniformClosedBallMeasure_isProbabilityMeasure
    (n : ℕ) (center : AmbientSpace n) (radius : ℝ) :
    IsProbabilityMeasure (uniformClosedBallMeasure n center radius) := by
  unfold uniformClosedBallMeasure
  infer_instance

/-- Lebesgue measure on `[0,1]`, packaged with its finiteness proof. -/
noncomputable def uniformUnitIntervalFiniteMeasure : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top⟩⟩

/-- Normalized Lebesgue measure on `[0,1]`, used for Metropolis and laziness
coins without discretizing their acceptance thresholds. -/
noncomputable def uniformUnitIntervalMeasure : Measure ℝ :=
  uniformUnitIntervalFiniteMeasure.normalize

instance uniformUnitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure uniformUnitIntervalMeasure := by
  unfold uniformUnitIntervalMeasure
  infer_instance

/-- The unnormalised Gaussian density `exp(-‖x‖²/(2s))` at variance `s`. -/
noncomputable def gaussianDensity {n : ℕ} (s : ℝ) (x : AmbientSpace n) : ℝ :=
  Real.exp (- (1 / (2 * s)) * ‖x‖ ^ 2)

theorem integral_gaussianDensity {n : ℕ} {s : ℝ} (hs : 0 < s) :
    ∫ x : AmbientSpace n, gaussianDensity s x =
      Real.rpow (2 * Real.pi * s) ((n : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := AmbientSpace n) (b := (1 / (2 * s) : ℝ)) (by positivity)
  rw [show (Real.pi / (1 / (2 * s))) = 2 * Real.pi * s by field_simp] at h
  simpa [gaussianDensity, finrank_euclideanSpace_fin] using h

theorem integrable_gaussianDensity {n : ℕ} {s : ℝ} (hs : 0 < s) :
    Integrable (gaussianDensity (n := n) s) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianDensity hs]
  exact (Real.rpow_pos_of_pos (by positivity) _).ne'

lemma initialVariance_pos (q : VolumeParams) : 0 < initialVariance q := by
  unfold initialVariance
  have hn : (0 : ℝ) < q.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) q.dim_ok)
  exact div_pos q.heps.1 (by positivity)

theorem initialGaussianIntegral_pos (q : VolumeParams) :
    0 < initialGaussianIntegral q := by
  unfold initialGaussianIntegral
  exact Real.rpow_pos_of_pos
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (initialVariance_pos q)) _

/-- The centered Gaussian with covariance `initialVariance q * I`, defined
directly by its normalized Lebesgue density.  This keeps the executable law
identical to the density used by the initial-tail proof and avoids any bridge
through Mathlib's standard-Gaussian volume API. -/
noncomputable def initialGaussianSamplingMeasure (q : VolumeParams) :
    Measure (AmbientSpace q.n) :=
  volume.withDensity fun x => ENNReal.ofReal
    (gaussianDensity (initialVariance q) x / initialGaussianIntegral q)

instance initialGaussianSamplingMeasure_isProbabilityMeasure (q : VolumeParams) :
    IsProbabilityMeasure (initialGaussianSamplingMeasure q) := by
  constructor
  unfold initialGaussianSamplingMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hZ := initialGaussianIntegral_pos q
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_gaussianDensity (initialVariance_pos q)).div_const _)]
  · rw [integral_div, integral_gaussianDensity (initialVariance_pos q)]
    change ENNReal.ofReal (initialGaussianIntegral q / initialGaussianIntegral q) = 1
    rw [div_self hZ.ne']
    simp
  · exact Filter.Eventually.of_forall fun x =>
      div_nonneg (Real.exp_pos _).le hZ.le

/-! ### Acceptance probabilities and estimator weights -/

/-- Metropolis acceptance probability for two points at variance `sigma2`. -/
noncomputable def gaussianMetropolisAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  min 1 (Real.exp (-‖y‖ ^ 2 / (2 * sigma2)) /
    Real.exp (-‖x‖ ^ 2 / (2 * sigma2)))

/-- Half the Metropolis acceptance probability makes the chain lazy. -/
noncomputable def lazyGaussianMetropolisAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  gaussianMetropolisAcceptance sigma2 x y / 2

/-- The body indicator cancels from a ratio at points known to be inside. -/
noncomputable def gaussianRatioWeight {n : ℕ} (sigma2 tau2 : ℝ)
    (x : AmbientSpace n) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (2 * tau2)) /
    Real.exp (-‖x‖ ^ 2 / (2 * sigma2))

/-- Estimator weight for the terminal Gaussian-to-uniform ratio: the reciprocal
of the variance-`sigma2` Gaussian density at a point known to be inside. -/
noncomputable def uniformRatioWeight {n : ℕ} (sigma2 : ℝ)
    (x : AmbientSpace n) : ℝ :=
  Real.exp (‖x‖ ^ 2 / (2 * sigma2))

/-- Homothety used by the KLS speedy-to-target rejection routine. -/
noncomputable def accuracyScaleFactor (q : VolumeParams) : ℝ :=
  1 - 1 / (2 * (q.n : ℝ))

/-! ### Sample counts and error budget -/

/-- The paper's sample count for accelerated phases and the terminal
Gaussian-to-uniform phase. -/
noncomputable def figureOneSampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (512 * protectedLog (terminalVariance q) / q.eps ^ 2)

/-- The all-epsilon starting variance lengthens the fixed-rate chain from
`O(n log n)` to `O(n log(n/eps))`; its empirical means therefore use the
matching logarithm. -/
noncomputable def figureOneFixedSampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)

/-- Phase-sensitive sample count.  Accelerated phases keep the paper's
`log terminalVariance` count, avoiding an unnecessary runtime penalty. -/
noncomputable def figureOnePhaseSampleCount (q : VolumeParams)
    (sigma2 : ℝ) : ℕ :=
  if sigma2 ≤ 1 then figureOneFixedSampleCount q else figureOneSampleCount q

/-- There is one empirical estimator for every Gaussian transition and one
more for the terminal Gaussian-to-uniform transition. -/
noncomputable def figureOneDependentPhaseCount (q : VolumeParams) : ℕ :=
  terminalPhaseSteps q + 1

/-- A uniform upper bound for the two phase-sensitive sample counts. -/
noncomputable def figureOneDependentMaxSampleCount (q : VolumeParams) : ℕ :=
  max (figureOneFixedSampleCount q) (figureOneSampleCount q)

/-- The truncation level used when Lemma 7.15 is instantiated at final
relative error `5 * q.eps / 8`.  The large absolute constant leaves a clean
probability budget below `3/16`. -/
noncomputable def figureOneDependentAlpha (q : VolumeParams) : ℝ :=
  1024 * (figureOneDependentPhaseCount q : ℝ) / q.eps ^ 2

/-- Dependence coefficient consumed by the recursive moment estimates in
Lemma 7.15. -/
noncomputable def figureOneDependentEpsilon (q : VolumeParams) : ℝ :=
  q.eps ^ 2 /
    (4096 * figureOneDependentAlpha q ^ 4 *
      (figureOneDependentPhaseCount q : ℝ))

/-- Per-sample mixing accuracy sufficient for Lemma 7.17(c).  With at most
`k` samples in each of `m` phases, `3 k m nu` is exactly the dependence
coefficient selected above. -/
noncomputable def figureOnePerSampleMixingError (q : VolumeParams) : ℝ :=
  figureOneDependentEpsilon q /
    (3 * (figureOneDependentMaxSampleCount q : ℝ) *
      (figureOneDependentPhaseCount q : ℝ))

/-- Number of speedy-to-target rejection retries allowed per sample. -/
noncomputable def figureOneSafeRetryCount (q : VolumeParams) : ℕ :=
  Nat.ceil (128 * protectedLog (4 / figureOnePerSampleMixingError q))

/-- The remaining half-budget is spread across the first block and every
possible retry block.  A factor `4`, rather than `2`, leaves one additional
quarter of slack in the component sum. -/
noncomputable def figureOneCorrectedBlockMixingError
    (q : VolumeParams) (attempts : ℕ) : ℝ :=
  figureOnePerSampleMixingError q / (4 * (attempts + 1 : ℝ))

/-- Core error consuming one eighth of the per-sample budget after the KLS
factor `96`. -/
noncomputable def figureOneScheduledCoreError (q : VolumeParams) : ℝ :=
  figureOnePerSampleMixingError q / 768

/-- Radial truncation error consuming a second eighth of the per-sample
budget. -/
noncomputable def figureOneScheduledRadialError (q : VolumeParams) : ℝ :=
  figureOnePerSampleMixingError q / 8

/-- A common logarithmic scale large enough for both the core and radial
accuracy requirements. -/
noncomputable def figureOneScheduledAccuracyLog (q : VolumeParams) : ℝ :=
  max
    (protectedLog ((q.n : ℝ) / figureOneScheduledCoreError q))
    (protectedLog ((q.n : ℝ) / figureOneScheduledRadialError q))

/-! ### Walk geometry and step counts -/

/-- Phase-`sigma2` truncation radius: proposals farther than this from the
origin are treated as improper. -/
noncomputable def figureOneScheduledPhaseRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  32 * Real.sqrt sigma2 *
    Real.sqrt ((q.n : ℝ) * figureOneScheduledAccuracyLog q)

/-- Radius of the uniform ball-walk proposal at phase variance `sigma2`. -/
noncomputable def figureOneScheduledProposalRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (Real.sqrt sigma2) 1 /
    (4096 * Real.sqrt
      ((q.n : ℝ) * figureOneScheduledAccuracyLog q))

/-- Exact generic speedy-mixing cost after the schedule-targeted proposal
radius is substituted. -/
noncomputable def figureOneScheduledWalkRequirement
    (q : VolumeParams) (sigma2 M mixError : ℝ) : ℝ :=
  4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
    (figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

/-- A real-valued warmness constant for carrying speedy endpoints between
successive cooling phases. -/
noncomputable def speedyAdjacentWarmConstant (q : VolumeParams) : ℝ :=
  Real.exp (1 / 2) * (4 * Real.exp (1 / 2))

/-- First proper block: accepted-state warmness followed by adjacent-phase
warmness, at the component error assigned to one block. -/
noncomputable def figureOneScheduledCorrectedFirstWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  figureOneScheduledWalkRequirement q sigma2
    (16 * speedyAdjacentWarmConstant q)
    (figureOneCorrectedBlockMixingError q attempts)

/-- Retry blocks start from the normalized rejected branch, which is
two-warm for the scheduled speedy stationary law. -/
noncomputable def figureOneScheduledCorrectedRetryWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  figureOneScheduledWalkRequirement q sigma2 2
    (figureOneCorrectedBlockMixingError q attempts)

/-- A single proper-step stride covering both block types at scheduled
geometry. -/
noncomputable def figureOneScheduledCorrectedProperStride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℕ :=
  Nat.ceil (max 1 (max
    (figureOneScheduledCorrectedFirstWalkRequirement q sigma2 attempts)
    (figureOneScheduledCorrectedRetryWalkRequirement q sigma2 attempts)))

/-! ### Query budget and caps -/

/-- Exact soft-O rate of the schedule-targeted executable.  The two extra
factors are logarithmic: one selects the accuracy body/radius and the other
is the squared warm-start mixing deadline. -/
noncomputable def volumeScheduledBaseComplexityRate (q : VolumeParams) : ℝ :=
  volumeBaseComplexityRate q * figureOneScheduledAccuracyLog q *
    protectedLog (1 / figureOneCorrectedBlockMixingError q
      (figureOneSafeRetryCount q - 1)) ^ 2

/-- A global query budget `ceil(64 * costConstant * rate q)`. -/
noncomputable def globalQueryBudgetOfRate
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (q : VolumeParams) : ℕ :=
  Nat.ceil (64 * costConstant * rate q)

/-- A deliberately slack absolute constant for the complete scheduled base
run.  Its slack absorbs endpoint and rejection queries and the finite retry
multiplier without altering the CV18 soft-O rate. -/
noncomputable def figureOneFinalScheduledExpectedCostConstant : ℝ := 10 ^ 30

/-- The single whole-run membership-query budget of one base run. -/
noncomputable def figureOneFinalScheduledQueryBudget (q : VolumeParams) : ℕ :=
  globalQueryBudgetOfRate figureOneFinalScheduledExpectedCostConstant
    volumeScheduledBaseComplexityRate q

/-- The real-valued local block cap required by the cap-loss estimate.  The
factor `16 * speedyAdjacentWarmConstant` is the larger of the first-block and
retry-block warmness constants. -/
noncomputable def figureOneFinalScheduledLocalCapRequirement
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  2 * (figureOneScheduledCorrectedProperStride q sigma2
      (figureOneSafeRetryCount q - 1) : ℝ) *
      (16 * speedyAdjacentWarmConstant q) /
    figureOneCorrectedBlockMixingError q (figureOneSafeRetryCount q - 1)

/-- The local collector cap contains the outer cutoff budget as a prefix and
then adds enough slack to make cap exhaustion cost one corrected block budget.
The outer query cutoff remains a separate global guard. -/
noncomputable def figureOneFinalScheduledLocalProposalCap
    (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  figureOneFinalScheduledQueryBudget q +
    Nat.ceil (figureOneFinalScheduledLocalCapRequirement q sigma2)

/-- Finite execution parameters for the balanced/proper-step phase collector.
The statistical sample counts are not configurable: they are the actual
Figure-One counts used by `VolumeProofDependentSchedule`. -/
structure BalancedCoolingParameters where
  proposalCap : (q : VolumeParams) → ℝ → ℕ
  properStride : (q : VolumeParams) → ℝ → ℕ
  retryLimit : (q : VolumeParams) → ℝ → ℕ

/-- The parameters shared by the final cost, mapped-law, and prefix arguments.
Only the global proposal cap differs from the earlier scheduled prototype. -/
noncomputable def figureOneFinalScheduledBalancedParameters :
    BalancedCoolingParameters where
  proposalCap := figureOneFinalScheduledLocalProposalCap
  properStride := fun q sigma2 =>
    figureOneScheduledCorrectedProperStride q sigma2
      (figureOneSafeRetryCount q - 1)
  retryLimit := fun q _ => figureOneSafeRetryCount q

/-! ### The Metropolis ball walk with proper-step clock -/

/-- Marked Metropolis proposal using the schedule-targeted radial test. -/
noncomputable def scheduledAccuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2 then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

/-- One raw ball-walk step: draw a uniform proposal in the ball of radius
`figureOneScheduledProposalRadius q sigma2` around `current`, then run the
marked Metropolis test.  The mark records whether the proposal was proper. -/
noncomputable def scheduledAccuracyMetropolisMarkedBallStep
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current
      (figureOneScheduledProposalRadius q sigma2)) inferInstance fun proposal =>
      scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal

/-- The dummy endpoint observation retained by the proper-proposal clock. -/
noncomputable def scheduledAccuracyZeroObservation
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n ℝ :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  .query target fun _ => .pure 0

/-- Capped proper-step block at the new body and proposal radius. -/
noncomputable def cappedScheduledAccuracyProperBlockAux
    (q : VolumeParams) (sigma2 : ℝ) (properStride : ℕ) :
    ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | 0, _, _ => .pure none
  | rawCap + 1, 0, current =>
      (scheduledAccuracyZeroObservation q sigma2 current).bind fun observed =>
        .pure (some (observed, current))
  | rawCap + 1, remainingProper + 1, current =>
      (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).bind
        fun result =>
          if result.1 then
            match remainingProper with
            | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                rawCap 0 result.2
            | nextRemaining + 1 =>
                cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap (nextRemaining + 1) result.2
          else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
            rawCap (remainingProper + 1) result.2
termination_by rawCap remainingProper current => rawCap

/-- Walk until `properStride` proper proposals have been made, giving up
(`none`) after `rawCap` raw proposals. -/
noncomputable def cappedScheduledAccuracyProperBlock
    (q : VolumeParams) (sigma2 : ℝ) (rawCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
    rawCap properStride current

/-! ### Speedy-to-target rejection and the per-phase estimator -/

/-- Schedule-targeted balanced KLS rejection. -/
noncomputable def scheduledBalancedAccuracyGaussianRejectionAttempt
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else .pure (false, target)

/-- Convert the retained speedy state of the last accepted trial into its
Gaussian target, while preserving failure and the accumulated observable. -/
noncomputable def balancedAccuracyRetryOutput (q : VolumeParams) :
    Option (ℝ × AmbientSpace q.n) → Option (ℝ × AmbientSpace q.n)
  | none => none
  | some (total, speedy) =>
      some (total, (accuracyScaleFactor q)⁻¹ • speedy)

/-- Finite balanced retries whose proper blocks and rejection tests both use
the schedule-targeted geometry. -/
noncomputable def scheduledBalancedAccuracyRetryCollectAux
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, current => .pure (some (total, current))
  | 0, _ + 1, _, _ => .pure none
  | attempts + 1, samples + 1, total, current =>
      (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).bind fun block =>
        match block with
        | none => .pure none
        | some (_, mixed) =>
            (scheduledBalancedAccuracyGaussianRejectionAttempt
              q sigma2 mixed).bind fun result =>
                if result.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit retryLimit samples
                    (total + weight result.2) mixed
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit attempts
                    (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

/-- One phase's sample collector: `samples` accepted target draws, each obtained
by a capped proper-step block followed by at most `retryLimit` rejection
retries, accumulating `weight` at the accepted points.  The retained state is
mapped back from the speedy core to the body. -/
noncomputable def scheduledBalancedAccuracyRetryCollect
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
    properStride retryLimit retryLimit samples 0 current).bind fun result =>
      .pure (balancedAccuracyRetryOutput q result)

/-- Average an accumulated phase observable without changing its retained
target-space state. -/
noncomputable def balancedCoolingAverage (samples : ℕ) :
    Option (ℝ × AmbientSpace n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some (total, current) => some (total / (samples : ℝ), current)

/-- Forget only the terminal retained state, as required by
`VolumeCoolingPrimitives.uniformRatioEstimate`. -/
noncomputable def balancedCoolingForgetState :
    Option (ℝ × AmbientSpace n) → Option ℝ
  | none => none
  | some (estimate, _) => some estimate

/-- One averaged Gaussian cooling phase driven by the scheduled-body sampler. -/
noncomputable def scheduledBalancedCoolingRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2) result)

/-- The scheduled terminal Gaussian-to-uniform phase, retaining its endpoint. -/
noncomputable def scheduledBalancedCoolingUniformEstimateWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOneSampleCount q) result)

/-- Forget the retained endpoint after the scheduled terminal phase. -/
noncomputable def scheduledBalancedCoolingUniformRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).bind
    fun result => .pure (balancedCoolingForgetState result)

/-! ### Initial sample and the Figure 1 primitives -/

/-- One Gaussian proposal and one membership query, aborting rather than
continuing from the origin when the proposal misses the truncated body. -/
noncomputable def figureOneAbortInitialSample (q : VolumeParams) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  .randomPoint (initialGaussianSamplingMeasure q) inferInstance fun point =>
    .query point fun inside =>
      .pure (if inside = true ∧
        ‖point‖ ≤ Real.sqrt (terminalVariance q) then some point else none)

/-- Scheduled primitives with paper-faithful aborting initialization. -/
noncomputable def scheduledBalancedAbortCoolingPrimitives
    (parameters : BalancedCoolingParameters) : VolumeCoolingPrimitives where
  initialSample := figureOneAbortInitialSample
  ratioEstimate := scheduledBalancedCoolingRatioEstimate parameters
  uniformRatioEstimate := scheduledBalancedCoolingUniformRatioEstimate parameters

/-- One complete base run of Figure 1: aborting initial sample, the Gaussian
cooling phases along `explicitScheduleVariances`, and the terminal
Gaussian-to-uniform phase.  A failed initialization costs exactly one query and
performs no cooling transitions. -/
noncomputable def figureOneFinalScheduledAbortBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  baseVolumeCoolingOn
    (scheduledBalancedAbortCoolingPrimitives
      figureOneFinalScheduledBalancedParameters)
    q (explicitScheduleVariances q)

/-! ### Global query cap and median amplification -/

/-- Run an oracle program with one shared membership-query budget.  Random
draws do not consume budget.  A pure result at budget zero still succeeds;
only an attempted query past the budget produces `none`. -/
noncomputable def MembershipOracleProgram.withQueryCap
    {n : ℕ} {Result : Type} :
    ℕ → MembershipOracleProgram n Result →
      MembershipOracleProgram n (Option Result)
  | _, .pure result => .pure (some result)
  | 0, .query _ _ => .pure none
  | budget + 1, .query point next =>
      .query point fun answer => withQueryCap budget (next answer)
  | budget, .randomNat law next =>
      .randomNat law fun seed => withQueryCap budget (next seed)
  | budget, .randomPoint law hprob next =>
      .randomPoint law hprob fun point => withQueryCap budget (next point)
  | budget, .randomReal law hprob next =>
      .randomReal law hprob fun value => withQueryCap budget (next value)

/-- The final scheduled aborting base program, guarded by the shared global
query cutoff and with cutoff failure represented by the harmless value zero. -/
noncomputable def figureOneFinalScheduledCappedValueProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
      (figureOneFinalScheduledQueryBudget q)).bind
    fun estimate => .pure (estimate.getD 0)

/-- Repeat an arbitrary real-valued oracle program independently. -/
noncomputable def repeatOracleProgram {n : ℕ}
    (base : MembershipOracleProgram n ℝ) :
    (m : ℕ) → MembershipOracleProgram n (Fin m → ℝ)
  | 0 => .pure Fin.elim0
  | m + 1 =>
      base.bind fun estimate =>
        (repeatOracleProgram base m).bind fun tail =>
          .pure (Fin.cons estimate tail)

/-- Median amplification of an arbitrary parameterized base program. -/
noncomputable def amplifyOracleProgram
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ) :
    VolumeAlgorithm :=
  fun q =>
    (repeatOracleProgram (base q) (confidenceRepetitions q)).bind fun estimates =>
      .pure (Arlib.Probability.medianOf estimates)

/-- **The certified CV18 volume algorithm.**  Independent repetitions of the
globally capped base run, combined by their median.  `cv18TheoremOneOne`
proves the accuracy and query guarantee for exactly this program. -/
noncomputable def cv18Program : VolumeAlgorithm :=
  amplifyOracleProgram figureOneFinalScheduledCappedValueProgram

/-- **Exact query rate for Theorem 1.1**: the per-run rate of the scheduled
program, multiplied by the median-amplification factor.  Dropping the
protected logarithmic factors gives the paper's `O*(roundness * n^3 / eps^2)`. -/
noncomputable def volumeTheoremOneOneRate (q : VolumeParams) : ℝ :=
  volumeScheduledBaseComplexityRate q * protectedLog (1 / q.p)

#modelClosure cv18Program
#modelClosure volumeTheoremOneOneRate

end ArlibCommunity.Algorithms.CV18
