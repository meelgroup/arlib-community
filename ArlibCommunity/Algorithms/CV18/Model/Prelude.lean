/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Prelude
import ArlibCommunity.Algorithms.CV18.Meta.ModelClosure
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# CV18 model: definitions

Every definition the statement of Theorem 1.1 (`Model/Theorem.lean`) and the
pseudocode (`Model/Pseudocode.lean`) rely on, in reading order:

1. **Problem.** The parameters, the convex body with its unit-ball promise,
   the membership oracle, the target (Lebesgue volume), and what counts as
   an accurate estimate.
2. **Oracle programs.** The language the algorithm is written in: a program
   may query the oracle, draw random numbers or points, and return a value.
   It never sees the body except through queries.  `do` notation is available
   through the `Monad` instance, and `runEstimate` gives a program's output law.
3. **Cooling schedule.** The variances Figure 1 visits.
4. **Sampling laws.** The distributions the program draws from.
5. **Acceptance probabilities and estimator weights.**
6. **Numeric parameters.** Sample counts, error budget, walk geometry and step
   counts, as explicit functions of the public parameters.
7. **Complexity expressions.** The query rate of Theorem 1.1 and the query
   budgets used by the program.

The only proofs in this file are the side conditions needed for the
definitions to type-check (each random draw is a probability measure).
-/

open MeasureTheory

open Arlib
namespace ArlibCommunity.Algorithms.CV18

/-! ## 1. Problem -/

/-- The paper's ambient Euclidean space `ℝⁿ`. -/
abbrev AmbientSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Numerical parameters for the general `R²` form stated immediately after
`thm:volume`. `roundness` is the dimension-free factor in
`E_K ‖X‖² ≤ roundness * n`; setting it to a universal constant gives the
headline well-rounded `O*(n³)` theorem. -/
structure VolumeParams where
  n : ℕ
  /-- The paper's fixed-variance lemma assumes `n ≥ 3`. Low dimensions must
  eventually be discharged by a separate branch. -/
  dim_ok : 3 ≤ n
  eps : ℝ
  heps : eps ∈ Set.Ioo 0 1
  p : ℝ
  hp : p ∈ Set.Ioo 0 1
  roundness : ℝ
  roundness_pos : 0 < roundness

/-- The centered closed Euclidean unit ball. -/
def unitBall (n : ℕ) : Set (AmbientSpace n) := Metric.closedBall 0 1

/-- A compact convex body containing the known centered unit ball.

Using `ConvexBody` records the boundedness and nonemptiness implicit in the
paper's phrase "convex body". -/
structure VolumeInput (n : ℕ) where
  body : ConvexBody (AmbientSpace n)
  unitBall_subset : unitBall n ⊆ (body : Set (AmbientSpace n))

/-- Exact black-box membership access to the body. -/
structure MembershipOracle {n : ℕ} (I : VolumeInput n) where
  query : AmbientSpace n → Bool
  correct : ∀ x, query x = true ↔ x ∈ (I.body : Set (AmbientSpace n))

/-- The ordinary Lebesgue volume targeted by `thm:volume`. -/
noncomputable def euclideanVolume {n : ℕ} (I : VolumeInput n) : ℝ :=
  (volume (I.body : Set (AmbientSpace n))).toReal

/-- The uniform second moment `E_K ‖X‖²`, written as a ratio of Lebesgue
integrals so that it does not depend on a Gaussian measure. -/
noncomputable def uniformSecondMoment {n : ℕ} (I : VolumeInput n) : ℝ :=
  (∫ x in (I.body : Set (AmbientSpace n)), ‖x‖ ^ 2) / euclideanVolume I

/-- The explicit well-roundedness promise supplied to the algorithm. -/
def WellRounded (q : VolumeParams) (I : VolumeInput q.n) : Prop :=
  uniformSecondMoment I ≤ q.roundness * (q.n : ℝ)

/-- Relative accuracy in the paper's `(1 ± ε)` convention. -/
def RelativeApprox (ε target estimate : ℝ) : Prop :=
  estimate ∈ Arlib.relErr ε target

/-- The estimates Theorem 1.1 counts as successes: within a factor `1 ± ε` of
the true volume. -/
def accurateOutcome (q : VolumeParams) (I : VolumeInput q.n) : Set ℝ :=
  {estimate | RelativeApprox q.eps (euclideanVolume I) estimate}

/-! ## 2. Oracle programs -/

/-- A membership-oracle program in dimension `n` returning a `Result`.

A program is a tree of steps: `query x next` asks the oracle whether `x` is in
the body and continues with `next answer`; the `random*` steps draw a value
from a probability law and continue with it; `pure r` returns `r`.  The body is
never an argument, so a program learns about it only through `query` steps.
This is what makes the theorem a statement about a membership-oracle
algorithm, and what lets `Pseudocode.lean` count queries from the program
itself.

The algorithm is written with `do` notation (see the `Monad` instance below and
the primitives `isMember`, `drawPoint`, `drawReal`); the constructors are only
needed to define the semantics and the cost model. -/
inductive MembershipOracleProgram (n : ℕ) (Result : Type) where
  | pure (result : Result)
  | query (point : AmbientSpace n) (next : Bool → MembershipOracleProgram n Result)
  | randomNat (law : PMF ℕ) (next : ℕ → MembershipOracleProgram n Result)
  | randomPoint (law : Measure (AmbientSpace n))
      (lawProbability : IsProbabilityMeasure law)
      (next : AmbientSpace n → MembershipOracleProgram n Result)
  | randomReal (law : Measure ℝ) (lawProbability : IsProbabilityMeasure law)
      (next : ℝ → MembershipOracleProgram n Result)

/-- A uniform randomized membership-oracle algorithm for ordinary volume. -/
abbrev VolumeAlgorithm := (q : VolumeParams) → MembershipOracleProgram q.n ℝ

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

/-- **The output law of a program** when every query is answered by `oracle`:
a `query` step follows the oracle's answer, and a random step averages the rest
of the program over its law.  (Query cost is not part of this law; it is read
off the program itself by `queryCost` in `Pseudocode.lean`.) -/
noncomputable def MembershipOracleProgram.runEstimate {n : ℕ} {Result : Type}
    [MeasurableSpace Result] (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Measure Result
  | .pure result => Measure.dirac result
  | .query point next => runEstimate oracle (next (oracle point))
  | .randomNat law next => law.toMeasure.bind fun seed => runEstimate oracle (next seed)
  | .randomPoint law _ next => law.bind fun point => runEstimate oracle (next point)
  | .randomReal law _ next => law.bind fun value => runEstimate oracle (next value)

/-- `do` notation for oracle programs: `let x ← p; rest` runs `p`, then `rest`. -/
noncomputable instance (n : ℕ) : Monad (MembershipOracleProgram n) where
  pure := .pure
  bind := MembershipOracleProgram.bind

/-- Ask the membership oracle whether `x` is in the body.  This is the only way
a program can learn anything about the body. -/
def isMember {n : ℕ} (x : AmbientSpace n) : MembershipOracleProgram n Bool :=
  .query x .pure

/-- Draw a point of `ℝⁿ` from the probability law `law`. -/
def drawPoint {n : ℕ} (law : Measure (AmbientSpace n)) [h : IsProbabilityMeasure law] :
    MembershipOracleProgram n (AmbientSpace n) :=
  .randomPoint law h .pure

/-- Draw a real number from the probability law `law`. -/
def drawReal {n : ℕ} (law : Measure ℝ) [h : IsProbabilityMeasure law] :
    MembershipOracleProgram n ℝ :=
  .randomReal law h .pure

/-- The output law of a volume algorithm on body `I`, when every query is
answered by `oracle`.  The algorithm is fixed before `I` and `oracle`. -/
noncomputable def volumeAlgorithmLaw (A : VolumeAlgorithm) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) : Measure ℝ :=
  (A q).runEstimate oracle.query

/-- The probability a law assigns to a set of outcomes (outer measure, so no
measurability side condition is needed). -/
noncomputable def outcomeProbability (mu : Measure ℝ) (S : Set ℝ) : ℝ :=
  (mu.toOuterMeasure S).toReal

/-! ## 3. Cooling schedule -/

/-- A logarithm protected below by one. This is the conventional meaning of
the displayed logarithmic complexity factors near parameter boundaries. -/
noncomputable def protectedLog (x : ℝ) : ℝ := max 1 (Real.log x)

/-- The variance scale at which the final Gaussian-to-uniform transition is
made.  Naming it here lets the exact query rate expose its logarithm. -/
noncomputable def terminalScale (q : VolumeParams) : ℝ :=
  max 1 (max (q.n : ℝ)
    (1024 * q.roundness * (q.n : ℝ) * protectedLog (8 / q.eps) ^ 2))

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
  terminalScale q

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
noncomputable def coolingSchedule (q : VolumeParams) : List ℝ :=
  List.ofFn fun i : Fin (terminalPhaseSteps q + 1) => scheduleValue q i

open scoped ENNReal

/-! ## 4. Sampling laws -/

/-- Lebesgue measure on the centered proposal ball, with its finiteness proof. -/
noncomputable def centeredBallFinite (n : ℕ) (radius : ℝ) :
    FiniteMeasure (AmbientSpace n) :=
  ⟨volume.restrict (Metric.closedBall 0 radius), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top⟩⟩

/-- Normalized Lebesgue measure on the proposal ball centered at zero. -/
noncomputable def centeredBall (n : ℕ) (radius : ℝ) :
    Measure (AmbientSpace n) :=
  (centeredBallFinite n radius).normalize

instance centeredBall_isProbabilityMeasure (n : ℕ) (radius : ℝ) :
    IsProbabilityMeasure (centeredBall n radius) := by
  unfold centeredBall
  infer_instance

/-- Uniform proposal measure on a ball, written as a translated centered law.
This presentation makes dependence on the current point measurably explicit. -/
noncomputable def uniformBall (n : ℕ) (center : AmbientSpace n)
    (radius : ℝ) : Measure (AmbientSpace n) :=
  (centeredBall n radius).map fun offset => center + offset

instance uniformBall_isProbabilityMeasure
    (n : ℕ) (center : AmbientSpace n) (radius : ℝ) :
    IsProbabilityMeasure (uniformBall n center radius) := by
  unfold uniformBall
  infer_instance

/-- Lebesgue measure on `[0,1]`, packaged with its finiteness proof. -/
noncomputable def uniformUnitFinite : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top⟩⟩

/-- Normalized Lebesgue measure on `[0,1]`, used for Metropolis and laziness
coins without discretizing their acceptance thresholds. -/
noncomputable def uniformUnit : Measure ℝ :=
  uniformUnitFinite.normalize

instance uniformUnit_isProbabilityMeasure :
    IsProbabilityMeasure uniformUnit := by
  unfold uniformUnit
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
noncomputable def initialGaussianLaw (q : VolumeParams) :
    Measure (AmbientSpace q.n) :=
  volume.withDensity fun x => ENNReal.ofReal
    (gaussianDensity (initialVariance q) x / initialGaussianIntegral q)

instance initialGaussianLaw_isProbabilityMeasure (q : VolumeParams) :
    IsProbabilityMeasure (initialGaussianLaw q) := by
  constructor
  unfold initialGaussianLaw
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

/-! ## 5. Acceptance probabilities and estimator weights -/

/-- Acceptance probability used after scaling the core back to `K`: the ratio
`e^{-‖x‖²/(2·variance)} / e^{-‖x‖²/(2·variance/c²)}` of the unnormalised Gaussian weights at
the two variances, in `ℝ≥0∞`. -/
noncomputable def gaussianScaleAcceptance {n : ℕ} (variance c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / (2 * variance))) /
    ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / (2 * (variance / c ^ 2))))

end ArlibCommunity.Algorithms.CV18

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal

/-- Metropolis acceptance probability for two points at variance `sigma2`. -/
noncomputable def metropolisAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  min 1 (Real.exp (-‖y‖ ^ 2 / (2 * sigma2)) /
    Real.exp (-‖x‖ ^ 2 / (2 * sigma2)))

/-- Half the Metropolis acceptance probability makes the chain lazy. -/
noncomputable def lazyAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  metropolisAcceptance sigma2 x y / 2

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
noncomputable def scaleFactor (q : VolumeParams) : ℝ :=
  1 - 1 / (2 * (q.n : ℝ))

/-! ## 6. Numeric parameters -/

/-! ### Sample counts and error budget -/

/-- The paper's sample count for accelerated phases and the terminal
Gaussian-to-uniform phase. -/
noncomputable def sampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (512 * protectedLog (terminalVariance q) / q.eps ^ 2)

/-- The all-epsilon starting variance lengthens the fixed-rate chain from
`O(n log n)` to `O(n log(n/eps))`; its empirical means therefore use the
matching logarithm. -/
noncomputable def fixedRateSampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)

/-- Phase-sensitive sample count.  Accelerated phases keep the paper's
`log terminalVariance` count, avoiding an unnecessary runtime penalty. -/
noncomputable def phaseSampleCount (q : VolumeParams)
    (sigma2 : ℝ) : ℕ :=
  if sigma2 ≤ 1 then fixedRateSampleCount q else sampleCount q

/-- There is one empirical estimator for every Gaussian transition and one
more for the terminal Gaussian-to-uniform transition. -/
noncomputable def numPhases (q : VolumeParams) : ℕ :=
  terminalPhaseSteps q + 1

/-- A uniform upper bound for the two phase-sensitive sample counts. -/
noncomputable def largestSampleCount (q : VolumeParams) : ℕ :=
  max (fixedRateSampleCount q) (sampleCount q)

/-- The truncation level used when Lemma 7.15 is instantiated at final
relative error `5 * q.eps / 8`.  The large absolute constant leaves a clean
probability budget below `3/16`. -/
noncomputable def truncationLevel (q : VolumeParams) : ℝ :=
  1024 * (numPhases q : ℝ) / q.eps ^ 2

/-- Dependence coefficient consumed by the recursive moment estimates in
Lemma 7.15. -/
noncomputable def dependenceError (q : VolumeParams) : ℝ :=
  q.eps ^ 2 /
    (4096 * truncationLevel q ^ 4 *
      (numPhases q : ℝ))

/-- Per-sample mixing accuracy sufficient for Lemma 7.17(c).  With at most
`k` samples in each of `m` phases, `3 k m nu` is exactly the dependence
coefficient selected above. -/
noncomputable def sampleMixingError (q : VolumeParams) : ℝ :=
  dependenceError q /
    (3 * (largestSampleCount q : ℝ) *
      (numPhases q : ℝ))

/-- Number of speedy-to-target rejection retries allowed per sample. -/
noncomputable def maxRetries (q : VolumeParams) : ℕ :=
  Nat.ceil (128 * protectedLog (4 / sampleMixingError q))

/-- The remaining half-budget is spread across the first block and every
possible retry block.  A factor `4`, rather than `2`, leaves one additional
quarter of slack in the component sum. -/
noncomputable def blockMixingError
    (q : VolumeParams) (attempts : ℕ) : ℝ :=
  sampleMixingError q / (4 * (attempts + 1 : ℝ))

/-- Core error consuming one eighth of the per-sample budget after the KLS
factor `96`. -/
noncomputable def coreMixingError (q : VolumeParams) : ℝ :=
  sampleMixingError q / 768

/-- Radial truncation error consuming a second eighth of the per-sample
budget. -/
noncomputable def radialError (q : VolumeParams) : ℝ :=
  sampleMixingError q / 8

/-- A common logarithmic scale large enough for both the core and radial
accuracy requirements. -/
noncomputable def accuracyLog (q : VolumeParams) : ℝ :=
  max
    (protectedLog ((q.n : ℝ) / coreMixingError q))
    (protectedLog ((q.n : ℝ) / radialError q))

/-! ### Walk geometry and step counts -/

/-- Phase-`sigma2` truncation radius: proposals farther than this from the
origin are treated as improper. -/
noncomputable def phaseRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  32 * Real.sqrt sigma2 *
    Real.sqrt ((q.n : ℝ) * accuracyLog q)

/-- Radius of the uniform ball-walk proposal at phase variance `sigma2`. -/
noncomputable def proposalRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (Real.sqrt sigma2) 1 /
    (4096 * Real.sqrt
      ((q.n : ℝ) * accuracyLog q))

/-- Exact generic speedy-mixing cost after the schedule-targeted proposal
radius is substituted. -/
noncomputable def walkRequirement
    (q : VolumeParams) (sigma2 M mixError : ℝ) : ℝ :=
  4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
    (proposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

/-- A real-valued warmness constant for carrying speedy endpoints between
successive cooling phases. -/
noncomputable def warmConstant (q : VolumeParams) : ℝ :=
  Real.exp (1 / 2) * (4 * Real.exp (1 / 2))

/-- First proper block: accepted-state warmness followed by adjacent-phase
warmness, at the component error assigned to one block. -/
noncomputable def firstWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  walkRequirement q sigma2
    (16 * warmConstant q)
    (blockMixingError q attempts)

/-- Retry blocks start from the normalized rejected branch, which is
two-warm for the scheduled speedy stationary law. -/
noncomputable def retryWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  walkRequirement q sigma2 2
    (blockMixingError q attempts)

/-- A single proper-step stride covering both block types at scheduled
geometry. -/
noncomputable def strideFor
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℕ :=
  Nat.ceil (max 1 (max
    (firstWalkRequirement q sigma2 attempts)
    (retryWalkRequirement q sigma2 attempts)))

/-- Proper walk steps between two consecutive samples of the phase at
variance `sigma2`: one stride long enough for both the first and every retry
block. -/
noncomputable def walkSteps (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  strideFor q sigma2 (maxRetries q - 1)

/-- Number of independent runs combined by the median (confidence
amplification). -/
noncomputable def confidenceRepetitions (q : VolumeParams) : ℕ :=
  Nat.ceil (8 * protectedLog (1 / q.p))

/-! ## 7. Complexity expressions and query budgets -/

/-- Query rate of one constant-success run. Figure 1 uses `log(C² n)` both in
its sample count and in summing the accelerated phases. The paper replaces it
by `log n` after imposing polynomial parameter bounds; the exact unrestricted
formal statement retains the terminal scale. -/
noncomputable def baseRate (q : VolumeParams) : ℝ :=
  max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2 *
    protectedLog (1 / q.eps) ^ 2 *
    protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
    protectedLog (terminalScale q) ^ 2

/-- Exact soft-O rate of the schedule-targeted executable.  The two extra
factors are logarithmic: one selects the accuracy body/radius and the other
is the squared warm-start mixing deadline. -/
noncomputable def runRate (q : VolumeParams) : ℝ :=
  baseRate q * accuracyLog q *
    protectedLog (1 / blockMixingError q
      (maxRetries q - 1)) ^ 2

/-- **Exact query rate for Theorem 1.1**: the per-run rate of the scheduled
program, multiplied by the median-amplification factor.  Dropping the
protected logarithmic factors gives the paper's `O*(roundness * n^3 / eps^2)`. -/
noncomputable def queryRate (q : VolumeParams) : ℝ :=
  runRate q * protectedLog (1 / q.p)

/-- The explicit constant in front of the query rate of Theorem 1.1. -/
noncomputable def queryConstant : ℝ := 9 * (64 * 10 ^ 30 + 1)

/-- A global query budget `ceil(64 * costConstant * rate q)`. -/
noncomputable def budgetOfRate
    (costConstant : ℝ) (rate : VolumeParams → ℝ)
    (q : VolumeParams) : ℕ :=
  Nat.ceil (64 * costConstant * rate q)

/-- A deliberately slack absolute constant for the complete scheduled base
run.  Its slack absorbs endpoint and rejection queries and the finite retry
multiplier without altering the CV18 soft-O rate. -/
noncomputable def runCostConstant : ℝ := 10 ^ 30

/-- The single whole-run membership-query budget of one base run. -/
noncomputable def queryBudget (q : VolumeParams) : ℕ :=
  budgetOfRate runCostConstant
    runRate q

/-- The real-valued local block cap required by the cap-loss estimate.  The
factor `16 * warmConstant` is the larger of the first-block and
retry-block warmness constants. -/
noncomputable def proposalCapRequirement
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  2 * (strideFor q sigma2
      (maxRetries q - 1) : ℝ) *
      (16 * warmConstant q) /
    blockMixingError q (maxRetries q - 1)

/-- The local collector cap contains the outer cutoff budget as a prefix and
then adds enough slack to make cap exhaustion cost one corrected block budget.
The outer query cutoff remains a separate global guard. -/
noncomputable def maxProposals
    (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  queryBudget q +
    Nat.ceil (proposalCapRequirement q sigma2)

end ArlibCommunity.Algorithms.CV18
