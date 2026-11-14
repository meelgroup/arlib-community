/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Std
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import ArlibCommunity.Foundations.Convex.Basic.GaussianWeight

/-!
# The certified program in its analysis form

The proof of Theorem 1.1 was developed against these definitions: the same
algorithm as `cv18Program` in `Model/Pseudocode.lean`, written directly with
the program constructors and with the sampling subroutines passed through a
`VolumeCoolingPrimitives` record.  `Analysis/PseudocodeBridge.lean` proves that
`cv18Program` is equal to `amplifyOracleProgram
figureOneFinalScheduledCappedValueProgram` defined here.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- `gaussianScaleAcceptance`, which the model states as an explicit ratio of exponentials, is
the ratio of the Gaussian weights `ArlibCommunity.Foundations.Convex.gaussianWeight` at the two
variances — the form the Markov-chain analysis uses. -/
theorem gaussianScaleAcceptance_eq {n : ℕ} (variance c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianScaleAcceptance variance c x =
      ArlibCommunity.Foundations.Convex.gaussianWeight variance x /
        ArlibCommunity.Foundations.Convex.gaussianWeight (variance / c ^ 2) x :=
  rfl


open scoped ENNReal

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
  proposalCap := maxProposals
  properStride := fun q sigma2 =>
    strideFor q sigma2
      (maxRetries q - 1)
  retryLimit := fun q _ => maxRetries q

/-! ### The Metropolis ball walk with proper-step clock -/

/-- Marked Metropolis proposal using the schedule-targeted radial test. -/
noncomputable def scheduledAccuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnit inferInstance fun coin =>
      if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ phaseRadius q sigma2 then
        .pure (true,
          if coin ≤ lazyAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

/-- One raw ball-walk step: draw a uniform proposal in the ball of radius
`proposalRadius q sigma2` around `current`, then run the
marked Metropolis test.  The mark records whether the proposal was proper. -/
noncomputable def scheduledAccuracyMetropolisMarkedBallStep
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformBall q.n current
      (proposalRadius q sigma2)) inferInstance fun proposal =>
      scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal

/-- The dummy endpoint observation retained by the proper-proposal clock. -/
noncomputable def scheduledAccuracyZeroObservation
    (q : VolumeParams) (_sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n ℝ :=
  let target := (scaleFactor q)⁻¹ • current
  .query target fun _ => .pure 0

/-- Capped proper-step block at the new body and proposal radius. -/
noncomputable def cappedScheduledAccuracyProperBlockAux
    (q : VolumeParams) (sigma2 : ℝ) (properStride : ℕ) :
    ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | 0, _, _ => .pure none
  | _rawCap + 1, 0, current =>
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
termination_by rawCap _remainingProper _current => rawCap

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
  let c := scaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnit inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ phaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            ArlibCommunity.Algorithms.CV18.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else .pure (false, target)

/-- Convert the retained speedy state of the last accepted trial into its
Gaussian target, while preserving failure and the accumulated observable. -/
noncomputable def balancedAccuracyRetryOutput (q : VolumeParams) :
    Option (ℝ × AmbientSpace q.n) → Option (ℝ × AmbientSpace q.n)
  | none => none
  | some (total, speedy) =>
      some (total, (scaleFactor q)⁻¹ • speedy)

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
termination_by attempts samples _total _current => (samples, attempts)

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
      (phaseSampleCount q sigma2)
      (scaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (phaseSampleCount q sigma2) result)

/-- The scheduled terminal Gaussian-to-uniform phase, retaining its endpoint. -/
noncomputable def scheduledBalancedCoolingUniformEstimateWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (sampleCount q)
      (scaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (sampleCount q) result)

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
  .randomPoint (initialGaussianLaw q) inferInstance fun point =>
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
cooling phases along `coolingSchedule`, and the terminal
Gaussian-to-uniform phase.  A failed initialization costs exactly one query and
performs no cooling transitions. -/
noncomputable def figureOneFinalScheduledAbortBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  baseVolumeCoolingOn
    (scheduledBalancedAbortCoolingPrimitives
      figureOneFinalScheduledBalancedParameters)
    q (coolingSchedule q)

/-- The final scheduled aborting base program, guarded by the shared global
query cutoff and with cutoff failure represented by the harmless value zero. -/
noncomputable def figureOneFinalScheduledCappedValueProgram
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
      (queryBudget q)).bind
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

end ArlibCommunity.Algorithms.CV18
