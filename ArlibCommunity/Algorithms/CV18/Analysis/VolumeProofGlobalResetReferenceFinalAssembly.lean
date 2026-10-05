/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceBaseCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledTheoremAssembly

/-!
# Final assembly from a global chronological reset reference

This module packages the one remaining analytic construction behind a single
proposition.  A `GlobalResetReferenceWitness` is a probability law on the
public loss-preserving trace whose coordinates have the exact reference
moments, satisfy the transported Lemma 7.17(c) hypothesis, and whose product
law is close to the executable chronological trace.

No existence claim is made here.  The final theorem says that existence of
these witnesses for all well-rounded inputs is exactly sufficient for the
fully quantified scheduled CV18 theorem; the already-closed query-cap and
amplification lanes are then applied without further premises.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The data produced by the chronological history-preserving reset
construction for one well-rounded CV18 input. -/
structure GlobalResetReferenceWitness
    (q : VolumeParams) (I : VolumeInput q.n) where
  reference : Measure (ScheduledBalancedCoolingTrace q.n)
  isProbabilityMeasure : IsProbabilityMeasure reference
  /-- Reference coordinates may differ from the public trace projection
  outside the finite recorded range.  In particular, the chronological
  construction extends those coordinates by their positive raw means. -/
  W : ℕ → ScheduledBalancedCoolingTrace q.n → ℝ
  coordinate_measurable : ∀ j, Measurable (W j)
  coordinate_nonnegative : ∀ j trace, 0 ≤ W j trace
  coordinate_memLp : ∀ j,
    MemLp (W j) 2 reference
  coordinate_mean : ∀ j,
    (∫ trace, W j trace ∂reference) =
      figureOneChronologicalRawMean q I j
  coordinate_second : ∀ j,
    (∫ trace, W j trace ^ 2 ∂reference) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2
  epsilon : ℝ
  epsilon_nonnegative : 0 ≤ epsilon
  epsilon_le : epsilon ≤
    (5 / 2 : ℝ) * figureOneDependentEpsilon q
  approxIndep : ∀ i, i < figureOneDependentPhaseCount q →
    ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference
          W)
        (figureOneChronologicalTruncatedPhase q I
          W) i)
      (figureOneChronologicalTruncatedPhase q I
        W (i + 1)) reference
  error : ENNReal
  boundary : ENNReal
  product_leUpTo : MeasureLeUpTo
    ((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
      (fun trace => initialGaussianIntegral q *
        dependentPhaseSampleProduct
          (scheduledBalancedTracePhaseVariable q)
          (figureOneDependentPhaseCount q) trace))
    (reference.map (fun trace => initialGaussianIntegral q *
      dependentPhaseSampleProduct W
        (figureOneDependentPhaseCount q) trace)) error
  error_le : error ≤
    figureOneScheduledGlobalResetReferenceError q + boundary
  boundary_le : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ)

/-- The sole remaining premise for the scheduled end-to-end theorem: every
well-rounded input admits a chronological reset-reference witness. -/
def GlobalResetReferenceExists : Prop :=
  ∀ (q : VolumeParams) (I : VolumeInput q.n), WellRounded q I →
    Nonempty (GlobalResetReferenceWitness q I)

/-- A global reset-reference witness discharges the sole analytic premise of
`volumeTheorem_finalScheduled_of_baseFailure`. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_globalResetReferenceExists
    (hglobal : GlobalResetReferenceExists)
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  obtain ⟨witness⟩ := hglobal q I hrounded
  let _ : IsProbabilityMeasure witness.reference :=
    witness.isProbabilityMeasure
  exact figureOneFinalScheduledAbortBase_failure_le_of_globalResetReference
    q I oracle hrounded witness.reference witness.W
      witness.coordinate_measurable witness.coordinate_nonnegative
      witness.coordinate_memLp witness.coordinate_mean
      witness.coordinate_second witness.epsilon_nonnegative
      witness.epsilon_le witness.approxIndep witness.product_leUpTo
      witness.error_le witness.boundary_le

/-- Final scheduled CV18 theorem from the single global reset-reference
existence proposition.  Query capping and amplification are unconditional in
the imported assembly theorem. -/
theorem volumeTheorem_finalScheduled_of_globalResetReferenceExists
    (hglobal : GlobalResetReferenceExists) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I), WellRounded q I →
          1 - q.p ≤ outcomeProbability
            (volumeAlgorithmLaw
              (amplifyOracleProgram figureOneFinalScheduledCappedValueProgram)
              q I oracle) (accurateOutcome q I) ∧
          ∃ calls,
            (amplifyOracleProgram
              figureOneFinalScheduledCappedValueProgram q).QueryBound calls ∧
            calls ≤ Nat.ceil
              (C * (volumeScheduledBaseComplexityRate q *
                protectedLog (1 / q.p))) := by
  apply volumeTheorem_finalScheduled_of_baseFailure
  intro q I oracle hrounded
  exact figureOneFinalScheduledAbortBase_failure_le_of_globalResetReferenceExists
    hglobal q I oracle hrounded

#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_globalResetReferenceExists
#print axioms volumeTheorem_finalScheduled_of_globalResetReferenceExists

end

end ArlibCommunity.Algorithms.CV18
