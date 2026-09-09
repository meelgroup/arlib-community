/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Prior
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceExists

/-!
# CV18 Theorem 1.1

This is the headline audit surface.  The statement below mentions only
objects defined under `Model/`: the input promise, oracle-program semantics,
success event, algorithm, and exact parameter-only query rate.  Its proof
selects the concrete scheduled implementation whose analysis is developed
under `Analysis/`.

The exact displayed rate retains all protected logarithmic factors.  Removing
them gives the paper's `O*(roundness * n^3 / eps^2)` notation; for a
well-rounded body with universal `roundness`, this is `O*(n^3 / eps^2)`.
The deterministic cooling schedule is an internal construction used by the
proof and is deliberately absent from the public theorem statement.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- Accuracy and worst-case membership-query guarantee for one uniform
volume algorithm at a specified model-level rate.  The membership cost is
computed from the program by `Arlib.Computation.Charged`, using the roster
carrier's membership operation. -/
def VolumeGuarantee (algorithm : VolumeAlgorithm)
    (rate : VolumeParams → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
        1 - q.p ≤ outcomeProbability
          (volumeAlgorithmLaw algorithm q I oracle) (accurateOutcome q I) ∧
        ∃ calls, (algorithm q).MembershipCostBound calls ∧
          calls ≤ Nat.ceil (C * rate q)

/-- Cousins--Vempala 2018, Theorem 1.1: there is a membership-oracle volume
algorithm succeeding with probability at least `1-p`, with the exact
polylogarithmic refinement of the paper's `O*` query bound.

The algorithm is selected before the body and its membership oracle are
quantified.  Its rate is a model-level function only of the public parameters;
the proof internally constructs the first terminal cooling schedule. -/
theorem cv18TheoremOneOne :
    ∃ algorithm : VolumeAlgorithm,
      VolumeGuarantee algorithm volumeTheoremOneOneRate := by
  let algorithm : VolumeAlgorithm :=
    amplifyOracleProgram figureOneFinalScheduledCappedValueProgram
  refine ⟨algorithm, ?_⟩
  obtain ⟨C, hC, htheorem⟩ := volumeTheorem_finalScheduled
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  have hsteps : modelTerminalPhaseSteps q = terminalPhaseSteps q := by
    unfold modelTerminalPhaseSteps terminalPhaseSteps
    rw [Nat.sInf_def]
    rfl
  have hrate : volumeTheoremOneOneRate q =
      volumeScheduledBaseComplexityRate q * protectedLog (1 / q.p) := by
    simp only [volumeTheoremOneOneRate, hsteps,
      volumeScheduledBaseComplexityRate, figureOneScheduledAccuracyLog,
      figureOneScheduledCoreError, figureOneScheduledRadialError,
      figureOneCorrectedBlockMixingError, figureOneSafeRetryCount,
      figureOnePerSampleMixingError, figureOneDependentEpsilon,
      figureOneDependentAlpha, figureOneDependentPhaseCount,
      figureOneDependentMaxSampleCount, figureOneFixedSampleCount,
      figureOneSampleCount]
  obtain ⟨haccuracy, calls, hcalls, hle⟩ := htheorem q I oracle hrounded
  refine ⟨haccuracy, calls, hcalls.toMembershipCostBound, ?_⟩
  simpa only [hrate] using hle

#modelClosureOfType cv18TheoremOneOne
#print axioms cv18TheoremOneOne

end ArlibCommunity.Algorithms.CV18
