/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Theorem

/-!
# CV18 Theorem 1.1 for the named program

`cv18TheoremOneOne` (in `Model/Theorem.lean`) is existential: it asserts that
*some* volume algorithm meets the Theorem 1.1 guarantee.  A downstream client
that executes a specific program needs the guarantee for that program, and a
proof of `∃` cannot be opened to recover its witness.

This file names the program the headline's proof selects and states the same
guarantee for it.  The statement is not `#modelClosureOfType`-sealed, because
the program is built from the scheduled Gaussian-cooling construction under
`Analysis/`.  Its *conclusion*, `VolumeGuarantee` at the model-level rate
`volumeTheoremOneOneRate`, is exactly the headline's.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- The scheduled, capped and median-amplified membership-oracle program
selected by the proof of `cv18TheoremOneOne`. -/
noncomputable def cv18Program : VolumeAlgorithm :=
  amplifyOracleProgram figureOneFinalScheduledCappedValueProgram

/-- Cousins--Vempala 2018, Theorem 1.1, for the concrete program
`cv18Program`: accuracy with probability at least `1 - p`, and a worst-case
membership-query bound at the exact model-level rate. -/
theorem cv18TheoremOneOne_program :
    VolumeGuarantee cv18Program volumeTheoremOneOneRate := by
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

/-- The existential headline is the corollary of the named-program form. -/
theorem cv18TheoremOneOne_of_program :
    ∃ algorithm : VolumeAlgorithm,
      VolumeGuarantee algorithm volumeTheoremOneOneRate :=
  ⟨cv18Program, cv18TheoremOneOne_program⟩

#print axioms cv18TheoremOneOne_program

end ArlibCommunity.Algorithms.CV18
