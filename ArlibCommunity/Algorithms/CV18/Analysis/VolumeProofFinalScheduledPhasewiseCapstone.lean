/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledTheoremAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSharpMomentTransfer

/-!
# Final scheduled theorem from paper-shaped phasewise bounds

This is the last quantitative assembly interface before the unconditional
CV18 theorem.  It turns a phasewise executable-mean comparison and the direct
executable second-moment comparison corresponding to CV18 equation (6) into
the amplified accuracy and query-complexity conclusion.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The executable moment slack divided by eight fits the much larger
`eps/128` aggregate phase-mean budget. -/
theorem figureOneExecutableMomentSlack_div_eight_phase_budget
    (q : VolumeParams) :
    (figureOneDependentPhaseCount q : ℝ) *
        (figureOneExecutableMomentSlack q / 8) ≤ q.eps / 128 := by
  have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have heps0 : 0 ≤ q.eps := q.heps.1.le
  have heps1 : q.eps ≤ 1 := q.heps.2.le
  rw [figureOneExecutableMomentSlack]
  have hcancel :
      (figureOneDependentPhaseCount q : ℝ) *
          (q.eps ^ 2 /
            (4096 * (figureOneDependentPhaseCount q : ℝ)) / 8) =
        q.eps ^ 2 / 32768 := by
    field_simp [hm.ne']
    ring
  rw [hcancel]
  nlinarith [sq_nonneg q.eps]

/-- The fully amplified scheduled volume theorem, reduced to the two local
finite-walk estimates that the paper uses inside each phase: relative first
moment accuracy and the sharp empirical-average second moment. -/
theorem volumeTheorem_finalScheduled_of_phasewise_ideal_bounds
    (hmean : ∀ (q : VolumeParams) (I : VolumeInput q.n),
      WellRounded q I → ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
        |scheduledFigureOneTraceRawMean q I j -
            figureOneChronologicalRawMean q I j| ≤
          figureOneExecutableMomentSlack q / 8 *
            figureOneChronologicalRawMean q I j)
    (hsecond : ∀ (q : VolumeParams) (I : VolumeInput q.n),
      WellRounded q I → ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
        (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
          ∂scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I
            (figureOneDependentPhaseCount q)) ≤
          (figureOneChronologicalMomentFactor q j +
              figureOneExecutableMomentSlack q / 8) *
            figureOneIdealPhaseMean q I
              (figureOneChronologicalPhaseAt q j) ^ 2) :
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
  apply figureOneFinalScheduledAbortBase_failure_le_of_executable_moments
    q I oracle hrounded
  · intro j hj1 hjm
    apply scheduledFigureOneTrace_second_le_executableMomentFactor_of_ideal_bounds
    · have hlower := (abs_le.mp (hmean q I hrounded j hj1 hjm)).1
      change (1 - figureOneExecutableMomentSlack q / 8) *
          figureOneChronologicalRawMean q I j ≤
        scheduledFigureOneTraceRawMean q I j
      linarith
    · exact hsecond q I hrounded j hj1 hjm
  · apply
      scheduledFigureOneTraceRawMeanProduct_relativeApprox_ideal_of_phasewise
        q I (delta := figureOneExecutableMomentSlack q / 8)
    · exact div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
    · have hs := figureOneExecutableMomentSlack_le_one q
      nlinarith
    · exact figureOneExecutableMomentSlack_div_eight_phase_budget q
    · exact hmean q I hrounded

#print axioms figureOneExecutableMomentSlack_div_eight_phase_budget
#print axioms volumeTheorem_finalScheduled_of_phasewise_ideal_bounds

end ArlibCommunity.Algorithms.CV18
