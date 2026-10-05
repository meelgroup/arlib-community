/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryAppend
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofActualMeanTruncation

/-! # Scheduled trace capstone with executable semantics discharged -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

private noncomputable def scheduledTracePhaseRepresentative
    (q : VolumeParams) (j : ℕ) : ℕ :=
  (j - 1) % figureOneDependentPhaseCount q + 1

private theorem scheduledTracePhaseRepresentative_pos
    (q : VolumeParams) (j : ℕ) :
    1 ≤ scheduledTracePhaseRepresentative q j := by
  simp [scheduledTracePhaseRepresentative]

private theorem scheduledTracePhaseRepresentative_le
    (q : VolumeParams) (j : ℕ) :
    scheduledTracePhaseRepresentative q j ≤ figureOneDependentPhaseCount q := by
  unfold scheduledTracePhaseRepresentative
  have hmod := Nat.mod_lt (j - 1) (figureOneDependentPhaseCount_pos q)
  omega

private theorem figureOneChronologicalPhaseAt_representative
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalPhaseAt q j =
      figureOneChronologicalPhaseAt q
        (scheduledTracePhaseRepresentative q j) := by
  unfold figureOneChronologicalPhaseAt scheduledTracePhaseRepresentative
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_cancel]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (figureOneDependentPhaseCount_pos q))]

private theorem scheduledBalancedTracePhaseVariable_representative
    (q : VolumeParams) (j : ℕ) :
    scheduledBalancedTracePhaseVariable q j =
      scheduledBalancedTracePhaseVariable q
        (scheduledTracePhaseRepresentative q j) := by
  funext trace
  unfold scheduledBalancedTracePhaseVariable
    scheduledBalancedTraceChronologicalPhaseVariable
    balancedCoolingChronologicalPhaseVariable
  rw [figureOneChronologicalPhaseAt_representative q j]

/-- A finite executable phase needs only a positive raw mean and the relaxed
second-moment estimate.  The truncation facts required by Lemma 7.15 then
follow from the generic actual-mean truncation package. -/
theorem scheduledFigureOneTrace_moment_package
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)))
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        4 * scheduledFigureOneTraceRawMean q I j ^ 2) :
    0 < scheduledFigureOneTraceTruncatedMean q I j ∧
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j ∧
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j ∧
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have hpackage := actualMeanTruncation_moment_package mu
    (measurable_scheduledBalancedTracePhaseVariable q j)
    (scheduledBalancedTracePhaseVariable_nonnegative q j) hWmem
    (raw := scheduledFigureOneTraceRawMean q I j)
    (alpha := figureOneDependentAlpha q) rfl hrawPos
    (figureOneDependentAlpha_ge_1024 q) hsecond
  simpa [mu, scheduledFigureOneTraceTruncatedPhase,
    scheduledFigureOneTraceTruncatedMean,
    scheduledFigureOneTraceTruncatedSecond, dependentTruncatedPhase] using hpackage

/-- The exact finite-schedule interpreter theorem removes `hpoint` from the
loss-preserving trace capstone.  The remaining premises are precisely the
finite Lemma 7.15/7.17 moment and dependence estimates. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (scheduledBalancedTracePhaseVariable q j)
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hmeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    FigureOnePostInitialDirectFailureBoundFor q I fun point =>
      (scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point).runEstimate
          oracle.query := by
  have hrawRepresentative : ∀ j,
      scheduledFigureOneTraceRawMean q I j =
        scheduledFigureOneTraceRawMean q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceRawMean
    rw [scheduledBalancedTracePhaseVariable_representative q j]
  have hphaseRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedPhase q I j =
        scheduledFigureOneTraceTruncatedPhase q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    funext trace
    unfold scheduledFigureOneTraceTruncatedPhase dependentTruncatedPhase
    rw [hrawRepresentative j,
      scheduledBalancedTracePhaseVariable_representative q j]
  have hmeanRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedMean q I j =
        scheduledFigureOneTraceTruncatedMean q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceTruncatedMean
    rw [hphaseRepresentative j]
  have hsecondRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedSecond q I j =
        scheduledFigureOneTraceTruncatedSecond q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceTruncatedSecond
    rw [hphaseRepresentative j]
  apply figureOnePostInitialDirectFailureBoundFor_of_trace_lemma717bc
    q I oracle hrounded
      (scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map
        figureOneFinalScheduledBalancedParameters q I oracle)
      hWint
  · intro j
    rw [hmeanRepresentative j]
    exact hmeanPos _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j]
    exact hrawMeanPos _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j, hmeanRepresentative j]
    exact hrawMean_le _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hmeanRepresentative j, hsecondRepresentative j]
    exact hmeanSecond _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j, hsecondRepresentative j]
    exact hrawSecond _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · exact hind
  · exact hrelative
  · exact htailSecond
  · exact hmeanApprox

#print axioms figureOnePostInitialDirectFailureBoundFor_of_trace_moments

/-- Legacy non-aborting transport of the reusable direct post-initial trace
bound. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (scheduledBalancedTracePhaseVariable q j)
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hmeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledBalancedBase_failure_le_of_directPostInitial
    q I oracle
  exact figureOnePostInitialDirectFailureBoundFor_of_trace_moments
    q I oracle hrounded hWint hmeanPos hrawMeanPos hrawMean_le
      hmeanSecond hrawSecond hind hrelative htailSecond hmeanApprox

#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_moments

/-- Executable trace capstone with the elementary truncation obligations
discharged.  The residual inputs are the phase `L²`/raw-moment estimates,
Lemma 7.17(c), and the two finite product comparisons. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_trace_raw_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWmem : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      MemLp (scheduledBalancedTracePhaseVariable q j) 2
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawSecondFour : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        4 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    FigureOnePostInitialDirectFailureBoundFor q I fun point =>
      (scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point).runEstimate
          oracle.query := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have hpackage : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceTruncatedMean q I j ∧
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j ∧
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j ∧
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j := by
    intro j hj1 hjm
    exact scheduledFigureOneTrace_moment_package q I j
      (hWmem j hj1 hjm) (hrawMeanPos j hj1 hjm)
      (hrawSecondFour j hj1 hjm)
  apply figureOnePostInitialDirectFailureBoundFor_of_trace_moments
    q I oracle hrounded
  · intro j hj1 hjm
    exact (hWmem j hj1 hjm).integrable (by norm_num)
  · intro j hj1 hjm
    exact (hpackage j hj1 hjm).1
  · exact hrawMeanPos
  · intro j hj1 hjm
    exact (hpackage j hj1 hjm).2.1
  · intro j hj1 hjm
    exact (hpackage j hj1 hjm).2.2.1
  · intro j hj1 hjm
    exact (hpackage j hj1 hjm).2.2.2
  · exact hind
  · exact hrelative
  · exact htailSecond
  · exact hmeanApprox

#print axioms figureOnePostInitialDirectFailureBoundFor_of_trace_raw_moments

/-- Legacy non-aborting transport of the raw-moment direct trace theorem. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWmem : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      MemLp (scheduledBalancedTracePhaseVariable q j) 2
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawSecondFour : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        4 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledBalancedBase_failure_le_of_directPostInitial
    q I oracle
  exact figureOnePostInitialDirectFailureBoundFor_of_trace_raw_moments
    q I oracle hrounded hWmem hrawMeanPos hrawSecondFour hind hrelative
      htailSecond hmeanApprox

#print axioms scheduledFigureOneTrace_moment_package
#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments

end ArlibCommunity.Algorithms.CV18
