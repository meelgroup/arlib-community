/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.FiniteReferenceSequence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledForwardTraceEndpoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalOuterStepErrorSum
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceConstruction
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianPrefixInvariantStep

/-!
# Finite assembly of the global chronological reset reference

This is the recurrence consumer.  It chooses all Gaussian reference laws,
accumulates their exact errors from the accepted initial trace, appends the
terminal reference, and packages the result as the sole final capstone
witness.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The finite recurrence and terminal assembly, parameterized only by the
one-step Gaussian invariant constructor. -/
theorem exists_globalResetReferenceWitness_of_gaussianStep
    (q : VolumeParams) (I : VolumeInput q.n)
    (hgaussianStep : ∀ phase, phase < terminalPhaseSteps q →
      ∀ source : Measure (ScheduledBalancedCoolingTrace q.n),
        IsProbabilityMeasure source →
        ScheduledGlobalGaussianPrefixInvariant q I phase source →
        ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
          IsProbabilityMeasure reference ∧
          MeasureLeUpTo
            (source.bind (scheduledBalancedTracePhaseKernel
              figureOneFinalScheduledBalancedParameters q I phase))
            reference (figureOneScheduledGaussianOuterStepError q phase) ∧
          ScheduledGlobalGaussianPrefixInvariant q I (phase + 1)
            reference) :
    Nonempty (GlobalResetReferenceWitness q I) := by
  let K := scheduledBalancedTracePhaseKernel
    figureOneFinalScheduledBalancedParameters q I
  let actualInitial :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        scheduledBalancedInitialTrace
  let referenceInitial := scheduledBalancedInitialAcceptedTraceReference q I
  let Invariant := ScheduledGlobalGaussianPrefixInvariant q I
  let stepError := figureOneScheduledGaussianOuterStepError q
  have hreferenceInitialProb : IsProbabilityMeasure referenceInitial := by
    exact scheduledBalancedInitialAcceptedTraceReference_isProbabilityMeasure
      q I
  have hreferenceInitialInvariant : Invariant 0 referenceInitial := by
    exact scheduledBalancedInitialAcceptedTraceReference_prefixInvariant q I
  have hinitial : MeasureLeUpTo actualInitial referenceInitial
      (scheduledBalancedStationaryTargetError q) := by
    simpa only [actualInitial, referenceInitial, scheduledBalancedForwardTraceLaw,
      iteratedKernelLaw] using
      scheduledBalancedForwardTraceLaw_zero_leUpTo_initialAcceptedReference
        q I
  have hKmeas : ∀ phase, Measurable (K phase) := by
    intro phase
    exact (scheduledBalancedTracePhaseKernel_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase).1
  have hKprob : ∀ phase trace, IsProbabilityMeasure (K phase trace) := by
    intro phase trace
    exact (scheduledBalancedTracePhaseKernel_measurable_and_probability
      figureOneFinalScheduledBalancedParameters q I phase).2 trace
  have hstep : ∀ phase, phase < terminalPhaseSteps q →
      ∀ source : Measure (ScheduledBalancedCoolingTrace q.n),
        IsProbabilityMeasure source → Invariant phase source →
        ∃ reference : Measure (ScheduledBalancedCoolingTrace q.n),
          IsProbabilityMeasure reference ∧
          MeasureLeUpTo (source.bind (K phase)) reference
            (stepError phase) ∧
          Invariant (phase + 1) reference := by
    intro phase hphase source hsourceProb hsource
    simpa only [K, stepError, Invariant] using
      hgaussianStep phase hphase source hsourceProb hsource
  obtain ⟨gaussianReference, hgaussianProb, hgaussianInvariant,
      hgaussianComparison⟩ :=
    exists_iteratedKernelLaw_le_finiteReference_of_initial
      K actualInitial referenceInitial Invariant stepError
      hreferenceInitialProb hreferenceInitialInvariant hinitial hKmeas hKprob
      (terminalPhaseSteps q) hstep
  let _ : IsProbabilityMeasure gaussianReference := hgaussianProb
  obtain ⟨reference, hreferenceProb, hterminalComparison,
      hreferenceInvariant⟩ :=
    exists_scheduledTerminalReference_of_gaussianPrefixInvariant
      q I gaussianReference hgaussianInvariant
  have hterminal : MeasureLeUpTo
      (gaussianReference.bind (K (terminalPhaseSteps q))) reference
      (figureOneScheduledTerminalOuterStepError q) := by
    simpa only [K, figureOneScheduledTerminalOuterStepError] using
      hterminalComparison
  have hcombined := MeasureLeUpTo.bind_then_replace hgaussianComparison
    (K (terminalPhaseSteps q)) (hKmeas (terminalPhaseSteps q))
    (hKprob (terminalPhaseSteps q)) hterminal
  have htrace : MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
      reference (figureOneScheduledGlobalOuterStepError q) := by
    rw [iteratedKernelLaw_scheduledGaussian_bind_terminal_eq_forwardTraceLaw
      q I] at hcombined
    simpa only [stepError, figureOneScheduledOuterStepError_sum_eq_global]
      using hcombined
  exact ⟨GlobalResetReferenceWitness.of_completed_prefixInvariant
    q I reference hreferenceProb hreferenceInvariant htrace⟩

/-- The chronological reset-reference witness required by the final CV18
capstone exists for every parameter/input pair. -/
theorem globalResetReferenceExists : GlobalResetReferenceExists := by
  intro q I _
  apply exists_globalResetReferenceWitness_of_gaussianStep q I
  intro phase hphase source hsourceProb hsource
  let _ : IsProbabilityMeasure source := hsourceProb
  exact exists_scheduledGlobalGaussianPrefixInvariant_succ
    q I phase hphase source hsource

/-- Premise-free, end-to-end scheduled formalization of CV18 Theorem 1.1.
The returned constant is universal; the probability and oracle-query bounds
are those of the executable amplified membership-oracle program. -/
theorem volumeTheorem_finalScheduled :
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
                protectedLog (1 / q.p))) :=
  volumeTheorem_finalScheduled_of_globalResetReferenceExists
    globalResetReferenceExists

#print axioms exists_globalResetReferenceWitness_of_gaussianStep
#print axioms globalResetReferenceExists
#print axioms volumeTheorem_finalScheduled

end

end ArlibCommunity.Algorithms.CV18
