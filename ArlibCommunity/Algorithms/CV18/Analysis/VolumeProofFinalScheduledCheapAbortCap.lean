/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledIdealPhase
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedHybridCap

/-! # The cheap initial-abort branch and the final global query cap

The failed initial rejection branch performs exactly one query.  It is
therefore absent from the event that the global query budget is exceeded.
This file starts the chronological counted reference from the exact ideal
phase-zero law, and transfers only that expensive-count event from the actual
initializer.  No initial-tail probability is charged to runtime.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exact ideal phase-zero state paired with the one query already spent by
the executable initializer. -/
noncomputable def figureOneFinalScheduledIdealCountedInitial
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (Option (AmbientSpace q.n) × ℕ) :=
  (figureOneFinalScheduledIdealPhaseStart q I 0).map fun state => (state, 1)

theorem figureOneFinalScheduledIdealCountedInitial_fst
    (q : VolumeParams) (I : VolumeInput q.n) :
    (figureOneFinalScheduledIdealCountedInitial q I).fst =
      figureOneFinalScheduledIdealPhaseStart q I 0 := by
  unfold figureOneFinalScheduledIdealCountedInitial Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  have hcomp : (Prod.fst ∘ fun state : Option (AmbientSpace q.n) =>
      (state, 1)) = id := by
    funext state
    rfl
  rw [hcomp, Measure.map_id]

theorem figureOneFinalScheduledIdealCountedInitial_cost
    (q : VolumeParams) (I : VolumeInput q.n) :
    countedQueryCost (figureOneFinalScheduledIdealCountedInitial q I) = 1 := by
  unfold countedQueryCost figureOneFinalScheduledIdealCountedInitial
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  let _ : IsProbabilityMeasure
      (figureOneFinalScheduledIdealPhaseStart q I 0) :=
    figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I 0
  simp

/-- Chronological counted reference started from the exact ideal phase-zero
law.  Its only discrepancy is the sum of phase exact-chance errors. -/
theorem exists_figureOneFinalScheduledIdealGaussianCountedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (steps : ℕ) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          (figureOneFinalScheduledIdealCountedInitial q I) steps)
        reference
        (∑ phase ∈ Finset.range steps,
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q) ∧
      reference.fst = figureOneFinalScheduledIdealPhaseStart q I steps ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range steps,
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) := by
  let ideal := figureOneFinalScheduledIdealPhaseStart q I
  let phaseCost : ℕ → ENNReal := fun phase =>
    ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase)) : ℕ) : ENNReal)
  let _ : IsProbabilityMeasure
      (figureOneFinalScheduledIdealCountedInitial q I) := by
    unfold figureOneFinalScheduledIdealCountedInitial
    let _ : IsProbabilityMeasure
        (figureOneFinalScheduledIdealPhaseStart q I 0) :=
      figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I 0
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hreference := exists_countedReference_iteratedKernelLaw
    (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
    (figureOneFinalScheduledIdealCountedInitial q I) ideal
    (initialError := 0)
    (fun phase => figureOnePhaseSampleCount q (scheduleValue q phase) •
      figureOneCorrectedTransitionBudget q)
    phaseCost
    (fun phase => by
      let _ : IsProbabilityMeasure (ideal phase) :=
        figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I phase
      infer_instance)
    (by
      rw [figureOneFinalScheduledIdealCountedInitial_fst]
      exact MeasureLeUpTo.refl (ideal 0))
    (fun phase => by
      unfold figureOneFinalScheduledGaussianCountedKernel
      exact measurable_countedContinuation oracle.query _
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).1
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).2)
    (fun phase state => by
      unfold figureOneFinalScheduledGaussianCountedKernel countedContinuation
      let _ : IsProbabilityMeasure
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram
            q phase state.1).run oracle.query) :=
        MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
            q I oracle phase).2 state.1).executionMeasurable
      exact Measure.isProbabilityMeasure_map (by fun_prop))
    (fun phase rho _hrho hmarginal => by
      have hprogram :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have hnext : ideal (phase + 1) =
          (figureOneScheduledAcceptedTargetAt q I phase).map some := by
        simp [ideal, figureOneFinalScheduledIdealPhaseStart]
      apply MembershipOracleProgram.countedContinuation_step oracle.query rho
        (ideal phase) (ideal (phase + 1))
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)
        hprogram.1 hprogram.2 hmarginal
      · rw [hnext]
        exact figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
          q I oracle phase
      · exact figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
          q I oracle phase)
    steps
  obtain ⟨reference, hdom, hmarginal, hcost⟩ := hreference
  refine ⟨reference, ?_, hmarginal, ?_⟩
  · simpa using hdom
  · change countedQueryCost reference ≤
      countedQueryCost (figureOneFinalScheduledIdealCountedInitial q I) +
        ∑ phase ∈ Finset.range steps, phaseCost phase at hcost
    rw [figureOneFinalScheduledIdealCountedInitial_cost] at hcost
    exact hcost

/-- Exact-ideal counted law after all Gaussian phases and the terminal
Gaussian-to-uniform collector. -/
noncomputable def figureOneFinalScheduledIdealCompleteCountedLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Measure (Option (AmbientSpace q.n) × ℕ) :=
  (iteratedKernelLaw
      (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
      (figureOneFinalScheduledIdealCountedInitial q I)
      (terminalPhaseSteps q)).bind
    (countedContinuation oracle.query
      (figureOneFinalScheduledRetainedTerminalProgram q))

/-- Complete chronological reference from the exact ideal initializer.  Its
error omits the cheap rejected-initial branch. -/
theorem exists_figureOneFinalScheduledIdealCompleteCountedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        (figureOneFinalScheduledIdealCompleteCountedLaw q I oracle)
        reference
        (∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q) ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) +
          ((384 * (figureOneSampleCount q *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (terminalVariance q) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (terminalVariance q)) : ℕ) : ENNReal) := by
  obtain ⟨gaussianReference, hgaussianDom, hgaussianMarginal,
      hgaussianCost⟩ :=
    exists_figureOneFinalScheduledIdealGaussianCountedReference
      q I oracle (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable
      q I oracle
  let terminalContinuation := countedContinuation oracle.query
    (figureOneFinalScheduledRetainedTerminalProgram q)
  let reference := gaussianReference.bind terminalContinuation
  refine ⟨reference, ?_, ?_⟩
  · exact hgaussianDom.bind_same
      (measurable_countedContinuation oracle.query _ hterminal.1 hterminal.2)
      (fun state => by
        dsimp only [terminalContinuation, countedContinuation]
        let _ : IsProbabilityMeasure
            ((figureOneFinalScheduledRetainedTerminalProgram q state.1).run
              oracle.query) :=
          MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
            (hterminal.2 state.1).executionMeasurable
        exact Measure.isProbabilityMeasure_map (by fun_prop))
  · have hcostEq :=
      MembershipOracleProgram.countedQueryCost_bind_countedContinuation
        oracle.query gaussianReference
        (figureOneFinalScheduledRetainedTerminalProgram q)
        hterminal.1 hterminal.2
    change countedQueryCost reference ≤ _
    rw [hcostEq, hgaussianMarginal]
    exact add_le_add hgaussianCost
      (figureOneFinalScheduledTerminalIdealExpectedCost_le q I oracle)

/-- Counted execution of every remaining phase from one post-initial state,
with the initializer's single query already present in the count. -/
noncomputable def figureOneFinalScheduledCountedLawFromInitial
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (state : Option (AmbientSpace q.n)) :
    Measure (Option (AmbientSpace q.n) × ℕ) :=
  (iteratedKernelLaw
      (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
      (Measure.dirac (state, 1)) (terminalPhaseSteps q)).bind
    (countedContinuation oracle.query
      (figureOneFinalScheduledRetainedTerminalProgram q))

theorem figureOneFinalScheduledCountedLawFromInitial_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Measurable (figureOneFinalScheduledCountedLawFromInitial q I oracle) ∧
    ∀ state, IsProbabilityMeasure
      (figureOneFinalScheduledCountedLawFromInitial q I oracle state) := by
  let phaseK := figureOneFinalScheduledGaussianCountedKernel q oracle.query
  let terminalK := countedContinuation oracle.query
    (figureOneFinalScheduledRetainedTerminalProgram q)
  have hphaseMeas : ∀ phase, Measurable (phaseK phase) := fun phase => by
    unfold phaseK figureOneFinalScheduledGaussianCountedKernel
    exact measurable_countedContinuation oracle.query _
      (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
        q I oracle phase).1
      (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
        q I oracle phase).2
  have hphaseProb : ∀ phase state,
      IsProbabilityMeasure (phaseK phase state) := fun phase state => by
    unfold phaseK figureOneFinalScheduledGaussianCountedKernel
      countedContinuation
    let _ : IsProbabilityMeasure
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram
          q phase state.1).run oracle.query) :=
      MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).2 state.1).executionMeasurable
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have hterminalMeas : Measurable terminalK := by
    unfold terminalK
    exact measurable_countedContinuation oracle.query _ hterminal.1 hterminal.2
  have hterminalProb : ∀ state,
      IsProbabilityMeasure (terminalK state) := fun state => by
    unfold terminalK countedContinuation
    let _ : IsProbabilityMeasure
        ((figureOneFinalScheduledRetainedTerminalProgram q state.1).run
          oracle.query) :=
      MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
        (hterminal.2 state.1).executionMeasurable
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hiter := iteratedKernelLaw_dirac_measurable_and_probability
    phaseK hphaseMeas hphaseProb (terminalPhaseSteps q)
  constructor
  · change Measurable (fun state =>
      (iteratedKernelLaw phaseK (Measure.dirac (state, 1))
        (terminalPhaseSteps q)).bind terminalK)
    exact (Measure.measurable_bind' hterminalMeas).comp
      (hiter.1.comp (by fun_prop))
  · intro state
    change IsProbabilityMeasure
      ((iteratedKernelLaw phaseK (Measure.dirac (state, 1))
        (terminalPhaseSteps q)).bind terminalK)
    let _ : IsProbabilityMeasure
        (iteratedKernelLaw phaseK (Measure.dirac (state, 1))
          (terminalPhaseSteps q)) := hiter.2 (state, 1)
    exact MeasureTheory.isProbabilityMeasure_bind hterminalMeas.aemeasurable
      (ae_of_all _ hterminalProb)

/-- Averaging the pointwise post-initial execution is exactly kernel
iteration from the corresponding counted initial marginal. -/
theorem bind_figureOneFinalScheduledCountedLawFromInitial
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (mu : Measure (Option (AmbientSpace q.n))) :
    mu.bind (figureOneFinalScheduledCountedLawFromInitial q I oracle) =
      (iteratedKernelLaw
        (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
        (mu.map fun state => (state, 1)) (terminalPhaseSteps q)).bind
      (countedContinuation oracle.query
        (figureOneFinalScheduledRetainedTerminalProgram q)) := by
  let phaseK := figureOneFinalScheduledGaussianCountedKernel q oracle.query
  let terminalK := countedContinuation oracle.query
    (figureOneFinalScheduledRetainedTerminalProgram q)
  have hphaseMeas : ∀ phase, Measurable (phaseK phase) := fun phase => by
    unfold phaseK figureOneFinalScheduledGaussianCountedKernel
    exact measurable_countedContinuation oracle.query _
      (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
        q I oracle phase).1
      (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
        q I oracle phase).2
  have hphaseProb : ∀ phase state,
      IsProbabilityMeasure (phaseK phase state) := fun phase state => by
    unfold phaseK figureOneFinalScheduledGaussianCountedKernel
      countedContinuation
    let _ : IsProbabilityMeasure
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram
          q phase state.1).run oracle.query) :=
      MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).2 state.1).executionMeasurable
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have hterminalMeas : Measurable terminalK := by
    unfold terminalK
    exact measurable_countedContinuation oracle.query _ hterminal.1 hterminal.2
  have hiterMeas :=
    (iteratedKernelLaw_dirac_measurable_and_probability
      phaseK hphaseMeas hphaseProb (terminalPhaseSteps q)).1.comp
        (show Measurable (fun state : Option (AmbientSpace q.n) =>
          (state, 1)) by fun_prop)
  change mu.bind (fun state =>
      (iteratedKernelLaw phaseK (Measure.dirac (state, 1))
        (terminalPhaseSteps q)).bind terminalK) = _
  calc
    mu.bind (fun state =>
        (iteratedKernelLaw phaseK (Measure.dirac (state, 1))
          (terminalPhaseSteps q)).bind terminalK) =
        (mu.bind fun state =>
          iteratedKernelLaw phaseK (Measure.dirac (state, 1))
            (terminalPhaseSteps q)).bind terminalK :=
      (Measure.bind_bind hiterMeas.aemeasurable
        hterminalMeas.aemeasurable).symm
    _ = _ := by
      rw [bind_iteratedKernelLaw_dirac_eq_iteratedKernelLaw_map
        phaseK hphaseMeas hphaseProb mu (fun state => (state, 1))
          (by fun_prop) (terminalPhaseSteps q)]

theorem figureOneFinalScheduledRetainedCompleteProgram_run_eq_initial_bind
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query =
      ((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind
          (figureOneFinalScheduledCountedLawFromInitial q I oracle) := by
  have hinitial :=
    figureOneAbortInitialSample_countedStronglyMeasurable q I oracle
  have hprefix :=
    figureOneFinalScheduledRetainedGaussianPrefixProgram_countedMeasurable
      q I oracle (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  calc
    (figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query =
        (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          ((figureOneAbortInitialSample q).run oracle.query)
          (terminalPhaseSteps q)).bind
        (countedContinuation oracle.query
          (figureOneFinalScheduledRetainedTerminalProgram q)) := by
      unfold figureOneFinalScheduledRetainedCompleteProgram
      rw [MembershipOracleProgram.run_bind_counted oracle.query _ _
        hprefix hterminal.2 hterminal.1]
      rw [figureOneFinalScheduledRetainedGaussianPrefixProgram_run]
    _ = (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          (((initialGaussianSamplingMeasure q).map
            (initialTruncatedOption q I)).map fun state => (state, 1))
          (terminalPhaseSteps q)).bind
        (countedContinuation oracle.query
          (figureOneFinalScheduledRetainedTerminalProgram q)) := by
      rw [(figureOneAbortInitialSample_fixedQueryCount q).run_eq_map_runEstimate
        oracle.query (figureOneAbortInitialSample_stronglyMeasurable q I oracle)]
      rw [runEstimate_figureOneAbortInitialSample q I oracle]
    _ = ((initialGaussianSamplingMeasure q).map
          (initialTruncatedOption q I)).bind
            (figureOneFinalScheduledCountedLawFromInitial q I oracle) := by
      symm
      exact bind_figureOneFinalScheduledCountedLawFromInitial q I oracle _

theorem figureOneFinalScheduledGaussianCountedKernel_none
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool)
    (phase count : ℕ) :
    figureOneFinalScheduledGaussianCountedKernel q oracle phase (none, count) =
      Measure.dirac (none, count) := by
  unfold figureOneFinalScheduledGaussianCountedKernel countedContinuation
    figureOneFinalScheduledRetainedGaussianPhaseProgram
  simp only [MembershipOracleProgram.run]
  rw [Measure.map_dirac' (by fun_prop)]
  rfl

theorem iterated_figureOneFinalScheduledGaussianCountedKernel_none
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (count : ℕ) : ∀ steps,
    iteratedKernelLaw
      (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
      (Measure.dirac (none, count)) steps = Measure.dirac (none, count) := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, ih]
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle steps
      unfold figureOneFinalScheduledGaussianCountedKernel
      rw [Measure.dirac_bind (measurable_countedContinuation oracle.query _
        hphase.1 hphase.2)]
      exact figureOneFinalScheduledGaussianCountedKernel_none
        q oracle.query steps count

theorem figureOneFinalScheduledCountedLawFromInitial_none
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    figureOneFinalScheduledCountedLawFromInitial q I oracle none =
      Measure.dirac (none, 1) := by
  unfold figureOneFinalScheduledCountedLawFromInitial
  rw [iterated_figureOneFinalScheduledGaussianCountedKernel_none q I oracle]
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  rw [Measure.dirac_bind (measurable_countedContinuation oracle.query _
    hterminal.1 hterminal.2)]
  unfold countedContinuation figureOneFinalScheduledRetainedTerminalProgram
  simp only [MembershipOracleProgram.run]
  rw [Measure.map_dirac' (by fun_prop)]
  rfl

/-- The actual complete retained execution is dominated on the expensive
query-count event by the exact-ideal complete law, paying only the stationary
initial-target replacement.  The rejected Gaussian initializer contributes
zero because its count is exactly one. -/
theorem figureOneFinalScheduledRetainedComplete_expensive_le_ideal
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (budget : ℕ) (hbudget : 1 ≤ budget) :
    ((figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query)
        {outcome | budget < outcome.2} ≤
      figureOneFinalScheduledIdealCompleteCountedLaw q I oracle
          {outcome | budget < outcome.2} +
        scheduledBalancedStationaryTargetError q := by
  let E : Set (Option (AmbientSpace q.n) × ℕ) :=
    {outcome | budget < outcome.2}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (measurable_snd.comp measurable_id)
  have hfrom :=
    figureOneFinalScheduledCountedLawFromInitial_measurable_and_probability
      q I oracle
  have hnone :
      figureOneFinalScheduledCountedLawFromInitial q I oracle none E = 0 := by
    rw [figureOneFinalScheduledCountedLawFromInitial_none q I oracle]
    rw [Measure.dirac_apply' _ hE]
    simp only [E, Set.mem_ofPred_eq, Prod.snd]
    simp [not_lt_of_ge hbudget]
  have hcheap := initialTruncatedOption_bind_apply_le_of_none_zero
    q I (figureOneFinalScheduledCountedLawFromInitial q I oracle)
      hfrom.1 E hE hnone
  have hstationary := scheduledBalancedInitialRetained_leUpTo_target q I
  rw [map_scheduledBalancedInitialTrace_retainedOption] at hstationary
  have hstationaryComplete := hstationary.bind_same hfrom.1 hfrom.2
  have hstationaryEvent := hstationaryComplete.event_le E
  have hactual :
      ((figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query) E =
        ((initialGaussianSamplingMeasure q).map
          (initialTruncatedOption q I)).bind
            (figureOneFinalScheduledCountedLawFromInitial q I oracle) E := by
    rw [figureOneFinalScheduledRetainedCompleteProgram_run_eq_initial_bind]
  have hideal :
      ((figureOneFinalScheduledIdealPhaseStart q I 0).bind
        (figureOneFinalScheduledCountedLawFromInitial q I oracle)) =
          figureOneFinalScheduledIdealCompleteCountedLaw q I oracle := by
    rw [bind_figureOneFinalScheduledCountedLawFromInitial]
    rfl
  change ((figureOneFinalScheduledRetainedCompleteProgram q).run
    oracle.query) E ≤ _
  rw [hactual]
  calc
    (((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind
          (figureOneFinalScheduledCountedLawFromInitial q I oracle)) E ≤
        (((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some).bind
            (figureOneFinalScheduledCountedLawFromInitial q I oracle)) E :=
      hcheap
    _ ≤ ((figureOneFinalScheduledIdealPhaseStart q I 0).bind
          (figureOneFinalScheduledCountedLawFromInitial q I oracle)) E +
        scheduledBalancedStationaryTargetError q := hstationaryEvent
    _ = figureOneFinalScheduledIdealCompleteCountedLaw q I oracle E +
        scheduledBalancedStationaryTargetError q := by rw [hideal]

/-- A complete warm chronological reference for the actual cap event.  Its
runtime error contains stationary and phase replacements, but no initial
Gaussian tail. -/
theorem exists_figureOneFinalScheduledCheapAbortCapReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (budget : ℕ) (hbudget : 1 ≤ budget) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      ((figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query)
          {outcome | budget < outcome.2} ≤
        reference {outcome | budget < outcome.2} +
          (scheduledBalancedStationaryTargetError q +
            ∑ phase ∈ Finset.range (terminalPhaseSteps q),
              figureOnePhaseSampleCount q (scheduleValue q phase) •
                figureOneCorrectedTransitionBudget q) ∧
      countedQueryCost reference ≤
        ENNReal.ofReal ((9 * 10 ^ 29) *
          volumeScheduledBaseComplexityRate q) := by
  obtain ⟨reference, hdom, hcost⟩ :=
    exists_figureOneFinalScheduledIdealCompleteCountedReference q I oracle
  refine ⟨reference, ?_, hcost.trans
    (figureOneFinalScheduledRetainedCompleteCostEnvelope_le q)⟩
  let E : Set (Option (AmbientSpace q.n) × ℕ) :=
    {outcome | budget < outcome.2}
  have hactual :=
    figureOneFinalScheduledRetainedComplete_expensive_le_ideal
      q I oracle budget hbudget
  have hideal := hdom.event_le E
  change ((figureOneFinalScheduledRetainedCompleteProgram q).run
      oracle.query) E ≤ reference E + _
  calc
    ((figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query) E ≤
        figureOneFinalScheduledIdealCompleteCountedLaw q I oracle E +
          scheduledBalancedStationaryTargetError q := hactual
    _ ≤ (reference E +
          ∑ phase ∈ Finset.range (terminalPhaseSteps q),
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) +
        scheduledBalancedStationaryTargetError q := by gcongr
    _ = reference E +
        (scheduledBalancedStationaryTargetError q +
          ∑ phase ∈ Finset.range (terminalPhaseSteps q),
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) := by
      ac_rfl

/-- Unconditional global-query-cap failure bound for the actual final
scheduled aborting base program. -/
theorem figureOneFinalScheduledAbortQueryCap_failure_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap
        (figureOneFinalScheduledQueryBudget q)).runEstimate oracle.query
          {none} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let budget := figureOneFinalScheduledQueryBudget q
  let delta := scheduledBalancedStationaryTargetError q +
    ∑ phase ∈ Finset.range (terminalPhaseSteps q),
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q
  have hbudgetNat : 1 ≤ budget := figureOneFinalScheduledQueryBudget_pos q
  obtain ⟨reference, hactualTail, href⟩ :=
    exists_figureOneFinalScheduledCheapAbortCapReference
      q I oracle budget hbudgetNat
  let tail := reference {outcome | budget < outcome.2}
  let base := ENNReal.ofReal
    (figureOneFinalScheduledExpectedCostConstant *
      volumeScheduledBaseComplexityRate q)
  have hbase0 : base ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr <|
      mul_pos figureOneFinalScheduledExpectedCostConstant_pos
        (volumeScheduledBaseComplexityRate_pos q)
  have hbaseTop : base ≠ ∞ := ENNReal.ofReal_ne_top
  have hbudget : ENNReal.ofReal (64 : ℝ) * base ≤
      (budget + 1 : ENNReal) := by
    have hceil : 64 * figureOneFinalScheduledExpectedCostConstant *
        volumeScheduledBaseComplexityRate q ≤ (budget : ℝ) := by
      simpa [budget, figureOneFinalScheduledQueryBudget,
        globalQueryBudgetOfRate] using Nat.le_ceil
          (64 * figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q)
    have h := ENNReal.ofReal_le_ofReal hceil
    rw [ENNReal.ofReal_natCast] at h
    calc
      ENNReal.ofReal (64 : ℝ) * base =
          ENNReal.ofReal (64 *
            (figureOneFinalScheduledExpectedCostConstant *
              volumeScheduledBaseComplexityRate q)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      _ = ENNReal.ofReal (64 *
          figureOneFinalScheduledExpectedCostConstant *
            volumeScheduledBaseComplexityRate q) := by ring_nf
      _ ≤ (budget : ENNReal) := h
      _ ≤ (budget + 1 : ENNReal) := by
        exact_mod_cast Nat.le_add_right budget 1
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun outcome : Option (AmbientSpace q.n) × ℕ =>
      (outcome.2 : ENNReal) by fun_prop)
    (budget + 1 : ENNReal) (μ := reference)
  have hevent : ({outcome : Option (AmbientSpace q.n) × ℕ |
      budget < outcome.2}) =
      {outcome | (budget + 1 : ENNReal) ≤ (outcome.2 : ENNReal)} := by
    ext outcome
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast Nat.add_one_le_iff
  rw [← hevent] at hmarkov
  have hwarmEq : ENNReal.ofReal ((9 * 10 ^ 29) *
      volumeScheduledBaseComplexityRate q) =
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    rw [← ENNReal.ofReal_mul
      (by positivity [figureOneFinalScheduledExpectedCostConstant_pos,
        volumeScheduledBaseComplexityRate_pos q] :
        0 ≤ figureOneFinalScheduledExpectedCostConstant *
          volumeScheduledBaseComplexityRate q)]
    congr 1
    simp only [figureOneFinalScheduledExpectedCostConstant]
    ring
  have hscaled : base * (tail * ENNReal.ofReal (64 : ℝ)) ≤
      base * ENNReal.ofReal (9 / 10 : ℝ) := by
    calc
      base * (tail * ENNReal.ofReal (64 : ℝ)) =
          (ENNReal.ofReal (64 : ℝ) * base) * tail := by ring
      _ ≤ (budget + 1 : ENNReal) * tail := by gcongr
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference := hmarkov
      _ ≤ ENNReal.ofReal ((9 * 10 ^ 29) *
          volumeScheduledBaseComplexityRate q) := href
      _ = base * ENNReal.ofReal (9 / 10 : ℝ) := hwarmEq
  have htailScaled : tail * ENNReal.ofReal (64 : ℝ) ≤
      ENNReal.ofReal (9 / 10 : ℝ) := by
    have hdiv : tail * ENNReal.ofReal (64 : ℝ) ≤
        (base * ENNReal.ofReal (9 / 10 : ℝ)) / base :=
      (ENNReal.le_div_iff_mul_le (Or.inl hbase0)
        (Or.inl hbaseTop)).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hcancel : (base * ENNReal.ofReal (9 / 10 : ℝ)) / base =
        ENNReal.ofReal (9 / 10 : ℝ) := by
      rw [ENNReal.div_eq_inv_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hbase0 hbaseTop, one_mul]
    simpa only [hcancel] using hdiv
  have htail : tail ≤ ENNReal.ofReal (9 / 640 : ℝ) := by
    have h := (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)).2 htailScaled
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)] at h
    norm_num at h
    exact h
  have hdelta : delta ≤ ENNReal.ofReal (1 / 640 : ℝ) := by
    calc
      delta ≤ ENNReal.ofReal (1 / 1280 : ℝ) :=
        figureOneFinalScheduledCountReferenceError_le q
      _ ≤ ENNReal.ofReal (1 / 640 : ℝ) := by norm_num
  have hcountEvent : MeasurableSet {count : ℕ | budget < count} :=
    measurableSet_lt measurable_const measurable_id
  have hpairEvent : MeasurableSet
      {outcome : Option (AmbientSpace q.n) × ℕ | budget < outcome.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hcountLaw :=
    figureOneFinalScheduledRetainedCompleteProgram_map_snd_eq_abortBase
      q I oracle
  have hcountEventEq := congrArg
    (fun μ : Measure ℕ => μ {count | budget < count}) hcountLaw
  rw [Measure.map_apply measurable_snd hcountEvent,
    Measure.map_apply measurable_snd hcountEvent] at hcountEventEq
  have hcap :=
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate_withQueryCap_apply_none
      oracle.query budget
      (figureOneFinalScheduledAbortBaseProgram_countedStronglyMeasurable
        q I oracle).executionMeasurable
  change ((figureOneFinalScheduledAbortBaseProgram q).withQueryCap budget).runEstimate
      oracle.query {none} ≤ _
  rw [hcap]
  calc
    (figureOneFinalScheduledAbortBaseProgram q).run oracle.query
        {outcome | budget < outcome.2} =
      (figureOneFinalScheduledRetainedCompleteProgram q).run oracle.query
        {outcome | budget < outcome.2} := hcountEventEq.symm
    _ ≤ tail + delta := hactualTail
    _ ≤ ENNReal.ofReal (9 / 640 : ℝ) +
        ENNReal.ofReal (1 / 640 : ℝ) := add_le_add htail hdelta
    _ = ENNReal.ofReal (1 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 9 / 640)
        (by norm_num : (0 : ℝ) ≤ 1 / 640)]
      congr 1
      norm_num

#print axioms figureOneFinalScheduledAbortQueryCap_failure_le

end ArlibCommunity.Algorithms.CV18
