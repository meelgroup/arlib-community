/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceFailureBudget

/-!
# Local outer-reset dependence budget

The chronological recurrence proves cross-phase dependence locally.  Its
independence calculation pays two copies of the operational transition
error and then the standard factor-three perturbation cost for the
transition-plus-fixed-reset comparison.  The accepted-endpoint reset is not
present: it preserves the complete score-history law.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- Five individual transition budgets fit within the global coefficient
selected for Lemma 7.17(c). -/
theorem five_mul_figureOnePerSampleMixingError_le_dependentEpsilon
    (q : VolumeParams) :
    5 * figureOnePerSampleMixingError q ≤
      figureOneDependentEpsilon q := by
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hsampleLower := figureOneSampleCount_cast_lower q
  have hlog : (1 : ℝ) ≤ protectedLog (terminalVariance q) :=
    le_max_left _ _
  have hepsSqPos : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have hepsSqOne : q.eps ^ 2 ≤ 1 := by
    nlinarith [q.heps.1, q.heps.2]
  have htwoSampleReal : (2 : ℝ) ≤ figureOneSampleCount q := by
    apply le_trans (b :=
      512 * protectedLog (terminalVariance q) / q.eps ^ 2)
    · rw [le_div_iff₀ hepsSqPos]
      nlinarith
    · exact hsampleLower
  have htwoMax : (2 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact htwoSampleReal.trans <| by
      exact_mod_cast (le_max_right
        (figureOneFixedSampleCount q) (figureOneSampleCount q))
  have hphase : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hmax0 : (0 : ℝ) ≤ figureOneDependentMaxSampleCount q := by positivity
  have hmaxPhase :
      (figureOneDependentMaxSampleCount q : ℝ) ≤
        figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hphase hmax0
  have hfactor : (5 : ℝ) ≤
      3 * figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hfactor hnu.le
  rw [figureOne_lemma717c_budget q] at hscaled
  exact hscaled

/-- Six individual transition budgets also fit: there are at least two
chronological phases and at least one sample in the uniform bound. -/
theorem six_mul_figureOnePerSampleMixingError_le_dependentEpsilon
    (q : VolumeParams) :
    6 * figureOnePerSampleMixingError q ≤
      figureOneDependentEpsilon q := by
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hmax : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hphase : (2 : ℝ) ≤ figureOneDependentPhaseCount q := by
    rw [figureOneDependentPhaseCount]
    exact_mod_cast Nat.succ_le_succ (terminalPhaseSteps_pos q)
  have hproduct : (2 : ℝ) ≤
      figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q := by
    have := mul_le_mul hmax hphase (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ figureOneDependentMaxSampleCount q)
    simpa only [one_mul] using this
  have hfactor : (6 : ℝ) ≤
      3 * figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hfactor hnu.le
  rw [figureOne_lemma717c_budget q] at hscaled
  exact hscaled

/-- Exact local coefficient used by the outer chronological reset step.  A
phase with at most the global maximum number of samples fits in the `5/2`
reference-side Lemma 7.17(c) allowance. -/
theorem figureOne_localTransitionReset_dependence_le
    (q : VolumeParams) {count : ℕ}
    (hcount : count ≤ figureOneDependentMaxSampleCount q) :
    (2 * figureOneCorrectedTransitionBudget q).toReal +
        3 * (figureOneCorrectedTransitionBudget q +
          scheduledResetReferenceError q (count - 1)).toReal ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
  let delta := figureOneCorrectedTransitionBudget q
  let reset := scheduledResetReferenceError q (count - 1)
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hdeltaTop : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have hresetTop : reset ≠ ⊤ := by
    exact scheduledResetReferenceError_ne_top q (count - 1)
  have hresetTransport := scheduledResetReference_transportEpsilon_le
    q hcount
  have hfive :=
    five_mul_figureOnePerSampleMixingError_le_dependentEpsilon q
  change (2 * delta).toReal + 3 * (delta + reset).toReal ≤ _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hdeltaTop hresetTop]
  simp only [delta, figureOneCorrectedTransitionBudget,
    ENNReal.toReal_ofReal hnu.le]
  dsimp only [reset] at hresetTransport ⊢
  nlinarith

/-- One-stage accepted-pair form of the local coefficient.  The endpoint
reset's stationary-target error occurs in the law comparison, but it does
not change the score-history law.  Even if it is retained syntactically
inside the perturbation term, the same `5/2` coefficient still suffices. -/
theorem figureOne_localTransitionResetStationary_dependence_le
    (q : VolumeParams) {count : ℕ}
    (hcount : count ≤ figureOneDependentMaxSampleCount q) :
    (2 * figureOneCorrectedTransitionBudget q).toReal +
        3 * (figureOneCorrectedTransitionBudget q +
          scheduledResetReferenceError q (count - 1) +
            scheduledBalancedStationaryTargetError q).toReal ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
  let delta := figureOneCorrectedTransitionBudget q
  let reset := scheduledResetReferenceError q (count - 1)
  let stationary := scheduledBalancedStationaryTargetError q
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have hdeltaTop : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have hresetTop : reset ≠ ⊤ :=
    scheduledResetReferenceError_ne_top q (count - 1)
  have hdeltaResetTop : delta + reset ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hdeltaTop, hresetTop⟩
  have htargetTop : figureOneCorrectedTargetBudget q ≠ ⊤ :=
    ENNReal.div_ne_top hdeltaTop (by norm_num)
  have hstationaryTop : stationary ≠ ⊤ :=
    ne_top_of_le_ne_top htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
  have hstationaryReal : stationary.toReal ≤
      figureOnePerSampleMixingError q / 4 := by
    have hreal := ENNReal.toReal_mono htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
    simpa [stationary, figureOneCorrectedTargetBudget, delta,
      figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hnu.le] using hreal
  have hresetTransport := scheduledResetReference_transportEpsilon_le
    q hcount
  have hsix :=
    six_mul_figureOnePerSampleMixingError_le_dependentEpsilon q
  change (2 * delta).toReal + 3 * (delta + reset + stationary).toReal ≤ _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hdeltaResetTop hstationaryTop,
    ENNReal.toReal_add hdeltaTop hresetTop]
  simp only [delta, figureOneCorrectedTransitionBudget,
    ENNReal.toReal_ofReal hnu.le]
  dsimp only [reset, stationary] at hresetTransport hstationaryReal ⊢
  nlinarith

/-! ## Global law-comparison split -/

/-- The complete outer law-comparison error before rearranging reset and
boundary terms: one initial accepted-target correction, every Gaussian
transition/reset/endpoint step, and the terminal transition/reset step. -/
noncomputable def figureOneScheduledGlobalOuterStepError
    (q : VolumeParams) : ENNReal :=
  scheduledBalancedStationaryTargetError q +
    (∑ phase ∈ Finset.range (terminalPhaseSteps q),
      ((figureOneCorrectedTransitionBudget q +
          scheduledResetReferenceError q
            (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) +
        scheduledBalancedStationaryTargetError q)) +
      (figureOneCorrectedTransitionBudget q +
        scheduledResetReferenceError q (figureOneSampleCount q - 1))

/-- Both phase-sensitive sample counts are at least three. -/
theorem figureOnePhaseSampleCount_three_le
    (q : VolumeParams) (sigma2 : ℝ) :
    3 ≤ figureOnePhaseSampleCount q sigma2 := by
  have hlogTerminal : (1 : ℝ) ≤ protectedLog (terminalVariance q) :=
    le_max_left _ _
  have hlogFixed : (1 : ℝ) ≤
      protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
  have hepsSqPos : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have hepsSqOne : q.eps ^ 2 ≤ 1 := by
    nlinarith [q.heps.1, q.heps.2]
  have hsample : (3 : ℝ) ≤ figureOneSampleCount q := by
    apply le_trans (b :=
      512 * protectedLog (terminalVariance q) / q.eps ^ 2)
    · rw [le_div_iff₀ hepsSqPos]
      nlinarith
    · exact figureOneSampleCount_cast_lower q
  have hfixed : (3 : ℝ) ≤ figureOneFixedSampleCount q := by
    apply le_trans (b :=
      4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)
    · rw [le_div_iff₀ hepsSqPos]
      nlinarith
    · exact figureOneFixedSampleCount_cast_lower q
  unfold figureOnePhaseSampleCount
  split_ifs
  · exact_mod_cast hfixed
  · exact_mod_cast hsample

/-- The global outer comparison splits into the fixed-reset sum plus exactly
the already-established transition/death boundary envelope. -/
theorem figureOneScheduledGlobalOuterStepError_le_reset_add_boundary
    (q : VolumeParams) :
    figureOneScheduledGlobalOuterStepError q ≤
      figureOneScheduledGlobalResetReferenceError q +
        (scheduledBalancedStationaryTargetError q +
          ∑ phase ∈ Finset.range (terminalPhaseSteps q),
            figureOnePhaseSampleCount q (scheduleValue q phase) •
              figureOneCorrectedTransitionBudget q) := by
  let steps := terminalPhaseSteps q
  let delta := figureOneCorrectedTransitionBudget q
  let stationary := scheduledBalancedStationaryTargetError q
  let reset : ℕ → ENNReal := fun phase =>
    scheduledResetReferenceError q
      (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
  let terminalReset :=
    scheduledResetReferenceError q (figureOneSampleCount q - 1)
  have hstationary : stationary ≤ delta :=
    (scheduledBalancedStationaryTargetError_le_targetBudget q).trans <| by
      unfold figureOneCorrectedTargetBudget
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      simpa only [one_mul, mul_comm] using
        mul_le_mul_left (by norm_num : (1 : ENNReal) ≤ (4 : ENNReal)) delta
  have hphaseCount : ∀ phase, phase ∈ Finset.range steps →
      3 ≤ figureOnePhaseSampleCount q (scheduleValue q phase) := by
    intro phase hphase
    exact figureOnePhaseSampleCount_three_le q _
  have hnonreset :
      (∑ _phase ∈ Finset.range steps, (delta + stationary)) + delta ≤
        ∑ phase ∈ Finset.range steps,
          figureOnePhaseSampleCount q (scheduleValue q phase) • delta := by
    have hdeltaSteps : delta ≤ steps • delta := by
      have hsteps : 1 ≤ steps := by
        exact terminalPhaseSteps_pos q
      simpa only [one_nsmul] using
        nsmul_le_nsmul_left (bot_le : (0 : ENNReal) ≤ delta) hsteps
    have hleft :
        (∑ _phase ∈ Finset.range steps, (delta + stationary)) + delta ≤
          ∑ _phase ∈ Finset.range steps, (3 • delta) := by
      calc
        (∑ _phase ∈ Finset.range steps, (delta + stationary)) + delta ≤
            (∑ _phase ∈ Finset.range steps, (2 • delta)) + delta := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro phase hphase
          simpa only [two_nsmul] using add_le_add le_rfl hstationary
        _ ≤ (∑ _phase ∈ Finset.range steps, (2 • delta)) + steps • delta :=
          add_le_add_right hdeltaSteps _
        _ = ∑ _phase ∈ Finset.range steps, (3 • delta) := by
          simp only [Finset.sum_const, Finset.card_range]
          rw [← nsmul_add]
          simp only [two_nsmul, three_nsmul, add_assoc]
    exact hleft.trans <| Finset.sum_le_sum fun phase hphase =>
      nsmul_le_nsmul_left (bot_le : 0 ≤ delta) (hphaseCount phase hphase)
  unfold figureOneScheduledGlobalOuterStepError
  change stationary +
      (∑ phase ∈ Finset.range steps, ((delta + reset phase) + stationary)) +
        (delta + terminalReset) ≤ _
  rw [show figureOneScheduledGlobalResetReferenceError q =
      (∑ phase ∈ Finset.range steps, reset phase) + terminalReset by rfl]
  have hsumRearrange :
      (∑ phase ∈ Finset.range steps,
          ((delta + reset phase) + stationary)) =
        ∑ phase ∈ Finset.range steps,
          (reset phase + (delta + stationary)) := by
    refine Finset.sum_congr
      (s₁ := Finset.range steps) (s₂ := Finset.range steps)
      (f := fun phase => (delta + reset phase) + stationary)
      (g := fun phase => reset phase + (delta + stationary)) rfl ?_
    intro phase hphase
    ac_rfl
  have hsumSplit :
      (∑ phase ∈ Finset.range steps,
          (reset phase + (delta + stationary))) =
        (∑ phase ∈ Finset.range steps, reset phase) +
          ∑ _phase ∈ Finset.range steps, (delta + stationary) := by
    exact Finset.sum_add_distrib
  calc
    stationary +
          (∑ phase ∈ Finset.range steps, ((delta + reset phase) + stationary)) +
        (delta + terminalReset) =
      ((∑ phase ∈ Finset.range steps, reset phase) + terminalReset) +
        (stationary +
          ((∑ _phase ∈ Finset.range steps, (delta + stationary)) + delta)) := by
      rw [hsumRearrange, hsumSplit]
      ac_rfl
    _ ≤ ((∑ phase ∈ Finset.range steps, reset phase) + terminalReset) +
        (stationary +
          ∑ phase ∈ Finset.range steps,
            figureOnePhaseSampleCount q (scheduleValue q phase) • delta) := by
      exact add_le_add_right (add_le_add_right hnonreset stationary) _

#print axioms
  figureOne_localTransitionResetStationary_dependence_le
#print axioms figureOnePhaseSampleCount_three_le
#print axioms
  figureOneScheduledGlobalOuterStepError_le_reset_add_boundary

#print axioms
  five_mul_figureOnePerSampleMixingError_le_dependentEpsilon
#print axioms figureOne_localTransitionReset_dependence_le

end

end ArlibCommunity.Algorithms.CV18
