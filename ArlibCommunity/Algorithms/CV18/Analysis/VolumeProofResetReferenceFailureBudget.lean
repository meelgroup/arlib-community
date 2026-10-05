/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalTraceDeviation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortAccuracy
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledIdealPhase

/-!
# Final failure budget for a chronological reset reference

The reference-side form of CV18 Lemma 7.15 spends `11/64`.  This module
packages the remaining ENNReal arithmetic: every within-phase fixed-reset
error over all Gaussian phases and the terminal phase is bounded at once,
and a final mapped-law comparison plus initial abort charge fits below
`13/64`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Sum of fixed-reset errors for all Gaussian collectors and the terminal
uniform collector. -/
noncomputable def figureOneScheduledGlobalResetReferenceError
    (q : VolumeParams) : ENNReal :=
  (∑ phase ∈ Finset.range (terminalPhaseSteps q),
      scheduledResetReferenceError q
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) +
    scheduledResetReferenceError q (figureOneSampleCount q - 1)

/-- ENNReal form of the one-step fixed-reset envelope. -/
theorem scheduledRetainedEndpointError_one_le_ofReal
    (q : VolumeParams) :
    scheduledRetainedEndpointError q 1 ≤
      ENNReal.ofReal
        ((3 / 2 : ℝ) * figureOnePerSampleMixingError q) := by
  rw [← ENNReal.toReal_le_toReal
    (scheduledRetainedEndpointError_ne_top q 1) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
    (figureOnePerSampleMixingError_pos q).le)]
  simpa only [mul_assoc] using
    scheduledRetainedEndpointError_one_toReal_le q

/-- The global reset error is bounded by `3/2` times the complete
sample-by-phase exact-chance count. -/
theorem figureOneScheduledGlobalResetReferenceError_le_count
    (q : VolumeParams) :
    figureOneScheduledGlobalResetReferenceError q ≤
      (figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q) •
          ENNReal.ofReal
            ((3 / 2 : ℝ) * figureOnePerSampleMixingError q) := by
  let endpoint := scheduledRetainedEndpointError q 1
  let maxSamples := figureOneDependentMaxSampleCount q
  have hphase : ∀ phase,
      scheduledResetReferenceError q
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) ≤
        maxSamples • endpoint := by
    intro phase
    rw [scheduledResetReferenceError_eq_nsmul]
    exact nsmul_le_nsmul_left (bot_le : 0 ≤ endpoint) <|
      (Nat.sub_le _ _).trans
        (figureOnePhaseSampleCount_le_dependentMax
          q (scheduleValue q phase))
  have hterminal :
      scheduledResetReferenceError q (figureOneSampleCount q - 1) ≤
        maxSamples • endpoint := by
    rw [scheduledResetReferenceError_eq_nsmul]
    exact nsmul_le_nsmul_left (bot_le : 0 ≤ endpoint) <|
      (Nat.sub_le _ _).trans (figureOneTerminalSampleCount_le_dependentMax q)
  have hsum :
      (∑ phase ∈ Finset.range (terminalPhaseSteps q),
        scheduledResetReferenceError q
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) ≤
      ∑ _phase ∈ Finset.range (terminalPhaseSteps q),
        maxSamples • endpoint := by
    exact Finset.sum_le_sum fun phase hmem => hphase phase
  calc
    figureOneScheduledGlobalResetReferenceError q ≤
        (∑ _phase ∈ Finset.range (terminalPhaseSteps q),
          maxSamples • endpoint) + maxSamples • endpoint :=
      add_le_add hsum hterminal
    _ = (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q) • endpoint := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        figureOneDependentPhaseCount, maxSamples, endpoint]
      push_cast
      ring
    _ ≤ (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q) •
            ENNReal.ofReal
              ((3 / 2 : ℝ) * figureOnePerSampleMixingError q) :=
      nsmul_le_nsmul_right
        (scheduledRetainedEndpointError_one_le_ofReal q) _

/-- Numerically, the complete chronological fixed-reset construction costs
at most `3/2560`, far below the event-transfer reserve. -/
theorem figureOneScheduledGlobalResetReferenceError_le
    (q : VolumeParams) :
    figureOneScheduledGlobalResetReferenceError q ≤
      ENNReal.ofReal (3 / 2560 : ℝ) := by
  let samples := figureOneDependentMaxSampleCount q *
    figureOneDependentPhaseCount q
  let base := samples • ENNReal.ofReal (figureOnePerSampleMixingError q)
  have hbase : base ≤ ENNReal.ofReal (1 / 1280 : ℝ) := by
    simpa [base, samples] using figureOne_exactChance_countReference_budget_le q
  have hglobal := figureOneScheduledGlobalResetReferenceError_le_count q
  have hrewrite :
      samples • ENNReal.ofReal
          ((3 / 2 : ℝ) * figureOnePerSampleMixingError q) =
        ENNReal.ofReal (3 / 2 : ℝ) * base := by
    simp only [base, samples, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    ring
  rw [hrewrite] at hglobal
  calc
    figureOneScheduledGlobalResetReferenceError q ≤
        ENNReal.ofReal (3 / 2 : ℝ) * base := hglobal
    _ ≤ ENNReal.ofReal (3 / 2 : ℝ) *
        ENNReal.ofReal (1 / 1280 : ℝ) := mul_le_mul' le_rfl hbase
    _ = ENNReal.ofReal (3 / 2560 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      congr 1
      norm_num

/-- The already-assembled retained boundary/death replacement envelope fits
the larger reserve used by the final event capstone. -/
theorem figureOneFinalScheduledCountReferenceError_le_boundaryReserve
    (q : VolumeParams) :
    scheduledBalancedStationaryTargetError q +
        ∑ phase ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q ≤
      ENNReal.ofReal (1 / 128 : ℝ) := by
  exact (figureOneFinalScheduledCountReferenceError_le q).trans
    (ENNReal.ofReal_le_ofReal (by norm_num))

/-- The initial abort/fallback accuracy charge has its canonical `1/64`
envelope. -/
theorem figureOneInitialAbortAccuracyError_le (q : VolumeParams) :
    ENNReal.ofReal (q.eps / 64) ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  exact ENNReal.ofReal_le_ofReal (by linarith [q.heps.2])

/-! ## Final ENNReal aggregation -/

/-- Numerical post-initial budget: Lemma 7.15's `11/64`, every reset, and
a generous `1/128` combined boundary/death envelope remain below `3/16`. -/
theorem figureOne_resetReference_postInitial_budget :
    ENNReal.ofReal (11 / 64 : ℝ) +
          ENNReal.ofReal (3 / 2560 : ℝ) +
        ENNReal.ofReal (1 / 128 : ℝ) ≤
      ENNReal.ofReal (3 / 16 : ℝ) := by
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 11 / 64)
    (by norm_num : (0 : ℝ) ≤ 3 / 2560)]
  rw [← ENNReal.ofReal_add (by norm_num :
    (0 : ℝ) ≤ 11 / 64 + 3 / 2560)
    (by norm_num : (0 : ℝ) ≤ 1 / 128)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Numerical full-base budget after the initial aborting truncation charge. -/
theorem figureOne_resetReference_base_budget :
    (ENNReal.ofReal (11 / 64 : ℝ) +
            ENNReal.ofReal (3 / 2560 : ℝ) +
          ENNReal.ofReal (1 / 128 : ℝ)) +
        ENNReal.ofReal (1 / 64 : ℝ) ≤
      ENNReal.ofReal (13 / 64 : ℝ) := by
  calc
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) +
        ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add figureOne_resetReference_postInitial_budget le_rfl
    _ = ENNReal.ofReal (13 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 16)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

/-- The reset error together with the full boundary/death reserve fits the
legacy `1/64` mapped-product interface exactly. -/
theorem figureOneScheduledGlobalReset_add_boundary_le_transferBudget
    (q : VolumeParams) {boundary : ENNReal}
    (hboundary : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ)) :
    figureOneScheduledGlobalResetReferenceError q + boundary ≤
      ENNReal.ofReal (1 / 64 : ℝ) := by
  calc
    figureOneScheduledGlobalResetReferenceError q + boundary ≤
        ENNReal.ofReal (3 / 2560 : ℝ) +
          ENNReal.ofReal (1 / 128 : ℝ) :=
      add_le_add (figureOneScheduledGlobalResetReferenceError_le q) hboundary
    _ = ENNReal.ofReal (23 / 2560 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 2560)
        (by norm_num : (0 : ℝ) ≤ 1 / 128)]
      congr 1
      norm_num
    _ ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
      ENNReal.ofReal_le_ofReal (by norm_num)

/-- Upgrade a concrete global trace/reference comparison to the existing
mapped-product `1/64` consumer after separately bounding its boundary/death
part. -/
theorem MeasureLeUpTo.mono_resetReference_finalTransfer
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) {actual reference : Measure Omega}
    {error boundary : ENNReal}
    (hcomparison : MeasureLeUpTo actual reference error)
    (herror : error ≤
      figureOneScheduledGlobalResetReferenceError q + boundary)
    (hboundary : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ)) :
    MeasureLeUpTo actual reference (ENNReal.ofReal (1 / 64 : ℝ)) :=
  hcomparison.mono_error <| herror.trans
    (figureOneScheduledGlobalReset_add_boundary_le_transferBudget q hboundary)

/-- Event-level post-initial capstone.  A single global trace/reference MLU
comparison transports the `11/64` reference tail.  The complete reset sum
and any already-assembled boundary/death error fitting `1/128` leave the
standard `3/16` post-initial budget. -/
theorem MeasureLeUpTo.event_add_boundary_le_three_sixteenths
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) {actual reference : Measure Omega}
    {error boundary : ENNReal} {event : Set Omega}
    (hcomparison : MeasureLeUpTo actual reference error)
    (href : reference event ≤ ENNReal.ofReal (11 / 64 : ℝ))
    (herror : error ≤ figureOneScheduledGlobalResetReferenceError q)
    (hboundary : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ)) :
    actual event + boundary ≤ ENNReal.ofReal (3 / 16 : ℝ) := by
  have hevent := hcomparison.event_le event
  calc
    actual event + boundary ≤
        (reference event + error) + boundary := add_le_add hevent le_rfl
    _ ≤ (ENNReal.ofReal (11 / 64 : ℝ) +
          ENNReal.ofReal (3 / 2560 : ℝ)) +
        ENNReal.ofReal (1 / 128 : ℝ) := by
      exact add_le_add
        (add_le_add href
          (herror.trans (figureOneScheduledGlobalResetReferenceError_le q)))
        hboundary
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) :=
      figureOne_resetReference_postInitial_budget

/-- Full uncapped-base arithmetic, with the initial abort/fallback charge
kept explicit.  This is the numerical interface needed after identifying the
base program's bad event with the transported post-initial event. -/
theorem MeasureLeUpTo.event_add_boundary_abort_le_thirteen_sixtyfour
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) {actual reference : Measure Omega}
    {error boundary abort : ENNReal} {event : Set Omega}
    (hcomparison : MeasureLeUpTo actual reference error)
    (href : reference event ≤ ENNReal.ofReal (11 / 64 : ℝ))
    (herror : error ≤ figureOneScheduledGlobalResetReferenceError q)
    (hboundary : boundary ≤ ENNReal.ofReal (1 / 128 : ℝ))
    (habort : abort ≤ ENNReal.ofReal (1 / 64 : ℝ)) :
    (actual event + boundary) + abort ≤
      ENNReal.ofReal (13 / 64 : ℝ) := by
  calc
    (actual event + boundary) + abort ≤
        ENNReal.ofReal (3 / 16 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add
        (hcomparison.event_add_boundary_le_three_sixteenths
          q href herror hboundary) habort
    _ = ENNReal.ofReal (13 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 16)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

#print axioms scheduledRetainedEndpointError_one_le_ofReal
#print axioms figureOneScheduledGlobalResetReferenceError_le_count
#print axioms figureOneScheduledGlobalResetReferenceError_le
#print axioms
  figureOneFinalScheduledCountReferenceError_le_boundaryReserve
#print axioms figureOneInitialAbortAccuracyError_le
#print axioms figureOne_resetReference_postInitial_budget
#print axioms figureOne_resetReference_base_budget
#print axioms
  figureOneScheduledGlobalReset_add_boundary_le_transferBudget
#print axioms MeasureLeUpTo.mono_resetReference_finalTransfer
#print axioms MeasureLeUpTo.event_add_boundary_le_three_sixteenths
#print axioms
  MeasureLeUpTo.event_add_boundary_abort_le_thirteen_sixtyfour

end


end ArlibCommunity.Algorithms.CV18
