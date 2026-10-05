/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorWarmCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutableHistory

/-! # Expected cost from an approximate optional phase-start law -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- A `MeasureLeUpTo` approximation of an optional phase-start law is enough
for the sharp warm-start cost bound.  The live target is scaled exactly as in
the executable collector; only the positive error measure is charged at the
syntactic local query cap. -/
theorem lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    {M error : ENNReal}
    (mu : Measure (Option (AmbientSpace q.n)))
    (target : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure target]
    (happrox : MeasureLeUpTo mu (target.map some) error)
    (hwarm : _root_.Arlib.IsWarm M
      (target.map fun point => accuracyScaleFactor q • point)
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hM : M ≤ 96)
    (proposalCap properStride retryLimit samples : ℕ)
    (hstride : 0 < properStride) :
    ∫⁻ state, match state with
        | none => 0
        | some point => countedQueryCost
            ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
              properStride retryLimit samples
              (accuracyScaleFactor q • point)).run oracle.query)
      ∂mu ≤
      ((384 * (samples * retryLimit * properStride) : ℕ) : ENNReal) +
        ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) * error := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun point =>
    accuracyScaleFactor q • point
  let cost : AmbientSpace q.n → ENNReal := fun current => countedQueryCost
    ((scheduledBalancedAccuracyRetryCollect q sigma2 weight proposalCap
      properStride retryLimit samples current).run oracle.query)
  let optionCost : Option (AmbientSpace q.n) → ENNReal := fun state =>
    match state with
    | none => 0
    | some point => cost (scale point)
  have hcollector := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle hsigma2 hweight proposalCap properStride retryLimit samples
  have hcost : Measurable cost :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hcollector.1
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hoptionCost : Measurable optionCost := by
    dsimp only [optionCost]
    convert Measurable.optionElim (0 : ENNReal) (hcost.comp hscale) using 1
    funext state
    cases state <;> rfl
  obtain ⟨bad, hle, hbad⟩ := happrox
  have htarget : ∫⁻ state, optionCost state ∂(target.map some) =
      ∫⁻ current, cost current ∂(target.map scale) := by
    rw [lintegral_map hoptionCost measurable_some]
    rw [lintegral_map hcost hscale]
  have hmain : ∫⁻ current, cost current ∂(target.map scale) ≤
      ((384 * (samples * retryLimit * properStride) : ℕ) : ENNReal) := by
    have hraw :=
      lintegral_scheduledBalancedAccuracyRetryCollect_countedQueryCost_le_of_isWarm
        q I oracle hsigma2 hweight hwarm proposalCap properStride retryLimit
          samples
    apply hraw.trans
    have hM2 : M * 2 ≤ 192 := by
      calc M * 2 ≤ 96 * 2 := by gcongr
        _ = 192 := by norm_num
    have hproper : (1 : ENNReal) ≤ properStride := by exact_mod_cast hstride
    calc
      ((samples * retryLimit : ℕ) : ENNReal) *
          ((properStride : ENNReal) * (M * 2) + 2 * M) ≤
        ((samples * retryLimit : ℕ) : ENNReal) *
          ((properStride : ENNReal) * 192 + 192) := by
        gcongr
        simpa [mul_comm] using hM2
      _ ≤ ((samples * retryLimit : ℕ) : ENNReal) *
          ((properStride : ENNReal) * 384) := by
        gcongr
        calc
          (properStride : ENNReal) * 192 + 192 ≤
              (properStride : ENNReal) * 192 +
                (properStride : ENNReal) * 192 := by
            gcongr
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hproper
                (by norm_num : (0 : ENNReal) ≤ 192)
          _ = (properStride : ENNReal) * 384 := by ring
      _ = ((384 * (samples * retryLimit * properStride) : ℕ) : ENNReal) := by
        push_cast
        ring
  have hcap : ∀ state, optionCost state ≤
      ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) := by
    intro state
    cases state with
    | none => simp [optionCost]
    | some point =>
        dsimp only [optionCost, cost, scale]
        simpa only [countedQueryCost] using
          (scheduledBalancedAccuracyRetryCollect_queryBound q sigma2 weight
            proposalCap properStride retryLimit samples
              (accuracyScaleFactor q • point)).lintegral_queryCount_le
            (hcollector.2 (accuracyScaleFactor q • point))
  have herror : ∫⁻ state, optionCost state ∂bad ≤
      ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) * error := by
    calc
      _ ≤ ∫⁻ _state,
          ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) ∂bad :=
        lintegral_mono hcap
      _ = ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) *
          bad Set.univ := by rw [lintegral_const]
      _ ≤ ((samples * retryLimit * (proposalCap + 2) : ℕ) : ENNReal) *
          error := by gcongr
  change ∫⁻ state, optionCost state ∂mu ≤ _
  calc
    _ ≤ ∫⁻ state, optionCost state ∂(target.map some + bad) :=
      lintegral_mono' hle le_rfl
    _ = (∫⁻ state, optionCost state ∂(target.map some)) +
        ∫⁻ state, optionCost state ∂bad :=
      lintegral_add_measure _ _ _
    _ = (∫⁻ current, cost current ∂(target.map scale)) +
        ∫⁻ state, optionCost state ∂bad := by rw [htarget]
    _ ≤ _ := add_le_add hmain herror

#print axioms
  lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo

end ArlibCommunity.Algorithms.CV18
