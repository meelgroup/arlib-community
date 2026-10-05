/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianPhaseMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSlackMoments

/-!
# Numerical death-loss budget for scheduled Gaussian phases

This discharges the finite-error hypotheses of the killed Gaussian collector
at the final CV18 parameters.  The square root of both the endpoint error and
the actual absorbing-death probability fits into `1 / 16384` of the
per-phase executable moment slack.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

theorem figureOneExecutableMomentSlack_pos (q : VolumeParams) :
    0 < figureOneExecutableMomentSlack q := by
  unfold figureOneExecutableMomentSlack
  exact div_pos (sq_pos_of_pos q.heps.1) <| mul_pos (by norm_num) <| by
    exact_mod_cast figureOneDependentPhaseCount_pos q

theorem figureOneExecutableMomentSlack_eq_inv_four_alpha
    (q : VolumeParams) :
    figureOneExecutableMomentSlack q =
      1 / (4 * figureOneDependentAlpha q) := by
  have hm : (figureOneDependentPhaseCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (figureOneDependentPhaseCount_pos q))
  have he : q.eps ≠ 0 := q.heps.1.ne'
  unfold figureOneExecutableMomentSlack figureOneDependentAlpha
  field_simp [hm, he]
  norm_num

theorem figureOneDependentEpsilon_eq_slack_div_alpha_four
    (q : VolumeParams) :
    figureOneDependentEpsilon q =
      figureOneExecutableMomentSlack q /
        figureOneDependentAlpha q ^ 4 := by
  unfold figureOneDependentEpsilon figureOneExecutableMomentSlack
  ring

/-- The endpoint-error budget used by the killed Gaussian collector is
quadratically smaller than the per-phase executable moment slack. -/
theorem figureOneScheduledGaussianPhase_error_toReal_le_slack_sq
    (q : VolumeParams) (phase : ℕ) :
    (2 * scheduledBalancedStationaryTargetError q +
        figureOnePhaseSampleCount q (scheduleValue q phase) •
          figureOneCorrectedTransitionBudget q).toReal ≤
      (figureOneExecutableMomentSlack q / 16384) ^ 2 := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let maxCount := figureOneDependentMaxSampleCount q
  let phases := figureOneDependentPhaseCount q
  let nu := figureOnePerSampleMixingError q
  let dependent := figureOneDependentEpsilon q
  let alpha := figureOneDependentAlpha q
  let slack := figureOneExecutableMomentSlack q
  let stationary := scheduledBalancedStationaryTargetError q
  let delta := figureOneCorrectedTransitionBudget q
  have hnu : 0 < nu := by
    simpa [nu] using figureOnePerSampleMixingError_pos q
  have hmax : 0 < maxCount := by
    simpa [maxCount] using figureOneDependentMaxSampleCount_pos q
  have hphases : 0 < phases := by
    simpa [phases] using figureOneDependentPhaseCount_pos q
  have halpha : (1024 : ℝ) ≤ alpha := by
    simpa [alpha] using figureOneDependentAlpha_ge_1024 q
  have hslack : 0 < slack := by
    simpa [slack] using figureOneExecutableMomentSlack_pos q
  have hcount : count ≤ maxCount := by
    simpa [count, maxCount] using
      figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hdeltaTop : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have htargetTop : figureOneCorrectedTargetBudget q ≠ ⊤ :=
    ENNReal.div_ne_top hdeltaTop (by norm_num)
  have hstationaryTop : stationary ≠ ⊤ :=
    ne_top_of_le_ne_top htargetTop <| by
      simpa [stationary] using
        scheduledBalancedStationaryTargetError_le_targetBudget q
  have hcountDeltaTop : count • delta ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hdeltaTop
  have hstationaryReal : stationary.toReal ≤ nu / 4 := by
    have h := ENNReal.toReal_mono htargetTop
      (scheduledBalancedStationaryTargetError_le_targetBudget q)
    simpa [stationary, figureOneCorrectedTargetBudget, delta,
      figureOneCorrectedTransitionBudget, nu, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hnu.le] using h
  have herrorReal :
      (2 * stationary + count • delta).toReal =
        2 * stationary.toReal + (count : ℝ) * nu := by
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) hstationaryTop) hcountDeltaTop,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_nsmul]
    simp [delta, figureOneCorrectedTransitionBudget, nu,
      ENNReal.toReal_ofReal hnu.le, nsmul_eq_mul]
  have hbudget :
      3 * (maxCount : ℝ) * (phases : ℝ) * nu = dependent := by
    simpa [maxCount, phases, nu, dependent] using figureOne_lemma717c_budget q
  have hfirst : 2 * stationary.toReal + (count : ℝ) * nu ≤
      dependent / (2 * (phases : ℝ)) := by
    have hcountReal : (count : ℝ) ≤ maxCount := by exact_mod_cast hcount
    have hmaxReal : (1 : ℝ) ≤ maxCount := by exact_mod_cast hmax
    have hphasesReal : (0 : ℝ) < phases := by exact_mod_cast hphases
    have hrough : 2 * stationary.toReal + (count : ℝ) * nu ≤
        (3 / 2 : ℝ) * maxCount * nu := by
      calc
        2 * stationary.toReal + (count : ℝ) * nu ≤
            nu / 2 + (maxCount : ℝ) * nu := by
          nlinarith [hstationaryReal,
            mul_le_mul_of_nonneg_right hcountReal hnu.le]
        _ ≤ (3 / 2 : ℝ) * maxCount * nu := by
          nlinarith
    calc
      _ ≤ (3 / 2 : ℝ) * maxCount * nu := hrough
      _ = dependent / (2 * (phases : ℝ)) := by
        rw [← hbudget]
        field_simp [hphasesReal.ne']
  have hlarge : (2 : ℝ) * 16384 ^ 2 ≤ alpha ^ 3 * phases := by
    have hpow : (1024 : ℝ) ^ 3 ≤ alpha ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) halpha 3
    have hphaseOne : (1 : ℝ) ≤ phases := by exact_mod_cast hphases
    calc
      (2 : ℝ) * 16384 ^ 2 ≤ 1024 ^ 3 := by norm_num
      _ ≤ alpha ^ 3 := hpow
      _ ≤ alpha ^ 3 * phases := by
        nlinarith [pow_nonneg (show 0 ≤ alpha by positivity) 3]
  have hdependent : dependent = slack / alpha ^ 4 := by
    simpa [dependent, slack, alpha] using
      figureOneDependentEpsilon_eq_slack_div_alpha_four q
  have hslackAlpha : slack = 1 / (4 * alpha) := by
    simpa [slack, alpha] using
      figureOneExecutableMomentSlack_eq_inv_four_alpha q
  have halphaPos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hsecond : dependent / (2 * (phases : ℝ)) ≤
      (slack / 16384) ^ 2 := by
    rw [hdependent, hslackAlpha]
    have hphasesReal : (0 : ℝ) < phases := by exact_mod_cast hphases
    field_simp [halphaPos.ne', hphasesReal.ne']
    nlinarith
  rw [show 2 * scheduledBalancedStationaryTargetError q +
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q =
      2 * stationary + count • delta by rfl,
    herrorReal]
  exact hfirst.trans hsecond

theorem figureOneScheduledGaussianPhase_error_ne_top
    (q : VolumeParams) (phase : ℕ) :
    2 * scheduledBalancedStationaryTargetError q +
        figureOnePhaseSampleCount q (scheduleValue q phase) •
          figureOneCorrectedTransitionBudget q ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top (by norm_num) <|
      ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
  · rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top

/-- The actual absorbing-death probability of the retained Gaussian shadow
inherits the same quadratic executable-slack bound. -/
theorem figureOneScheduledGaussianShadow_dead_real_le_slack_sq
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)).real {state | state.2 = none} ≤
      (figureOneExecutableMomentSlack q / 16384) ^ 2 := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let stationary := scheduledBalancedStationaryTargetError q
  let delta := figureOneCorrectedTransitionBudget q
  have htop := figureOneScheduledGaussianPhase_error_ne_top q phase
  have hdead := figureOneScheduledGaussianShadow_dead_real_le q I phase htop
  dsimp only at hdead
  have herrorLe : stationary + (count - 1) • delta ≤
      2 * stationary + count • delta := by
    apply add_le_add
    · simpa [two_mul] using
        self_le_add_right stationary stationary
    · rw [nsmul_eq_mul, nsmul_eq_mul]
      gcongr
      omega
  calc
    _ ≤ (stationary + (count - 1) • delta).toReal := by
      simpa [count, stationary, delta] using hdead
    _ ≤ (2 * stationary + count • delta).toReal :=
      ENNReal.toReal_mono htop herrorLe
    _ ≤ (figureOneExecutableMomentSlack q / 16384) ^ 2 := by
      simpa [count, stationary, delta] using
        figureOneScheduledGaussianPhase_error_toReal_le_slack_sq q phase

/-- Square-root form consumed by the all-or-nothing killing estimate. -/
theorem sqrt_figureOneScheduledGaussianShadow_dead_real_le_slack
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    Real.sqrt ((iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial (count - 1)).real {state | state.2 = none}) ≤
      figureOneExecutableMomentSlack q / 16384 := by
  dsimp only
  have h := Real.sqrt_le_sqrt <|
    figureOneScheduledGaussianShadow_dead_real_le_slack_sq q I phase
  have hs : 0 ≤ figureOneExecutableMomentSlack q / 16384 :=
    div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hs] using h

/-- With the standard coarse `2 * idealMean` L² witnesses, the two losses
from finite endpoint replacement and final collector death together consume
less than one eighth of the executable per-phase moment slack. -/
theorem integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower_final_parameters
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let idealMean :=
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    0 < idealMean →
    (∫ x, weight x ^ 2
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        (2 * idealMean) ^ 2 →
    MemLp (fun state : ℝ × Option (AmbientSpace q.n) => state.1) 2
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)) →
    (∫ state, (state.1 / (count : ℝ)) ^ 2
      ∂iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)) ≤ (2 * idealMean) ^ 2 →
    (1 - figureOneExecutableMomentSlack q / 8) * idealMean ≤
      ∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂figureOneScheduledGaussianPhaseTarget q I phase := by
  dsimp only
  let idealMean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let initial :=
    (truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
        (fun x => (weight x, some x))
  intro hideal hsecond hshadowMem hshadowSecond
  let eta := figureOneExecutableMomentSlack q / 16384
  have heta : 0 < eta := by
    exact div_pos (figureOneExecutableMomentSlack_pos q) (by norm_num)
  have htop := figureOneScheduledGaussianPhase_error_ne_top q phase
  have hepsEta :
      (2 * scheduledBalancedStationaryTargetError q +
          count • figureOneCorrectedTransitionBudget q).toReal ≤ eta ^ 2 := by
    simpa [count, eta] using
      figureOneScheduledGaussianPhase_error_toReal_le_slack_sq q phase
  have hbase :=
    integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower_explicit
      q I phase (eta := eta) (R := 2 * idealMean) (A := 2 * idealMean)
      heta (mul_pos (by norm_num) hideal)
      (mul_nonneg (by norm_num) hideal.le) htop
      (by simpa [count] using hepsEta)
      (by simpa [weight, idealMean] using hsecond)
      (by simpa [count, weight, K, initial] using hshadowMem)
      (by simpa [count, weight, K, initial] using hshadowSecond)
  have hslack0 := figureOneExecutableMomentSlack_nonneg q
  have hloss :
      2 * eta * (2 * idealMean) +
          (2 * idealMean) *
            Real.sqrt
              ((scheduledBalancedStationaryTargetError q +
                (count - 1) • figureOneCorrectedTransitionBudget q).toReal) ≤
        figureOneExecutableMomentSlack q / 8 * idealMean := by
    have hsqrtError :
        Real.sqrt
            ((scheduledBalancedStationaryTargetError q +
              (count - 1) • figureOneCorrectedTransitionBudget q).toReal) ≤
          eta := by
      have herrorLe :
          scheduledBalancedStationaryTargetError q +
              (count - 1) • figureOneCorrectedTransitionBudget q ≤
            2 * scheduledBalancedStationaryTargetError q +
              count • figureOneCorrectedTransitionBudget q := by
        apply add_le_add
        · simpa [two_mul] using
            self_le_add_right (scheduledBalancedStationaryTargetError q)
              (scheduledBalancedStationaryTargetError q)
        · rw [nsmul_eq_mul, nsmul_eq_mul]
          gcongr
          omega
      have hreal := ENNReal.toReal_mono htop herrorLe
      have hsquare := hreal.trans hepsEta
      have hsqrt := Real.sqrt_le_sqrt hsquare
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg heta.le] using hsqrt
    have hmul := mul_le_mul_of_nonneg_left hsqrtError
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hideal.le)
    calc
      2 * eta * (2 * idealMean) +
          (2 * idealMean) *
            Real.sqrt
              ((scheduledBalancedStationaryTargetError q +
                (count - 1) • figureOneCorrectedTransitionBudget q).toReal) ≤
          2 * eta * (2 * idealMean) + (2 * idealMean) * eta := by
        gcongr
      _ ≤ figureOneExecutableMomentSlack q / 8 * idealMean := by
        dsimp only [eta]
        nlinarith [mul_nonneg hslack0 hideal.le]
  dsimp only [eta] at hbase
  have hloss' := hloss
  dsimp only [eta] at hloss'
  exact hbase.trans' <| by
    dsimp only [idealMean, count] at hloss'
    nlinarith

#print axioms figureOneScheduledGaussianPhase_error_toReal_le_slack_sq
#print axioms figureOneScheduledGaussianPhase_error_ne_top
#print axioms figureOneScheduledGaussianShadow_dead_real_le_slack_sq
#print axioms sqrt_figureOneScheduledGaussianShadow_dead_real_le_slack
#print axioms
  integral_figureOneScheduledGaussianPhaseTarget_liveRaw_lower_final_parameters

end ArlibCommunity.Algorithms.CV18
