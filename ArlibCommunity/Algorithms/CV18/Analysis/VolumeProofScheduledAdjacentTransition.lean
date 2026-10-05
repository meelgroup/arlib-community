/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGoodBadTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledSpeedyWarmStart

/-! # Consecutive scheduled transition with cap-loss mass

This specializes the good/bad transition theorem to consecutive CV18 cooling
phases, discharging both adjacent warmness and its constant arithmetic.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

theorem two_speedyAdjacentWarmConstant_add_one_le_eight
    (q : VolumeParams) :
    2 * ENNReal.ofReal (speedyAdjacentWarmConstant q) + 1 ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) := by
  rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num,
    ← ENNReal.ofReal_add
      (by positivity [speedyAdjacentWarmConstant_pos q] :
        0 ≤ 2 * speedyAdjacentWarmConstant q)
      (by norm_num : (0 : ℝ) ≤ 1)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [speedyAdjacentWarmConstant_one_le q]

/-- Consecutive scheduled phases need only an additive bad submeasure in the
retained marginal.  The actual final executable transition then pays exactly
twice that bad mass in addition to its corrected transition budget. -/
theorem bind_figureOneFinalScheduledAdjacentTransition_leUpTo_of_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (rho mu bad : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu] [IsFiniteMeasure bad]
    {eta : ENNReal}
    (hmuWarm : Arlib.IsWarm 2 mu rho)
    (hrho : rho ≤
      ellGaussianProb
          (figureOneScheduledPhaseBody q I (scheduleValue q phase))
          (figureOneScheduledProposalRadius q (scheduleValue q phase))
          (scheduleValue q phase) + bad)
    (hbad : bad Set.univ ≤ eta) :
    MeasureLeUpTo
      (mu.bind
        (scheduledBalancedAccuracyTransitionLawAux q I
          (scheduleValue q (phase + 1))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q (phase + 1)))))
      ((truncatedGaussianProbability q I (scheduleValue q (phase + 1))
        (scheduleValue_pos q (phase + 1)) : Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q + 2 * eta) := by
  apply bind_figureOneFinalScheduledBalancedTransition_leUpTo_of_good_bad
    q I (scheduleValue_pos q (phase + 1)) rho mu
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q phase))
        (figureOneScheduledProposalRadius q (scheduleValue q phase))
        (scheduleValue q phase)) bad hmuWarm hrho
  · exact scheduledPhase_speedyStationary_adjacent_isWarm q I phase
  · exact hbad
  · exact two_speedyAdjacentWarmConstant_add_one_le_eight q

#print axioms two_speedyAdjacentWarmConstant_add_one_le_eight
#print axioms bind_figureOneFinalScheduledAdjacentTransition_leUpTo_of_good_bad

end ArlibCommunity.Algorithms.CV18
