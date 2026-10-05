/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledShadowReference
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSharpMomentTransfer

/-!
# Moment-factor slack for fixed-cost sample resets

The history-preserving exact-coordinate reference increases the within-phase
dependence coefficient by a fixed constant factor.  Its optimized `L³`
covariance contribution therefore uses a quarter, rather than one eighth,
of the executable moment slack.  The final phase factor has enough algebraic
room for that larger second-moment perturbation while retaining the original
one-eighth first-moment loss.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A quarter of second-moment slack and an eighth of mean slack still fit
inside the executable phase factor. -/
theorem figureOneExecutableMomentFactor_quarter_perturbation_budget
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalMomentFactor q j +
        figureOneExecutableMomentSlack q / 4 ≤
      figureOneChronologicalMomentFactor q j *
        (1 + figureOneExecutableMomentSlack q) *
          (1 - figureOneExecutableMomentSlack q / 8) ^ 2 := by
  let f := figureOneChronologicalMomentFactor q j
  let s := figureOneExecutableMomentSlack q
  have hf : 1 ≤ f := figureOneChronologicalMomentFactor_one_le q j
  have hs0 : 0 ≤ s := figureOneExecutableMomentSlack_nonneg q
  have hs1 : s ≤ 1 := figureOneExecutableMomentSlack_le_one q
  have hs2 : s ^ 2 ≤ s := by nlinarith [sq_nonneg s]
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  have hgain : s / 4 ≤
      (1 + s) * (1 - s / 8) ^ 2 - 1 := by
    nlinarith
  have hgain0 : 0 ≤
      (1 + s) * (1 - s / 8) ^ 2 - 1 :=
    (div_nonneg hs0 (by norm_num)).trans hgain
  have hscale : s / 4 ≤ f *
      ((1 + s) * (1 - s / 8) ^ 2 - 1) :=
    hgain.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hf hgain0)
  dsimp only [f, s] at hscale ⊢
  nlinarith

/-- Direct phase-moment assembly with the larger quarter-slack allowance
needed by the fixed-cost exact-coordinate reset route. -/
theorem scheduledFigureOneTrace_second_le_executableMomentFactor_of_ideal_bounds_quarter
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hmeanLower :
      (1 - figureOneExecutableMomentSlack q / 8) *
          figureOneIdealPhaseMean q I
            (figureOneChronologicalPhaseAt q j) ≤
        scheduledFigureOneTraceRawMean q I j)
    (hsecondUpper :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (figureOneChronologicalMomentFactor q j +
            figureOneExecutableMomentSlack q / 4) *
          figureOneIdealPhaseMean q I
            (figureOneChronologicalPhaseAt q j) ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneExecutableMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let slack := figureOneExecutableMomentSlack q
  let factor := figureOneChronologicalMomentFactor q j
  let idealMean := figureOneIdealPhaseMean q I
    (figureOneChronologicalPhaseAt q j)
  let actualMean := scheduledFigureOneTraceRawMean q I j
  have hslack0 : 0 ≤ slack := figureOneExecutableMomentSlack_nonneg q
  have hslack1 : slack ≤ 1 := figureOneExecutableMomentSlack_le_one q
  have hideal0 : 0 ≤ idealMean :=
    (figureOneIdealPhaseMean_pos q I
      (figureOneChronologicalPhaseAt q j)).le
  have hlower0 : 0 ≤ (1 - slack / 8) * idealMean := by
    exact mul_nonneg (by nlinarith) hideal0
  have hactual0 : 0 ≤ actualMean := hlower0.trans hmeanLower
  have hsquare : ((1 - slack / 8) * idealMean) ^ 2 ≤ actualMean ^ 2 :=
    (sq_le_sq₀ hlower0 hactual0).2 hmeanLower
  have hcoefficient0 : 0 ≤ factor * (1 + slack) :=
    mul_nonneg
      (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
      (by linarith)
  calc
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        (factor + slack / 4) * idealMean ^ 2 := hsecondUpper
    _ ≤ (factor * (1 + slack) * (1 - slack / 8) ^ 2) *
          idealMean ^ 2 :=
      mul_le_mul_of_nonneg_right
        (figureOneExecutableMomentFactor_quarter_perturbation_budget q j)
        (sq_nonneg idealMean)
    _ = factor * (1 + slack) *
          ((1 - slack / 8) * idealMean) ^ 2 := by ring
    _ ≤ factor * (1 + slack) * actualMean ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hcoefficient0
    _ = figureOneExecutableMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2 := by
      rfl

#print axioms figureOneExecutableMomentFactor_quarter_perturbation_budget
#print axioms
  scheduledFigureOneTrace_second_le_executableMomentFactor_of_ideal_bounds_quarter

end ArlibCommunity.Algorithms.CV18
