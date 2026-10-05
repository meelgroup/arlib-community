/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetEventTransfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFixedThirdMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAcceleratedThirdMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments

/-!
# Concrete equation-(6) budget for scheduled Gaussian reset references

This module selects the fixed or accelerated stationary coordinate moment
bounds at an arbitrary nonterminal schedule phase.  The shared rational
`L³` constant `129 / 64`, together with the transported reset-reference
dependence coefficient, fits in one eighth of the executable moment slack.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Both branches of the scheduled Gaussian update have the same rational
relative `L³` bound. -/
theorem scheduleValue_gaussian_thirdMoment_le_rational_mean_cube
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase)
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q phase) (scheduleValue q (phase + 1))
    (∫ x, weight x ^ 3 ∂nu) ≤
      ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
  by_cases hsone : scheduleValue q phase ≤ 1
  · exact scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube
      q I phase hsone
  · exact scheduleValue_accelerated_thirdMoment_le_rational_mean_cube
      q I phase hsone

/-- The sharp stationary coordinate second-moment factor, selected according
to the fixed/accelerated schedule branch. -/
theorem scheduleValue_gaussian_relativeSecondMoment_le_branchFactor
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    ((∫ x, gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2) ≤
      if scheduleValue q phase ≤ 1 then
        1 + 2 / (q.n : ℝ)
      else
        1 + scheduleValue q phase / terminalVariance q := by
  by_cases hsone : scheduleValue q phase ≤ 1
  · simpa [hsone] using
      scheduleValue_fixedRate_relativeSecondMoment_le q I phase hsone
  · have hsharp := figureOneSharpAcceleratedMoments q I
      ⟨⟨phase, hphase⟩, hsone⟩
    simpa [hsone] using hsharp

/-- The selected coordinate factor, divided by the actual phase-sensitive
sample count, is exactly the existing chronological ideal-average factor. -/
theorem scheduleValue_gaussian_branchAverageFactor_eq_chronological
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    1 + ((if scheduleValue q phase ≤ 1 then
        1 + 2 / (q.n : ℝ)
      else
        1 + scheduleValue q phase / terminalVariance q) - 1) /
          (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) =
      figureOneChronologicalMomentFactor q (phase + 1) := by
  have hphaseDependent : phase < figureOneDependentPhaseCount q := by
    rw [figureOneDependentPhaseCount]
    omega
  rw [figureOneChronologicalMomentFactor,
    figureOneChronologicalPhaseAt_succ q phase hphaseDependent]
  have horder :
      figureOneChronologicalPhaseOrder q ⟨phase, hphaseDependent⟩ =
        if hsone : scheduleValue q phase ≤ 1 then
          FigureOneIdealPhase.fixed ⟨⟨phase, hphase⟩, hsone⟩
        else
          FigureOneIdealPhase.accelerated ⟨⟨phase, hphase⟩, hsone⟩ := by
    simpa using figureOneChronologicalPhaseOrder_apply_transition q
      (⟨phase, hphase⟩ : Fin (terminalPhaseSteps q))
  rw [horder]
  by_cases hsone : scheduleValue q phase ≤ 1
  · simp [hsone, figureOneIdealPhaseFactor, figureOnePhaseSampleCount]
  · simp [hsone, figureOneIdealPhaseFactor, figureOnePhaseSampleCount]

/-- Scalar equation-(6) arithmetic: the reset-transported approximate
independence term, including the finite-count factor and the uniform `L³`
constant, consumes at most `slack / 8`. -/
theorem scheduledGaussianResetReference_equationSix_budget
    (q : VolumeParams) {count : ℕ} (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    (factor mean : ℝ) :
    (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
        3 * (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
              (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) *
            ((129 / 64 : ℝ) * mean) ^ 2 ≤
      (1 + ((factor - 1) / (count : ℝ) +
          figureOneExecutableMomentSlack q / 8)) * mean ^ 2 := by
  let epsilon := figureOneDependentEpsilon q +
    3 * (scheduledResetReferenceError q (count - 1)).toReal
  have hdependent : 0 < figureOneDependentEpsilon q := by
    unfold figureOneDependentEpsilon
    have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
      exact_mod_cast figureOneDependentPhaseCount_pos q
    exact div_pos (sq_pos_of_pos q.heps.1)
      (mul_pos
        (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
  have hepsilon : 0 ≤ epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilonLe : epsilon ≤
      (5 / 2 : ℝ) * figureOneDependentEpsilon q := by
    simpa [epsilon] using
      scheduledResetReference_transportEpsilon_le q hcountMax
  have hcoefficient :=
    figureOne_fixedThirdMoment_dependence_le_slack_div_eight_of_le_reset
      q hepsilon hepsilonLe
  have hcountR : (1 : ℝ) ≤ count := by exact_mod_cast hcount
  have hcountPos : (0 : ℝ) < count := by exact_mod_cast hcount
  have hfinite0 : 0 ≤ 1 - 1 / (count : ℝ) := by
    rw [sub_nonneg, div_le_one hcountPos]
    exact hcountR
  have hfinite1 : 1 - 1 / (count : ℝ) ≤ 1 := by
    linarith [one_div_nonneg.mpr hcountPos.le]
  have hmeanSq : 0 ≤ mean ^ 2 := sq_nonneg mean
  have hslack0 : 0 ≤ figureOneExecutableMomentSlack q / 8 :=
    div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  have hdependence :
      3 * epsilon ^ (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * ((129 / 64 : ℝ) * mean) ^ 2 ≤
        figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by
    calc
      3 * epsilon ^ (1 / 3 : ℝ) *
            (1 - 1 / (count : ℝ)) * ((129 / 64 : ℝ) * mean) ^ 2 =
          (3 * epsilon ^ (1 / 3 : ℝ) * (129 / 64 : ℝ) ^ 2) *
            (1 - 1 / (count : ℝ)) * mean ^ 2 := by ring
      _ ≤ (figureOneExecutableMomentSlack q / 8) * 1 * mean ^ 2 := by
        gcongr
      _ = figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by ring
  dsimp only [epsilon] at hdependence
  nlinarith

/-- Schedule-level form of the scalar budget, with its independent-average
term identified as the chronological ideal factor used by the final phase
assembly. -/
theorem scheduledGaussianResetReference_equationSix_budget_chronological
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let mean :=
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
    let factor := if scheduleValue q phase ≤ 1 then
      1 + 2 / (q.n : ℝ)
    else
      1 + scheduleValue q phase / terminalVariance q
    (1 + (factor - 1) / (count : ℝ)) * mean ^ 2 +
        3 * (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
              (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) *
            ((129 / 64 : ℝ) * mean) ^ 2 ≤
      (figureOneChronologicalMomentFactor q (phase + 1) +
          figureOneExecutableMomentSlack q / 8) * mean ^ 2 := by
  dsimp only
  have hcount := figureOnePhaseSampleCount_pos q (scheduleValue q phase)
  have hcountMax :=
    figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hbudget := scheduledGaussianResetReference_equationSix_budget
    q hcount hcountMax
      (if scheduleValue q phase ≤ 1 then
        1 + 2 / (q.n : ℝ)
      else
        1 + scheduleValue q phase / terminalVariance q)
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)))
  have hfactorEq :=
    scheduleValue_gaussian_branchAverageFactor_eq_chronological
      q phase hphase
  calc
    _ ≤ (1 + (((if scheduleValue q phase ≤ 1 then
            1 + 2 / (q.n : ℝ)
          else
            1 + scheduleValue q phase / terminalVariance q) - 1) /
              (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) +
            figureOneExecutableMomentSlack q / 8)) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2 :=
      hbudget
    _ = (figureOneChronologicalMomentFactor q (phase + 1) +
          figureOneExecutableMomentSlack q / 8) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2 := by
      rw [← hfactorEq]
      ring

/-- Fully concrete Gaussian reset-reference specialization of equation (6).
It supplies all coordinate moments and the scalar moment budget to the
generic initialized-history deviation theorem. -/
theorem initializedScheduledRetainedHistory_gaussian_relativeDeviation_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) {eps : ℝ} (heps : 0 < eps) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let mean :=
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
    let factor := if scheduleValue q phase ≤ 1 then
      1 + 2 / (q.n : ℝ)
    else
      1 + scheduleValue q phase / terminalVariance q
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * mean ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) - mean|} ≤
      ENNReal.ofReal ((((factor - 1) / (count : ℝ) +
        figureOneExecutableMomentSlack q / 8)) / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let mean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  let factor := if scheduleValue q phase ≤ 1 then
    1 + 2 / (q.n : ℝ)
  else
    1 + scheduleValue q phase / terminalVariance q
  have hcount : 0 < count := by
    simpa [count] using
      figureOnePhaseSampleCount_pos q (scheduleValue q phase)
  have hcountMax : count ≤ figureOneDependentMaxSampleCount q := by
    simpa [count] using
      figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hmean : 0 < mean := by
    rw [show mean =
        gaussianIntegral (truncatedBody q I) (scheduleValue q (phase + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q phase) by
      simpa [mean] using
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (phase + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q phase))
  have hfactor : 1 ≤ factor := by
    dsimp [factor]
    split_ifs
    · have hn : (0 : ℝ) < q.n := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
      exact le_add_of_nonneg_right (div_nonneg (by norm_num) hn.le)
    · have hs : 0 < scheduleValue q phase := scheduleValue_pos q phase
      have hT : 0 < terminalVariance q := terminalVariance_pos' q
      exact le_add_of_nonneg_right (div_nonneg hs.le hT.le)
  have hdelta : 0 ≤ (factor - 1) / (count : ℝ) +
      figureOneExecutableMomentSlack q / 8 := by
    exact add_nonneg
      (div_nonneg (sub_nonneg.mpr hfactor) (Nat.cast_nonneg count))
      (div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num))
  have hrelativeSecond :=
    scheduleValue_gaussian_relativeSecondMoment_le_branchFactor
      q I phase hphase
  have hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor * mean ^ 2 := by
    apply (div_le_iff₀ (pow_pos hmean 2)).mp
    simpa [factor, mean] using hrelativeSecond
  have hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        ((129 / 64 : ℝ) * mean) ^ 3 := by
    simpa [mean] using
      scheduleValue_gaussian_thirdMoment_le_rational_mean_cube q I phase
  have hA : 0 < (129 / 64 : ℝ) * mean := mul_pos (by norm_num) hmean
  have hbudget := scheduledGaussianResetReference_equationSix_budget
    q hcount hcountMax factor mean
  have hresult :=
    initializedScheduledRetainedHistory_relativeDeviation_le_of_coordinate_moments
      q I phase count hcount hcountMax hA hdelta heps
      hcoordinateSecond hcoordinateThird hbudget
  simpa [count, mean, factor] using hresult

#print axioms scheduleValue_gaussian_thirdMoment_le_rational_mean_cube
#print axioms scheduleValue_gaussian_relativeSecondMoment_le_branchFactor
#print axioms scheduleValue_gaussian_branchAverageFactor_eq_chronological
#print axioms scheduledGaussianResetReference_equationSix_budget
#print axioms
  scheduledGaussianResetReference_equationSix_budget_chronological
#print axioms
  initializedScheduledRetainedHistory_gaussian_relativeDeviation_le

end ArlibCommunity.Algorithms.CV18
