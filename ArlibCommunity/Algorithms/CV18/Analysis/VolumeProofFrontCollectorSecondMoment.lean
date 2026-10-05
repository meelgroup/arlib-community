/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectorAverageSecondMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance

/-!
# Second moment of the front Markov collector average

This identifies the accumulator used by the CV18 proper-walk semantics with
the centered `markovSumLaw` controlled by the spectral covariance theorem.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open Arlib.MarkovChains

/-- The raw average returned by a stationary front-recursive Markov collector
has the usual mean-square plus spectral-variance bound. -/
theorem integral_bind_frontMarkovCollectLaw_average_sq_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (mean : ℝ)
    (hmem : MemLp (fun x => f x - mean) 2 pi)
    (hmean : ∫ x, (f x - mean) ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x - mean| ≤ B)
    (hgap : 0 < spectralGap P pi) {samples : ℕ} (hsamples : 0 < samples) :
    (∫ output, (output.1 / (samples : ℝ)) ^ 2
      ∂pi.bind (frontMarkovCollectLaw P f samples)) ≤
      mean ^ 2 +
        3 * ((spectralGap P pi)⁻¹ *
          varianceReal pi (fun x => f x - mean)) / samples := by
  let centered : S → ℝ := fun x => f x - mean
  let rawLaw := pi.bind (frontMarkovCollectLaw P f samples)
  let centeredLaw := pi.bind (frontMarkovCollectLaw P centered samples)
  let shift : ℝ × S → ℝ × S := fun output =>
    (output.1 - (samples : ℝ) * mean, output.2)
  let restoreAverage : ℝ × S → ℝ := fun output =>
    ((output.1 + (samples : ℝ) * mean) / samples) ^ 2
  have hcentered : Measurable centered := hf.sub measurable_const
  have hrawKernel := frontMarkovCollectLaw_measurable_and_probability
    P hf samples
  have hcenteredKernel := frontMarkovCollectLaw_measurable_and_probability
    P hcentered samples
  have hshift : Measurable shift := by fun_prop
  have hrestore : Measurable restoreAverage := by fun_prop
  let _ : IsProbabilityMeasure rawLaw :=
    isProbabilityMeasure_bind hrawKernel.1.aemeasurable
      (ae_of_all _ hrawKernel.2)
  let _ : IsProbabilityMeasure centeredLaw :=
    isProbabilityMeasure_bind hcenteredKernel.1.aemeasurable
      (ae_of_all _ hcenteredKernel.2)
  have hshiftLaw : rawLaw.map shift = centeredLaw := by
    dsimp only [rawLaw, centeredLaw]
    rw [map_bind_eq_bind_map_of_measurable pi hrawKernel.1 hshift]
    apply Measure.bind_congr_right
    filter_upwards with current
    exact frontMarkovCollectLaw_map_sub_const P hf mean samples current
  have hcenteredLaw : centeredLaw =
      (markovSumLaw P centered samples pi).map
        (fun stateSum => (stateSum.2, stateSum.1)) := by
    dsimp only [centeredLaw]
    exact bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap
      P hcentered samples pi
  have hrewrite :
      (∫ output, (output.1 / (samples : ℝ)) ^ 2 ∂rawLaw) =
        ∫ output, restoreAverage output ∂centeredLaw := by
    calc
      (∫ output, (output.1 / (samples : ℝ)) ^ 2 ∂rawLaw) =
          ∫ output, restoreAverage (shift output) ∂rawLaw := by
        apply integral_congr_ae
        filter_upwards with output
        dsimp only [restoreAverage, shift]
        congr 1
        ring
      _ = ∫ output, restoreAverage output ∂rawLaw.map shift := by
        rw [integral_map hshift.aemeasurable hrestore.aestronglyMeasurable]
      _ = ∫ output, restoreAverage output ∂centeredLaw := by rw [hshiftLaw]
  rw [hrewrite, hcenteredLaw]
  rw [integral_map (by fun_prop : Measurable fun stateSum : S × ℝ =>
      (stateSum.2, stateSum.1)).aemeasurable hrestore.aestronglyMeasurable]
  exact integral_markovSumLaw_centered_average_sq_le
    P hrev hpsd hne hcentered hmem hmean hB hfbound hgap hsamples mean

#print axioms integral_bind_frontMarkovCollectLaw_average_sq_le

end ArlibCommunity.Algorithms.CV18
