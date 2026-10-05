/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovVariance

/-!
# Second moment of a stationary Markov collector average

This is the measure-theoretic form of CV18 Lemma 7.15, Eq. (6), before
specializing the observable, spectral gap, and sample count.  The existing
Markov variance theorem controls the centered accumulated sum.  Here we
restore its mean and divide by the sample count, producing exactly the raw
second moment of the empirical average.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

/-- Restoring the mean in a centered stationary Markov sum adds exactly the
square of the deterministic total mean. -/
theorem integral_markovSumLaw_centered_add_mean_sq_le
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) (samples : ℕ) (mean : ℝ) :
    (∫ stateSum,
        (stateSum.2 + (samples : ℝ) * mean) ^ 2
      ∂markovSumLaw P f samples pi) ≤
      ((samples : ℝ) * mean) ^ 2 +
        (samples : ℝ) *
          (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) := by
  let mu := markovSumLaw P f samples pi
  let totalMean := (samples : ℝ) * mean
  let _ : IsProbabilityMeasure mu :=
    markovSumLaw_isProbabilityMeasure P hf pi samples
  have hsndMem : MemLp (fun stateSum : S × ℝ => stateSum.2) 2 mu := by
    apply MemLp.of_bound (by fun_prop) ((samples : ℝ) * B)
    filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hfbound pi samples]
      with stateSum hstateSum
    simpa [Real.norm_eq_abs] using hstateSum
  have hsndInt : Integrable (fun stateSum : S × ℝ => stateSum.2) mu :=
    hsndMem.integrable (by norm_num)
  have hsndSqInt : Integrable
      (fun stateSum : S × ℝ => stateSum.2 ^ 2) mu :=
    hsndMem.integrable_sq
  have hzero : ∫ stateSum, stateSum.2 ∂mu = 0 :=
    integral_snd_markovSumLaw_eq_zero P hrev hf hmean hB hfbound samples
  have hsecond := integral_markovSumLaw_sq_le P hrev hpsd hne hf hmem
    hmean hB hfbound hgap samples
  change (∫ stateSum, (stateSum.2 + totalMean) ^ 2 ∂mu) ≤ _
  have hexpand : (∫ stateSum, (stateSum.2 + totalMean) ^ 2 ∂mu) =
      (∫ stateSum, stateSum.2 ^ 2 ∂mu) + totalMean ^ 2 := by
    calc
      (∫ stateSum, (stateSum.2 + totalMean) ^ 2 ∂mu) =
          ∫ stateSum,
            (stateSum.2 ^ 2 + 2 * totalMean * stateSum.2) +
              totalMean ^ 2 ∂mu := by
        apply integral_congr_ae
        filter_upwards with stateSum
        ring
      _ = (∫ stateSum,
            stateSum.2 ^ 2 + 2 * totalMean * stateSum.2 ∂mu) +
          ∫ _stateSum, totalMean ^ 2 ∂mu := by
        rw [integral_add]
        · exact (hsndSqInt.add (hsndInt.const_mul _))
        · exact integrable_const _
      _ = ((∫ stateSum, stateSum.2 ^ 2 ∂mu) +
            ∫ stateSum, 2 * totalMean * stateSum.2 ∂mu) +
          totalMean ^ 2 := by
        rw [integral_add hsndSqInt (hsndInt.const_mul _), integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      _ = (∫ stateSum, stateSum.2 ^ 2 ∂mu) + totalMean ^ 2 := by
        rw [show (∫ stateSum, 2 * totalMean * stateSum.2 ∂mu) =
            2 * totalMean * ∫ stateSum, stateSum.2 ∂mu by
          rw [integral_const_mul], hzero]
        ring
  rw [hexpand]
  calc
    (∫ stateSum, stateSum.2 ^ 2 ∂mu) + totalMean ^ 2 ≤
        (samples : ℝ) *
            (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) +
          totalMean ^ 2 := add_le_add hsecond le_rfl
    _ = ((samples : ℝ) * mean) ^ 2 +
        (samples : ℝ) *
          (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) := by
      dsimp only [totalMean]
      ring

/-- Raw second moment of the empirical average of a stationary Markov path.
This is the direct dependent-sample replacement for the IID calculation in
CV18 Eq. (6). -/
theorem integral_markovSumLaw_centered_average_sq_le
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) {samples : ℕ} (hsamples : 0 < samples)
    (mean : ℝ) :
    (∫ stateSum,
        ((stateSum.2 + (samples : ℝ) * mean) / samples) ^ 2
      ∂markovSumLaw P f samples pi) ≤
      mean ^ 2 +
        3 * ((spectralGap P pi)⁻¹ * varianceReal pi f) / samples := by
  have hsamplesR : (0 : ℝ) < samples := by exact_mod_cast hsamples
  have hsum := integral_markovSumLaw_centered_add_mean_sq_le
    P hrev hpsd hne hf hmem hmean hB hfbound hgap samples mean
  rw [show (∫ stateSum,
      ((stateSum.2 + (samples : ℝ) * mean) / samples) ^ 2
        ∂markovSumLaw P f samples pi) =
      (∫ stateSum,
        (stateSum.2 + (samples : ℝ) * mean) ^ 2
          ∂markovSumLaw P f samples pi) / (samples : ℝ) ^ 2 by
    simp_rw [div_pow]
    rw [integral_div]]
  apply (div_le_iff₀ (sq_pos_of_pos hsamplesR)).2
  calc
    (∫ stateSum,
        (stateSum.2 + (samples : ℝ) * mean) ^ 2
          ∂markovSumLaw P f samples pi) ≤
        ((samples : ℝ) * mean) ^ 2 +
          (samples : ℝ) *
            (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) := hsum
    _ = (mean ^ 2 +
          3 * ((spectralGap P pi)⁻¹ * varianceReal pi f) / samples) *
        (samples : ℝ) ^ 2 := by
      field_simp [hsamplesR.ne']

#print axioms integral_markovSumLaw_centered_add_mean_sq_le
#print axioms integral_markovSumLaw_centered_average_sq_le

end Arlib.MarkovChains
