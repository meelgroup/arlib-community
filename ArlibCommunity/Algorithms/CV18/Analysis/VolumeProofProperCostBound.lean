/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperCostedRestart
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.WastedSteps

/-!
# Warm-start bound for CV18 proper-proposal cost

CV18 counts a proposal as proper when it lands in the body.  Metropolis
rejection happens after that event and therefore remains inside the speedy
Gaussian transition.  Consequently the cost observable is `ell⁻¹`, not the
accepted-move observable `(ell * speedyMetropolisMove)⁻¹`.

This file proves the exact Gaussian reweighting and the warm-start accumulated
cost bound.  The remaining analytic input is precisely the paper's weighted
average-local-conductance lower bound.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-- The local-conductance factor in the speedy stationary density cancels the
one-proper-proposal waiting cost exactly. -/
theorem lintegral_inv_ell_ellGaussianMeasure
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ) :
    ∫⁻ x, (ell K delta x)⁻¹ ∂(ellGaussianMeasure K delta variance) =
      ∫⁻ x in K, gaussianWeight variance x := by
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K delta x)⁻¹ := (measurable_ell hK delta).inv
  rw [ellGaussianMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_ell_mul_gaussianWeight hK delta variance)
      hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_ell_ne_zero hK hdelta] with x hx
  have hxtop : ell K delta x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K delta x)
  simp only [Pi.mul_apply]
  calc
    ell K delta x * gaussianWeight variance x * (ell K delta x)⁻¹ =
        (ell K delta x * (ell K delta x)⁻¹) * gaussianWeight variance x := by ring
    _ = gaussianWeight variance x := by
      rw [ENNReal.mul_inv_cancel hx hxtop, one_mul]

/-- Under the weighted average-local-conductance hypothesis
`lambda * ∫_K g ≤ ∫_K ell*g`, one stationary proper step has cost at most
`1/lambda`, stated without division. -/
theorem mul_lintegral_inv_ell_ellGaussianProb_le_one
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ) :
    lambda * ∫⁻ x, (ell K delta x)⁻¹ ∂(ellGaussianProb K delta variance) ≤ 1 := by
  rw [ellGaussianProb, lintegral_smul_measure, smul_eq_mul,
    lintegral_inv_ell_ellGaussianMeasure hK hdelta variance]
  calc
    lambda * ((ellGaussianMeasure K delta variance Set.univ)⁻¹ *
        ∫⁻ x in K, gaussianWeight variance x) =
      (ellGaussianMeasure K delta variance Set.univ)⁻¹ *
        (lambda * ∫⁻ x in K, gaussianWeight variance x) := by ring
    _ ≤ (ellGaussianMeasure K delta variance Set.univ)⁻¹ *
        ellGaussianMeasure K delta variance Set.univ := by gcongr
    _ = 1 := ENNReal.inv_mul_cancel hZ0 hZtop

/-- CV18's warm-start linearity argument for the correct proper-proposal
observable. -/
theorem mul_sum_lintegral_inv_ell_iterate_speedyMetropolisGaussian_le
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance)) (t : ℕ) :
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K delta variance) mu i) ≤
      (t : ℝ≥0∞) * M := by
  have hsum := sum_lintegral_iterate_le_of_isWarm hwarm
    (step_invariant (invariant_speedyMetropolisGaussian hK delta variance))
    (fun x => (ell K delta x)⁻¹) t
  have hstationary := mul_lintegral_inv_ell_ellGaussianProb_le_one
    hK hdelta variance hZ0 hZtop hlambda
  calc
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K delta variance) mu i) ≤
      lambda * ((t : ℝ≥0∞) *
        (M * ∫⁻ x, (ell K delta x)⁻¹
          ∂(ellGaussianProb K delta variance))) := by gcongr
    _ = (t : ℝ≥0∞) * M *
        (lambda * ∫⁻ x, (ell K delta x)⁻¹
          ∂(ellGaussianProb K delta variance)) := by ring
    _ ≤ (t : ℝ≥0∞) * M * 1 := by gcongr
    _ = (t : ℝ≥0∞) * M := mul_one _

/-- The honest stopped raw-trajectory kernel costs at most `ell⁻¹` at every
ambient state.  It is equal at every non-stuck state and parks at zero cost at
a stuck state. -/
theorem lintegral_fst_properProposalCostedKernel_le_inv_ell
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    (delta variance : ℝ) (x : GaussianState n) :
    ∫⁻ y, y.1 ∂(properProposalCostedKernel K hK delta variance x) ≤
      (ell K delta x)⁻¹ := by
  classical
  rw [properProposalCostedKernel, Kernel.piecewise_apply]
  split_ifs with hx
  · rw [Kernel.deterministic_apply (by fun_prop),
      lintegral_dirac' (0, x) measurable_fst]
    exact zero_le
  · rw [lintegral_fst_properProposalCostedKernelRaw hK delta variance x]

/-- Expected raw proposals used by the concrete independently restarted
proper-step experiment satisfy the paper's warm-start bound. -/
theorem mul_lintegral_properProposalTotalCost_le
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance)) (t : ℕ) :
    lambda * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu)) ≤
      (t : ℝ≥0∞) * M := by
  rw [lintegral_restartedTotalCost_eq_sum_stateMeans _
    (speedyMetropolisGaussian K delta variance)
    (map_snd_properProposalCostedKernel_eq_speedy hK delta variance)]
  calc
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (∫⁻ y, y.1 ∂properProposalCostedKernel K hK delta variance x)
          ∂(iterate (speedyMetropolisGaussian K delta variance) mu i) ≤
      lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K delta variance) mu i) := by
        gcongr with i hi x
        exact lintegral_fst_properProposalCostedKernel_le_inv_ell
          hK delta variance x
    _ ≤ (t : ℝ≥0∞) * M :=
      mul_sum_lintegral_inv_ell_iterate_speedyMetropolisGaussian_le
        hK hdelta variance hZ0 hZtop hlambda hwarm t

/-- Markov's inequality converts the expected-cost theorem into the exact
cutoff/restart failure bound.  The multiplicative form avoids any artificial
nonzero or finiteness assumptions on `lambda` and `cutoff`. -/
theorem mul_mul_measure_properProposalTotalCost_ge_le
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance))
    (t : ℕ) (cutoff : ℝ≥0∞) :
    lambda * cutoff *
        restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega} ≤
      (t : ℝ≥0∞) * M := by
  have hmarkov := mul_meas_ge_le_lintegral
    (measurable_restartedTotalCost (S := GaussianState n) t) cutoff
    (μ := restartedCostExecution
      (properProposalCostedKernel K hK delta variance) mu)
  calc
    lambda * cutoff *
        restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega} =
      lambda * (cutoff *
        restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega}) := by ring
    _ ≤ lambda * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (properProposalCostedKernel K hK delta variance) mu)) := by gcongr
    _ ≤ (t : ℝ≥0∞) * M :=
      mul_lintegral_properProposalTotalCost_le hK hdelta variance
        hZ0 hZtop hlambda hwarm t

end Arlib.MarkovChains
