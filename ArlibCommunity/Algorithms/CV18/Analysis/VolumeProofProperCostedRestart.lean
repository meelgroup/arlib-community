/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCostedRestartTrajectory

/-!
# Costed independent restarts for the Gaussian proper-proposal experiment
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal ProbabilityTheory

variable {n : ℕ}

abbrev GaussianState (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev LiftedGaussianPath (n : ℕ) := ℕ → Bool × GaussianState n

/-- Tail-sum realization of the number of ordinary proposal transitions used before the
first proper proposal.  The starting state is retained explicitly so this is jointly
measurable and can be mapped from a started-trajectory kernel. -/
noncomputable def properProposalWaitCost
    (p : GaussianState n × LiftedGaussianPath n) : ℝ≥0∞ :=
  ∑' k : ℕ,
    {q : GaussianState n × LiftedGaussianPath n |
      ∀ i ≤ k, q.2 i = (false, q.1)}.indicator
        (1 : (GaussianState n × LiftedGaussianPath n) → ℝ≥0∞) p

theorem measurableSet_joint_holdsUntil (k : ℕ) :
    MeasurableSet {q : GaussianState n × LiftedGaussianPath n |
      ∀ i ≤ k, q.2 i = (false, q.1)} := by
  have heq : {q : GaussianState n × LiftedGaussianPath n |
      ∀ i ≤ k, q.2 i = (false, q.1)} =
      ⋂ i ∈ Set.Iic k,
        {q : GaussianState n × LiftedGaussianPath n | q.2 i = (false, q.1)} := by
    ext q
    simp
  rw [heq]
  exact MeasurableSet.biInter (Set.finite_Iic k).countable fun i _ =>
    measurableSet_eq_fun
      ((measurable_pi_apply i).comp measurable_snd)
      (measurable_const.prodMk measurable_fst)

theorem measurable_properProposalWaitCost :
    Measurable (properProposalWaitCost (n := n)) := by
  unfold properProposalWaitCost
  apply Measurable.tsum
  intro k
  exact measurable_const.indicator (measurableSet_joint_holdsUntil k)

/-- Attach the starting state to the full independently generated lifted trajectory. -/
noncomputable def properProposalStartedTrajectoryKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (GaussianState n) (GaussianState n × LiftedGaussianPath n) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (GaussianState n) (properProposalTrajectoryKernel K hK δ s))

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalStartedTrajectoryKernel K hK δ s) := by
  unfold properProposalStartedTrajectoryKernel
  infer_instance

/-- One honest costed speedy transition: independently generate the ordinary lifted proposal
trajectory, stop at its first proper proposal, return both the realized proposal count and
the stopped state. -/
noncomputable def properProposalCostedKernelRaw
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (GaussianState n) (ℝ≥0∞ × GaussianState n) :=
  Kernel.map (properProposalStartedTrajectoryKernel K hK δ s)
    (fun p => (properProposalWaitCost p, firstProperMarkedState p.2))

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalCostedKernelRaw K hK δ s) := by
  unfold properProposalCostedKernelRaw
  exact Kernel.IsMarkovKernel.map _
    (measurable_properProposalWaitCost.prodMk
      (measurable_firstProperMarkedState.comp measurable_snd))

/-- Total costed kernel.  At a stuck point it uses the speedy chain's prescribed parked
behavior with zero operational proposals; elsewhere it runs the stopped trajectory. -/
noncomputable def properProposalCostedKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (GaussianState n) (ℝ≥0∞ × GaussianState n) := by
  classical
  exact Kernel.piecewise (measurableSet_stuckPoints hK δ)
    (Kernel.deterministic (fun x => (0, x)) (by fun_prop))
    (properProposalCostedKernelRaw K hK δ s)

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalCostedKernel K hK δ s) := by
  classical
  unfold properProposalCostedKernel
  infer_instance

private theorem startedTrajectoryKernel_apply
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (δ s : ℝ) (x : GaussianState n) :
    properProposalStartedTrajectoryKernel K hK δ s x =
      (properProposalTrajectoryKernel K hK δ s x).map (fun ω => (x, ω)) := by
  ext A hA
  rw [properProposalStartedTrajectoryKernel, Kernel.compProd_apply hA,
    Kernel.id_apply, lintegral_dirac']
  · rw [Kernel.prodMkLeft_apply, Measure.map_apply (by fun_prop) hA]
  · exact Kernel.measurable_kernel_prodMk_left' hA x

/-- Forgetting the realized cost gives exactly one speedy Gaussian transition. -/
theorem map_snd_properProposalCostedKernel_eq_speedy
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (δ s : ℝ)
    (x : GaussianState n) :
    (properProposalCostedKernel K hK δ s x).map Prod.snd =
      speedyMetropolisGaussian K δ s x := by
  classical
  rw [properProposalCostedKernel, Kernel.piecewise_apply]
  split_ifs with hx
  · rw [Kernel.deterministic_apply (by fun_prop), Measure.map_dirac]
    ext A hA
    rw [speedyMetropolisGaussian_apply_set hK δ s x hA, Measure.dirac_apply' _ hA]
    have hden : volume (Metric.ball x δ ∩ K) = 0 := mem_stuckPoints_iff.1 hx
    have hnum : ∫⁻ y in A ∩ K, metropolisDensity s δ x y = 0 := by
      apply le_zero_iff.mp
      exact (lintegral_metropolisDensity_le (A ∩ K) δ s x).trans
        ((measure_mono (inter_subset_inter_right _ inter_subset_right)).trans_eq hden)
    have hnumK : ∫⁻ y in K, metropolisDensity s δ x y = 0 := by
      apply le_zero_iff.mp
      exact (lintegral_metropolisDensity_le K δ s x).trans_eq hden
    rw [hden, hnum, speedyMetropolisMove_apply, hnumK]
    simp
  · have hpair : Measurable
        (fun p : GaussianState n × LiftedGaussianPath n =>
          (properProposalWaitCost p, firstProperMarkedState p.2)) :=
      measurable_properProposalWaitCost.prodMk
        (measurable_firstProperMarkedState.comp measurable_snd)
    rw [properProposalCostedKernelRaw, Kernel.map_apply _ hpair,
      startedTrajectoryKernel_apply]
    rw [Measure.map_map measurable_snd hpair]
    rw [Measure.map_map (measurable_snd.comp hpair) (by fun_prop)]
    change (properProposalTrajectoryKernel K hK δ s x).map firstProperMarkedState = _
    rw [← Kernel.map_apply _ measurable_firstProperMarkedState,
      ← properProposalStoppedKernel]
    exact properProposalStoppedKernel_apply_eq_speedy hK δ s x (by
      simpa only [StuckPoints, Set.mem_setOf_eq] using hx)

/-- At a non-stuck state, the one-step realized proposal count has mean exactly `ell⁻¹`. -/
theorem lintegral_fst_properProposalCostedKernelRaw
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (δ s : ℝ)
    (x : GaussianState n) :
    ∫⁻ y, y.1 ∂(properProposalCostedKernelRaw K hK δ s x) = (ell K δ x)⁻¹ := by
  have hpair : Measurable
      (fun p : GaussianState n × LiftedGaussianPath n =>
        (properProposalWaitCost p, firstProperMarkedState p.2)) :=
    measurable_properProposalWaitCost.prodMk
      (measurable_firstProperMarkedState.comp measurable_snd)
  rw [properProposalCostedKernelRaw, Kernel.map_apply _ hpair,
    lintegral_map measurable_fst hpair, startedTrajectoryKernel_apply,
    lintegral_map, properProposalTrajectoryKernel_apply]
  · have hcost : ∀ ω : LiftedGaussianPath n,
        properProposalWaitCost (x, ω) =
          ∑' k : ℕ, {ω' : LiftedGaussianPath n |
            ∀ i ≤ k, ω' i = (false, x)}.indicator
              (1 : LiftedGaussianPath n → ℝ≥0∞) ω := by
      intro ω
      unfold properProposalWaitCost
      apply tsum_congr
      intro k
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [lintegral_congr hcost]
    exact lintegral_firstProperTime_pathMeasure_properProposalGaussianLift hK δ s x
  · exact measurable_properProposalWaitCost
  · fun_prop

/-- The total kernel's operational mean is bounded by the filtered-walk exit-time integrand
used in `WastedStepsGaussian`.  Off stuck points its mean is exactly `ell⁻¹`; multiplying the
denominator by the Metropolis move probability can only enlarge the reciprocal.  At stuck
points the total implementation parks at zero cost. -/
theorem lintegral_fst_properProposalCostedKernel_le_exitMean
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (δ s : ℝ)
    (x : GaussianState n) :
    ∫⁻ y, y.1 ∂(properProposalCostedKernel K hK δ s x) ≤
      (ell K δ x * speedyMetropolisMove K δ s x)⁻¹ := by
  classical
  rw [properProposalCostedKernel, Kernel.piecewise_apply]
  split_ifs with hx
  · rw [Kernel.deterministic_apply (by fun_prop), lintegral_dirac' (0, x) measurable_fst]
    simp
  · rw [lintegral_fst_properProposalCostedKernelRaw hK δ s x]
    rw [ENNReal.inv_le_inv]
    calc
      ell K δ x * speedyMetropolisMove K δ s x
          = speedyMetropolisMove K δ s x * ell K δ x := mul_comm _ _
      _ ≤ 1 * ell K δ x :=
        mul_le_mul_left (speedyMetropolisMove_le_one K δ s x) (ell K δ x)
      _ = ell K δ x := one_mul _

/-- The finite independently restarted execution of the costed proper-proposal kernel has
exactly the speedy Gaussian output law. -/
theorem map_properProposalCostedExecution_output
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (δ s : ℝ)
    (μ : Measure (GaussianState n)) [IsProbabilityMeasure μ] (t : ℕ) :
    (restartedCostExecution (properProposalCostedKernel K hK δ s) μ).map
        (fun ω => (ω t).2) =
      iterate (speedyMetropolisGaussian K δ s) μ t :=
  map_restartedCostExecution_output _ _
    (map_snd_properProposalCostedKernel_eq_speedy hK δ s) μ t

/-- Expected realized proposal count is bounded by the exact sum of Gaussian exit-time means
along the speedy-chain marginals. -/
theorem lintegral_properProposalTotalCost_le_exitMeanSum
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (δ s : ℝ)
    (μ : Measure (GaussianState n)) [IsProbabilityMeasure μ] (t : ℕ) :
    ∫⁻ ω, restartedTotalCost t ω
        ∂(restartedCostExecution (properProposalCostedKernel K hK δ s) μ) ≤
      ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ s x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K δ s) μ i) := by
  rw [lintegral_restartedTotalCost_eq_sum_stateMeans _
    (speedyMetropolisGaussian K δ s)
    (map_snd_properProposalCostedKernel_eq_speedy hK δ s)]
  apply Finset.sum_le_sum
  intro i hi
  exact lintegral_mono fun x =>
    lintegral_fst_properProposalCostedKernel_le_exitMean hK δ s x

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.map_properProposalCostedExecution_output
#print axioms Arlib.MarkovChains.lintegral_properProposalTotalCost_le_exitMeanSum
