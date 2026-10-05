/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperStep
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MarkedTimeChange

/-!
# Proper proposals for the Gaussian Metropolis ball walk

The "proper steps" in Cousins--Vempala are the proposals which land in `K`, not the
accepted moves of the Metropolis filter.  Consequently a proper-step clock must leave the
Metropolis rejection atom inside the time-changed chain.  This file records the one-step
identity behind that construction: the ordinary Gaussian Metropolis kernel is a mixture of

* a proper proposal, with probability `ell K δ x`, followed by one
  `speedyMetropolisGaussian` step; and
* an improper proposal, with probability `1 - ell K δ x`, which stays at `x`.

In particular, counting changes of state would condition on both events (landing in `K` and
passing the Metropolis filter) and therefore would not give the speedy Metropolis chain.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## The marked one-step kernel -/

/-- One Gaussian Metropolis step with its **proper-proposal mark exposed**.  The mark is
`true` with probability `ell K δ x`; on that branch the output position is one speedy
Metropolis step.  On the `false` branch the proposal lay outside `K` and the position stays
at `x`.

The measurability proof is why `hK` is an explicit argument: the mixing coefficient `ell`
and the speedy kernel are measurable on a measurable body. -/
noncomputable def properProposalGaussianAux (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (Bool × EuclideanSpace ℝ (Fin n)) where
  toFun x := ell K δ x •
      (speedyMetropolisGaussian K δ s x).map (fun y => (true, y))
    + (1 - ell K δ x) • Measure.dirac (false, x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have htrue : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) :=
      measurable_const.prodMk measurable_id
    have hfalse : Measurable (fun x : EuclideanSpace ℝ (Fin n) => (false, x)) :=
      measurable_const.prodMk measurable_id
    simp_rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply htrue ht, Measure.dirac_apply' _ ht]
    exact ((measurable_ell hK δ).mul
      (Kernel.measurable_coe (speedyMetropolisGaussian K δ s) (htrue ht))).add
      ((measurable_const.sub (measurable_ell hK δ)).mul
        (measurable_one.indicator (hfalse ht)))

/-- Event evaluation for the marked proposal kernel. -/
theorem properProposalGaussianAux_apply_set {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n))
    {t : Set (Bool × EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) :
    properProposalGaussianAux K hK δ s x t =
      ell K δ x * speedyMetropolisGaussian K δ s x
          ((fun y : EuclideanSpace ℝ (Fin n) => (true, y)) ⁻¹' t)
        + (1 - ell K δ x) * t.indicator 1 (false, x) := by
  change (ell K δ x •
      (speedyMetropolisGaussian K δ s x).map (fun y => (true, y))
    + (1 - ell K δ x) • Measure.dirac (false, x)) t = _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul,
    Measure.map_apply (by fun_prop : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (true, y))) ht,
    Measure.dirac_apply' _ ht]

instance isMarkovKernel_properProposalGaussianAux
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalGaussianAux K hK δ s) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [properProposalGaussianAux_apply_set hK δ s x MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (ell_le_one K δ x)

/-- Forgetting the explicit proposal mark recovers the ordinary Gaussian Metropolis kernel.
This is the measure-level link from the marked path model back to the sampler's real chain. -/
theorem map_snd_properProposalGaussianAux_apply
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (properProposalGaussianAux K hK δ s x).map
        (fun p : Bool × EuclideanSpace ℝ (Fin n) => p.2) = metropolisGaussian K δ s x := by
  ext t ht
  have hsnd : Measurable (fun p : Bool × EuclideanSpace ℝ (Fin n) => p.2) := measurable_snd
  rw [Measure.map_apply hsnd ht,
    properProposalGaussianAux_apply_set hK δ s x (hsnd ht),
    metropolisGaussian_apply_eq_properProposalMixture hK δ s x,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply' _ ht]
  rfl

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.map_snd_properProposalGaussianAux_apply
