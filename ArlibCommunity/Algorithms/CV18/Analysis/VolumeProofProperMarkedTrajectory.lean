/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperTrajectory
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MarkedTimeChange

/-!
# The proper-proposal clock on an actual Gaussian Metropolis trajectory

`properProposalGaussianAux` exposes the Boolean event that the proposal landed in the body.
This file turns that one-step coupling into a homogeneous chain on `Bool × X`.  The second
coordinate is the real Gaussian Metropolis chain, while a `false` first coordinate records an
improper proposal and forces the position to remain fixed.

The principal path-level result is the exact geometric law, and hence exact mean, of the
waiting time for the first proper proposal.  It is deliberately different from the accepted
move clock in `WastedStepsGaussian`: a proper proposal can be rejected by the Gaussian
Metropolis filter.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## The homogeneous marked trajectory -/

/-- The marked proposal kernel lifted to the product state space.  The incoming mark is
irrelevant; the new mark describes the transition which has just been made. -/
noncomputable def properProposalGaussianLift
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (Bool × EuclideanSpace ℝ (Fin n)) (Bool × EuclideanSpace ℝ (Fin n)) :=
  Kernel.comap (properProposalGaussianAux K hK δ s) Prod.snd measurable_snd

@[simp] theorem properProposalGaussianLift_apply
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    properProposalGaussianLift K hK δ s p = properProposalGaussianAux K hK δ s p.2 := rfl

instance isMarkovKernel_properProposalGaussianLift
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalGaussianLift K hK δ s) := by
  rw [properProposalGaussianLift]
  infer_instance

/-- Forgetting the mark after one lifted transition gives exactly one transition of the
ordinary Gaussian Metropolis kernel. -/
theorem map_snd_properProposalGaussianLift_apply
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    (properProposalGaussianLift K hK δ s p).map Prod.snd =
      metropolisGaussian K δ s p.2 := by
  rw [properProposalGaussianLift_apply]
  exact map_snd_properProposalGaussianAux_apply hK δ s p.2

/-- Kernel-level form of the projection identity.  This is the lumping relation which says
that the second coordinate of the lifted chain evolves autonomously by `metropolisGaussian`.
-/
theorem map_snd_properProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel.map (properProposalGaussianLift K hK δ s) Prod.snd =
      Kernel.comap (metropolisGaussian K δ s) Prod.snd measurable_snd := by
  ext p
  rw [Kernel.map_apply _ measurable_snd, Kernel.comap_apply,
    map_snd_properProposalGaussianLift_apply hK δ s]

/-- At every deterministic time, the position coordinate of the lifted trajectory has the
same law as the actual Gaussian Metropolis trajectory.  Thus the marked construction is a
genuine coupling to the sampler rather than a separate chain with only matching coefficients.
-/
theorem map_state_eval_pathMeasure_properProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) (a : ℕ) :
    (pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac p)).map
        (fun ω => (ω a).2) =
      (pathMeasure (metropolisGaussian K δ s) (Measure.dirac p.2)).map
        (fun ω => ω a) := by
  induction a with
  | zero =>
      rw [show (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => (ω 0).2) =
          Prod.snd ∘ (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => ω 0) from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply 0),
        map_eval_pathMeasure_zero, map_eval_pathMeasure_zero,
        Measure.map_dirac]
  | succ a ih =>
      have ih' :
          (pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac p)).map
              (Prod.snd ∘ fun ω => ω a) =
            (pathMeasure (metropolisGaussian K δ s) (Measure.dirac p.2)).map
              (fun ω => ω a) := by
        change (pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac p)).map
            (fun ω => (ω a).2) = _
        exact ih
      rw [show (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => (ω (a + 1)).2) =
          Prod.snd ∘ (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => ω (a + 1)) from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply (a + 1)),
        map_eval_pathMeasure_succ, Measure.map_comp _ _ measurable_snd,
        map_snd_properProposalGaussianLift hK δ s,
        bind_comap, Measure.map_map measurable_snd (measurable_pi_apply a),
        ih', map_eval_pathMeasure_succ]

/-- An improper proposal has exactly mass `1 - ell`; on this branch the position is forced
to remain at its previous value. -/
theorem properProposalGaussianLift_apply_false_singleton
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    properProposalGaussianLift K hK δ s p {(false, p.2)} = 1 - ell K δ p.2 := by
  have hempty :
      (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) ⁻¹' {(false, p.2)} = ∅ := by
    ext y
    simp
  rw [properProposalGaussianLift_apply,
    properProposalGaussianAux_apply_set hK δ s p.2 (measurableSet_singleton _)]
  rw [hempty, measure_empty, mul_zero, zero_add]
  simp

/-- The proper branch has subprobability law `ell(x)` times the speedy kernel.  This is the
one-renewal identity from which the marked-chain law would follow after a strong-Markov
argument at successive marked times. -/
theorem properProposalGaussianLift_apply_true_prod
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    properProposalGaussianLift K hK δ s p ({true} ×ˢ t) =
      ell K δ p.2 * speedyMetropolisGaussian K δ s p.2 t := by
  rw [properProposalGaussianLift_apply,
    properProposalGaussianAux_apply_set hK δ s p.2 (measurableSet_singleton true |>.prod ht)]
  simp

/-! ## Exact proper-proposal waiting time -/

/-- Along the actual lifted trajectory, the probability that the first `k` transitions were
all improper is `(1 - ell K δ x)^k`.  With initial mark `false`, that event is equivalently
that the lifted chain is still at `(false,x)` through time `k`. -/
theorem pathMeasure_properProposalGaussianLift_dirac_holdsUntil
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))
        {ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = (false, x)}
      = (1 - ell K δ x) ^ k := by
  rw [pathMeasure_dirac_holdsUntil,
    properProposalGaussianLift_apply_false_singleton hK δ s]

/-- The tail sum of the first-proper-proposal time is exactly `ell(x)⁻¹`. -/
theorem tsum_pathMeasure_properProposalGaussianLift_dirac_holdsUntil
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑' k : ℕ, pathMeasure (properProposalGaussianLift K hK δ s)
        (Measure.dirac (false, x))
        {ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = (false, x)}
      = (ell K δ x)⁻¹ := by
  simp_rw [pathMeasure_properProposalGaussianLift_dirac_holdsUntil hK δ s]
  rw [ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (ell_le_one K δ x)]

/-- Integral (tail-sum) form of the expected number of ordinary Metropolis transitions until
the first proper proposal. -/
theorem lintegral_firstProperTime_pathMeasure_properProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ ω, (∑' k : ℕ,
        {ω' : ℕ → Bool × EuclideanSpace ℝ (Fin n) |
          ∀ i ≤ k, ω' i = (false, x)}.indicator
            (1 : (ℕ → Bool × EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
      ∂(pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x)))
      = (ell K δ x)⁻¹ := by
  rw [lintegral_tsum fun k =>
    (measurable_one.indicator (measurableSet_holdsUntil (false, x) k)).aemeasurable]
  have h : ∀ k : ℕ,
      ∫⁻ ω, {ω' : ℕ → Bool × EuclideanSpace ℝ (Fin n) |
          ∀ i ≤ k, ω' i = (false, x)}.indicator
            (1 : (ℕ → Bool × EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω
        ∂(pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x)))
        = pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))
            {ω' : ℕ → Bool × EuclideanSpace ℝ (Fin n) |
              ∀ i ≤ k, ω' i = (false, x)} :=
    fun k => lintegral_indicator_one (measurableSet_holdsUntil (false, x) k)
  simp_rw [h]
  exact tsum_pathMeasure_properProposalGaussianLift_dirac_holdsUntil hK δ s x

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.map_snd_properProposalGaussianLift_apply
#print axioms Arlib.MarkovChains.map_snd_properProposalGaussianLift
#print axioms Arlib.MarkovChains.map_state_eval_pathMeasure_properProposalGaussianLift
#print axioms Arlib.MarkovChains.properProposalGaussianLift_apply_false_singleton
#print axioms Arlib.MarkovChains.properProposalGaussianLift_apply_true_prod
#print axioms Arlib.MarkovChains.pathMeasure_properProposalGaussianLift_dirac_holdsUntil
#print axioms Arlib.MarkovChains.tsum_pathMeasure_properProposalGaussianLift_dirac_holdsUntil
#print axioms Arlib.MarkovChains.lintegral_firstProperTime_pathMeasure_properProposalGaussianLift
