/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisIsoperimetry
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.OverlapPerPair
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Conductance of the Gaussian walks (Cousins–Vempala)

Conductance lower bounds of order `δ/(σ√n)` for the Metropolis-filtered Gaussian ball walk and for the speedy Metropolis–Gaussian walk on a bounded convex body.  Each walk is any Markov kernel whose step is the corresponding step law; such kernels exist (`exists_metropolisKernel`, `exists_speedyKernel`).

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A kernel whose step at every point is the Metropolis–Gaussian step exists. -/
theorem exists_metropolisKernel {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    ∃ P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∀ x, P x = metropolisGaussianStep K δ s x :=
  ⟨metropolisGaussian K δ s, fun _ => rfl⟩

/-- A kernel whose step at every point is the speedy Metropolis–Gaussian step exists. -/
theorem exists_speedyKernel {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ s : ℝ) :
    ∃ P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∀ x, P x = speedyMetropolisGaussianStep K δ s x :=
  ⟨speedyMetropolisGaussian K δ s, fun x => by rw [speedyMetropolisGaussian_eq hK]; rfl⟩

/-- **Conductance of the Metropolis-filtered Gaussian ball walk** on a bounded convex body, at
step `δ ≤ σ/(8√n)`, given a floor `θ` on the local conductance. -/
theorem metropolis_conductance_ge {n : ℕ} (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n)
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ x, P x = metropolisGaussianStep K δ (σ ^ 2) x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance P (uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (σ ^ 2))) K) := by
  have hPeq : P = metropolisGaussian K δ (σ ^ 2) := Kernel.ext fun x => hP x
  subst hPeq
  exact conductance_metropolisGaussian_sharp_sqrt_ge_of_convex hn hσ hδ hδσ hR hK hKc hKR hKtop
    hK0 hell hfloor hRσ

/-- **Conductance of the speedy Metropolis–Gaussian walk** with respect to its `ℓ`-weighted
Gaussian target, in dimension `n ≥ 21`. -/
theorem speedy_conductance_ge {n : ℕ} (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ x, P x = speedyMetropolisGaussianStep K δ (σ ^ 2) x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance P (ellGaussianProb K δ (σ ^ 2)) := by
  have hPeq : P = speedyMetropolisGaussian K δ (σ ^ 2) := Kernel.ext fun x => by
    rw [hP x, speedyMetropolisGaussian_eq hK]; rfl
  subst hPeq
  exact conductance_speedyMetropolisGaussian_ge_uncond hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ

#foundationsModelClosure exists_metropolisKernel
#print axioms exists_metropolisKernel
#foundationsModelClosure exists_speedyKernel
#print axioms exists_speedyKernel
#foundationsModelClosure metropolis_conductance_ge
#print axioms metropolis_conductance_ge
#foundationsModelClosure speedy_conductance_ge
#print axioms speedy_conductance_ge

end ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance
