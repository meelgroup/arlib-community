/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.ConvexBodyMixing
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# The lazy ball walk mixes on a polytope

On an inflated polytope containing a ball of radius `γ` and of diameter at most `D`, the lazy ball walk with step `δ ≤ γ`, started `M`-warm, is within total variation `ε` of uniform after an explicit number of steps.  The walk is any Markov kernel whose step is `lazyLaw (ballWalkStep K δ)`; such a kernel exists (`exists_kernel`).

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A kernel whose step at every point is the lazy ball-walk step exists. -/
theorem exists_kernel {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (δ : ℝ) :
    ∃ P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∀ x, P x = lazyLaw (ballWalkStep K δ) x :=
  ⟨lazy (ballWalk K δ), fun x => by rw [ballWalk_eq hKm]; rfl⟩

/-- **Unconditional mixing of the lazy ball walk on an inflated polytope.** -/
theorem lazy_mixes_polytope {n : ℕ} {ι : Type*} (hn : 1 ≤ n)
    (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (κ : ℝ)
    {D : ℝ} (hD : ∀ x ∈ Polytope.inflate A b κ, ∀ y ∈ Polytope.inflate A b κ, dist x y ≤ D)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball c γ ⊆ Polytope.inflate A b κ)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ)
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ x, P x = lazyLaw (ballWalkStep (Polytope.inflate A b κ) δ) x)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (uniformOn volume (Polytope.inflate A b κ)))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min ((γ / (γ + D)) ^ n / 32)
        ((1 / 2 : ℝ) ^ n / D * ((γ / (γ + D)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin P (uniformOn volume (Polytope.inflate A b κ)) mu0 t (ENNReal.ofReal eps) := by
  have hPeq : P = lazy (ballWalk (Polytope.inflate A b κ) δ) := Kernel.ext fun x => by
    rw [hP x, ballWalk_eq (Polytope.measurableSet_inflate A b κ)]; rfl
  subst hPeq
  exact mixesWithin_lazy_ballWalk_polytope hn A b κ hD hγ hball hδ hδγ hM hwarm heps ht

#foundationsModelClosure exists_kernel
#print axioms exists_kernel
#foundationsModelClosure lazy_mixes_polytope
#print axioms lazy_mixes_polytope

end ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing
