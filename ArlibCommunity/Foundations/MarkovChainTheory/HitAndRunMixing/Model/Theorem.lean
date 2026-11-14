/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductanceUncond
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunMixingUncond
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Hit-and-run mixes (Lovász–Vempala)

On a convex body containing a unit ball and of diameter at most `D`, in dimension `n ≥ 21`, hit-and-run has conductance at least `1/(2³¹ n D)` (Lovász–Vempala, Theorem 4.2), and its lazy version mixes from a warm start within an explicit number of steps (Theorem 1.1).  The walk is any Markov kernel whose step at every point is `hitAndRunStep`; such a kernel exists (`exists_kernel`).

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A kernel whose step at every point is the hit-and-run step exists. -/
theorem exists_kernel {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) :
    ∃ P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∀ x, P x = hitAndRunStep K x :=
  ⟨hitAndRun K, fun x => by rw [hitAndRun_eq hKm]; rfl⟩

/-- **Lovász–Vempala Theorem 4.2**: the conductance of hit-and-run. -/
theorem conductance_ge {n : ℕ} (hn : 21 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ x, P x = hitAndRunStep K x) :
    ENNReal.ofReal (1 / 8000 / (245760 * (n : ℝ) * D)) ≤ conductance P (uniformOn volume K) := by
  have hPeq : P = hitAndRun K := Kernel.ext fun x => by rw [hP x, hitAndRun_eq hKm]; rfl
  subst hPeq
  exact conductance_hitAndRun_ge_uncond hn hKc hKcl hKm hKb hball hD

/-- **Lovász–Vempala Theorem 1.1**: the lazy hit-and-run walk, started from a law that is
`M`-warm outside an exceptional set of mass at most `ε/2`, is within total variation `ε` of
uniform after `hrDeadlineUncond n D M ε` steps. -/
theorem lazy_mixes {n : ℕ} (hn : 21 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ x, P x = lazyLaw (hitAndRunStep K) x)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    {m : ℕ} (hm : hrDeadlineUncond n D M eps ≤ (m : ℝ)) :
    TVLe (iterate P sigma m) (uniformOn volume K) (ENNReal.ofReal eps) := by
  have hPeq : P = lazy (hitAndRun K) := Kernel.ext fun x => by rw [hP x, hitAndRun_eq hKm]; rfl
  subst hPeq
  exact tvLe_iterate_lazy_hitAndRun_uncond hn hKc hKcl hKm hKb hball hD hM heps0 heps1 hSm hS hdom hm

#foundationsModelClosure exists_kernel
#print axioms exists_kernel
#foundationsModelClosure conductance_ge
#print axioms conductance_ge
#foundationsModelClosure lazy_mixes
#print axioms lazy_mixes

end ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing
