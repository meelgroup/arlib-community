/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoMeasurableUncond
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoWeighted
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Isoperimetry for Gaussian-restricted log-concave densities (Cousins–Vempala)

For a density `h = f · e^{-‖x‖²/(2σ²)}` with `f` log-concave, and any measurable partition `S₁, S₂, S₃` of `ℝⁿ` in which `S₁` and `S₂` are separated either in distance or in density ratio, the `h`-mass of `S₃` is large.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.GaussianIsoperimetry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Cousins–Vempala's isoperimetric inequality** (their Theorem 3.4) for measurable sets, at a
log-concave density times a Gaussian. -/
theorem gaussianRestricted_isoperimetry {n : ℕ} (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x :=
  gaussianRestricted_isoperimetry_measurable_logTwo hn hσ hd hf₀ hfc hh hhc hhB hhi hpart
    hS₁ hS₂ hS₃ hmass hsep

/-- **The same inequality for the density `1_K · f · e^{-‖x‖²/(2σ²)}`** on a bounded convex body,
for a continuous log-concave `f` that is positive and Lipschitz in the exponent on `K`. -/
theorem weightedIndicator_isoperimetry {n : ℕ} (hn : 2 ≤ n) {σ d R B Lf : ℝ}
    (hσ : 0 < σ) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hflc : IsLogConcave f) (hfc : Continuous f) (hfB : ∀ x, f x ≤ B)
    (hfKpos : ∀ x ∈ K, 0 < f x)
    (hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v) :
    d / σ * ((∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
      ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
  weightedIndicator_isoperimetry_measurable_logTwo hn hσ hLf hK hKc hKR hK0 hf0 hflc hfc hfB
    hfKpos hfLip hLσ hpart hS₁ hS₂ hS₃ hsep

#foundationsModelClosure gaussianRestricted_isoperimetry
#print axioms gaussianRestricted_isoperimetry
#foundationsModelClosure weightedIndicator_isoperimetry
#print axioms weightedIndicator_isoperimetry

end ArlibCommunity.Foundations.Convex.GaussianIsoperimetry
