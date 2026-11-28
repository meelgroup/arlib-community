/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.IsoConcaveWeight
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.ChordContinuity
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationNeedleInBody
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Cross-ratio isoperimetry (Lovász–Vempala)

For a convex body `K` and a continuous weight `h ≤ 1/3` that is at most `min(1, d_K(u,v))/3` on every chord joining two disjoint sets, the uniform measure of the remainder is at least `E[h]` times the smaller of the two sets' measures, where `d_K` is the cross-ratio distance of `K`.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The weighted cross-ratio isoperimetric inequality** of Lovász–Vempala, for a continuous
weight, with the Localization Lemma and the chord transfer discharged. -/
theorem crossRatio_isoperimetry {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂) :=
  hIso_continuous hKc hKcl hKm hKb hK0 hKtop (htrans_of_compact hKc hKcl hKb)
    (hloc_needle_in_body hn hKc hKcl hKb)

#foundationsModelClosure crossRatio_isoperimetry
#print axioms crossRatio_isoperimetry

end ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry
