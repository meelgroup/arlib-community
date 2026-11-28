/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationNeedleInBody
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# The Localization Lemma

Kannan–Lovász–Simonovits: if continuous `g₁, g₂` on a convex body satisfy `∫_K g₁ = 0 < ∫_K g₂`, then there is a needle — a segment inside `K` with a log-concave density `D` on it — on which the same holds.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.Localization

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The Localization Lemma**, one equality and one strict inequality, with the needle inside
the body. -/
theorem localization {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K) :
    ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t :=
  hloc_needle_in_body hn hKc hKcl hKb

#foundationsModelClosure localization
#print axioms localization

end ArlibCommunity.Foundations.Convex.Localization
