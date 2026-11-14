/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Prelude
import ArlibCommunity.Foundations.Convex.ConvexIsoperimetry.Analysis.IsoBall
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Isoperimetry for convex bodies

For a convex body `K` of diameter at most `D`, two subsets at distance `d` force the remainder of `K` to carry measure at least proportional to `d/D` times the product of their measures.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.ConvexIsoperimetry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The three-set isoperimetric inequality for a convex body**, in volumes. -/
theorem isoperimetry_volume {n : ℕ} {K A B : Set (EuclideanSpace ℝ (Fin n))} {d D : ℝ} (hd : 0 < d)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ENNReal.ofReal (d / D) * volume A * volume B
      ≤ 2 ^ n * volume ((K \ A) \ B) * volume K :=
  volume_mul_volume_le_of_separated hd hK hKm hA hB hAK hBK hsep hdiam

/-- **The same inequality for the uniform probability measure on `K`.** -/
theorem isoperimetry_uniformOn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {D : ℝ}
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n / D) * ENNReal.ofReal d
          * uniformOn volume K A * uniformOn volume K B
        ≤ uniformOn volume K ((K \ A) \ B) :=
  uniformOn_iso_of_convex hK hKm hK0 hKtop hdiam

#foundationsModelClosure isoperimetry_volume
#print axioms isoperimetry_volume
#foundationsModelClosure isoperimetry_uniformOn
#print axioms isoperimetry_uniformOn

end ArlibCommunity.Foundations.Convex.ConvexIsoperimetry
