/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.BrunnMinkowski.Model.Prelude
import ArlibCommunity.Foundations.Convex.BrunnMinkowski.Analysis.BrunnSharp
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# The Brunn–Minkowski inequality and Brunn's theorem

The sharp, `1/n`-concave Brunn–Minkowski inequality for nonempty measurable sets of `ℝⁿ`, and Brunn's theorem that the `1/m`-th power of the slice volume of a convex body is concave.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.BrunnMinkowski

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped Pointwise in
/-- **The sharp Brunn–Minkowski inequality in `ℝⁿ`.** -/
theorem brunn_minkowski {n : ℕ} (hn : n ≠ 0) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ (1 / (n : ℝ))
        + ENNReal.ofReal (1 - lam) * volume B ^ (1 / (n : ℝ))
      ≤ volume (lam • A + (1 - lam) • B) ^ (1 / (n : ℝ)) :=
  brunn_minkowski_sharp hn hlam0 hlam1 hA hB hAne hBne

/-- **Brunn's theorem.**  For a convex measurable `K ⊆ ℝ^(m+1)`, the `1/m`-th power of the
volume of the slice at `t` is concave on any interval of nonempty, finite-volume slices. -/
theorem brunn_slice_concave {m : ℕ} (hm : m ≠ 0) {K : Set (Fin (m + 1) → ℝ)}
    (hKconv : Convex ℝ K) (hKmeas : MeasurableSet K) {S : Set ℝ} (hS : Convex ℝ S)
    (hne : ∀ t ∈ S, (slice K t).Nonempty) (hfin : ∀ t ∈ S, volume (slice K t) ≠ ⊤) :
    ConcaveOn ℝ S (fun t => (volume (slice K t)).toReal ^ (1 / (m : ℝ))) :=
  brunn_slice_concaveOn hm hKconv hKmeas hS hne hfin

#foundationsModelClosure brunn_minkowski
#print axioms brunn_minkowski
#foundationsModelClosure brunn_slice_concave
#print axioms brunn_slice_concave

end ArlibCommunity.Foundations.Convex.BrunnMinkowski
