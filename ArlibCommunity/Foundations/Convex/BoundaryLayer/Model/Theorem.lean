/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.BoundaryLayer.Analysis.KLS97Sharp
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# The boundary layer of a convex body (Kannan–Lovász–Simonovits)

For a convex body containing a ball of radius `r`, the average over `x ∈ K` of the volume of `B(x,t) \ K` is at most `10 t √n / (2r)` times the volume of `B(0,t)`: the sharp `√n` order of KLS97, Corollary 4.6.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.BoundaryLayer

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **KLS97 Corollary 4.6 at the sharp order `√n`.** -/
theorem boundaryLayer_le {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {z : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hn : n ≠ 0) (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤) (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (10 * (t * Real.sqrt n) / (2 * r)) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) :=
  lintegral_volume_closedBall_sdiff_le_sqrt hn hKc hKcl hKfin hball hr ht

#foundationsModelClosure boundaryLayer_le
#print axioms boundaryLayer_le

end ArlibCommunity.Foundations.Convex.BoundaryLayer
