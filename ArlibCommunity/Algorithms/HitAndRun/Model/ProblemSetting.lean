/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Prelude
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Hit-and-run problem setting

The geometric hypotheses of the Lovász hit-and-run theorem are packaged as
data: a convex, closed, measurable, bounded body which contains a Euclidean
unit ball and whose diameter is at most `diameter`.  The body is accessed only through a
membership oracle; the target is the uniform law on it.
-/

namespace ArlibCommunity.Algorithms.HitAndRun

open MeasureTheory

/-- A rounded convex body together with the diameter parameter appearing in
the mixing bound. -/
structure Problem (n : ℕ) where
  body : Body n
  center : State n
  diameter : ℝ
  convex_body : Convex ℝ body
  closed_body : IsClosed body
  measurable_body : MeasurableSet body
  bounded_body : Bornology.IsBounded body
  unitBall_subset : Metric.closedBall center 1 ⊆ body
  diam_le : Metric.diam body ≤ diameter

/-- **The target distribution**: normalized Lebesgue measure on the body,
`vol(K ∩ ·) / vol(K)`. -/
noncomputable def target {n : ℕ} (K : Body n) : Measure (State n) :=
  (volume K)⁻¹ • volume.restrict K

/-- The exceptional-set warm-start condition used in the paper's mixing
argument.  Outside `S`, the initial law is at most `M` times uniform measure. -/
def WarmStart {n : ℕ} (K : Body n) (sigma : Measure (State n))
    (M eps : ℝ) (S : Set (State n)) : Prop :=
  MeasurableSet S ∧
    sigma S ≤ ENNReal.ofReal (eps / 2) ∧
    ∀ A : Set (State n), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * target K A


/-- **Exact black-box membership access** to the body. -/
structure MembershipOracle {n : ℕ} (p : Problem n) where
  query : State n → Bool
  correct : ∀ x, query x = true ↔ x ∈ p.body

end ArlibCommunity.Algorithms.HitAndRun
