/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.ProblemSetting
import ArlibCommunity.Algorithms.HitAndRun.Model.Pseudocode

/-!
# Proof of the unconditional hit-and-run mixing theorem

The imported background discharges the overlap, localization,
isoperimetry/conductance, warm-start, and lazy-chain arguments.  The theorem
below is the small model-facing assembly of that chain.
-/

namespace ArlibCommunity.Algorithms.HitAndRun.TheoremProof

open MeasureTheory
open scoped ENNReal

theorem hitAndRun_mixes {n : ℕ} (hn : 21 ≤ n) (p : Problem n)
    {sigma : Measure (State n)} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (State n)} (hWarm : WarmStart p.body sigma M eps S)
    {m : ℕ} (hm : deadline n p.diameter M eps ≤ (m : ℝ)) :
    Arlib.TVLe (run p.body sigma m) (target p.body) (ENNReal.ofReal eps) := by
  rcases hWarm with ⟨hSm, hS, hdom⟩
  simpa [run, lazyStep, step, target] using
    Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_uncond hn
      p.convex_body p.closed_body p.measurable_body p.bounded_body
      p.unitBall_subset p.diam_le hM heps0 heps1 hSm hS hdom
      (by simpa [deadline, Arlib.MarkovChains.hrDeadlineUncond] using hm)

end ArlibCommunity.Algorithms.HitAndRun.TheoremProof
