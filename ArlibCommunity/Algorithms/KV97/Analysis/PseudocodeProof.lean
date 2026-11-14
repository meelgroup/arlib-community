/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Model.Pseudocode
import ArlibCommunity.Algorithms.KV97.Analysis.RoundLaw
import ArlibCommunity.Algorithms.KV97.Analysis.ProdKernel

/-!
# The pseudocode's output law

The law of the program's output, `output sampler`, puts mass
`∫ Pr[round p = x] dsampler(p)` on a lattice point `x`, and `Pr[round p = x]` is the product
tent kernel `prodTent (toState x) p`.  These two facts turn the program into the integral
that `Analysis/Theorem2.lean` bounds.
-/

namespace ArlibCommunity.Algorithms.KV97.PseudocodeProof

open MeasureTheory

variable {n : ℕ}

/-- `Pr[round p = x]` is the product tent kernel at `p`. -/
theorem round_singleton (p : State n) (x : LatticePoint n) :
    round p {x} = ENNReal.ofReal (prodTent (toState x) p) := by
  rw [round, roundLaw_singleton]
  rfl

/-- Rounding depends measurably on the point being rounded. -/
theorem measurable_round : Measurable (round (n := n)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h : ∀ p : State n, round p s = ∑' z : LatticePoint n, s.indicator (fun z => round p {z}) z :=
    fun p => (Measure.tsum_indicator_apply_singleton (round p) s hs).symm
  simp_rw [h]
  refine Measurable.ennreal_tsum fun z => ?_
  by_cases hz : z ∈ s
  · simp only [Set.indicator_of_mem hz, round_singleton]
    exact ENNReal.measurable_ofReal.comp (measurable_prodTent _)
  · simp only [Set.indicator_of_notMem hz]
    exact measurable_const

/-- **The output law.**  The program returns `x` with probability
`∫ prodTent (toState x) p dsampler(p)`. -/
theorem output_singleton (sampler : Measure (State n)) (x : LatticePoint n) :
    output sampler {x} = ∫⁻ p, ENNReal.ofReal (prodTent (toState x) p) ∂sampler := by
  rw [output, Measure.bind_apply (measurableSet_singleton x) measurable_round.aemeasurable]
  simp_rw [round_singleton]

end ArlibCommunity.Algorithms.KV97.PseudocodeProof
