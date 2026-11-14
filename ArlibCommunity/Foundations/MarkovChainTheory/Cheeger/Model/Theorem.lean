/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Analysis.Cheeger
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Cheeger's inequality

For a reversible Markov kernel on a general measurable space, the conductance `Φ` and the spectral gap — the infimum of Rayleigh quotients over non-constant square-integrable functions — satisfy `Φ²/2 ≤ gap ≤ 2Φ`.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.Cheeger

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Cheeger's inequality, both directions.** -/
theorem cheeger_inequality {Ω : Type*} [MeasurableSpace Ω] {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hne : (rayleighSet P pi).Nonempty) :
    (conductance P pi).toReal ^ 2 / 2 ≤ spectralGap P pi ∧
      ENNReal.ofReal (spectralGap P pi) ≤ 2 * conductance P pi :=
  cheeger hrev hne

#foundationsModelClosure cheeger_inequality
#print axioms cheeger_inequality

end ArlibCommunity.Foundations.MarkovChainTheory.Cheeger
