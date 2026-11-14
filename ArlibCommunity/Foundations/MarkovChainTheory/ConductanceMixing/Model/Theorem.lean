/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing.Analysis.L2Mixing
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# Mixing from conductance (Lovász–Simonovits)

A reversible chain with nonnegative spectrum, started from an `M`-warm law, is within total variation `√M · (1 - φ²/2)^s` of stationarity after `s` steps, for any `φ` below its conductance.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The Lovász–Simonovits decay bound.** -/
theorem tvLe_iterate_le {Ω : Type*} [MeasurableSpace Ω] {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) (hne : (rayleighSet P pi).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0]
    {M phi : ℝ} (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi)
    (hphi : phi ≤ (conductance P pi).toReal) (s : ℕ) :
    TVLe (iterate P mu0 s) pi (ENNReal.ofReal (Real.sqrt M * (1 - phi ^ 2 / 2) ^ s)) :=
  tvLe_iterate_of_conductance hrev hpsd hne hM hwarm hphi0 hphi s

#foundationsModelClosure tvLe_iterate_le
#print axioms tvLe_iterate_le

end ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing
