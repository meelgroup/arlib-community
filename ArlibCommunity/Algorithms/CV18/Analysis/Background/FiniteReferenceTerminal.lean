/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.FiniteReferenceSequence

/-!
# A terminal step after a finite reference sequence

The chronological CV18 construction uses the generic finite-reference
recurrence for its Gaussian prefix and then performs one differently shaped
terminal reset.  This module composes those comparisons while retaining the
exact initial, prefix-sum, and terminal errors.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Append one actual kernel to an already compared finite iteration and
replace its output by a terminal reference law. -/
theorem MeasureLeUpTo.iteratedKernelLaw_bind_then_replace
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S)
    (actualInitial prefixLaw target : Measure S)
    (t : ℕ) {prefixError terminalError : ENNReal}
    (hprefix : MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t) prefixLaw prefixError)
    (hkernelMeasurable : Measurable (actualK t))
    (hkernelProbability : ∀ state, IsProbabilityMeasure (actualK t state))
    (hterminal : MeasureLeUpTo (prefixLaw.bind (actualK t)) target
      terminalError) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK actualInitial t).bind (actualK t)) target
      (prefixError + terminalError) := by
  exact hprefix.bind_then_replace (actualK t) hkernelMeasurable
    hkernelProbability hterminal

/-- Combined finite-reference consumer with a distinct final invariant.
It constructs the Gaussian prefix from an explicit initial replacement,
performs one terminal reference step, and returns the exact accumulated
comparison at the successor horizon. -/
theorem exists_iteratedKernelLaw_le_finiteReference_with_terminal_of_initial
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S)
    (actualInitial referenceInitial : Measure S)
    (Invariant : ℕ → Measure S → Prop)
    (FinalInvariant : Measure S → Prop)
    (stepError : ℕ → ENNReal) (terminalError : ENNReal)
    {initialError : ENNReal}
    (hreferenceInitialProb : IsProbabilityMeasure referenceInitial)
    (hreferenceInitialInvariant : Invariant 0 referenceInitial)
    (hinitial : MeasureLeUpTo actualInitial referenceInitial initialError)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t → ∀ source : Measure S,
      IsProbabilityMeasure source → Invariant i source →
      ∃ target : Measure S,
        IsProbabilityMeasure target ∧
        MeasureLeUpTo (source.bind (actualK i)) target (stepError i) ∧
        Invariant (i + 1) target)
    (hterminal : ∀ source : Measure S,
      IsProbabilityMeasure source → Invariant t source →
      ∃ target : Measure S,
        IsProbabilityMeasure target ∧
        MeasureLeUpTo (source.bind (actualK t)) target terminalError ∧
        FinalInvariant target) :
    ∃ target : Measure S,
      IsProbabilityMeasure target ∧
      FinalInvariant target ∧
      MeasureLeUpTo (iteratedKernelLaw actualK actualInitial (t + 1)) target
        (initialError +
          (∑ i ∈ Finset.range t, stepError i) + terminalError) := by
  obtain ⟨prefixLaw, hprefixProb, hprefixInvariant, hprefixComparison⟩ :=
    exists_iteratedKernelLaw_le_finiteReference_of_initial
      actualK actualInitial referenceInitial Invariant stepError
      hreferenceInitialProb hreferenceInitialInvariant hinitial
      hactualMeas hactualProb t hstep
  obtain ⟨target, htargetProb, hterminalComparison, htargetInvariant⟩ :=
    hterminal prefixLaw hprefixProb hprefixInvariant
  refine ⟨target, htargetProb, htargetInvariant, ?_⟩
  simpa only [iteratedKernelLaw_succ] using
    MeasureLeUpTo.iteratedKernelLaw_bind_then_replace
      actualK actualInitial prefixLaw target t hprefixComparison
      (hactualMeas t) (hactualProb t) hterminalComparison

#print axioms MeasureLeUpTo.iteratedKernelLaw_bind_then_replace
#print axioms
  exists_iteratedKernelLaw_le_finiteReference_with_terminal_of_initial

end

end ArlibCommunity.Algorithms.CV18
