/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRandomizedIdealHistory

/-!
# Finite existential reference sequences

The exact-chance argument in CV18 chooses a new reference law after every
phase.  This file packages the finite dependent choice needed to make those
one-step witnesses into one law sequence, and then accumulates their
`MeasureLeUpTo` errors without replacing them by a uniform upper bound.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Law-sequence exact chance with a different additive error at each step. -/
theorem MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_sum
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (actualInitial : Measure S)
    (referenceLaw : ℕ → Measure S) (stepError : ℕ → ENNReal)
    (hinitial : MeasureLeUpTo actualInitial (referenceLaw 0) 0)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t →
      MeasureLeUpTo ((referenceLaw i).bind (actualK i))
        (referenceLaw (i + 1)) (stepError i)) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t) (referenceLaw t)
      (∑ i ∈ Finset.range t, stepError i) := by
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      have ih' := ih fun i hi => hstep i (hi.trans (Nat.lt_succ_self t))
      have hnext := MeasureLeUpTo.bind_then_replace ih' (actualK t)
        (hactualMeas t) (hactualProb t) (hstep t (Nat.lt_succ_self t))
      simpa only [iteratedKernelLaw_succ, Finset.sum_range_succ] using hnext

/-- Law-sequence exact chance with an explicit initial replacement error.
This is the form used when the executable initial state is first reset to a
warm accepted law before the chronological phase recurrence begins. -/
theorem MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_add_sum
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (actualInitial : Measure S)
    (referenceLaw : ℕ → Measure S) (stepError : ℕ → ENNReal)
    {initialError : ENNReal}
    (hinitial : MeasureLeUpTo actualInitial (referenceLaw 0) initialError)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t →
      MeasureLeUpTo ((referenceLaw i).bind (actualK i))
        (referenceLaw (i + 1)) (stepError i)) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t) (referenceLaw t)
      (initialError + ∑ i ∈ Finset.range t, stepError i) := by
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      have ih' := ih fun i hi => hstep i (hi.trans (Nat.lt_succ_self t))
      have hnext := MeasureLeUpTo.bind_then_replace ih' (actualK t)
        (hactualMeas t) (hactualProb t) (hstep t (Nat.lt_succ_self t))
      simpa only [iteratedKernelLaw_succ, Finset.sum_range_succ,
        add_assoc] using hnext

/-- Finitely many existential one-step reference constructions can be chosen
coherently as a single sequence.  `Invariant i` may record all moment,
marginal, and prefix-dependence facts accumulated through phase `i`. -/
theorem exists_finiteReferenceLawSequence
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (initial : Measure S)
    (Invariant : ℕ → Measure S → Prop) (stepError : ℕ → ENNReal)
    (hinitialProb : IsProbabilityMeasure initial)
    (hinitialInvariant : Invariant 0 initial)
    (t : ℕ)
    (hstep : ∀ i, i < t → ∀ source : Measure S,
      IsProbabilityMeasure source → Invariant i source →
      ∃ target : Measure S,
        IsProbabilityMeasure target ∧
        MeasureLeUpTo (source.bind (actualK i)) target (stepError i) ∧
        Invariant (i + 1) target) :
    ∃ referenceLaw : ℕ → Measure S,
      referenceLaw 0 = initial ∧
      (∀ i, i ≤ t → IsProbabilityMeasure (referenceLaw i)) ∧
      (∀ i, i ≤ t → Invariant i (referenceLaw i)) ∧
      ∀ i, i < t →
        MeasureLeUpTo ((referenceLaw i).bind (actualK i))
          (referenceLaw (i + 1)) (stepError i) := by
  induction t with
  | zero =>
      refine ⟨fun _ => initial, rfl, ?_, ?_, ?_⟩
      · intro i hi
        have : i = 0 := by omega
        simpa [this] using hinitialProb
      · intro i hi
        have : i = 0 := by omega
        simpa [this] using hinitialInvariant
      · intro i hi
        omega
  | succ t ih =>
      have hprefix : ∀ i, i < t → ∀ source : Measure S,
          IsProbabilityMeasure source → Invariant i source →
          ∃ target : Measure S,
            IsProbabilityMeasure target ∧
            MeasureLeUpTo (source.bind (actualK i)) target (stepError i) ∧
            Invariant (i + 1) target := by
        intro i hi
        exact hstep i (hi.trans (Nat.lt_succ_self t))
      obtain ⟨referenceLaw, hzero, hprob, hinvariant, hcomparison⟩ :=
        ih hprefix
      obtain ⟨next, hnextProb, hnextComparison, hnextInvariant⟩ :=
        hstep t (Nat.lt_succ_self t) (referenceLaw t)
          (hprob t le_rfl) (hinvariant t le_rfl)
      let extended : ℕ → Measure S := fun i =>
        if i = t + 1 then next else referenceLaw i
      refine ⟨extended, ?_, ?_, ?_, ?_⟩
      · simp [extended, hzero]
      · intro i hi
        by_cases hit : i = t + 1
        · simpa [extended, hit] using hnextProb
        · have hit' : i ≤ t := by omega
          simpa [extended, hit] using hprob i hit'
      · intro i hi
        by_cases hit : i = t + 1
        · simpa [extended, hit] using hnextInvariant
        · have hit' : i ≤ t := by omega
          simpa [extended, hit] using hinvariant i hit'
      · intro i hi
        by_cases hit : i = t
        · subst i
          simpa [extended] using hnextComparison
        · have hlt : i < t := by omega
          have hsucc : i + 1 ≠ t + 1 := by omega
          have hi : i ≠ t + 1 := by omega
          simpa [extended, hit, hi, hsucc] using hcomparison i hlt

/-- Combined consumer: construct the finite reference sequence and compare
the executable iteration directly with its final reference law. -/
theorem exists_iteratedKernelLaw_le_finiteReference
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (initial : Measure S)
    (Invariant : ℕ → Measure S → Prop) (stepError : ℕ → ENNReal)
    (hinitialProb : IsProbabilityMeasure initial)
    (hinitialInvariant : Invariant 0 initial)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t → ∀ source : Measure S,
      IsProbabilityMeasure source → Invariant i source →
      ∃ target : Measure S,
        IsProbabilityMeasure target ∧
        MeasureLeUpTo (source.bind (actualK i)) target (stepError i) ∧
        Invariant (i + 1) target) :
    ∃ reference : Measure S,
      IsProbabilityMeasure reference ∧
      Invariant t reference ∧
      MeasureLeUpTo (iteratedKernelLaw actualK initial t) reference
        (∑ i ∈ Finset.range t, stepError i) := by
  obtain ⟨referenceLaw, hzero, hprob, hinvariant, hstepComparison⟩ :=
    exists_finiteReferenceLawSequence actualK initial Invariant stepError
      hinitialProb hinitialInvariant t hstep
  refine ⟨referenceLaw t, hprob t le_rfl, hinvariant t le_rfl, ?_⟩
  apply MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_sum
    actualK initial referenceLaw stepError
  · simpa [hzero] using MeasureLeUpTo.refl initial
  · exact hactualMeas
  · exact hactualProb
  · exact hstepComparison

/-- Construct a finite reference from a separately supplied initial reference
law and retain the initial replacement error in the final comparison. -/
theorem exists_iteratedKernelLaw_le_finiteReference_of_initial
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S)
    (actualInitial referenceInitial : Measure S)
    (Invariant : ℕ → Measure S → Prop) (stepError : ℕ → ENNReal)
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
        Invariant (i + 1) target) :
    ∃ reference : Measure S,
      IsProbabilityMeasure reference ∧
      Invariant t reference ∧
      MeasureLeUpTo (iteratedKernelLaw actualK actualInitial t) reference
        (initialError + ∑ i ∈ Finset.range t, stepError i) := by
  obtain ⟨referenceLaw, hzero, hprob, hinvariant, hstepComparison⟩ :=
    exists_finiteReferenceLawSequence actualK referenceInitial Invariant
      stepError hreferenceInitialProb hreferenceInitialInvariant t hstep
  refine ⟨referenceLaw t, hprob t le_rfl, hinvariant t le_rfl, ?_⟩
  apply MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_add_sum
    actualK actualInitial referenceLaw stepError
  · simpa [hzero] using hinitial
  · exact hactualMeas
  · exact hactualProb
  · exact hstepComparison

#print axioms MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_sum
#print axioms MeasureLeUpTo.iteratedKernelLaw_le_lawSequence_add_sum
#print axioms exists_finiteReferenceLawSequence
#print axioms exists_iteratedKernelLaw_le_finiteReference
#print axioms exists_iteratedKernelLaw_le_finiteReference_of_initial

end

end ArlibCommunity.Algorithms.CV18
