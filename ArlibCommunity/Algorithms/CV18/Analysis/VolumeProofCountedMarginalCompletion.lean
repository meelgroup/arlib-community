/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance
import Mathlib.Probability.Kernel.Disintegration.Integral

/-! # Cost-preserving completion of an approximate endpoint marginal -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem compProd_mono_left_cv18
    {S C : Type*} [MeasurableSpace S] [MeasurableSpace C]
    {mu nu : Measure S} [SFinite mu] [SFinite nu]
    (h : mu ≤ nu) (K : Kernel S C) [IsSFiniteKernel K] :
    mu.compProd K ≤ nu.compProd K := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA]
  exact lintegral_mono' h le_rfl

private theorem isFiniteMeasure_bind_probability_cv18
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (mu : Measure S) [IsFiniteMeasure mu] (K : S → Measure T)
    (hKmeas : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state)) :
    IsFiniteMeasure (mu.bind K) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hKmeas.aemeasurable]
  have hmass : ∀ state, K state Set.univ = 1 := fun state =>
    @measure_univ _ _ (K state) (hKprob state)
  simp_rw [hmass]
  simp

/-- A small additive error in the endpoint marginal of a counted law can be
lifted to the full counted law without paying a syntactic cost cap.

The reference keeps the largest sublaw needed from the original experiment,
and completes the missing endpoint mass at count zero.  Consequently its
endpoint marginal is exactly `target`, its expected count is no larger than
the original expected count, and the discarded joint mass is at most the
original marginal error. -/
theorem exists_countedReference_of_fst_leUpTo
    {S : Type*} [MeasurableSpace S]
    (joint : Measure (S × ℕ)) [IsFiniteMeasure joint]
    (target : Measure S) [IsFiniteMeasure target]
    {delta : ENNReal}
    (hmargin : MeasureLeUpTo joint.fst target delta) :
    ∃ reference : Measure (S × ℕ),
      MeasureLeUpTo joint reference delta ∧
      reference.fst = target ∧
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) ≤
        ∫⁻ outcome, (outcome.2 : ENNReal) ∂joint := by
  let marginal := joint.fst
  let badMarginal := marginal - target
  let conditional : Kernel S ℕ := joint.condKernel
  let badJoint := badMarginal.compProd conditional
  let goodJoint := joint - badJoint
  have hbadMarginal : badMarginal ≤ marginal := by
    exact Measure.sub_le
  have hbadJoint : badJoint ≤ joint := by
    calc
      badJoint ≤ marginal.compProd conditional :=
        compProd_mono_left_cv18 hbadMarginal conditional
      _ = joint := by
        exact joint.disintegrate conditional
  have hsplit : goodJoint + badJoint = joint := by
    exact Measure.sub_add_cancel_of_le hbadJoint
  have hmarginalLe : marginal ≤ badMarginal + target := by
    exact (Measure.sub_le_iff_le_add (μ := marginal) (ν := target)
      (ξ := badMarginal)).mp le_rfl
  have hjointLe : joint ≤ target.compProd conditional + badJoint := by
    calc
      joint = marginal.compProd conditional :=
        (joint.disintegrate conditional).symm
      _ ≤ (badMarginal + target).compProd conditional :=
        compProd_mono_left_cv18 hmarginalLe conditional
      _ = badJoint + target.compProd conditional := by
        rw [Measure.compProd_add_left]
      _ = target.compProd conditional + badJoint := add_comm _ _
  have hgoodJoint : goodJoint ≤ target.compProd conditional := by
    exact Measure.sub_le_of_le_add (by simpa [add_comm] using hjointLe)
  have hgoodMargin : goodJoint.fst ≤ target := by
    calc
      goodJoint.fst ≤ (target.compProd conditional).fst := by
        exact Measure.map_mono hgoodJoint measurable_fst
      _ = target := Measure.fst_compProd target conditional
  let missing := target - goodJoint.fst
  let zeroCount : S → S × ℕ := fun state => (state, 0)
  let reference := goodJoint + missing.map zeroCount
  refine ⟨reference, ?_, ?_, ?_⟩
  · obtain ⟨error, hle, herror⟩ := hmargin
    have hbadMarginalError : badMarginal ≤ error := by
      apply Measure.sub_le_of_le_add
      simpa [add_comm] using hle
    have hbadMass : badMarginal Set.univ ≤ delta := by
      exact (Measure.le_iff'.mp hbadMarginalError Set.univ).trans herror
    refine ⟨badJoint, ?_, ?_⟩
    · rw [← hsplit]
      change goodJoint + badJoint ≤
        (goodJoint + missing.map zeroCount) + badJoint
      exact add_le_add (Measure.le_add_right le_rfl) le_rfl
    · simpa [badJoint] using hbadMass
  · have hmissingSplit : missing + goodJoint.fst = target := by
      exact Measure.sub_add_cancel_of_le hgoodMargin
    change (goodJoint + missing.map zeroCount).map Prod.fst = target
    rw [Measure.map_add goodJoint (missing.map zeroCount) measurable_fst]
    change goodJoint.fst + (missing.map zeroCount).map Prod.fst = target
    rw [Measure.map_map measurable_fst (by fun_prop)]
    have hcomp : Prod.fst ∘ zeroCount = id := by
      funext state
      rfl
    rw [hcomp, Measure.map_id]
    simpa [add_comm] using hmissingSplit
  · have hgoodLe : goodJoint ≤ joint := Measure.sub_le
    calc
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) =
          (∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint) +
            ∫⁻ outcome, (outcome.2 : ENNReal) ∂missing.map zeroCount := by
        rw [lintegral_add_measure]
      _ = (∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint) + 0 := by
        congr 1
        rw [lintegral_map (by fun_prop) (by fun_prop)]
        simp
      _ = ∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint := add_zero _
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂joint :=
        lintegral_mono' hgoodLe le_rfl

/-- Chronological counted-reference induction.

At each stage, the executable counted kernel is run from the already
completed reference prefix.  The only state-distribution fact exposed to the
next phase is the exact first marginal.  `exists_countedReference_of_fst_leUpTo`
then discards the new endpoint error and fills its missing mass at count zero.
Thus errors add as probabilities, while expected query counts add only the
per-phase reference costs; there is no `cost cap * error` term. -/
theorem exists_countedReference_iteratedKernelLaw
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → (S × ℕ) → Measure (S × ℕ))
    (actualInitial : Measure (S × ℕ)) [IsFiniteMeasure actualInitial]
    (ideal : ℕ → Measure S)
    {initialError : ENNReal} (stepError phaseCost : ℕ → ENNReal)
    (hidealFinite : ∀ i, IsFiniteMeasure (ideal i))
    (hinitial : MeasureLeUpTo actualInitial.fst (ideal 0) initialError)
    (hKmeas : ∀ i, Measurable (actualK i))
    (hKprob : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i (rho : Measure (S × ℕ)),
      IsFiniteMeasure rho → rho.fst = ideal i →
      MeasureLeUpTo ((rho.bind (actualK i)).fst) (ideal (i + 1))
          (stepError i) ∧
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂rho.bind (actualK i)) ≤
        (∫⁻ outcome, (outcome.2 : ENNReal) ∂rho) + phaseCost i) :
    ∀ t, ∃ reference : Measure (S × ℕ),
      MeasureLeUpTo (iteratedKernelLaw actualK actualInitial t) reference
        (initialError + ∑ i ∈ Finset.range t, stepError i) ∧
      reference.fst = ideal t ∧
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) ≤
        (∫⁻ outcome, (outcome.2 : ENNReal) ∂actualInitial) +
          ∑ i ∈ Finset.range t, phaseCost i := by
  intro t
  induction t with
  | zero =>
      let _ : IsFiniteMeasure (ideal 0) := hidealFinite 0
      obtain ⟨reference, hdom, hmarginal, hcost⟩ :=
        exists_countedReference_of_fst_leUpTo actualInitial (ideal 0) hinitial
      refine ⟨reference, ?_, hmarginal, ?_⟩
      · simpa using hdom
      · simpa using hcost
  | succ t ih =>
      obtain ⟨reference, hdom, hmarginal, hcost⟩ := ih
      have hreferenceFinite : IsFiniteMeasure reference := ⟨by
        rw [← Measure.fst_univ, hmarginal]
        exact measure_lt_top (ideal t) Set.univ⟩
      let _ : IsFiniteMeasure reference := hreferenceFinite
      let _ : IsFiniteMeasure (ideal (t + 1)) := hidealFinite (t + 1)
      have hphase := hstep t reference hreferenceFinite hmarginal
      let _ : IsFiniteMeasure (reference.bind (actualK t)) :=
        isFiniteMeasure_bind_probability_cv18 reference (actualK t)
          (hKmeas t) (hKprob t)
      obtain ⟨nextReference, hnextDom, hnextMarginal, hnextCost⟩ :=
        exists_countedReference_of_fst_leUpTo
          (reference.bind (actualK t)) (ideal (t + 1)) hphase.1
      refine ⟨nextReference, ?_, hnextMarginal, ?_⟩
      · have hbind := hdom.bind_same (hKmeas t) (hKprob t)
        simpa only [iteratedKernelLaw_succ, Finset.sum_range_succ,
          add_assoc] using hbind.trans hnextDom
      · calc
          (∫⁻ outcome, (outcome.2 : ENNReal) ∂nextReference) ≤
              ∫⁻ outcome, (outcome.2 : ENNReal)
                ∂reference.bind (actualK t) := hnextCost
          _ ≤ (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) +
              phaseCost t := hphase.2
          _ ≤ ((∫⁻ outcome, (outcome.2 : ENNReal) ∂actualInitial) +
                ∑ i ∈ Finset.range t, phaseCost i) + phaseCost t := by
              gcongr
          _ = (∫⁻ outcome, (outcome.2 : ENNReal) ∂actualInitial) +
                ∑ i ∈ Finset.range (t + 1), phaseCost i := by
              rw [Finset.sum_range_succ]
              exact add_assoc _ _ _

#print axioms exists_countedReference_of_fst_leUpTo
#print axioms exists_countedReference_iteratedKernelLaw

end ArlibCommunity.Algorithms.CV18
