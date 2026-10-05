/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset

/-!
# Finite coordinate-marginal resets

This file iterates the history-preserving maximal-coupling reset on a random
function.  Resetting one coordinate leaves every other coordinate marginal
unchanged.  Consequently a finite list of prescribed marginals can be imposed
with exactly the sum of the individual total-variation errors.

The construction does not assert that the reset coordinates are independent.
That distinction is important in the CV18 application: dependence is retained
and later controlled by Lemma 7.17(c).
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Reset one coordinate of a random function to a prescribed marginal while
leaving every other coordinate marginal unchanged. -/
theorem exists_coordinateMarginalReset_of_tvLe
    {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (mu : Measure (ι → X)) (coordinate : ι) (target : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure target]
    {epsilon : ENNReal}
    (hcoordinate : Arlib.TVLe
      (mu.map fun value => value coordinate) target epsilon) :
    ∃ reference : Measure (ι → X),
      IsProbabilityMeasure reference ∧
      Arlib.TVLe mu reference epsilon ∧
      reference.map (fun value => value coordinate) = target ∧
      ∀ other, other ≠ coordinate →
        reference.map (fun value => value other) =
          mu.map fun value => value other := by
  let pair : (ι → X) → (ι → X) × X := fun value =>
    (value, value coordinate)
  let paired := mu.map pair
  have hpair : Measurable pair :=
    measurable_id.prodMk (measurable_pi_apply coordinate)
  let _ : IsProbabilityMeasure paired :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have hpairedSnd : paired.map Prod.snd =
      mu.map (fun value => value coordinate) := by
    rw [show paired = mu.map pair by rfl,
      Measure.map_map measurable_snd hpair]
    rfl
  obtain ⟨reset, hresetProb, hresetFst, hresetSnd, hresetTV⟩ :=
    exists_historyPreservingReset_of_tvLe paired target (by
      rw [hpairedSnd]
      exact hcoordinate)
  let _ : IsProbabilityMeasure reset := hresetProb
  let replace : ((ι → X) × X) → (ι → X) := fun state =>
    Function.update state.1 coordinate state.2
  let reference := reset.map replace
  have hreplace : Measurable replace := by
    exact measurable_update'
  have hreferenceProb : IsProbabilityMeasure reference :=
    Measure.isProbabilityMeasure_map hreplace.aemeasurable
  have hpairedReplace : paired.map replace = mu := by
    rw [show paired = mu.map pair by rfl,
      Measure.map_map hreplace hpair]
    calc
      mu.map (replace ∘ pair) = mu.map id := by
        apply Measure.map_congr
        filter_upwards with value
        simp [replace, pair]
      _ = mu := Measure.map_id
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
  · have hmapped := hresetTV.map hreplace
    simpa only [reference, hpairedReplace] using hmapped
  · calc
      reference.map (fun value => value coordinate) =
          reset.map ((fun value => value coordinate) ∘ replace) :=
        Measure.map_map (measurable_pi_apply coordinate) hreplace
      _ = reset.map Prod.snd := by
        apply Measure.map_congr
        filter_upwards with state
        simp [replace]
      _ = target := hresetSnd
  · intro other hother
    calc
      reference.map (fun value => value other) =
          reset.map ((fun value => value other) ∘ replace) :=
        Measure.map_map (measurable_pi_apply other) hreplace
      _ = reset.map ((fun value => value other) ∘ Prod.fst) := by
        apply Measure.map_congr
        filter_upwards with state
        simp [replace, Function.update, hother]
      _ = (reset.map Prod.fst).map (fun value => value other) :=
        (Measure.map_map (measurable_pi_apply other) measurable_fst).symm
      _ = (paired.map Prod.fst).map (fun value => value other) := by
        rw [hresetFst]
      _ = mu.map (fun value => value other) := by
        rw [show paired = mu.map pair by rfl,
          Measure.map_map measurable_fst hpair]
        have hfstPair : Prod.fst ∘ pair = id := by
          funext value
          rfl
        rw [hfstPair, Measure.map_id]

/-- Sequentially reset the first `count` coordinates of an `ℕ`-indexed
random function.  Coordinates outside that prefix retain their original
marginals, and total variation grows only linearly by `∑ i<count, error i`.
-/
theorem exists_finiteCoordinateMarginalReset
    {X : Type*} [MeasurableSpace X]
    (mu : Measure (ℕ → X)) [IsProbabilityMeasure mu]
    (target : ℕ → Measure X)
    (htargetProb : ∀ i, IsProbabilityMeasure (target i))
    (error : ℕ → ENNReal)
    (hcoordinate : ∀ i,
      Arlib.TVLe (mu.map fun value => value i) (target i) (error i))
    (count : ℕ) :
    ∃ reference : Measure (ℕ → X),
      IsProbabilityMeasure reference ∧
      Arlib.TVLe mu reference (∑ i ∈ Finset.range count, error i) ∧
      (∀ i, i < count →
        reference.map (fun value => value i) = target i) ∧
      (∀ i, count ≤ i →
        reference.map (fun value => value i) =
          mu.map fun value => value i) := by
  induction count with
  | zero =>
      refine ⟨mu, inferInstance, ?_, ?_, ?_⟩
      · simpa using Arlib.TVLe.refl mu
      · intro i hi
        omega
      · intro i _
        rfl
  | succ count ih =>
      obtain ⟨oldReference, holdProb, holdTV, holdExact, holdFuture⟩ := ih
      let _ : IsProbabilityMeasure oldReference := holdProb
      let _ : IsProbabilityMeasure (target count) := htargetProb count
      have holdCoordinate : oldReference.map (fun value => value count) =
          mu.map fun value => value count := holdFuture count le_rfl
      have hresetCoordinate : Arlib.TVLe
          (oldReference.map fun value => value count)
          (target count) (error count) := by
        rw [holdCoordinate]
        exact hcoordinate count
      obtain ⟨reference, hreferenceProb, hstepTV, hnew, hother⟩ :=
        exists_coordinateMarginalReset_of_tvLe
          oldReference count (target count) hresetCoordinate
      refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
      · rw [Finset.sum_range_succ]
        exact holdTV.trans hstepTV
      · intro i hi
        by_cases hinew : i = count
        · subst i
          exact hnew
        · exact (hother i hinew).trans (holdExact i (by omega))
      · intro i hi
        have hinew : i ≠ count := by omega
        exact (hother i hinew).trans (holdFuture i (by omega))

#print axioms exists_coordinateMarginalReset_of_tvLe
#print axioms exists_finiteCoordinateMarginalReset

end

end ArlibCommunity.Algorithms.CV18
