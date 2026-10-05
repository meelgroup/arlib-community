/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# History-preserving replacement of an approximate marginal

This file supplies a generic coupling layer used by the chronological CV18
hybrid argument.  It changes the second coordinate of a joint probability law
to an exact target law while preserving the complete first-coordinate history.
-/

private theorem map_withDensity_comp
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure A) (f : A → X) (g : X → ENNReal)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (mu.withDensity (g ∘ f)) = (Measure.map f mu).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs, ← lintegral_indicator (hf hs),
    lintegral_map (hg.indicator hs) hf]
  apply lintegral_congr
  intro a
  by_cases ha : f a ∈ s <;> simp [ha]

/-- Pull a submeasure of the second marginal back to the whole joint law,
without changing the conditional distribution of the history given the state. -/
private noncomputable def liftSecondSubmeasure
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure (A × X)) (good : Measure X) : Measure (A × X) :=
  mu.withDensity ((good.rnDeriv (Measure.map Prod.snd mu)) ∘ Prod.snd)

private theorem map_snd_liftSecondSubmeasure
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure (A × X)) (good : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure good]
    (hgood : good ≤ Measure.map Prod.snd mu) :
    Measure.map Prod.snd (liftSecondSubmeasure mu good) = good := by
  rw [liftSecondSubmeasure, map_withDensity_comp mu Prod.snd _ measurable_snd
    (Measure.measurable_rnDeriv _ _)]
  exact Measure.withDensity_rnDeriv_eq good (Measure.map Prod.snd mu)
    (Measure.absolutelyContinuous_of_le hgood)

private theorem liftSecondSubmeasure_le
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure (A × X)) (good : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure good]
    (hgood : good ≤ Measure.map Prod.snd mu) :
    liftSecondSubmeasure mu good ≤ mu := by
  rw [liftSecondSubmeasure]
  apply (withDensity_mono ?_).trans_eq withDensity_one
  exact ae_of_ae_map measurable_snd.aemeasurable
    (Measure.rnDeriv_le_one_of_le hgood)

/-- Replace the part of a joint law outside a shared submeasure by an
independent residual coupling.  This is the algebraic core of maximal
coupling; unlike a coupling that only returns two states, it preserves the
entire first coordinate exactly. -/
theorem exists_historyPreservingReset_of_shared
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure (A × X)) (tau : Measure X) (shared : Measure (A × X))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {epsilon : ENNReal}
    (hshared : shared ≤ mu)
    (hsharedTarget : Measure.map Prod.snd shared ≤ tau)
    (hbadMass : (mu - shared) Set.univ ≤ epsilon) :
    ∃ nu : Measure (A × X),
      IsProbabilityMeasure nu ∧
      Measure.map Prod.fst nu = Measure.map Prod.fst mu ∧
      Measure.map Prod.snd nu = tau ∧
      Arlib.TVLe mu nu epsilon := by
  let bad : Measure (A × X) := mu - shared
  let missing : Measure X := tau - Measure.map Prod.snd shared
  let d : ENNReal := bad Set.univ
  letI : IsFiniteMeasure shared := isFiniteMeasure_of_le mu hshared
  have hbad_add : bad + shared = mu := by
    exact Measure.sub_add_cancel_of_le hshared
  have hmissing_add : missing + Measure.map Prod.snd shared = tau := by
    exact Measure.sub_add_cancel_of_le hsharedTarget
  have hmissing_univ : missing Set.univ = d := by
    change (tau - Measure.map Prod.snd shared) Set.univ =
      (mu - shared) Set.univ
    rw [Measure.sub_apply MeasurableSet.univ hsharedTarget,
      Measure.sub_apply MeasurableSet.univ hshared]
    simp only [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ,
      measure_univ]
  by_cases hd : d = 0
  · have hbad_zero : bad = 0 := Measure.measure_univ_eq_zero.mp hd
    have hshared_eq : shared = mu := by
      simpa [hbad_zero] using hbad_add
    have hmissing_zero : missing = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [hmissing_univ, hd]
    have hsnd_eq : Measure.map Prod.snd shared = tau := by
      simpa [hmissing_zero] using hmissing_add
    refine ⟨shared, ?_, ?_, hsnd_eq, ?_⟩
    · rw [hshared_eq]
      infer_instance
    · rw [hshared_eq]
    · rw [hshared_eq]
      exact (Arlib.TVLe.refl mu).mono bot_le
  · have hd_top : d ≠ ⊤ := by
      exact (measure_ne_top bad Set.univ)
    let replacement : Measure (A × X) :=
      (Measure.map Prod.fst bad).prod (d⁻¹ • missing)
    have hrepl_fst :
        Measure.map Prod.fst replacement = Measure.map Prod.fst bad := by
      simp only [replacement, Measure.map_fst_prod, Measure.smul_apply,
        hmissing_univ, smul_eq_mul, ENNReal.inv_mul_cancel hd hd_top, one_smul]
    have hrepl_snd : Measure.map Prod.snd replacement = missing := by
      have hbad_fst_univ : Measure.map Prod.fst bad Set.univ = d := by
        simp [d, Measure.map_apply measurable_fst MeasurableSet.univ]
      simp only [replacement, Measure.map_snd_prod, hbad_fst_univ, smul_smul,
        ENNReal.mul_inv_cancel hd hd_top, one_smul]
    let nu : Measure (A × X) := shared + replacement
    have hshared_add : shared + bad = mu := by
      simpa [add_comm] using hbad_add
    have hnu_fst : Measure.map Prod.fst nu = Measure.map Prod.fst mu := by
      rw [show nu = shared + replacement from rfl,
        Measure.map_add shared replacement measurable_fst, hrepl_fst,
        ← Measure.map_add shared bad measurable_fst, hshared_add]
    have hnu_snd : Measure.map Prod.snd nu = tau := by
      simp only [nu, Measure.map_add shared replacement measurable_snd, hrepl_snd]
      simpa [add_comm] using hmissing_add
    have hnu_prob : IsProbabilityMeasure nu := by
      constructor
      calc
        nu Set.univ = Measure.map Prod.snd nu Set.univ := by
          rw [Measure.map_apply measurable_snd MeasurableSet.univ]
          simp
        _ = 1 := by rw [hnu_snd, measure_univ]
    letI : IsProbabilityMeasure nu := hnu_prob
    have hdom : MeasureLeUpTo mu nu epsilon := by
      refine ⟨bad, ?_, hbadMass⟩
      rw [← hbad_add]
      apply Measure.le_iff'.mpr
      intro s
      simp only [nu, Measure.add_apply]
      calc
        bad s + shared s = shared s + bad s := add_comm _ _
        _ ≤ shared s + replacement s + bad s := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right
              (show shared s ≤ shared s + replacement s from le_add_right le_rfl) (bad s)
    exact ⟨nu, hnu_prob, hnu_fst, hnu_snd, hdom.to_tvLe⟩

private theorem sub_univ_le_of_tvLe
    {X : Type*} [MeasurableSpace X]
    (mu tau : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure tau]
    {epsilon : ENNReal} (h : Arlib.TVLe mu tau epsilon) :
    (mu - tau) Set.univ ≤ epsilon := by
  obtain ⟨S, hS⟩ := exists_isHahnDecomposition mu tau
  have hzero : (mu - tau) S = 0 :=
    Measure.sub_apply_eq_zero_of_isHahnDecomposition hS
  have happly : (mu - tau) Sᶜ = mu Sᶜ - tau Sᶜ := by
    calc
      (mu - tau) Sᶜ = (mu - tau).restrict Sᶜ Set.univ := by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp
      _ = (mu.restrict Sᶜ - tau.restrict Sᶜ) Set.univ := by
        rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
      _ = mu.restrict Sᶜ Set.univ - tau.restrict Sᶜ Set.univ :=
        Measure.sub_apply MeasurableSet.univ hS.compl.le_on
      _ = mu Sᶜ - tau Sᶜ := by
        rw [Measure.restrict_apply MeasurableSet.univ,
          Measure.restrict_apply MeasurableSet.univ]
        simp
  rw [← measure_add_measure_compl hS.measurableSet, hzero, zero_add, happly]
  apply tsub_le_iff_right.mpr
  simpa [add_comm] using h.left hS.measurableSet.compl

/-- A maximal-coupling reset of the second coordinate.  The returned law has
the exact requested state marginal, retains the complete history marginal,
and differs from the original joint law by no more than the state-marginal TV
error.  No countability or standard-Borel assumption is needed. -/
theorem exists_historyPreservingReset_of_tvLe
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (mu : Measure (A × X)) (tau : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {epsilon : ENNReal}
    (h : Arlib.TVLe (Measure.map Prod.snd mu) tau epsilon) :
    ∃ nu : Measure (A × X),
      IsProbabilityMeasure nu ∧
      Measure.map Prod.fst nu = Measure.map Prod.fst mu ∧
      Measure.map Prod.snd nu = tau ∧
      Arlib.TVLe mu nu epsilon := by
  let marginal : Measure X := Measure.map Prod.snd mu
  let excess : Measure X := marginal - tau
  let good : Measure X := marginal - excess
  let shared : Measure (A × X) := liftSecondSubmeasure mu good
  have hexcess_le : excess ≤ marginal := by
    exact Measure.sub_le
  letI : IsFiniteMeasure excess := isFiniteMeasure_of_le marginal hexcess_le
  have hgood_le_marginal : good ≤ marginal := Measure.sub_le
  letI : IsFiniteMeasure good := isFiniteMeasure_of_le marginal hgood_le_marginal
  have hmarginal_le : marginal ≤ tau + excess := by
    have hle := (Measure.sub_le_iff_le_add
      (μ := marginal) (ν := tau) (ξ := excess)).mp le_rfl
    simpa [excess, add_comm] using hle
  have hgood_le_tau : good ≤ tau := by
    exact Measure.sub_le_of_le_add hmarginal_le
  have hshared_snd : Measure.map Prod.snd shared = good := by
    exact map_snd_liftSecondSubmeasure mu good hgood_le_marginal
  have hshared_le : shared ≤ mu :=
    liftSecondSubmeasure_le mu good hgood_le_marginal
  letI : IsFiniteMeasure shared := isFiniteMeasure_of_le mu hshared_le
  have hshared_univ : shared Set.univ = good Set.univ := by
    calc
      shared Set.univ = Measure.map Prod.snd shared Set.univ := by
        rw [Measure.map_apply measurable_snd MeasurableSet.univ]
        simp
      _ = good Set.univ := by rw [hshared_snd]
  have hexcess_mass : excess Set.univ ≤ epsilon := by
    exact sub_univ_le_of_tvLe marginal tau h
  have hbad_mass : (mu - shared) Set.univ ≤ epsilon := by
    calc
      (mu - shared) Set.univ = mu Set.univ - shared Set.univ :=
        Measure.sub_apply MeasurableSet.univ hshared_le
      _ = marginal Set.univ - good Set.univ := by
        rw [hshared_univ]
        congr 1
        simp [marginal, Measure.map_apply measurable_snd MeasurableSet.univ]
      _ = excess Set.univ := by
        rw [show good Set.univ = marginal Set.univ - excess Set.univ by
          exact Measure.sub_apply MeasurableSet.univ hexcess_le]
        exact ENNReal.sub_sub_cancel (measure_ne_top marginal Set.univ) (hexcess_le Set.univ)
      _ ≤ epsilon := hexcess_mass
  exact exists_historyPreservingReset_of_shared mu tau shared hshared_le
    (hshared_snd.le.trans hgood_le_tau) hbad_mass

#print axioms exists_historyPreservingReset_of_shared
#print axioms exists_historyPreservingReset_of_tvLe

end ArlibCommunity.Algorithms.CV18
