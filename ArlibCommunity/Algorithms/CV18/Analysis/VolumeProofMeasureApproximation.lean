/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ContinuousProgramSemantics
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.TV
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Additive domination of probability experiments

The paper repeatedly replaces a warm-start walk output by a stationary draw.
For the final failure estimate only the one-sided consequence of total
variation is needed.  `MeasureLeUpTo μ ν δ` records that `μ` is dominated by
`ν` plus an error measure of total mass at most `δ`.  Unlike a supremum-over-
events definition, this form composes directly through dependent Giry binds.
-/

/-- `μ ≤[δ] ν` means that `μ` is bounded by `ν` plus a positive error measure
whose total mass is at most `δ`. -/
def MeasureLeUpTo {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (δ : ENNReal) : Prop :=
  ∃ error : Measure α, μ ≤ ν + error ∧ error Set.univ ≤ δ

/-- A total-variation estimate between finite measures supplies the positive
error measure required by dependent `MeasureLeUpTo` composition, with no loss
in the error budget.  The error is the positive measure difference `μ - ν`;
Hahn decomposition identifies its total mass with a single measurable-event
discrepancy controlled by TV. -/
theorem MeasureLeUpTo.of_tvLe
    {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ENNReal} (h : Arlib.TVLe μ ν ε) :
    MeasureLeUpTo μ ν ε := by
  let error : Measure α := μ - ν
  refine ⟨error, ?_, ?_⟩
  · have hle := (Measure.sub_le_iff_le_add
      (μ := μ) (ν := ν) (ξ := error)).mp le_rfl
    simpa [error, add_comm] using hle
  · obtain ⟨S, hS⟩ := exists_isHahnDecomposition μ ν
    have hzero : error S = 0 := by
      exact Measure.sub_apply_eq_zero_of_isHahnDecomposition hS
    have happly : error Sᶜ = μ Sᶜ - ν Sᶜ := by
      calc
        error Sᶜ = error.restrict Sᶜ Set.univ := by
          rw [Measure.restrict_apply MeasurableSet.univ]
          simp
        _ = (μ.restrict Sᶜ - ν.restrict Sᶜ) Set.univ := by
          rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
        _ = μ.restrict Sᶜ Set.univ - ν.restrict Sᶜ Set.univ :=
          Measure.sub_apply MeasurableSet.univ hS.compl.le_on
        _ = μ Sᶜ - ν Sᶜ := by
          rw [Measure.restrict_apply MeasurableSet.univ,
            Measure.restrict_apply MeasurableSet.univ]
          simp
    rw [← measure_add_measure_compl hS.measurableSet, hzero, zero_add, happly]
    apply tsub_le_iff_right.mpr
    simpa [add_comm] using h.left hS.measurableSet.compl

theorem MeasureLeUpTo.refl {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : MeasureLeUpTo μ μ 0 := by
  refine ⟨0, ?_, by simp⟩
  simp

theorem MeasureLeUpTo.event_le {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {δ : ENNReal} (h : MeasureLeUpTo μ ν δ)
    (S : Set α) :
    μ S ≤ ν S + δ := by
  obtain ⟨error, hle, hmass⟩ := h
  calc
    μ S ≤ (ν + error) S := Measure.le_iff'.mp hle S
    _ = ν S + error S := Measure.add_apply _ _ _
    _ ≤ ν S + error Set.univ :=
      add_le_add le_rfl (measure_mono (μ := error) (Set.subset_univ S))
    _ ≤ ν S + δ := add_le_add_right hmass _

/-- For probability measures, additive domination is already a total-
variation estimate with the same error.  The reverse event inequality follows
from complements, so the positive error measure in `MeasureLeUpTo` costs no
additional factor. -/
theorem MeasureLeUpTo.to_tvLe
    {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ENNReal} (h : MeasureLeUpTo μ ν δ) :
    Arlib.TVLe μ ν δ := by
  apply Arlib.tvLe_of_forall_le
  intro S _hS
  exact h.event_le S

theorem measure_bind_mono_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} (hμν : μ ≤ ν)
    {K : α → Measure β} (hK : Measurable K) :
    μ.bind K ≤ ν.bind K := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.bind_apply hS hK.aemeasurable,
    Measure.bind_apply hS hK.aemeasurable]
  exact lintegral_mono' hμν le_rfl

theorem measure_bind_add_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) {K : α → Measure β} (hK : Measurable K) :
    (μ + ν).bind K = μ.bind K + ν.bind K := by
  ext S hS
  rw [Measure.bind_apply hS hK.aemeasurable]
  rw [Measure.add_apply,
    Measure.bind_apply hS hK.aemeasurable,
    Measure.bind_apply hS hK.aemeasurable,
    lintegral_add_measure]

theorem measure_bind_mono_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {K L : α → Measure β}
    (hK : Measurable K) (hL : Measurable L)
    (hKL : ∀ x, K x ≤ L x) :
    μ.bind K ≤ μ.bind L := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.bind_apply hS hK.aemeasurable,
    Measure.bind_apply hS hL.aemeasurable]
  apply lintegral_mono
  intro x
  exact Measure.le_iff'.mp (hKL x) S

theorem measure_bind_apply_univ
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {K : α → Measure β} (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    μ.bind K Set.univ = μ Set.univ := by
  rw [Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
  have hfun : (fun x => K x Set.univ) = fun _ => (1 : ENNReal) := by
    funext x
    let _ := hKprob x
    exact measure_univ
  rw [hfun, lintegral_one]

/-- Additive domination is preserved by applying the same probability
kernel.  The error mass cannot grow. -/
theorem MeasureLeUpTo.bind_same
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {δ : ENNReal} (h : MeasureLeUpTo μ ν δ)
    {K : α → Measure β} (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    MeasureLeUpTo (μ.bind K) (ν.bind K) δ := by
  obtain ⟨error, hle, hmass⟩ := h
  refine ⟨error.bind K, ?_, ?_⟩
  · calc
      μ.bind K ≤ (ν + error).bind K := measure_bind_mono_left hle hK
      _ = ν.bind K + error.bind K := measure_bind_add_left ν error hK
  · rw [measure_bind_apply_univ error hK hKprob]
    exact hmass

/-- A pointwise family of kernel errors integrates to an error of the same
mass when the input is a probability measure. -/
theorem measure_bind_pointwise_leUpTo
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {K L error : α → Measure β}
    (hK : Measurable K) (hL : Measurable L) (herror : Measurable error)
    {δ : ENNReal}
    (hle : ∀ x, K x ≤ L x + error x)
    (hmass : ∀ x, error x Set.univ ≤ δ) :
    MeasureLeUpTo (μ.bind K) (μ.bind L) δ := by
  refine ⟨μ.bind error, ?_, ?_⟩
  · calc
      μ.bind K ≤ μ.bind (fun x => L x + error x) :=
        measure_bind_mono_right μ hK (hL.add herror) hle
      _ = μ.bind L + μ.bind error := by
        ext S hS
        rw [Measure.bind_apply (m := μ) (f := fun x => L x + error x)
          hS (hL.add herror).aemeasurable]
        rw [Measure.add_apply,
          Measure.bind_apply hS hL.aemeasurable,
          Measure.bind_apply hS herror.aemeasurable]
        simp_rw [Measure.add_apply]
        exact lintegral_add_left
          ((Measure.measurable_coe hS).comp hL) _
  · rw [Measure.bind_apply MeasurableSet.univ herror.aemeasurable]
    calc
      (∫⁻ x, error x Set.univ ∂μ) ≤ ∫⁻ _x, δ ∂μ :=
        lintegral_mono hmass
      _ = δ := by simp

/-- Sequential composition adds the two error budgets.  This is the union
bound needed to replace every dependent walk draw by its stationary draw. -/
theorem MeasureLeUpTo.bind
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} [IsProbabilityMeasure ν]
    {δ η : ENNReal} (hμν : MeasureLeUpTo μ ν δ)
    {K L error : α → Measure β}
    (hK : Measurable K) (hL : Measurable L) (herror : Measurable error)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hle : ∀ x, K x ≤ L x + error x)
    (hmass : ∀ x, error x Set.univ ≤ η) :
    MeasureLeUpTo (μ.bind K) (ν.bind L) (δ + η) := by
  obtain ⟨oldError, hold, holdMass⟩ := hμν
  have hsame : μ.bind K ≤ ν.bind K + oldError.bind K := by
    calc
      μ.bind K ≤ (ν + oldError).bind K := measure_bind_mono_left hold hK
      _ = ν.bind K + oldError.bind K :=
        measure_bind_add_left ν oldError hK
  have hnew : MeasureLeUpTo (ν.bind K) (ν.bind L) η :=
    measure_bind_pointwise_leUpTo ν hK hL herror hle hmass
  obtain ⟨newError, hnewLe, hnewMass⟩ := hnew
  refine ⟨newError + oldError.bind K, ?_, ?_⟩
  · calc
      μ.bind K ≤ ν.bind K + oldError.bind K := hsame
      _ ≤ (ν.bind L + newError) + oldError.bind K :=
        add_le_add hnewLe le_rfl
      _ = ν.bind L + (newError + oldError.bind K) := by ac_rfl
  · rw [Measure.add_apply]
    calc
      newError Set.univ + (oldError.bind K) Set.univ ≤ η + δ := by
        apply add_le_add hnewMass
        rw [measure_bind_apply_univ oldError hK hKprob]
        exact holdMass
      _ = δ + η := by ac_rfl

end ArlibCommunity.Algorithms.CV18
