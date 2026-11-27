/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ProgramSemantics
import Arlib.Approximation.Concentration
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal Classical

/-- ENNReal-valued expectation under a general measure. -/
noncomputable def measureExpectation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ENNReal) : ENNReal := ∫⁻ x, g x ∂μ

theorem measurable_goodCount {m : ℕ} {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable fun v : Fin m → ℝ =>
      (Finset.univ.filter fun i => v i ∈ S).card := by
  have hsum : Measurable fun v : Fin m → ℝ =>
      ∑ i ∈ Finset.univ, if v i ∈ S then 1 else 0 := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact Measurable.ite ((measurable_pi_apply i) hS) measurable_const measurable_const
  convert hsum using 1
  funext v
  rw [Finset.card_filter]

theorem measurable_goodWeight {m : ℕ} {S : Set ℝ} (hS : MeasurableSet S)
    (c : ENNReal) :
    Measurable fun v : Fin m → ℝ =>
      c ^ (Finset.univ.filter fun i => v i ∈ S).card := by
  exact (measurable_const.pow (measurable_goodCount hS))

theorem measureExpectation_dirac {α : Type*} [MeasurableSpace α]
    (a : α) (g : α → ENNReal) (hg : Measurable g) :
    measureExpectation (Measure.dirac a) g = g a := by
  unfold measureExpectation
  exact lintegral_dirac' a hg

theorem measureExpectation_oneDraw
    (μ : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) (c : ENNReal) :
    measureExpectation μ (fun x => c ^ (if x ∈ S then 1 else 0)) =
      μ Sᶜ + μ S * c := by
  have hfun : (fun x : ℝ => c ^ (if x ∈ S then 1 else 0)) =
      Sᶜ.indicator (fun _ => (1 : ENNReal)) + S.indicator (fun _ => c) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  unfold measureExpectation
  rw [hfun]
  change (∫⁻ x, Sᶜ.indicator (fun _ => (1 : ENNReal)) x +
    S.indicator (fun _ => c) x ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator hS.compl)]
  rw [lintegral_indicator_const hS.compl, lintegral_indicator_const hS]
  simp [mul_comm]

theorem measureExpectation_repeatEstimateMeasure_pow
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S) (c : ENNReal) :
    ∀ m : ℕ,
      measureExpectation (repeatEstimateMeasure μ m) (fun v =>
        c ^ (Finset.univ.filter fun i => v i ∈ S).card) =
      (μ Sᶜ + μ S * c) ^ m := by
  intro m
  induction m with
  | zero =>
      rw [repeatEstimateMeasure, measureExpectation_dirac _ _ (measurable_goodWeight hS c)]
      simp
  | succ m ih =>
      let _ : IsProbabilityMeasure (repeatEstimateMeasure μ m) :=
        repeatEstimateMeasure_isProbabilityMeasure μ m
      unfold measureExpectation at ih ⊢
      rw [repeatEstimateMeasure]
      have hkernel : Measurable fun estimate : ℝ =>
          (repeatEstimateMeasure μ m).map fun tail =>
            (Fin.cons estimate tail : Fin (m + 1) → ℝ) :=
        measurable_measure_map_param (repeatEstimateMeasure μ m) (measurable_finCons m)
      rw [Measure.lintegral_bind hkernel.aemeasurable
        (measurable_goodWeight hS c).aemeasurable]
      have hinner (estimate : ℝ) :
          (∫⁻ v, c ^ (Finset.univ.filter fun i => v i ∈ S).card
              ∂((repeatEstimateMeasure μ m).map fun tail =>
                (Fin.cons estimate tail : Fin (m + 1) → ℝ))) =
            c ^ (if estimate ∈ S then 1 else 0) * (μ Sᶜ + μ S * c) ^ m := by
        have hcons : Measurable fun tail : Fin m → ℝ =>
            (Fin.cons estimate tail : Fin (m + 1) → ℝ) :=
          (measurable_finCons m).comp
            ((measurable_const : Measurable fun _ : (Fin m → ℝ) => estimate).prodMk
              measurable_id)
        have hmap := lintegral_map (μ := repeatEstimateMeasure μ m)
          (measurable_goodWeight hS c) hcons
        rw [hmap]
        simp_rw [Arlib.Approximation.card_filter_cons]
        simp_rw [pow_add]
        rw [lintegral_const_mul, ih]
        exact measurable_goodWeight hS c
      simp_rw [hinner]
      rw [lintegral_mul_const]
      · have hone := measureExpectation_oneDraw μ hS c
        unfold measureExpectation at hone
        rw [hone, pow_succ']
      · exact measurable_const.pow
          (Measurable.ite hS measurable_const measurable_const)

def minorityEvent (m : ℕ) (S : Set ℝ) : Set (Fin m → ℝ) :=
  {v | ¬ m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}

theorem minorityEvent_measurable {m : ℕ} {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (minorityEvent m S) := by
  unfold minorityEvent
  simp only [not_lt]
  exact measurableSet_le
    (measurable_const.mul (measurable_goodCount hS)) measurable_const

theorem measure_minority_le_mgf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S) (m : ℕ) :
    repeatEstimateMeasure μ m (minorityEvent m S) ≤
      ENNReal.ofReal (Real.exp ((m : ℝ) / 2)) *
        (μ Sᶜ + μ S * ENNReal.ofReal (Real.exp (-1))) ^ m := by
  let c : ENNReal := ENNReal.ofReal (Real.exp (-1))
  let a : ENNReal := ENNReal.ofReal (Real.exp ((m : ℝ) / 2))
  have hbad := minorityEvent_measurable (m := m) hS
  rw [← lintegral_indicator_one hbad]
  calc
    (∫⁻ v, (minorityEvent m S).indicator 1 v ∂repeatEstimateMeasure μ m) ≤
        ∫⁻ v, a * c ^ (Finset.univ.filter fun i => v i ∈ S).card
          ∂repeatEstimateMeasure μ m := by
      apply lintegral_mono
      intro v
      by_cases hv : v ∈ minorityEvent m S
      · rw [Set.indicator_of_mem hv]
        have hle : 2 * (Finset.univ.filter fun i => v i ∈ S).card ≤ m := by
          simpa [minorityEvent] using hv
        have hNR : (((Finset.univ.filter fun i => v i ∈ S).card : ℕ) : ℝ) ≤
            (m : ℝ) / 2 := by
          have h2 : ((2 * (Finset.univ.filter fun i => v i ∈ S).card : ℕ) : ℝ) ≤
              (m : ℝ) := by exact_mod_cast hle
          push_cast at h2
          linarith
        dsimp [a, c]
        rw [← ENNReal.ofReal_pow (Real.exp_nonneg _),
          ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_nat_mul,
          ← Real.exp_add, ENNReal.one_le_ofReal]
        exact Real.one_le_exp (by linarith)
      · rw [Set.indicator_of_notMem hv]
        exact zero_le
    _ = a * measureExpectation (repeatEstimateMeasure μ m) (fun v =>
          c ^ (Finset.univ.filter fun i => v i ∈ S).card) := by
      unfold measureExpectation
      rw [lintegral_const_mul]
      exact measurable_goodWeight hS c
    _ = _ := by
      rw [measureExpectation_repeatEstimateMeasure_pow μ hS c m]

theorem measure_mgf_step_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S)
    (h : 3 / 4 ≤ (μ S).toReal) :
    μ Sᶜ + μ S * ENNReal.ofReal (Real.exp (-1)) ≤
      ENNReal.ofReal (1 / 4 + 3 / 4 * Real.exp (-1)) := by
  have hSne : μ S ≠ ∞ := measure_ne_top μ S
  have hScne : μ Sᶜ ≠ ∞ := measure_ne_top μ Sᶜ
  have hp1 : (μ S).toReal ≤ 1 := by
    exact measureReal_le_one
  have hexp0 : (0 : ℝ) ≤ Real.exp (-1) := Real.exp_nonneg _
  have hexp1 : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hcompl : (μ Sᶜ).toReal = 1 - (μ S).toReal := by
    have hc := measure_compl hS (measure_ne_top μ S)
    have hc' := congrArg ENNReal.toReal hc
    have hSle : μ S ≤ 1 := by
      simpa using measure_mono (μ := μ) (Set.subset_univ S)
    rw [measure_univ] at hc'
    rw [ENNReal.toReal_sub_of_le hSle ENNReal.one_ne_top,
      ENNReal.toReal_one] at hc'
    simpa using hc'
  rw [← ENNReal.ofReal_toReal hScne, ← ENNReal.ofReal_toReal hSne,
    ← ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_add (ENNReal.toReal_nonneg) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hcompl]
  nlinarith [h, hp1, hexp0, hexp1]

theorem measure_minority_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S) (m : ℕ)
    (h : 3 / 4 ≤ (μ S).toReal) :
    repeatEstimateMeasure μ m (minorityEvent m S) ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := by
  have hstep := measure_mgf_step_le μ hS h
  refine le_trans (measure_minority_le_mgf μ hS m) ?_
  refine le_trans (mul_le_mul_right (pow_le_pow_left' hstep m) _) ?_
  rw [← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (Arlib.Approximation.exp_pow_bound (by positivity)
      Arlib.Approximation.exp_half_mul_quarter_le m)

def majorityEvent (m : ℕ) (S : Set ℝ) : Set (Fin m → ℝ) :=
  {v | m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}

theorem majorityEvent_eq_compl (m : ℕ) (S : Set ℝ) :
    majorityEvent m S = (minorityEvent m S)ᶜ := by
  ext v
  simp [majorityEvent, minorityEvent]

theorem repeatEstimateMeasure_majority_toReal_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S) (m : ℕ)
    (h : 3 / 4 ≤ (μ S).toReal) :
    1 - Real.exp (-(m : ℝ) / 8) ≤
      (repeatEstimateMeasure μ m (majorityEvent m S)).toReal := by
  let _ : IsProbabilityMeasure (repeatEstimateMeasure μ m) :=
    repeatEstimateMeasure_isProbabilityMeasure μ m
  have hbad : (repeatEstimateMeasure μ m (minorityEvent m S)).toReal ≤
      Real.exp (-(m : ℝ) / 8) :=
    ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
      (measure_minority_le μ hS m h)
  have hcompl := measure_compl (minorityEvent_measurable (m := m) hS)
    (measure_ne_top (repeatEstimateMeasure μ m) (minorityEvent m S))
  have hcompl' := congrArg ENNReal.toReal hcompl
  have hminority_le_one : repeatEstimateMeasure μ m (minorityEvent m S) ≤ 1 := by
    simpa using measure_mono (μ := repeatEstimateMeasure μ m)
      (Set.subset_univ (minorityEvent m S))
  rw [measure_univ] at hcompl'
  rw [ENNReal.toReal_sub_of_le hminority_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one] at hcompl'
  rw [majorityEvent_eq_compl]
  rw [hcompl']
  linarith

theorem repeatEstimateMeasure_median_Icc_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (m : ℕ)
    (h : 3 / 4 ≤ (μ (Set.Icc a b)).toReal) :
    1 - Real.exp (-(m : ℝ) / 8) ≤
      (repeatEstimateMeasure μ m
        {v | Arlib.Probability.medianOf v ∈ Set.Icc a b}).toReal := by
  let _ : IsProbabilityMeasure (repeatEstimateMeasure μ m) :=
    repeatEstimateMeasure_isProbabilityMeasure μ m
  have hmajority := repeatEstimateMeasure_majority_toReal_ge μ measurableSet_Icc m h
  refine le_trans hmajority (ENNReal.toReal_mono (measure_ne_top _ _) ?_)
  apply measure_mono
  intro v hv
  exact Arlib.Approximation.median_mem_Icc_of_majority v (by
    simpa [majorityEvent] using hv)

end ArlibCommunity.Algorithms.CV18
