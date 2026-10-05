/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledShadowReference
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments
import Mathlib.Algebra.Order.Chebyshev

/-!
# First moment of the exact-shadow scheduled phase average

The history-preserving reset construction gives one reference probability law
whose every recorded coordinate has the exact truncated-Gaussian marginal.
Linearity therefore identifies the mean of its empirical average without any
independence assumption.  A pointwise finite-sum Cauchy bound also gives the
coarse second moment needed for one-sided `L²` transfer.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Symmetric square-root first-moment transfer when both probability laws
have the same second-moment bound. -/
theorem Arlib.TVLe.abs_integral_sub_le_of_nonnegative_secondMoment_sqrt
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfmemMu : MemLp f 2 mu) (hfmemNu : MemLp f 2 nu)
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hepsEta : epsilon.toReal ≤ eta ^ 2)
    (hsecondMu : (∫ x, f x ^ 2 ∂mu) ≤ R ^ 2)
    (hsecondNu : (∫ x, f x ^ 2 ∂nu) ≤ R ^ 2) :
    |(∫ x, f x ∂mu) - ∫ x, f x ∂nu| ≤ 2 * eta * R := by
  have hlowerMu :=
    Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt
      htv hepsilon hf hf0 hfmemMu hfmemNu heta hR hepsEta hsecondNu
  have hlowerNu :=
    Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt
      htv.symm hepsilon hf hf0 hfmemNu hfmemMu heta hR hepsEta hsecondMu
  rw [abs_le]
  constructor <;> linarith

/-- An exact optional coordinate has exactly the Gaussian-ratio mean. -/
theorem integral_retainedSampleObservation_eq_gaussianMean_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I phase) :
    (∫ history, retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) j history ∂reference) =
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hcoordinateMeas : Measurable
      (fun history : RetainedSampleHistory (AmbientSpace q.n) => history.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hoption : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  calc
    (∫ history, retainedSampleObservation weight j history ∂reference) =
        ∫ result, retainedOptionWeight weight result
          ∂reference.map (fun history => history.1 j) := by
      rw [integral_map hcoordinateMeas.aemeasurable
        hoption.aestronglyMeasurable]
      rfl
    _ = ∫ result, retainedOptionWeight weight result
          ∂scheduledRetainedExactSome q I phase := by rw [hcoordinate]
    _ = ∫ x, weight x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
      unfold scheduledRetainedExactSome
      rw [integral_map measurable_some.aemeasurable
        hoption.aestronglyMeasurable]
      rfl

/-- The same exact-coordinate statement for the second moment. -/
theorem integral_retainedSampleObservation_sq_eq_gaussianSecond_of_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    (hcoordinate : reference.map (fun history => history.1 j) =
      scheduledRetainedExactSome q I phase) :
    (∫ history, retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) j history ^ 2 ∂reference) =
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hcoordinateMeas : Measurable
      (fun history : RetainedSampleHistory (AmbientSpace q.n) => history.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hoption : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  calc
    (∫ history, retainedSampleObservation weight j history ^ 2 ∂reference) =
        ∫ result, retainedOptionWeight weight result ^ 2
          ∂reference.map (fun history => history.1 j) := by
      rw [integral_map hcoordinateMeas.aemeasurable
        (hoption.pow_const 2).aestronglyMeasurable]
      rfl
    _ = ∫ result, retainedOptionWeight weight result ^ 2
          ∂scheduledRetainedExactSome q I phase := by rw [hcoordinate]
    _ = ∫ x, weight x ^ 2
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
      unfold scheduledRetainedExactSome
      rw [integral_map measurable_some.aemeasurable
        (hoption.pow_const 2).aestronglyMeasurable]
      rfl

/-- Exact coordinate marginals suffice to identify the empirical-average
mean.  No independence of the reference coordinates is used. -/
theorem integral_exactShadowHistory_average_eq_gaussianMean
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcoordinates : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase) :
    (∫ history,
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)
      ∂reference) =
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hcoordInt : ∀ j, j < count →
      Integrable (retainedSampleObservation weight j) reference := by
    intro j hj
    have hcoordMeas : Measurable
        (fun history : RetainedSampleHistory (AmbientSpace q.n) =>
          history.1 j) := (measurable_pi_apply j).comp measurable_fst
    have hoptMeas : Measurable (retainedOptionWeight weight) :=
      measurable_retainedOptionWeight hweight
    apply (integrable_map_measure hoptMeas.aestronglyMeasurable
      hcoordMeas.aemeasurable).1
    rw [hcoordinates j hj]
    unfold scheduledRetainedExactSome
    apply (integrable_map_measure hoptMeas.aestronglyMeasurable
      measurable_some.aemeasurable).2
    simpa [weight, Function.comp_def, retainedOptionWeight] using
      (gaussianRatioWeight_memLp q I (scheduleValue_pos q phase)
        (scheduleValue_pos q (phase + 1)) 2).integrable (by norm_num)
  have hcountR : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
  rw [integral_div]
  rw [integral_finset_sum (s := Finset.range count) (fun j hj =>
    hcoordInt j (Finset.mem_range.mp hj))]
  have hterm : ∀ j ∈ Finset.range count,
      (∫ history, retainedSampleObservation weight j history ∂reference) =
        ∫ x, weight x ∂exact := by
    intro j hj
    simpa [weight, exact] using
      integral_retainedSampleObservation_eq_gaussianMean_of_map_eq
        q I phase j reference (hcoordinates j (Finset.mem_range.mp hj))
  rw [Finset.sum_congr rfl hterm]
  simp [hcountR, exact, weight]

/-- The exact-shadow average has second moment no larger than the exact
one-coordinate second moment.  This is the dependence-free Jensen bound. -/
theorem integral_exactShadowHistory_average_sq_le_gaussianSecond
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcoordinates : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase) :
    MemLp (fun history =>
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)) 2
        reference ∧
    (∫ history,
        ((∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)) ^ 2
      ∂reference) ≤
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have hcoordSqInt : ∀ j, j < count →
      Integrable (fun history => (retainedSampleObservation weight j history) ^ 2)
        reference := by
    intro j hj
    have hcoordMeas : Measurable
        (fun history : RetainedSampleHistory (AmbientSpace q.n) =>
          history.1 j) := (measurable_pi_apply j).comp measurable_fst
    have hoptMeas : Measurable (retainedOptionWeight weight) :=
      measurable_retainedOptionWeight hweight
    apply (integrable_map_measure (hoptMeas.pow_const 2).aestronglyMeasurable
      hcoordMeas.aemeasurable).1
    rw [hcoordinates j hj]
    unfold scheduledRetainedExactSome
    apply (integrable_map_measure (hoptMeas.pow_const 2).aestronglyMeasurable
      measurable_some.aemeasurable).2
    simpa [weight, Function.comp_def, retainedOptionWeight] using
      (gaussianRatioWeight_memLp q I (scheduleValue_pos q phase)
        (scheduleValue_pos q (phase + 1)) 2).integrable_sq
  have hsumSqInt : Integrable (fun history =>
      ∑ j ∈ Finset.range count,
        retainedSampleObservation weight j history ^ 2) reference :=
    integrable_finsetSum _ fun j hj =>
      hcoordSqInt j (Finset.mem_range.mp hj)
  have hcountR : (0 : ℝ) < count := by exact_mod_cast hcount
  have hpoint : ∀ history : RetainedSampleHistory (AmbientSpace q.n),
      ((∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)) ^ 2 ≤
        (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history ^ 2) / (count : ℝ) := by
    intro history
    let total := ∑ j ∈ Finset.range count,
      retainedSampleObservation weight j history
    let squares := ∑ j ∈ Finset.range count,
      retainedSampleObservation weight j history ^ 2
    have hsum : total ^ 2 ≤ (count : ℝ) * squares := by
      simpa [total, squares, Finset.card_range] using
        (sq_sum_le_card_mul_sum_sq
          (s := Finset.range count)
          (f := fun j => retainedSampleObservation weight j history))
    dsimp only [total, squares] at hsum ⊢
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hcountR)).2
    field_simp [hcountR.ne']
    simpa [mul_comm] using hsum
  have havgSqMeas : Measurable (fun history :
      RetainedSampleHistory (AmbientSpace q.n) =>
      ((∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)) ^ 2) :=
    (((Finset.range count).measurable_fun_sum fun j _ =>
      measurable_retainedSampleObservation hweight j).div_const _).pow_const 2
  have hsumSqDivInt : Integrable (fun history =>
      (∑ j ∈ Finset.range count,
        retainedSampleObservation weight j history ^ 2) / (count : ℝ))
      reference := hsumSqInt.div_const _
  have havgSqInt : Integrable (fun history =>
      ((∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)) ^ 2)
      reference := by
    apply hsumSqDivInt.mono' havgSqMeas.aestronglyMeasurable
    filter_upwards with history
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint history
  have havgMeas : Measurable (fun history :
      RetainedSampleHistory (AmbientSpace q.n) =>
      (∑ j ∈ Finset.range count,
        retainedSampleObservation weight j history) / (count : ℝ)) :=
    ((Finset.range count).measurable_fun_sum fun j _ =>
      measurable_retainedSampleObservation hweight j).div_const _
  refine ⟨(memLp_two_iff_integrable_sq
    havgMeas.aestronglyMeasurable).2 havgSqInt, ?_⟩
  calc
    (∫ history,
        ((∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history) / (count : ℝ)) ^ 2
      ∂reference) ≤
        ∫ history, (∑ j ∈ Finset.range count,
          retainedSampleObservation weight j history ^ 2) / (count : ℝ)
          ∂reference := by
      exact integral_mono havgSqInt hsumSqDivInt hpoint
    _ = (∑ j ∈ Finset.range count,
          ∫ history, retainedSampleObservation weight j history ^ 2
            ∂reference) / (count : ℝ) := by
      rw [integral_div, integral_finset_sum (s := Finset.range count)
        (fun j hj => hcoordSqInt j (Finset.mem_range.mp hj))]
    _ = _ := by
      have hterm : ∀ j ∈ Finset.range count,
          (∫ history, retainedSampleObservation weight j history ^ 2
            ∂reference) =
            ∫ x, weight x ^ 2
              ∂(truncatedGaussianProbability q I (scheduleValue q phase)
                (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
        intro j hj
        simpa [weight] using
          integral_retainedSampleObservation_sq_eq_gaussianSecond_of_map_eq
            q I phase j reference (hcoordinates j (Finset.mem_range.mp hj))
      rw [Finset.sum_congr rfl hterm]
      simp [hcountR.ne', weight]

/-- The all-coordinate reset theorem, packaged with the exact first moment
and the coarse reference second moment of the resulting phase average. -/
theorem exists_initializedScheduledRetainedShadowReference_average_moments
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        reference (scheduledShadowReferenceError q (count - 1)) ∧
      (∫ history,
          (∑ j ∈ Finset.range count, retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) j history) / (count : ℝ)
        ∂reference) =
        ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)) x
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) ∧
      (∫ history,
          ((∑ j ∈ Finset.range count, retainedSampleObservation
            (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1))) j history) / (count : ℝ)) ^ 2
        ∂reference) ≤
        ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)) x ^ 2
          ∂(truncatedGaussianProbability q I (scheduleValue q phase)
            (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)) := by
  obtain ⟨reference, hprob, hmlu, hcoordinates, _hstate⟩ :=
    exists_initializedScheduledRetainedShadowReference_all
      q I phase (count - 1)
  let _ : IsProbabilityMeasure reference := hprob
  have hcoords : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase := by
    intro j hj
    exact hcoordinates j (by omega)
  refine ⟨reference, hprob, hmlu, ?_, ?_⟩
  · exact integral_exactShadowHistory_average_eq_gaussianMean
      q I phase count hcount reference hcoords
  · exact (integral_exactShadowHistory_average_sq_le_gaussianSecond
      q I phase count hcount reference hcoords).2

/-- The exact-shadow law turns the executable pre-kill phase-average mean
into a direct one-sided `L²` perturbation of the ideal Gaussian mean.  This
is the phase-average adapter needed on the lower side of the capstone's
`hmean`; the remaining final-death loss is handled separately by the
complete-target killing lemma. -/
theorem integral_initializedScheduledRetainedHistory_average_lower_of_shadowReference
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (herrorTop : scheduledShadowReferenceError q (count - 1) ≠ ⊤)
    (herror : (scheduledShadowReferenceError q (count - 1)).toReal ≤ eta ^ 2)
    (hexactSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2)
    (hactualMem :
      MemLp (fun history : RetainedSampleHistory (AmbientSpace q.n) =>
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)) 2
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1))) :
    (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) -
        2 * eta * R ≤
      ∫ history,
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)
        ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let average : RetainedSampleHistory (AmbientSpace q.n) → ℝ := fun history =>
    (∑ j ∈ Finset.range count,
      retainedSampleObservation weight j history) / (count : ℝ)
  let actual := initializedScheduledRetainedHistoryLaw q I phase (count - 1)
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, _hstate⟩ :=
    exists_initializedScheduledRetainedShadowReference_all
      q I phase (count - 1)
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hcoords : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase := by
    intro j hj
    exact hcoordinates j (by omega)
  have hrefMean := integral_exactShadowHistory_average_eq_gaussianMean
    q I phase count hcount reference hcoords
  have hrefMoments :=
    integral_exactShadowHistory_average_sq_le_gaussianSecond
      q I phase count hcount reference hcoords
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have havgMeas : Measurable average :=
    ((Finset.range count).measurable_fun_sum fun j _ =>
      measurable_retainedSampleObservation hweight j).div_const _
  have havg0 : ∀ history, 0 ≤ average history := by
    intro history
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      cases hstate : history.1 j with
      | none => simp [retainedSampleObservation, hstate, retainedOptionWeight]
      | some x =>
          simp only [retainedSampleObservation, hstate, retainedOptionWeight]
          exact gaussianRatioWeight_nonnegative _ _ x
    · positivity
  have htv : Arlib.TVLe actual reference
      (scheduledShadowReferenceError q (count - 1)) := by
    exact hmlu.to_tvLe
  have htransfer :=
    Arlib.TVLe.integral_sub_le_of_nonnegative_secondMoment_sqrt
      htv herrorTop havgMeas havg0 (by simpa [average, actual, weight] using hactualMem)
      hrefMoments.1 heta hR herror (hrefMoments.2.trans hexactSecond)
  rw [hrefMean] at htransfer
  simpa [average, actual, weight] using htransfer

/-- Once equation (6) supplies the executable pre-kill average second
moment, the exact-shadow construction gives the full two-sided first-moment
comparison with the ideal Gaussian mean.  Thus first-moment work introduces
no additional independence obligation beyond the second-moment lane. -/
theorem integral_initializedScheduledRetainedHistory_average_abs_sub_gaussianMean_le
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count) {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (herrorTop : scheduledShadowReferenceError q (count - 1) ≠ ⊤)
    (herror : (scheduledShadowReferenceError q (count - 1)).toReal ≤ eta ^ 2)
    (hexactSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ R ^ 2)
    (hactualMem :
      MemLp (fun history : RetainedSampleHistory (AmbientSpace q.n) =>
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)) 2
        (initializedScheduledRetainedHistoryLaw q I phase (count - 1)))
    (hactualSecond :
      (∫ history,
        ((∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)) ^ 2
        ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) ≤
          R ^ 2) :
    |(∫ history,
        (∑ j ∈ Finset.range count, retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1))) j history) / (count : ℝ)
        ∂initializedScheduledRetainedHistoryLaw q I phase (count - 1)) -
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))| ≤
        2 * eta * R := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let average : RetainedSampleHistory (AmbientSpace q.n) → ℝ := fun history =>
    (∑ j ∈ Finset.range count,
      retainedSampleObservation weight j history) / (count : ℝ)
  let actual := initializedScheduledRetainedHistoryLaw q I phase (count - 1)
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinates, _hstate⟩ :=
    exists_initializedScheduledRetainedShadowReference_all
      q I phase (count - 1)
  let _ : IsProbabilityMeasure actual := by
    simpa [actual] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase (count - 1)
  let _ : IsProbabilityMeasure reference := hreferenceProb
  have hcoords : ∀ j, j < count →
      reference.map (fun history => history.1 j) =
        scheduledRetainedExactSome q I phase := by
    intro j hj
    exact hcoordinates j (by omega)
  have hrefMean := integral_exactShadowHistory_average_eq_gaussianMean
    q I phase count hcount reference hcoords
  have hrefMoments :=
    integral_exactShadowHistory_average_sq_le_gaussianSecond
      q I phase count hcount reference hcoords
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1))
  have havgMeas : Measurable average :=
    ((Finset.range count).measurable_fun_sum fun j _ =>
      measurable_retainedSampleObservation hweight j).div_const _
  have havg0 : ∀ history, 0 ≤ average history := by
    intro history
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      cases hstate : history.1 j with
      | none => simp [retainedSampleObservation, hstate, retainedOptionWeight]
      | some x =>
          simp only [retainedSampleObservation, hstate, retainedOptionWeight]
          exact gaussianRatioWeight_nonnegative _ _ x
    · positivity
  have htv : Arlib.TVLe actual reference
      (scheduledShadowReferenceError q (count - 1)) := hmlu.to_tvLe
  have htransfer :=
    Arlib.TVLe.abs_integral_sub_le_of_nonnegative_secondMoment_sqrt
      htv herrorTop havgMeas havg0
      (by simpa [average, actual, weight] using hactualMem)
      hrefMoments.1 heta hR herror
      (by simpa [average, actual, weight] using hactualSecond)
      (hrefMoments.2.trans hexactSecond)
  rw [hrefMean] at htransfer
  simpa [average, actual, weight] using htransfer

#print axioms integral_retainedSampleObservation_eq_gaussianMean_of_map_eq
#print axioms
  Arlib.TVLe.abs_integral_sub_le_of_nonnegative_secondMoment_sqrt
#print axioms integral_retainedSampleObservation_sq_eq_gaussianSecond_of_map_eq
#print axioms integral_exactShadowHistory_average_eq_gaussianMean
#print axioms integral_exactShadowHistory_average_sq_le_gaussianSecond
#print axioms
  exists_initializedScheduledRetainedShadowReference_average_moments
#print axioms
  integral_initializedScheduledRetainedHistory_average_lower_of_shadowReference
#print axioms
  integral_initializedScheduledRetainedHistory_average_abs_sub_gaussianMean_le

end

end ArlibCommunity.Algorithms.CV18
