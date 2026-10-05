/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProductAccuracy

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-!
# Canonical ideal independent Figure-1 experiment

Each Gaussian phase and the terminal phase receives its own finite vector of
independent draws from the exact stationary law.  This is the ideal experiment
to which the executable dependent walk will be coupled.
-/

inductive FigureOneIdealPhase (q : VolumeParams) where
  | fixed (k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1})
  | accelerated
      (k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1})
  | terminal
deriving DecidableEq, Fintype

def figureOneIdealPhaseEquiv (q : VolumeParams) :
    FigureOneIdealPhase q ≃
      ({k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1} ⊕
        ({k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1} ⊕ Unit)) where
  toFun
    | .fixed k => .inl k
    | .accelerated k => .inr (.inl k)
    | .terminal => .inr (.inr ())
  invFun
    | .inl k => .fixed k
    | .inr (.inl k) => .accelerated k
    | .inr (.inr _) => .terminal
  left_inv i := by cases i <;> rfl
  right_inv i := by rcases i with i | i <;> cases i <;> rfl

@[simp] theorem figureOneIdealPhaseEquiv_symm_fixed
    (q : VolumeParams)
    (k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1}) :
    (figureOneIdealPhaseEquiv q).symm (.inl k) = .fixed k := rfl

@[simp] theorem figureOneIdealPhaseEquiv_symm_accelerated
    (q : VolumeParams)
    (k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1}) :
    (figureOneIdealPhaseEquiv q).symm (.inr (.inl k)) = .accelerated k := rfl

@[simp] theorem figureOneIdealPhaseEquiv_symm_terminal
    (q : VolumeParams) (u : Unit) :
    (figureOneIdealPhaseEquiv q).symm (.inr (.inr u)) = .terminal := by
  cases u
  rfl

noncomputable def figureOneIdealPhaseSampleCount (q : VolumeParams) :
    FigureOneIdealPhase q → ℕ
  | .fixed _ => figureOneFixedSampleCount q
  | .accelerated _ => figureOneSampleCount q
  | .terminal => figureOneSampleCount q

abbrev FigureOneIdealPhaseSampleSpace (q : VolumeParams)
    (i : FigureOneIdealPhase q) :=
  Fin (figureOneIdealPhaseSampleCount q i) → AmbientSpace q.n

noncomputable def figureOneIdealPhaseLaw
    (q : VolumeParams) (I : VolumeInput q.n) :
    (i : FigureOneIdealPhase q) → Measure (FigureOneIdealPhaseSampleSpace q i)
  | .fixed k => Measure.pi fun _ =>
      (truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
  | .accelerated k => Measure.pi fun _ =>
      (truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
  | .terminal => Measure.pi fun _ =>
      (truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n))

theorem figureOneIdealPhaseLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (i : FigureOneIdealPhase q) :
    IsProbabilityMeasure (figureOneIdealPhaseLaw q I i) := by
  cases i <;> simp only [figureOneIdealPhaseLaw] <;> infer_instance

theorem idealEmpiricalAverage_memLp
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {k : ℕ} {w : α → ℝ} (p : ENNReal)
    (hw : MemLp w p ν) :
    MemLp (idealEmpiricalAverage k w) p (Measure.pi fun _ : Fin k => ν) := by
  have hcoordinate : ∀ i : Fin k,
      MemLp (fun samples : Fin k → α => w (samples i)) p
        (Measure.pi fun _ : Fin k => ν) := by
    intro i
    exact hw.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin k => ν) i)
  have hsum : MemLp
      (fun samples : Fin k → α => ∑ i, w (samples i)) p
      (Measure.pi fun _ : Fin k => ν) :=
    memLp_finsetSum Finset.univ fun i _ => hcoordinate i
  have hscaled := hsum.const_mul (1 / (k : ℝ))
  convert hscaled using 1
  funext samples
  simp [idealEmpiricalAverage, div_eq_mul_inv, mul_comm]

noncomputable def figureOneIdealPhaseEstimator (q : VolumeParams) :
    (i : FigureOneIdealPhase q) → FigureOneIdealPhaseSampleSpace q i → ℝ
  | .fixed k => idealEmpiricalAverage (figureOneFixedSampleCount q)
      (gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)))
  | .accelerated k => idealEmpiricalAverage (figureOneSampleCount q)
      (gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)))
  | .terminal => idealEmpiricalAverage (figureOneSampleCount q)
      (uniformRatioWeight (terminalVariance q))

theorem figureOneIdealPhaseEstimator_measurable
    (q : VolumeParams) (i : FigureOneIdealPhase q) :
    Measurable (figureOneIdealPhaseEstimator q i) := by
  cases i with
  | fixed k =>
      exact measurable_idealEmpiricalAverage _
        (measurable_gaussianRatioWeight _ _)
  | accelerated k =>
      exact measurable_idealEmpiricalAverage _
        (measurable_gaussianRatioWeight _ _)
  | terminal =>
      exact measurable_idealEmpiricalAverage _
        (measurable_uniformRatioWeight _)

theorem figureOneIdealPhaseEstimator_memLp
    (q : VolumeParams) (I : VolumeInput q.n) (i : FigureOneIdealPhase q)
    (p : ENNReal) :
    MemLp (figureOneIdealPhaseEstimator q i) p
      (figureOneIdealPhaseLaw q I i) := by
  cases i with
  | fixed k =>
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        FigureOneIdealPhaseSampleSpace, figureOneIdealPhaseSampleCount]
      convert
        idealEmpiricalAverage_memLp
          (truncatedGaussianProbability q I (scheduleValue q k)
            (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
          p
          (gaussianRatioWeight_memLp q I (scheduleValue_pos q k)
            (scheduleValue_pos q (k + 1)) p) using 1 <;> rfl
  | accelerated k =>
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        FigureOneIdealPhaseSampleSpace, figureOneIdealPhaseSampleCount]
      convert
        idealEmpiricalAverage_memLp
          (truncatedGaussianProbability q I (scheduleValue q k)
            (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
          p
          (gaussianRatioWeight_memLp q I (scheduleValue_pos q k)
            (scheduleValue_pos q (k + 1)) p) using 1 <;> rfl
  | terminal =>
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        FigureOneIdealPhaseSampleSpace, figureOneIdealPhaseSampleCount]
      convert
        idealEmpiricalAverage_memLp
          (truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n))
          p (uniformRatioWeight_memLp q I (terminalVariance_pos' q) p) using 1 <;> rfl

noncomputable def figureOneIdealPhaseMean
    (q : VolumeParams) (I : VolumeInput q.n) : FigureOneIdealPhase q → ℝ
  | .fixed k =>
      gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
        gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  | .accelerated k =>
      gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
        gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  | .terminal => euclideanVolume (truncatedVolumeInput q I) /
      gaussianIntegral (truncatedBody q I) (terminalVariance q)

noncomputable def figureOneIdealPhaseFactor (q : VolumeParams) :
    FigureOneIdealPhase q → ℝ
  | .fixed _ =>
      1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
  | .accelerated k => 1 + (scheduleValue q k / terminalVariance q) /
      (figureOneSampleCount q : ℝ)
  | .terminal => 1 + (Real.exp (1 / 2) - 1) /
      (figureOneSampleCount q : ℝ)

/-- The sole geometric moment input still missing from the ideal product: the
paper's sharp accelerated localization estimate on every accelerated
scheduled transition. -/
def FigureOneSharpAcceleratedMoments
    (q : VolumeParams) (I : VolumeInput q.n) : Prop :=
  ∀ k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1},
    ((∫ x, gaussianRatioWeight (scheduleValue q k)
          (scheduleValue q (k + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k)
          (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 2) ≤
      1 + scheduleValue q k / terminalVariance q

/-- Exact first moments and phase-sensitive second moments for every
coordinate of the ideal experiment, conditional only on the isolated sharp
accelerated localization statement. -/
theorem figureOneIdealPhase_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (i : FigureOneIdealPhase q) :
    (∫ samples, figureOneIdealPhaseEstimator q i samples
        ∂figureOneIdealPhaseLaw q I i) = figureOneIdealPhaseMean q I i ∧
      (∫ samples, (figureOneIdealPhaseEstimator q i samples) ^ 2
        ∂figureOneIdealPhaseLaw q I i) ≤
        figureOneIdealPhaseFactor q i *
          (figureOneIdealPhaseMean q I i) ^ 2 := by
  cases i with
  | fixed k =>
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        figureOneIdealPhaseMean, figureOneIdealPhaseFactor,
        FigureOneIdealPhaseSampleSpace, figureOneIdealPhaseSampleCount]
      convert scheduledFixedIdealEmpiricalAverage_moments q I k k.property using 1 <;>
        rfl
  | accelerated k =>
      have hacc : 1 < scheduleValue q k := lt_of_not_ge k.property
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        figureOneIdealPhaseMean, figureOneIdealPhaseFactor,
        FigureOneIdealPhaseSampleSpace, figureOneIdealPhaseSampleCount]
      convert
        scheduledAcceleratedIdealEmpiricalAverage_moments_of_relativeSecondMoment
          q I k hacc (hsharp k) using 1 <;> rfl
  | terminal =>
      simp only [figureOneIdealPhaseEstimator, figureOneIdealPhaseLaw,
        figureOneIdealPhaseMean, figureOneIdealPhaseFactor,
        FigureOneIdealPhaseSampleSpace,
        figureOneIdealPhaseSampleCount]
      exact terminalIdealEmpiricalAverage_moments q I

/-! ## One product probability space for all ideal phases -/

abbrev FigureOneIdealExperimentSpace (q : VolumeParams) :=
  (i : FigureOneIdealPhase q) → FigureOneIdealPhaseSampleSpace q i

noncomputable def figureOneIdealExperimentLaw
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (FigureOneIdealExperimentSpace q) :=
  Measure.pi (figureOneIdealPhaseLaw q I)

theorem figureOneIdealExperimentLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) :
    IsProbabilityMeasure (figureOneIdealExperimentLaw q I) := by
  let _ (i : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I i) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I i
  unfold figureOneIdealExperimentLaw
  infer_instance

noncomputable def figureOneIdealCoordinate (q : VolumeParams) :
    (i : FigureOneIdealPhase q) → FigureOneIdealExperimentSpace q → ℝ :=
  fun i samples => figureOneIdealPhaseEstimator q i (samples i)

noncomputable def figureOneIdealProduct (q : VolumeParams) :
    FigureOneIdealExperimentSpace q → ℝ :=
  fun samples => ∏ i, figureOneIdealCoordinate q i samples

theorem figureOneIdealCoordinate_measurable
    (q : VolumeParams) (i : FigureOneIdealPhase q) :
    Measurable (figureOneIdealCoordinate q i) :=
  (figureOneIdealPhaseEstimator_measurable q i).comp (measurable_pi_apply i)

theorem figureOneIdealProduct_measurable (q : VolumeParams) :
    Measurable (figureOneIdealProduct q) := by
  unfold figureOneIdealProduct
  exact Finset.univ.measurable_fun_prod fun i _ =>
    figureOneIdealCoordinate_measurable q i

/-- The real-valued output law of the fully independent Figure-1 experiment. -/
noncomputable def figureOneIdealEstimateLaw
    (q : VolumeParams) (I : VolumeInput q.n) : Measure ℝ :=
  (figureOneIdealExperimentLaw q I).map fun samples =>
    initialGaussianIntegral q * figureOneIdealProduct q samples

theorem figureOneIdealScaledProduct_measurable (q : VolumeParams) :
    Measurable fun samples =>
      initialGaussianIntegral q * figureOneIdealProduct q samples :=
  measurable_const.mul (figureOneIdealProduct_measurable q)

theorem figureOneIdealEstimateLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) :
    IsProbabilityMeasure (figureOneIdealEstimateLaw q I) := by
  unfold figureOneIdealEstimateLaw
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  exact Measure.isProbabilityMeasure_map
    (figureOneIdealScaledProduct_measurable q).aemeasurable

theorem figureOneIdealEstimateLaw_apply
    (q : VolumeParams) (I : VolumeInput q.n) {S : Set ℝ}
    (hS : MeasurableSet S) :
    figureOneIdealEstimateLaw q I S =
      figureOneIdealExperimentLaw q I
        {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∈ S} := by
  unfold figureOneIdealEstimateLaw
  rw [Measure.map_apply (figureOneIdealScaledProduct_measurable q) hS]
  rfl

theorem figureOneIdealCoordinate_memLp
    (q : VolumeParams) (I : VolumeInput q.n) (i : FigureOneIdealPhase q)
    (p : ENNReal) :
    MemLp (figureOneIdealCoordinate q i) p
      (figureOneIdealExperimentLaw q I) := by
  let _ (j : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I j) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I j
  exact (figureOneIdealPhaseEstimator_memLp q I i p).comp_measurePreserving
    (measurePreserving_eval (figureOneIdealPhaseLaw q I) i)

theorem figureOneIdealCoordinates_iIndepFun
    (q : VolumeParams) (I : VolumeInput q.n) :
    iIndepFun (figureOneIdealCoordinate q)
      (figureOneIdealExperimentLaw q I) := by
  let _ (i : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I i) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I i
  unfold figureOneIdealCoordinate figureOneIdealExperimentLaw
  exact iIndepFun_pi fun i =>
    (figureOneIdealPhaseEstimator_memLp q I i 2).aestronglyMeasurable.aemeasurable

theorem figureOneIdealProduct_memLp_two
    (q : VolumeParams) (I : VolumeInput q.n) :
    MemLp (figureOneIdealProduct q) 2
      (figureOneIdealExperimentLaw q I) := by
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  have hcoordinate : ∀ i : FigureOneIdealPhase q,
      MemLp (figureOneIdealCoordinate q i) ⊤
        (figureOneIdealExperimentLaw q I) := fun i =>
    figureOneIdealCoordinate_memLp q I i ⊤
  have htop : MemLp
      (fun samples => ∏ i, figureOneIdealCoordinate q i samples) ⊤
      (figureOneIdealExperimentLaw q I) := by
    have h := MemLp.prod'
      (s := (Finset.univ : Finset (FigureOneIdealPhase q)))
      (p := fun _ : FigureOneIdealPhase q => (⊤ : ENNReal))
      (fun i _ => hcoordinate i)
    simpa using h
  change MemLp
    (fun samples => ∏ i, figureOneIdealCoordinate q i samples) 2
    (figureOneIdealExperimentLaw q I)
  exact htop.mono_exponent (by simp)

theorem figureOneIdealCoordinate_mean
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (i : FigureOneIdealPhase q) :
    (∫ samples, figureOneIdealCoordinate q i samples
      ∂figureOneIdealExperimentLaw q I) = figureOneIdealPhaseMean q I i := by
  let _ (j : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I j) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I j
  rw [show figureOneIdealCoordinate q i =
      fun samples => figureOneIdealPhaseEstimator q i (samples i) by rfl,
    figureOneIdealExperimentLaw,
    integral_comp_eval
      (figureOneIdealPhaseEstimator_memLp q I i 2).aestronglyMeasurable]
  exact (figureOneIdealPhase_moments q I hsharp i).1

theorem figureOneIdealCoordinate_secondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (i : FigureOneIdealPhase q) :
    (∫ samples, figureOneIdealCoordinate q i samples ^ 2
      ∂figureOneIdealExperimentLaw q I) ≤
      figureOneIdealPhaseFactor q i * (figureOneIdealPhaseMean q I i) ^ 2 := by
  let _ (j : FigureOneIdealPhase q) :
      IsProbabilityMeasure (figureOneIdealPhaseLaw q I j) :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I j
  change (∫ samples,
      (fun x => (figureOneIdealPhaseEstimator q i x) ^ 2) (samples i)
      ∂Measure.pi (figureOneIdealPhaseLaw q I)) ≤ _
  have heq :
      (∫ samples,
          (fun x => (figureOneIdealPhaseEstimator q i x) ^ 2) (samples i)
          ∂Measure.pi (figureOneIdealPhaseLaw q I)) =
        ∫ x, (figureOneIdealPhaseEstimator q i x) ^ 2
          ∂figureOneIdealPhaseLaw q I i := by
    convert integral_comp_eval
      ((figureOneIdealPhaseEstimator_memLp q I i 2).aestronglyMeasurable.pow 2)
      using 1 <;> rfl
  rw [heq]
  exact (figureOneIdealPhase_moments q I hsharp i).2

theorem figureOneIdealPhaseMean_pos
    (q : VolumeParams) (I : VolumeInput q.n) (i : FigureOneIdealPhase q) :
    0 < figureOneIdealPhaseMean q I i := by
  cases i with
  | fixed k =>
      exact div_pos
        (gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q (k + 1)))
        (gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q k))
  | accelerated k =>
      exact div_pos
        (gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q (k + 1)))
        (gaussianIntegral_pos q (truncatedVolumeInput q I)
          (scheduleValue_pos q k))
  | terminal =>
      exact div_pos (euclideanVolume_pos q (truncatedVolumeInput q I))
        (gaussianIntegral_pos q (truncatedVolumeInput q I)
          (terminalVariance_pos' q))

theorem figureOneIdealPhaseFactor_one_le
    (q : VolumeParams) (i : FigureOneIdealPhase q) :
    1 ≤ figureOneIdealPhaseFactor q i := by
  cases i with
  | fixed k =>
      simp only [figureOneIdealPhaseFactor]
      have hn : (0 : ℝ) < q.n := by exact_mod_cast
        (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
      have hc : (0 : ℝ) < figureOneFixedSampleCount q := by
        exact_mod_cast figureOneFixedSampleCount_pos q
      have hdelta : 0 ≤ (2 / (q.n : ℝ)) /
          (figureOneFixedSampleCount q : ℝ) := by positivity
      linarith
  | accelerated k =>
      simp only [figureOneIdealPhaseFactor]
      have hc : (0 : ℝ) < figureOneSampleCount q := by
        exact_mod_cast figureOneSampleCount_pos q
      have hs : 0 ≤ scheduleValue q (k : Fin (terminalPhaseSteps q)) :=
        (scheduleValue_pos q k).le
      have hT : 0 ≤ terminalVariance q := (terminalVariance_pos' q).le
      have hdelta : 0 ≤ (scheduleValue q ↑k / terminalVariance q) /
          (figureOneSampleCount q : ℝ) := div_nonneg (div_nonneg hs hT) hc.le
      linarith
  | terminal =>
      simp only [figureOneIdealPhaseFactor]
      have hc : (0 : ℝ) < figureOneSampleCount q := by
        exact_mod_cast figureOneSampleCount_pos q
      have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
      have hdelta : 0 ≤ (Real.exp (1 / 2) - 1) /
          (figureOneSampleCount q : ℝ) := div_nonneg (sub_nonneg.mpr he) hc.le
      linarith

theorem figureOneIdealPhaseFactor_product_eq (q : VolumeParams) :
    (∏ i, figureOneIdealPhaseFactor q i) =
      (∏ k : Fin (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
        else
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)) *
      (1 + (Real.exp (1 / 2) - 1) /
        (figureOneSampleCount q : ℝ)) := by
  classical
  let fixedFactor : Fin (terminalPhaseSteps q) → ℝ := fun _ =>
    1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
  let acceleratedFactor : Fin (terminalPhaseSteps q) → ℝ := fun k =>
    1 + (scheduleValue q k / terminalVariance q) /
      (figureOneSampleCount q : ℝ)
  let terminalFactor : ℝ := 1 + (Real.exp (1 / 2) - 1) /
    (figureOneSampleCount q : ℝ)
  have hreindex :
      (∏ i, figureOneIdealPhaseFactor q i) =
        (∏ j :
            ({k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1} ⊕
              ({k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1} ⊕ Unit)),
          figureOneIdealPhaseFactor q ((figureOneIdealPhaseEquiv q).symm j)) := by
    exact ((figureOneIdealPhaseEquiv q).symm.prod_comp
      (figureOneIdealPhaseFactor q)).symm
  rw [hreindex, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [figureOneIdealPhaseEquiv_symm_fixed,
    figureOneIdealPhaseEquiv_symm_accelerated,
    figureOneIdealPhaseEquiv_symm_terminal,
    figureOneIdealPhaseFactor, Fintype.prod_unique]
  rw [← mul_assoc]
  let combinedFactor : Fin (terminalPhaseSteps q) → ℝ := fun k =>
    if scheduleValue q k ≤ 1 then fixedFactor k else acceleratedFactor k
  change
    ((∏ k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1},
        fixedFactor k) *
      (∏ k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1},
        acceleratedFactor k)) * terminalFactor =
      (∏ k : Fin (terminalPhaseSteps q), combinedFactor k) * terminalFactor
  congr 1
  have hfixed :
      (∏ k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1},
        fixedFactor k) =
      ∏ k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1},
        combinedFactor k := by
    apply Fintype.prod_congr
    intro k
    simp [combinedFactor, k.property]
  have haccelerated :
      (∏ k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1},
        acceleratedFactor k) =
      ∏ k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1},
        combinedFactor k := by
    apply Fintype.prod_congr
    intro k
    simp [combinedFactor, k.property]
  rw [hfixed, haccelerated,
    Fintype.prod_subtype_mul_prod_subtype
      (fun k : Fin (terminalPhaseSteps q) => scheduleValue q k ≤ 1)
      combinedFactor]

theorem figureOneIdealPhaseFactor_product_le (q : VolumeParams) :
    (∏ i, figureOneIdealPhaseFactor q i) ≤
      Real.exp (13 * q.eps ^ 2 / 512) := by
  rw [figureOneIdealPhaseFactor_product_eq]
  let f : ℕ → ℝ := fun k =>
    if scheduleValue q k ≤ 1 then
      1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
    else
      1 + (scheduleValue q k / terminalVariance q) /
        (figureOneSampleCount q : ℝ)
  change (∏ k : Fin (terminalPhaseSteps q), f k) * _ ≤ _
  rw [Fin.prod_univ_eq_prod_range f]
  change
    ((∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
        else
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)) *
      (1 + (Real.exp (1 / 2) - 1) /
        (figureOneSampleCount q : ℝ))) ≤ _
  exact idealEmpiricalProduct_factor_le q

/-- The ideal independent Figure-1 product obeys the exact Chebyshev bound;
the only geometric hypothesis is the isolated accelerated localization
moment statement. -/
theorem figureOneIdealProduct_relativeDeviation_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) :
    (figureOneIdealExperimentLaw q I)
      {samples | q.eps * (∏ i, figureOneIdealPhaseMean q I i) ≤
        |figureOneIdealProduct q samples -
          ∏ i, figureOneIdealPhaseMean q I i|} ≤
      ENNReal.ofReal ((∏ i, figureOneIdealPhaseFactor q i) - 1) /
        ENNReal.ofReal (q.eps ^ 2) := by
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  apply measure_independent_product_relativeDeviation_le
    (figureOneIdealExperimentLaw q I)
    (figureOneIdealCoordinates_iIndepFun q I)
    (fun i => (figureOneIdealCoordinate_memLp q I i 2).aestronglyMeasurable)
    (figureOneIdealProduct_memLp_two q I)
    (fun i => figureOneIdealCoordinate_mean q I hsharp i)
    (figureOneIdealPhaseMean_pos q I)
    (figureOneIdealPhaseFactor_one_le q)
    (figureOneIdealCoordinate_secondMoment_le q I hsharp)
    q.heps.1

theorem figureOneIdealProduct_failure_le_one_div_32
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) :
    (figureOneIdealExperimentLaw q I)
      {samples | q.eps * (∏ i, figureOneIdealPhaseMean q I i) ≤
        |figureOneIdealProduct q samples -
          ∏ i, figureOneIdealPhaseMean q I i|} ≤
      ENNReal.ofReal (1 / 32 : ℝ) := by
  have htail := figureOneIdealProduct_relativeDeviation_le q I hsharp
  refine htail.trans ?_
  have hfactor := figureOneIdealPhaseFactor_product_le q
  have hexcess : (∏ i, figureOneIdealPhaseFactor q i) - 1 ≤
      q.eps ^ 2 / 32 := by
    exact le_trans (sub_le_sub_right hfactor 1)
      (idealEmpiricalProduct_exponentialExcess_le q)
  have hreal : ((∏ i, figureOneIdealPhaseFactor q i) - 1) / q.eps ^ 2 ≤
      (1 / 32 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos q.heps.1)]
    nlinarith
  rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos q.heps.1)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem figureOneIdealProduct_failure_half_eps_le_one_div_8
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) :
    (figureOneIdealExperimentLaw q I)
      {samples | (q.eps / 2) * (∏ i, figureOneIdealPhaseMean q I i) ≤
        |figureOneIdealProduct q samples -
          ∏ i, figureOneIdealPhaseMean q I i|} ≤
      ENNReal.ofReal (1 / 8 : ℝ) := by
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  have htail := measure_independent_product_relativeDeviation_le
    (figureOneIdealExperimentLaw q I)
    (figureOneIdealCoordinates_iIndepFun q I)
    (fun i => (figureOneIdealCoordinate_memLp q I i 2).aestronglyMeasurable)
    (figureOneIdealProduct_memLp_two q I)
    (fun i => figureOneIdealCoordinate_mean q I hsharp i)
    (figureOneIdealPhaseMean_pos q I)
    (figureOneIdealPhaseFactor_one_le q)
    (figureOneIdealCoordinate_secondMoment_le q I hsharp)
    (show 0 < q.eps / 2 by exact div_pos q.heps.1 (by norm_num))
  refine htail.trans ?_
  have hfactor := figureOneIdealPhaseFactor_product_le q
  have hexcess : (∏ i, figureOneIdealPhaseFactor q i) - 1 ≤
      q.eps ^ 2 / 32 := by
    exact le_trans (sub_le_sub_right hfactor 1)
      (idealEmpiricalProduct_exponentialExcess_le q)
  have hreal : ((∏ i, figureOneIdealPhaseFactor q i) - 1) /
      (q.eps / 2) ^ 2 ≤ (1 / 8 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos
      (show 0 < q.eps / 2 by exact div_pos q.heps.1 (by norm_num)))]
    nlinarith
  rw [← ENNReal.ofReal_div_of_pos
    (sq_pos_of_pos
      (show 0 < q.eps / 2 by exact div_pos q.heps.1 (by norm_num)))]
  exact ENNReal.ofReal_le_ofReal hreal

theorem adjacentRatioProduct_range_telescopes
    (Z : ℕ → ℝ) (hZ : ∀ k, Z k ≠ 0) :
    ∀ N : ℕ,
      Z 0 * (∏ k ∈ Finset.range N, Z (k + 1) / Z k) = Z N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ]
      calc
        Z 0 * ((∏ k ∈ Finset.range N, Z (k + 1) / Z k) *
            (Z (N + 1) / Z N)) =
            (Z 0 * ∏ k ∈ Finset.range N, Z (k + 1) / Z k) *
              (Z (N + 1) / Z N) := by ring
        _ = Z N * (Z (N + 1) / Z N) := by rw [ih]
        _ = Z (N + 1) := by field_simp [hZ N]

theorem figureOneIdealPhaseMean_product_eq
    (q : VolumeParams) (I : VolumeInput q.n) :
    (∏ i, figureOneIdealPhaseMean q I i) =
      (∏ k : Fin (terminalPhaseSteps q),
        gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q k)) *
      (euclideanVolume (truncatedVolumeInput q I) /
        gaussianIntegral (truncatedBody q I) (terminalVariance q)) := by
  classical
  let ratio : Fin (terminalPhaseSteps q) → ℝ := fun k =>
    gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
      gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  let terminalRatio : ℝ := euclideanVolume (truncatedVolumeInput q I) /
    gaussianIntegral (truncatedBody q I) (terminalVariance q)
  have hreindex :
      (∏ i, figureOneIdealPhaseMean q I i) =
        (∏ j :
            ({k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1} ⊕
              ({k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1} ⊕ Unit)),
          figureOneIdealPhaseMean q I ((figureOneIdealPhaseEquiv q).symm j)) := by
    exact ((figureOneIdealPhaseEquiv q).symm.prod_comp
      (figureOneIdealPhaseMean q I)).symm
  rw [hreindex, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [figureOneIdealPhaseEquiv_symm_fixed,
    figureOneIdealPhaseEquiv_symm_accelerated,
    figureOneIdealPhaseEquiv_symm_terminal,
    figureOneIdealPhaseMean, Fintype.prod_unique]
  rw [← mul_assoc]
  change
    ((∏ k : {k : Fin (terminalPhaseSteps q) // scheduleValue q k ≤ 1}, ratio k) *
      (∏ k : {k : Fin (terminalPhaseSteps q) // ¬ scheduleValue q k ≤ 1}, ratio k)) *
        terminalRatio = (∏ k : Fin (terminalPhaseSteps q), ratio k) * terminalRatio
  rw [Fintype.prod_subtype_mul_prod_subtype]

theorem figureOneIdealMean_bridge
    (q : VolumeParams) (I : VolumeInput q.n) :
    initialGaussianIntegral q * (∏ i, figureOneIdealPhaseMean q I i) =
      (initialGaussianIntegral q /
        gaussianIntegral (truncatedBody q I) (initialVariance q)) *
        euclideanVolume (truncatedVolumeInput q I) := by
  rw [figureOneIdealPhaseMean_product_eq]
  let Z : ℕ → ℝ := fun k =>
    gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  have hZ : ∀ k, Z k ≠ 0 := fun k =>
    (gaussianIntegral_pos q (truncatedVolumeInput q I)
      (scheduleValue_pos q k)).ne'
  have htel := adjacentRatioProduct_range_telescopes Z hZ
    (terminalPhaseSteps q)
  rw [← Fin.prod_univ_eq_prod_range
    (fun k => Z (k + 1) / Z k) (terminalPhaseSteps q)] at htel
  have hstart : Z 0 = gaussianIntegral (truncatedBody q I)
      (initialVariance q) := by simp [Z, scheduleValue]
  have hfinish : Z (terminalPhaseSteps q) =
      gaussianIntegral (truncatedBody q I) (terminalVariance q) := by
    simp [Z, scheduleValue_terminalPhaseSteps]
  rw [hstart, hfinish] at htel
  have hinitial : gaussianIntegral (truncatedBody q I) (initialVariance q) ≠ 0 := by
    simpa using (gaussianIntegral_pos q (truncatedVolumeInput q I)
      (initialVariance_pos q)).ne'
  have hterminal : gaussianIntegral (truncatedBody q I) (terminalVariance q) ≠ 0 := by
    simpa using (gaussianIntegral_pos q (truncatedVolumeInput q I)
      (terminalVariance_pos' q)).ne'
  have hprod :
      (∏ k : Fin (terminalPhaseSteps q), Z (k + 1) / Z k) =
        gaussianIntegral (truncatedBody q I) (terminalVariance q) /
          gaussianIntegral (truncatedBody q I) (initialVariance q) := by
    apply (eq_div_iff hinitial).2
    simpa [mul_comm] using htel
  change initialGaussianIntegral q *
      ((∏ k : Fin (terminalPhaseSteps q), Z (k + 1) / Z k) *
        (euclideanVolume (truncatedVolumeInput q I) /
          gaussianIntegral (truncatedBody q I) (terminalVariance q))) = _
  rw [hprod]
  field_simp [hinitial, hterminal]

theorem figureOneIdealMean_relativeApprox_truncatedVolume
    (q : VolumeParams) (I : VolumeInput q.n) :
    RelativeApprox (q.eps / 32)
      (euclideanVolume (truncatedVolumeInput q I))
      (initialGaussianIntegral q * (∏ i, figureOneIdealPhaseMean q I i)) := by
  rw [figureOneIdealMean_bridge]
  exact relativeApprox_div_mul
    (gaussianIntegral_pos q (truncatedVolumeInput q I) (initialVariance_pos q))
    (euclideanVolume_pos q (truncatedVolumeInput q I)).le
    (volume_proof_truncated_initial_tail q I)

theorem figureOneIdealScaledProduct_three_quarters_accuracy_failure_le_one_div_8
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) :
    (figureOneIdealExperimentLaw q I)
      {samples | ¬ RelativeApprox (3 * q.eps / 4)
        (euclideanVolume (truncatedVolumeInput q I))
        (initialGaussianIntegral q * figureOneIdealProduct q samples)} ≤
      ENNReal.ofReal (1 / 8 : ℝ) := by
  let mean := ∏ i, figureOneIdealPhaseMean q I i
  let target := euclideanVolume (truncatedVolumeInput q I)
  let A := initialGaussianIntegral q
  have hA : 0 < A := by
    dsimp [A, initialGaussianIntegral]
    exact Real.rpow_pos_of_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (initialVariance_pos q)) _
  have hmean : 0 < mean := by
    dsimp [mean]
    exact Finset.prod_pos fun i _ => figureOneIdealPhaseMean_pos q I i
  have htarget : 0 < target := by
    dsimp [target]
    exact euclideanVolume_pos q (truncatedVolumeInput q I)
  have hcenter : RelativeApprox (q.eps / 32) target (A * mean) := by
    simpa [A, mean, target] using
      figureOneIdealMean_relativeApprox_truncatedVolume q I
  have hsubset :
      {samples | ¬ RelativeApprox (3 * q.eps / 4) target
          (A * figureOneIdealProduct q samples)} ⊆
        {samples | (q.eps / 2) * mean ≤
          |figureOneIdealProduct q samples - mean|} := by
    intro samples hbad
    by_contra hdev
    have hdev' : |figureOneIdealProduct q samples - mean| <
        (q.eps / 2) * mean := lt_of_not_ge hdev
    have hscaled : |A * figureOneIdealProduct q samples - A * mean| <
        (q.eps / 2) * (A * mean) := by
      rw [← mul_sub, abs_mul, abs_of_pos hA]
      nlinarith
    have hcenterBounds := hcenter
    unfold RelativeApprox Arlib.relErr at hcenterBounds
    have hlower : (1 - 3 * q.eps / 4) * target ≤
        A * figureOneIdealProduct q samples := by
      have hdiffLower := (abs_lt.mp hscaled).1
      have hbase : (1 - q.eps / 32) * target ≤ A * mean := hcenterBounds.1
      have hnonneg : 0 ≤ target := htarget.le
      have hc : 0 ≤ 1 - q.eps / 2 := by linarith [q.heps.2]
      have hbaseScaled := mul_le_mul_of_nonneg_left hbase hc
      have hcoefficient :
          (1 - 3 * q.eps / 4) * target ≤
            (1 - q.eps / 2) * ((1 - q.eps / 32) * target) := by
        nlinarith [mul_nonneg q.heps.1.le hnonneg,
          mul_nonneg (sq_nonneg q.eps) hnonneg]
      nlinarith
    have hupper : A * figureOneIdealProduct q samples ≤
        (1 + 3 * q.eps / 4) * target := by
      have hdiffUpper := (abs_lt.mp hscaled).2
      have hbase : A * mean ≤ (1 + q.eps / 32) * target := hcenterBounds.2
      have hnonneg : 0 ≤ target := htarget.le
      have hc : 0 ≤ 1 + q.eps / 2 := by linarith [q.heps.1]
      have hbaseScaled := mul_le_mul_of_nonneg_left hbase hc
      have hcoefficient :
          (1 + q.eps / 2) * ((1 + q.eps / 32) * target) ≤
            (1 + 3 * q.eps / 4) * target := by
        nlinarith [mul_nonneg q.heps.1.le hnonneg,
          mul_nonneg q.heps.1.le
            (mul_nonneg (sub_nonneg.mpr q.heps.2.le) hnonneg)]
      nlinarith
    exact hbad ⟨hlower, hupper⟩
  calc
    (figureOneIdealExperimentLaw q I)
        {samples | ¬ RelativeApprox (3 * q.eps / 4) target
          (A * figureOneIdealProduct q samples)} ≤
      (figureOneIdealExperimentLaw q I)
        {samples | (q.eps / 2) * mean ≤
          |figureOneIdealProduct q samples - mean|} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
      simpa [mean] using
        figureOneIdealProduct_failure_half_eps_le_one_div_8 q I hsharp

def FigureOneRadialTruncationBound
    (q : VolumeParams) (I : VolumeInput q.n) : Prop :=
  RelativeApprox (q.eps / 8) (euclideanVolume I)
    (euclideanVolume (truncatedVolumeInput q I))

theorem truncatedVolume_le_volume
    (q : VolumeParams) (I : VolumeInput q.n) :
    euclideanVolume (truncatedVolumeInput q I) ≤ euclideanVolume I := by
  unfold euclideanVolume
  apply ENNReal.toReal_mono I.body.isCompact.measure_lt_top.ne
  exact measure_mono Set.inter_subset_left

theorem relativeApprox_full_of_three_quarters_truncated
    (q : VolumeParams) (I : VolumeInput q.n)
    (htrunc : FigureOneRadialTruncationBound q I) {estimate : ℝ}
    (hestimate : RelativeApprox (3 * q.eps / 4)
      (euclideanVolume (truncatedVolumeInput q I)) estimate) :
    RelativeApprox q.eps (euclideanVolume I) estimate := by
  let volumeFull := euclideanVolume I
  let volumeTruncated := euclideanVolume (truncatedVolumeInput q I)
  have hfull : 0 < volumeFull := by
    dsimp [volumeFull]
    exact euclideanVolume_pos q I
  have htruncated0 : 0 ≤ volumeTruncated := by
    dsimp [volumeTruncated]
    exact (euclideanVolume_pos q (truncatedVolumeInput q I)).le
  have hmono : volumeTruncated ≤ volumeFull := by
    simpa [volumeTruncated, volumeFull] using truncatedVolume_le_volume q I
  unfold FigureOneRadialTruncationBound RelativeApprox Arlib.relErr at htrunc
  unfold RelativeApprox Arlib.relErr at hestimate ⊢
  constructor
  · have hfactor : 0 ≤ 1 - 3 * q.eps / 4 := by linarith [q.heps.2]
    have hscaled := mul_le_mul_of_nonneg_left htrunc.1 hfactor
    calc
      (1 - q.eps) * volumeFull ≤
          (1 - 3 * q.eps / 4) * ((1 - q.eps / 8) * volumeFull) := by
        nlinarith [mul_nonneg q.heps.1.le hfull.le,
          mul_nonneg (sq_nonneg q.eps) hfull.le]
      _ ≤ (1 - 3 * q.eps / 4) * volumeTruncated := hscaled
      _ ≤ estimate := hestimate.1
  · calc
      estimate ≤ (1 + 3 * q.eps / 4) * volumeTruncated := hestimate.2
      _ ≤ (1 + 3 * q.eps / 4) * volumeFull := by
        gcongr
        linarith [q.heps.1]
      _ ≤ (1 + q.eps) * volumeFull := by
        nlinarith [q.heps.1, hfull]

theorem figureOneIdealScaledProduct_realVolume_failure_le_one_div_8
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (htrunc : FigureOneRadialTruncationBound q I) :
    (figureOneIdealExperimentLaw q I)
      {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
        accurateOutcome q I} ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
  have hsubset :
      {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
          accurateOutcome q I} ⊆
        {samples | ¬ RelativeApprox (3 * q.eps / 4)
          (euclideanVolume (truncatedVolumeInput q I))
          (initialGaussianIntegral q * figureOneIdealProduct q samples)} := by
    intro samples hbad hgood
    exact hbad (relativeApprox_full_of_three_quarters_truncated q I htrunc hgood)
  exact (measure_mono hsubset).trans
    (figureOneIdealScaledProduct_three_quarters_accuracy_failure_le_one_div_8
      q I hsharp)

end

end ArlibCommunity.Algorithms.CV18
