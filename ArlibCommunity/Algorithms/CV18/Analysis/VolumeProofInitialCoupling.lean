/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Coupling the executable and ideal initial laws

The executable sampler draws from the explicitly normalized full Gaussian and
falls back to the origin outside `truncatedBody`.  The successful part of that
draw is exactly a scalar multiple of the restricted Gaussian probability used
by the stationary walk analysis.
-/

theorem initialGaussianSamplingMeasure_restrict_truncatedBody
    (q : VolumeParams) (I : VolumeInput q.n) :
    (initialGaussianSamplingMeasure q).restrict (truncatedBody q I) =
      ENNReal.ofReal
          (gaussianIntegral (truncatedBody q I) (initialVariance q) /
            initialGaussianIntegral q) •
        (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)) := by
  ext S hS
  rw [Measure.restrict_apply hS,
    initialGaussianSamplingMeasure_apply q
      (hS.inter (truncatedBody_measurable q I)),
    Measure.smul_apply, smul_eq_mul,
    truncatedGaussianProbability_apply q I (initialVariance_pos q) hS]
  have hInt : IntegrableOn
      (gaussianDensity (initialVariance q))
      (S ∩ truncatedBody q I) :=
    (integrable_gaussianDensity (initialVariance_pos q)).integrableOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (S ∩ truncatedBody q I)]
      gaussianDensity (initialVariance q) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  have hZ : 0 < gaussianIntegral (truncatedBody q I) (initialVariance q) := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I)
      (initialVariance_pos q)
  have hZfull := initialGaussianIntegral_pos q
  rw [← ENNReal.ofReal_inv_of_pos hZ]
  rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ (gaussianIntegral (truncatedBody q I) (initialVariance q))⁻¹)]
  rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ gaussianIntegral (truncatedBody q I) (initialVariance q) /
        initialGaussianIntegral q)]
  apply congrArg ENNReal.ofReal
  field_simp [hZ.ne', hZfull.ne']

/-- Replacing a failed draw by a deterministic fallback changes the law of
any subsequent probabilistic computation by at most the rejected mass. -/
theorem bind_fallback_apply_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A)
    (fallback : α → α) (hfallback : Measurable fallback)
    (hfallback_on : ∀ x ∈ A, fallback x = x)
    (K : α → Measure β) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (E : Set β) (hE : MeasurableSet E) :
    μ.bind (K ∘ fallback) E ≤
      (μ.restrict A).bind K E + μ Aᶜ := by
  rw [Measure.bind_apply hE (hK.comp hfallback).aemeasurable,
    Measure.bind_apply hE hK.aemeasurable]
  calc
    (∫⁻ x, (K ∘ fallback) x E ∂μ) =
        ∫⁻ x, (K ∘ fallback) x E
          ∂(μ.restrict A + μ.restrict Aᶜ) := by
      rw [Measure.restrict_add_restrict_compl hA]
    _ = (∫⁻ x, (K ∘ fallback) x E ∂μ.restrict A) +
        ∫⁻ x, (K ∘ fallback) x E ∂μ.restrict Aᶜ := by
      rw [lintegral_add_measure]
    _ = (∫⁻ x, K x E ∂μ.restrict A) +
        ∫⁻ x, (K ∘ fallback) x E ∂μ.restrict Aᶜ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      simp only [Function.comp_apply, hfallback_on x hx]
    _ ≤ (∫⁻ x, K x E ∂μ.restrict A) + μ Aᶜ := by
      gcongr
      calc
        (∫⁻ x, (K ∘ fallback) x E ∂μ.restrict Aᶜ) ≤
            ∫⁻ _x, (1 : ENNReal) ∂μ.restrict Aᶜ := by
          apply lintegral_mono
          intro x
          let _ := hKprob (fallback x)
          have hle := measure_mono (Set.subset_univ E : E ⊆ Set.univ)
            (μ := K (fallback x))
          change K (fallback x) E ≤ 1
          simpa only [measure_univ] using hle
        _ = μ Aᶜ := by
          rw [lintegral_one, Measure.restrict_apply_univ]

/-- Mapping a draw and then running a kernel is the same as binding the
kernel composed with that map. -/
theorem map_bind_eq_bind_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure α) (f : α → γ) (hf : Measurable f)
    (K : γ → Measure β) (hK : Measurable K) :
    (μ.map f).bind K = μ.bind (K ∘ f) := by
  ext E hE
  rw [Measure.bind_apply hE hK.aemeasurable,
    Measure.bind_apply hE (hK.comp hf).aemeasurable]
  have hm : AEMeasurable (fun x => K x E) (μ.map f) :=
    ((Measure.measurable_coe hE).comp hK).aemeasurable
  rw [lintegral_map' hm hf.aemeasurable]
  rfl

/-- The scalar multiplying the ideal initial restricted Gaussian is a
probability and hence is at most one. -/
theorem initialGaussianRestrictedMassCoefficient_le_one
    (q : VolumeParams) (I : VolumeInput q.n) :
    ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) (initialVariance q) /
          initialGaussianIntegral q) ≤ 1 := by
  let c : ENNReal := ENNReal.ofReal
    (gaussianIntegral (truncatedBody q I) (initialVariance q) /
      initialGaussianIntegral q)
  let ν : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q)
  have hrestrict := initialGaussianSamplingMeasure_restrict_truncatedBody q I
  change c ≤ 1
  change (initialGaussianSamplingMeasure q).restrict (truncatedBody q I) =
      c • ν at hrestrict
  have hmass := congrArg (fun m : Measure (AmbientSpace q.n) => m Set.univ)
    hrestrict
  have hA := truncatedBody_measurable q I
  rw [Measure.restrict_apply_univ, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
    at hmass
  rw [← hmass]
  simpa only [measure_univ] using
    (measure_mono (Set.subset_univ (truncatedBody q I))
      (μ := initialGaussianSamplingMeasure q))

/-- The successful part of the executable initial draw is dominated by the
ideal normalized restricted-Gaussian law. -/
theorem initialGaussianRestriction_bind_le
    {β : Type*} [MeasurableSpace β]
    (q : VolumeParams) (I : VolumeInput q.n)
    (K : AmbientSpace q.n → Measure β) (_hK : Measurable K)
    (E : Set β) (_hE : MeasurableSet E) :
    ((initialGaussianSamplingMeasure q).restrict (truncatedBody q I)).bind K E ≤
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind K) E := by
  rw [initialGaussianSamplingMeasure_restrict_truncatedBody q I,
    Measure.bind_smul, Measure.smul_apply]
  rw [smul_eq_mul]
  apply mul_le_of_le_one_left
  · exact bot_le
  exact initialGaussianRestrictedMassCoefficient_le_one q I

/-- Coupling bound for the actual initial fallback followed by any measurable
probability kernel.  This is the reusable interface needed by the complete
Figure-1 continuation: its event probability is at most the ideal-start event
probability plus `eps / 64`. -/
theorem initialTruncatedFallback_bind_apply_le
    {β : Type*} [MeasurableSpace β]
    (q : VolumeParams) (I : VolumeInput q.n)
    (K : AmbientSpace q.n → Measure β) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (E : Set β) (hE : MeasurableSet E) :
    (((initialGaussianSamplingMeasure q).map
        (initialTruncatedFallback q I)).bind K) E ≤
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind K) E +
          ENNReal.ofReal (q.eps / 64) := by
  rw [map_bind_eq_bind_comp _ _
    (measurable_initialTruncatedFallback q I) K hK]
  calc
    (initialGaussianSamplingMeasure q).bind
        (K ∘ initialTruncatedFallback q I) E ≤
      ((initialGaussianSamplingMeasure q).restrict
          (truncatedBody q I)).bind K E +
        initialGaussianSamplingMeasure q (truncatedBody q I)ᶜ :=
      bind_fallback_apply_le
        (initialGaussianSamplingMeasure q) (truncatedBody q I)
        (truncatedBody_measurable q I) (initialTruncatedFallback q I)
        (measurable_initialTruncatedFallback q I)
        (fun x hx => by
          simp [initialTruncatedFallback, Set.indicator_of_mem hx])
        K hK hKprob E hE
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind K) E +
        ENNReal.ofReal (q.eps / 64) := by
      exact add_le_add
        (initialGaussianRestriction_bind_le q I K hK E hE)
        (initialGaussianSamplingMeasure_truncatedBody_compl_le q I)

/-- Estimate law of the complete Figure-1 computation after initialization. -/
noncomputable def figureOneContinuationLaw
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) : Measure ℝ :=
  (figureOnePointContinuation S q point).runEstimate oracle.query

theorem figureOneContinuationLaw_measurable
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Measurable (figureOneContinuationLaw S q I oracle) := by
  exact (figureOnePointContinuation_measurable_and_strong S q I oracle).1

theorem figureOneContinuationLaw_isProbabilityMeasure
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    IsProbabilityMeasure (figureOneContinuationLaw S q I oracle point) := by
  unfold figureOneContinuationLaw
  exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
    ((figureOnePointContinuation_measurable_and_strong S q I oracle).2 point
      |>.estimateMeasurable)

/-- The interpreter law of the base program factors into the actual fallback
start followed by the named continuation kernel. -/
theorem runEstimate_figureOneBaseVolumeCooling_eq_initialFallback_bind
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (baseVolumeCooling figureOnePrimitives S q).runEstimate oracle.query =
      ((initialGaussianSamplingMeasure q).map
        (initialTruncatedFallback q I)).bind
          (figureOneContinuationLaw S q I oracle) := by
  let initialProgram : Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ := fun initialPoint =>
    match initialPoint with
    | none => .pure 0
    | some point => figureOnePointContinuation S q point
  have hcont := figureOnePointContinuation_measurable_and_strong S q I oracle
  have hinitialStrong : ∀ initialPoint,
      (initialProgram initialPoint).StronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hcont.2 point
  have hinitialRun : Measurable fun initialPoint =>
      (initialProgram initialPoint).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hcont.1 using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have hbase : baseVolumeCooling figureOnePrimitives S q =
      (figureOneInitialSample q).bind initialProgram := by
    unfold baseVolumeCooling
    change (figureOneInitialSample q).bind _ = _
    congr 1
  rw [hbase, MembershipOracleProgram.runEstimate_bind oracle.query _
    initialProgram (figureOneInitialSample_stronglyMeasurable q I oracle)
    hinitialStrong hinitialRun,
    runEstimate_figureOneInitialSample q I oracle]
  calc
    ((initialGaussianSamplingMeasure q).map
        (some ∘ initialTruncatedFallback q I)).bind
          (fun initialPoint =>
            (initialProgram initialPoint).runEstimate oracle.query) =
      (initialGaussianSamplingMeasure q).bind
        ((fun initialPoint =>
          (initialProgram initialPoint).runEstimate oracle.query) ∘
            (some ∘ initialTruncatedFallback q I)) :=
      map_bind_eq_bind_comp _ _
        (measurable_some.comp (measurable_initialTruncatedFallback q I))
        _ hinitialRun
    _ = (initialGaussianSamplingMeasure q).bind
        (figureOneContinuationLaw S q I oracle ∘
          initialTruncatedFallback q I) := by
      congr 1
    _ = ((initialGaussianSamplingMeasure q).map
          (initialTruncatedFallback q I)).bind
            (figureOneContinuationLaw S q I oracle) :=
      (map_bind_eq_bind_comp _ _
        (measurable_initialTruncatedFallback q I)
        _ (figureOneContinuationLaw_measurable S q I oracle)).symm

/-- Any measurable event for the executable base run is bounded by the same
event under an ideal restricted-Gaussian start plus the initial rejection
budget `eps / 64`. -/
theorem figureOneBaseVolumeCooling_event_le_idealStart_add
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (baseVolumeCooling figureOnePrimitives S q).runEstimate oracle.query E ≤
      ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (figureOneContinuationLaw S q I oracle)) E +
      ENNReal.ofReal (q.eps / 64) := by
  rw [runEstimate_figureOneBaseVolumeCooling_eq_initialFallback_bind]
  exact initialTruncatedFallback_bind_apply_le q I
    (figureOneContinuationLaw S q I oracle)
    (figureOneContinuationLaw_measurable S q I oracle)
    (figureOneContinuationLaw_isProbabilityMeasure S q I oracle) E hE

/-- A quarter upper bound on the measurable failure event gives the base
success probability required by the amplification theorem. -/
theorem outcomeProbability_ge_three_quarters_of_failure_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : VolumeParams) (I : VolumeInput q.n)
    (hfail : μ (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
    3 / 4 ≤ outcomeProbability μ (accurateOutcome q I) := by
  rw [outcomeProbability_eq_measure]
  let A := accurateOutcome q I
  have hA : MeasurableSet A := accurateOutcome_measurable q I
  have hsum : μ A + μ Aᶜ = 1 := by
    rw [← measure_union disjoint_compl_right hA.compl, Set.union_compl_self,
      measure_univ]
  have hAne : μ A ≠ ⊤ := measure_ne_top μ A
  have hAcne : μ Aᶜ ≠ ⊤ := measure_ne_top μ Aᶜ
  have hsumReal : (μ A).toReal + (μ Aᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add hAne hAcne, hsum, ENNReal.toReal_one]
  have hfailReal : (μ Aᶜ).toReal ≤ 1 / 4 := by
    apply (ENNReal.toReal_mono (by simp) hfail).trans_eq
    norm_num
  change 3 / 4 ≤ (μ A).toReal
  linarith

end ArlibCommunity.Algorithms.CV18
