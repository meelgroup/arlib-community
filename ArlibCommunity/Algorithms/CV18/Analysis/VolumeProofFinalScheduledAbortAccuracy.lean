/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalPhase

/-! # Initial accuracy coupling for the aborting scheduled executable

The live part of the initial Gaussian draw agrees with the restriction to the
truncated body.  The rejected part is sent to an arbitrary probability law
(the executable uses `dirac 0`), and is charged once by the initial Gaussian
tail bound.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Coupling an aborting initial draw to the normalized truncated Gaussian.
The abort output can have any probability law; its entire contribution is
bounded by the rejected initial mass. -/
theorem initialTruncatedOption_bind_apply_le
    {β : Type*} [MeasurableSpace β]
    (q : VolumeParams) (I : VolumeInput q.n)
    (abortLaw : Measure β) (hAbortProb : IsProbabilityMeasure abortLaw)
    (K : AmbientSpace q.n → Measure β) (hK : Measurable K)
    (hKprob : ∀ point, IsProbabilityMeasure (K point))
    (E : Set β) (hE : MeasurableSet E) :
    (((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind (fun initialPoint =>
          match initialPoint with
          | none => abortLaw
          | some point => K point)) E ≤
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind K) E +
          ENNReal.ofReal (q.eps / 64) := by
  let L : Option (AmbientSpace q.n) → Measure β := fun initialPoint =>
    match initialPoint with
    | none => abortLaw
    | some point => K point
  have hL : Measurable L := by
    convert Measurable.optionElim abortLaw hK using 1
    funext initialPoint
    cases initialPoint <;> rfl
  rw [map_bind_eq_bind_comp _ _ (measurable_initialTruncatedOption q I) L hL]
  rw [Measure.bind_apply hE
    (hL.comp (measurable_initialTruncatedOption q I)).aemeasurable,
    Measure.bind_apply hE hK.aemeasurable]
  calc
    (∫⁻ point, (L ∘ initialTruncatedOption q I) point E
        ∂initialGaussianSamplingMeasure q) =
        ∫⁻ point, (L ∘ initialTruncatedOption q I) point E
          ∂((initialGaussianSamplingMeasure q).restrict (truncatedBody q I) +
            (initialGaussianSamplingMeasure q).restrict
              (truncatedBody q I)ᶜ) := by
      rw [Measure.restrict_add_restrict_compl
        (truncatedBody_measurable q I)]
    _ = (∫⁻ point, (L ∘ initialTruncatedOption q I) point E
          ∂(initialGaussianSamplingMeasure q).restrict (truncatedBody q I)) +
        ∫⁻ point, (L ∘ initialTruncatedOption q I) point E
          ∂(initialGaussianSamplingMeasure q).restrict
            (truncatedBody q I)ᶜ := by
      rw [lintegral_add_measure]
    _ = (∫⁻ point, K point E
          ∂(initialGaussianSamplingMeasure q).restrict (truncatedBody q I)) +
        ∫⁻ point, (L ∘ initialTruncatedOption q I) point E
          ∂(initialGaussianSamplingMeasure q).restrict
            (truncatedBody q I)ᶜ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards
        [ae_restrict_mem (truncatedBody_measurable q I)] with point hpoint
      simp [L, initialTruncatedOption, hpoint]
    _ ≤ (∫⁻ point, K point E
          ∂(initialGaussianSamplingMeasure q).restrict (truncatedBody q I)) +
        initialGaussianSamplingMeasure q (truncatedBody q I)ᶜ := by
      gcongr
      calc
        (∫⁻ point, (L ∘ initialTruncatedOption q I) point E
            ∂(initialGaussianSamplingMeasure q).restrict
              (truncatedBody q I)ᶜ) ≤
            ∫⁻ _point, (1 : ENNReal)
              ∂(initialGaussianSamplingMeasure q).restrict
                (truncatedBody q I)ᶜ := by
          apply lintegral_mono
          intro point
          have hprob : IsProbabilityMeasure
              (L (initialTruncatedOption q I point)) := by
            unfold L
            cases initialTruncatedOption q I point with
            | none => exact hAbortProb
            | some point => exact hKprob point
          let _ := hprob
          have hle := measure_mono (Set.subset_univ E : E ⊆ Set.univ)
            (μ := L (initialTruncatedOption q I point))
          change L (initialTruncatedOption q I point) E ≤ 1
          simpa only [measure_univ] using hle
        _ = initialGaussianSamplingMeasure q (truncatedBody q I)ᶜ := by
          rw [lintegral_one, Measure.restrict_apply_univ]
    _ ≤ (∫⁻ point, K point E
          ∂(truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q))) + ENNReal.ofReal (q.eps / 64) := by
      exact add_le_add
        (lintegral_mono'
          (initialGaussianSamplingMeasure_restrict_truncatedBody_le q I)
          le_rfl)
        (initialGaussianSamplingMeasure_truncatedBody_compl_le q I)

/-- For an event which is impossible after the abort output, the rejected
initial Gaussian mass costs nothing.  Only the live restriction remains, and
that restriction is dominated by the normalized truncated Gaussian.  This is
the event-specific form needed for the global query-cap event: aborting after
the initial query cannot exhaust that cap. -/
theorem initialTruncatedOption_bind_apply_le_of_none_zero
    {β : Type*} [MeasurableSpace β]
    (q : VolumeParams) (I : VolumeInput q.n)
    (K : Option (AmbientSpace q.n) → Measure β) (hK : Measurable K)
    (E : Set β) (hE : MeasurableSet E) (hnone : K none E = 0) :
    (((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind K) E ≤
      (((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some).bind K) E := by
  rw [map_bind_eq_bind_comp _ _ (measurable_initialTruncatedOption q I) K hK]
  rw [Measure.bind_apply hE
    (hK.comp (measurable_initialTruncatedOption q I)).aemeasurable]
  calc
    (∫⁻ point, (K ∘ initialTruncatedOption q I) point E
        ∂initialGaussianSamplingMeasure q) =
        ∫⁻ point, (K ∘ initialTruncatedOption q I) point E
          ∂((initialGaussianSamplingMeasure q).restrict (truncatedBody q I) +
            (initialGaussianSamplingMeasure q).restrict
              (truncatedBody q I)ᶜ) := by
      rw [Measure.restrict_add_restrict_compl
        (truncatedBody_measurable q I)]
    _ = (∫⁻ point, (K ∘ initialTruncatedOption q I) point E
          ∂(initialGaussianSamplingMeasure q).restrict (truncatedBody q I)) +
        ∫⁻ point, (K ∘ initialTruncatedOption q I) point E
          ∂(initialGaussianSamplingMeasure q).restrict
            (truncatedBody q I)ᶜ := by
      rw [lintegral_add_measure]
    _ = (∫⁻ point, K (some point) E
          ∂(initialGaussianSamplingMeasure q).restrict (truncatedBody q I)) + 0 := by
      congr 1
      · apply lintegral_congr_ae
        filter_upwards
          [ae_restrict_mem (truncatedBody_measurable q I)] with point hpoint
        simp [initialTruncatedOption, hpoint]
      · rw [← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards
          [ae_restrict_mem (truncatedBody_measurable q I).compl] with point hpoint
        have hpoint' : point ∉ truncatedBody q I := hpoint
        simp [initialTruncatedOption, hpoint', hnone]
    _ ≤ ∫⁻ point, K (some point) E
          ∂(truncatedGaussianProbability q I (initialVariance q)
            (initialVariance_pos q)) := by
      rw [add_zero]
      exact lintegral_mono'
        (initialGaussianSamplingMeasure_restrict_truncatedBody_le q I) le_rfl
    _ = (((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some).bind K) E := by
      rw [map_bind_eq_bind_comp _ _ measurable_some K hK]
      rw [Measure.bind_apply hE (hK.comp measurable_some).aemeasurable]
      rfl

/-- Exact initial-law decomposition for the aborting scheduled base program. -/
theorem figureOneFinalScheduledAbortBaseProgram_runEstimate_eq_initial_bind
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query =
      ((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind (fun initialPoint =>
          match initialPoint with
          | none => Measure.dirac (0 : ℝ)
          | some point =>
              (scheduledBalancedFigureOnePointContinuation
                figureOneFinalScheduledBalancedParameters q point).runEstimate
                  oracle.query) := by
  let tail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point
  have hpoint := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  have htailStrong : ∀ initialPoint,
      (tail initialPoint).StronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact (hpoint.2 point).stronglyMeasurable
  have htailRun : Measurable fun initialPoint =>
      (tail initialPoint).runEstimate oracle.query := by
    have hpointRun : Measurable fun point =>
        (scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point).runEstimate
            oracle.query := by
      rw [show (fun point =>
          (scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).runEstimate
              oracle.query) = fun point =>
            ((scheduledBalancedFigureOnePointContinuation
              figureOneFinalScheduledBalancedParameters q point).run
                oracle.query).map Prod.fst by
        funext point
        exact MembershipOracleProgram.runEstimate_eq_map_fst_run
          oracle.query _ (hpoint.2 point).executionMeasurable]
      exact (Measure.measurable_map _ measurable_fst).comp hpoint.1
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hpointRun using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have hbase : figureOneFinalScheduledAbortBaseProgram q =
      (figureOneAbortInitialSample q).bind tail := by
    unfold figureOneFinalScheduledAbortBaseProgram baseVolumeCooling tail
    congr 1
    funext initialPoint
    cases initialPoint with
    | none => rfl
    | some point =>
        exact scheduledBalancedAbort_pointContinuation_eq
          figureOneFinalScheduledBalancedParameters q point
  have htailLaw : (fun initialPoint =>
      (tail initialPoint).runEstimate oracle.query) = fun initialPoint =>
        match initialPoint with
        | none => Measure.dirac (0 : ℝ)
        | some point =>
            (scheduledBalancedFigureOnePointContinuation
              figureOneFinalScheduledBalancedParameters q point).runEstimate
                oracle.query := by
    funext initialPoint
    cases initialPoint <;> rfl
  rw [hbase]
  rw [MembershipOracleProgram.runEstimate_bind oracle.query _ tail
    (figureOneAbortInitialSample_stronglyMeasurable q I oracle)
      htailStrong htailRun]
  rw [runEstimate_figureOneAbortInitialSample q I oracle]
  rw [htailLaw]

/-- Accuracy transport from the already formalized post-initial CV18 bound
to the paper-faithful aborting executable. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_directPostInitial
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hpost : FigureOnePostInitialDirectFailureBoundFor q I fun point =>
      (scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point).runEstimate
          oracle.query) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let continuation : AmbientSpace q.n → Measure ℝ := fun point =>
    (scheduledBalancedFigureOnePointContinuation
      figureOneFinalScheduledBalancedParameters q point).runEstimate
        oracle.query
  have hpoint := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  have hcontinuationMeas : Measurable continuation := by
    rw [show continuation = fun point =>
        ((scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point).run
            oracle.query).map Prod.fst by
      funext point
      exact MembershipOracleProgram.runEstimate_eq_map_fst_run
        oracle.query _ (hpoint.2 point).executionMeasurable]
    exact (Measure.measurable_map _ measurable_fst).comp hpoint.1
  have hcontinuationProb : ∀ point,
      IsProbabilityMeasure (continuation point) := fun point =>
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      (hpoint.2 point).stronglyMeasurable.estimateMeasurable
  have hinitial := initialTruncatedOption_bind_apply_le q I
    (Measure.dirac (0 : ℝ)) inferInstance continuation hcontinuationMeas
      hcontinuationProb (accurateOutcome q I)ᶜ
        (accurateOutcome_measurable q I).compl
  rw [figureOneFinalScheduledAbortBaseProgram_runEstimate_eq_initial_bind]
  unfold FigureOnePostInitialDirectFailureBoundFor at hpost
  calc
    ((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind (fun initialPoint =>
          match initialPoint with
          | none => Measure.dirac (0 : ℝ)
          | some point => continuation point) (accurateOutcome q I)ᶜ ≤
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation) (accurateOutcome q I)ᶜ +
            ENNReal.ofReal (q.eps / 64) := hinitial
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) := by
      exact add_le_add hpost (ENNReal.ofReal_le_ofReal (by
        linarith [q.heps.2]))
    _ = ENNReal.ofReal (13 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 16)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

#print axioms initialTruncatedOption_bind_apply_le
#print axioms figureOneFinalScheduledAbortBaseProgram_runEstimate_eq_initial_bind
#print axioms figureOneFinalScheduledAbortBase_failure_le_of_directPostInitial

end ArlibCommunity.Algorithms.CV18
