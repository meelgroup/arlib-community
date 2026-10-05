/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ProgramSemantics
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofTruncation

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-! # Concrete Figure-1 oracle programs -/

/-- The centered Gaussian with covariance `initialVariance q * I`, defined
directly by its normalized Lebesgue density.  This keeps the executable law
identical to the density used by the initial-tail proof and avoids any bridge
through Mathlib's standard-Gaussian volume API. -/
noncomputable def initialGaussianSamplingMeasure (q : VolumeParams) :
    Measure (AmbientSpace q.n) :=
  volume.withDensity fun x => ENNReal.ofReal
    (gaussianDensity (initialVariance q) x / initialGaussianIntegral q)

theorem initialGaussianIntegral_pos (q : VolumeParams) :
    0 < initialGaussianIntegral q := by
  unfold initialGaussianIntegral
  exact Real.rpow_pos_of_pos
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (initialVariance_pos q)) _

instance initialGaussianSamplingMeasure_isProbabilityMeasure (q : VolumeParams) :
    IsProbabilityMeasure (initialGaussianSamplingMeasure q) := by
  constructor
  unfold initialGaussianSamplingMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hZ := initialGaussianIntegral_pos q
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_gaussianDensity (initialVariance_pos q)).div_const _)]
  · rw [integral_div, integral_gaussianDensity (initialVariance_pos q)]
    change ENNReal.ofReal (initialGaussianIntegral q / initialGaussianIntegral q) = 1
    rw [div_self hZ.ne']
    simp
  · exact Filter.Eventually.of_forall fun x =>
      div_nonneg (Real.exp_pos _).le hZ.le

theorem initialGaussianSamplingMeasure_apply (q : VolumeParams)
    {S : Set (AmbientSpace q.n)} (hS : MeasurableSet S) :
    initialGaussianSamplingMeasure q S = ENNReal.ofReal
      ((∫ x in S, gaussianDensity (initialVariance q) x) /
        initialGaussianIntegral q) := by
  unfold initialGaussianSamplingMeasure
  rw [withDensity_apply _ hS]
  have hZ := initialGaussianIntegral_pos q
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_gaussianDensity (initialVariance_pos q)).integrableOn.div_const _)]
  · congr 1
    rw [integral_div]
  · filter_upwards [ae_restrict_mem hS] with x hx
    exact div_nonneg (Real.exp_pos _).le hZ.le

/-- The single initial membership test rejects with only the tail probability
already budgeted by the all-epsilon starting variance. -/
theorem initialGaussianSamplingMeasure_body_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    initialGaussianSamplingMeasure q
        ((I.body : Set (AmbientSpace q.n))ᶜ) ≤
      ENNReal.ofReal (q.eps / 64) := by
  rw [initialGaussianSamplingMeasure_apply q I.body.isClosed.measurableSet.compl]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (initialGaussianIntegral_pos q)]
  calc
    (∫ x in (I.body : Set (AmbientSpace q.n))ᶜ,
        gaussianDensity (initialVariance q) x) ≤
        ∫ x in (unitBall q.n)ᶜ,
          gaussianDensity (initialVariance q) x := by
      apply setIntegral_mono_set
        (integrable_gaussianDensity (initialVariance_pos q)).integrableOn
      · filter_upwards with x
        exact (Real.exp_pos _).le
      · filter_upwards with x
        intro hx
        exact Set.compl_subset_compl.mpr I.unitBall_subset hx
    _ ≤ q.eps / 64 * initialGaussianIntegral q := initial_tail_mass_le q

theorem initialGaussianSamplingMeasure_truncatedBody_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    initialGaussianSamplingMeasure q (truncatedBody q I)ᶜ ≤
      ENNReal.ofReal (q.eps / 64) := by
  rw [initialGaussianSamplingMeasure_apply q (truncatedBody_measurable q I).compl]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (initialGaussianIntegral_pos q)]
  calc
    (∫ x in (truncatedBody q I)ᶜ,
        gaussianDensity (initialVariance q) x) ≤
        ∫ x in (unitBall q.n)ᶜ,
          gaussianDensity (initialVariance q) x := by
      apply setIntegral_mono_set
        (integrable_gaussianDensity (initialVariance_pos q)).integrableOn
      · filter_upwards with x
        exact (Real.exp_pos _).le
      · filter_upwards with x
        intro hx
        exact Set.compl_subset_compl.mpr (unitBall_subset_truncatedBody q I) hx
    _ ≤ q.eps / 64 * initialGaussianIntegral q := initial_tail_mass_le q

noncomputable def initialTruncatedFallback (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) : AmbientSpace q.n :=
  (truncatedBody q I).indicator id point

theorem measurable_initialTruncatedFallback (q : VolumeParams)
    (I : VolumeInput q.n) : Measurable (initialTruncatedFallback q I) := by
  unfold initialTruncatedFallback
  exact measurable_id.indicator (truncatedBody_measurable q I)

/-- One Gaussian proposal and one membership query.  Proposals outside either
the oracle body or the fixed truncation ball fall back to the origin, which is
in the truncated body by the unit-ball promise. -/
noncomputable def figureOneInitialSample (q : VolumeParams) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  .randomPoint (initialGaussianSamplingMeasure q) inferInstance fun point =>
    .query point fun inside =>
      .pure (some (if inside = true ∧
        ‖point‖ ≤ Real.sqrt (terminalVariance q) then point else 0))

theorem figureOneInitialSample_queryBound (q : VolumeParams) :
    (figureOneInitialSample q).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro point
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

theorem figureOneInitialSample_stronglyMeasurable (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneInitialSample q).StronglyMeasurable oracle.query := by
  simp only [figureOneInitialSample, MembershipOracleProgram.StronglyMeasurable]
  constructor
  · simp only [MembershipOracleProgram.runEstimate]
    apply Measure.measurable_dirac.comp
    have hif : Measurable fun point : AmbientSpace q.n =>
        if oracle.query point = true ∧
            ‖point‖ ≤ Real.sqrt (terminalVariance q) then point else 0 := by
      apply Measurable.ite
      · exact (oracle.measurable_query (measurableSet_singleton true)).inter
          (measurableSet_le measurable_norm measurable_const)
      · exact measurable_id
      · exact measurable_const
    exact measurable_some.comp hif
  · intro point
    trivial

theorem runEstimate_figureOneInitialSample
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneInitialSample q).runEstimate oracle.query =
      (initialGaussianSamplingMeasure q).map
        (some ∘ initialTruncatedFallback q I) := by
  unfold figureOneInitialSample
  simp only [MembershipOracleProgram.runEstimate]
  have hmap : Measurable (some ∘ initialTruncatedFallback q I) :=
    measurable_some.comp (measurable_initialTruncatedFallback q I)
  have hfun : (fun point : AmbientSpace q.n =>
      some (if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) then point else 0)) =
      some ∘ initialTruncatedFallback q I := by
    funext point
    apply congrArg some
    unfold initialTruncatedFallback truncatedBody
    by_cases hc : oracle.query point = true ∧
        ‖point‖ ≤ Real.sqrt (terminalVariance q)
    · have hp : point ∈
          (I.body : Set (AmbientSpace q.n)) ∩
            Metric.closedBall 0 (Real.sqrt (terminalVariance q)) := by
        exact ⟨(oracle.correct point).mp hc.1, by
          simpa [Metric.mem_closedBall, dist_zero_right] using hc.2⟩
      simp [hc, Set.indicator_of_mem hp]
    · have hp : point ∉
          (I.body : Set (AmbientSpace q.n)) ∩
            Metric.closedBall 0 (Real.sqrt (terminalVariance q)) := by
        intro hp
        apply hc
        exact ⟨(oracle.correct point).mpr hp.1, by
          simpa [Metric.mem_closedBall, dist_zero_right] using hp.2⟩
      simp [hc, Set.indicator_of_notMem hp]
  rw [show (fun point : AmbientSpace q.n =>
      Measure.dirac (some (if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) then point else 0))) =
      (fun point => Measure.dirac ((some ∘ initialTruncatedFallback q I) point)) by
    funext point
    rw [congrFun hfun point]]
  rw [Measure.bind_dirac_eq_map _ hmap]

/-- Half the Metropolis acceptance probability makes the chain lazy. -/
noncomputable def lazyGaussianMetropolisAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  gaussianMetropolisAcceptance sigma2 x y / 2

/-- Accept only points in both the oracle body and the fixed truncation ball.
The oracle is queried even outside the ball, giving one query per step. -/
noncomputable def truncatedMetropolisProposalProgram (q : VolumeParams)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      .pure <| if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
        then proposal else current

/-- Estimate-only law of a proposal after the membership answer is read. -/
noncomputable def truncatedMetropolisProposalEstimateLaw
    {n : ℕ} (oracle : AmbientSpace n → Bool) (terminal sigma2 : ℝ)
    (current proposal : AmbientSpace n) : Measure (AmbientSpace n) :=
  uniformUnitIntervalMeasure.map fun coin =>
    if oracle proposal = true ∧ ‖proposal‖ ≤ Real.sqrt terminal ∧
        coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
      then proposal else current

theorem measurable_truncatedMetropolisProposalEstimateLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) :
    Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 p.1 p.2 := by
  unfold truncatedMetropolisProposalEstimateLaw
  apply measurable_measure_map_param
  have horacle : Measurable fun p :
      (AmbientSpace q.n × AmbientSpace q.n) × ℝ => oracle.query p.1.2 :=
    oracle.measurable_query.comp (measurable_snd.comp measurable_fst)
  have hnorm : Measurable fun p :
      (AmbientSpace q.n × AmbientSpace q.n) × ℝ => ‖p.1.2‖ := by fun_prop
  have haccept : Measurable fun p :
      (AmbientSpace q.n × AmbientSpace q.n) × ℝ =>
        lazyGaussianMetropolisAcceptance sigma2 p.1.1 p.1.2 := by
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  apply Measurable.ite
  · exact (horacle (measurableSet_singleton true)).inter
      ((measurableSet_le hnorm measurable_const).inter
        (measurableSet_le measurable_snd haccept))
  · exact measurable_snd.comp measurable_fst
  · exact measurable_fst.comp measurable_fst

theorem runEstimate_truncatedMetropolisProposalProgram
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisProposalProgram q sigma2 current proposal).runEstimate
        oracle.query =
      truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal := by
  unfold truncatedMetropolisProposalProgram
    truncatedMetropolisProposalEstimateLaw
  simp only [MembershipOracleProgram.runEstimate]
  have hout : Measurable fun coin : ℝ =>
      if oracle.query proposal = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
        then proposal else current := by
    apply Measurable.ite
    · measurability
    · exact measurable_const
    · exact measurable_const
  rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hout]

theorem truncatedMetropolisProposalProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisProposalProgram q sigma2 current proposal).StronglyMeasurable
      oracle.query := by
  simp only [truncatedMetropolisProposalProgram,
    MembershipOracleProgram.StronglyMeasurable]
  constructor
  · simp only [MembershipOracleProgram.runEstimate]
    apply Measure.measurable_dirac.comp
    apply Measurable.ite
    · measurability
    · exact measurable_const
    · exact measurable_const
  · intro coin
    trivial

/-- The proposal radius displayed in the paper. -/
noncomputable def figureOneProposalRadius (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (Real.sqrt sigma2) 1 /
    (4096 * Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps)))

noncomputable def truncatedMetropolisBallStep (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (AmbientSpace q.n) :=
  .randomPoint
      (uniformClosedBallMeasure q.n current (figureOneProposalRadius q sigma2))
      inferInstance fun proposal =>
    truncatedMetropolisProposalProgram q sigma2 current proposal

/-- Explicit estimate law of one truncated lazy ball-walk step. -/
noncomputable def truncatedMetropolisBallStepEstimateLaw
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (AmbientSpace q.n) :=
  (centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2)).bind fun offset =>
    truncatedMetropolisProposalEstimateLaw oracle (terminalVariance q) sigma2
      current (current + offset)

theorem measurable_truncatedMetropolisBallStepEstimateLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) :
    Measurable fun current =>
      truncatedMetropolisBallStepEstimateLaw q oracle.query sigma2 current := by
  unfold truncatedMetropolisBallStepEstimateLaw
  apply measurable_measure_bind_param
  exact (measurable_truncatedMetropolisProposalEstimateLaw q I oracle sigma2).comp
    (measurable_fst.prodMk (measurable_fst.add measurable_snd))

theorem runEstimate_truncatedMetropolisBallStep
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisBallStep q sigma2 current).runEstimate oracle.query =
      truncatedMetropolisBallStepEstimateLaw q oracle.query sigma2 current := by
  simp only [truncatedMetropolisBallStep, MembershipOracleProgram.runEstimate]
  rw [show (fun proposal =>
      (truncatedMetropolisProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) =
      (fun proposal => truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal) by
    funext proposal
    exact runEstimate_truncatedMetropolisProposalProgram
      q I oracle sigma2 current proposal]
  ext s hs
  have hproposal : Measurable fun proposal : AmbientSpace q.n =>
      truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal :=
    (measurable_truncatedMetropolisProposalEstimateLaw q I oracle sigma2).comp
      (measurable_const.prodMk measurable_id)
  have hoffset : Measurable fun offset : AmbientSpace q.n =>
      truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current (current + offset) :=
    hproposal.comp (measurable_const.add measurable_id)
  unfold truncatedMetropolisBallStepEstimateLaw uniformClosedBallMeasure
  rw [Measure.bind_apply hs hproposal.aemeasurable,
    Measure.bind_apply hs hoffset.aemeasurable]
  exact lintegral_map (Measure.measurable_coe hs |>.comp hproposal)
    (by fun_prop)

theorem truncatedMetropolisBallStep_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisBallStep q sigma2 current).StronglyMeasurable oracle.query := by
  simp only [truncatedMetropolisBallStep,
    MembershipOracleProgram.StronglyMeasurable]
  constructor
  · rw [show (fun proposal =>
        (truncatedMetropolisProposalProgram q sigma2 current proposal).runEstimate
          oracle.query) =
      (fun proposal => truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal) by
      funext proposal
      exact runEstimate_truncatedMetropolisProposalProgram
        q I oracle sigma2 current proposal]
    exact (measurable_truncatedMetropolisProposalEstimateLaw q I oracle sigma2).comp
      (measurable_const.prodMk measurable_id)
  · exact fun proposal =>
      truncatedMetropolisProposalProgram_stronglyMeasurable
        q I oracle sigma2 current proposal

theorem truncatedMetropolisBallStep_queryBound (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  exact .pure _ 0

/-- A fixed number of lazy Metropolis steps. -/
noncomputable def truncatedMetropolisBallWalk (q : VolumeParams)
    (sigma2 : ℝ) : ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (AmbientSpace q.n)
  | 0, current => .pure current
  | steps + 1, current =>
      (truncatedMetropolisBallStep q sigma2 current).bind
        (truncatedMetropolisBallWalk q sigma2 steps)

theorem truncatedMetropolisBallWalk_queryBound (q : VolumeParams)
    (sigma2 : ℝ) : ∀ steps current,
    (truncatedMetropolisBallWalk q sigma2 steps current).QueryBound steps := by
  intro steps
  induction steps with
  | zero =>
      intro current
      exact .pure _ 0
  | succ steps ih =>
      intro current
      simp only [truncatedMetropolisBallWalk]
      have h := (truncatedMetropolisBallStep_queryBound q sigma2 current).bind ih
      simpa [Nat.add_comm] using h

theorem truncatedMetropolisBallWalk_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) : ∀ steps,
      Measurable (fun current =>
        (truncatedMetropolisBallWalk q sigma2 steps current).runEstimate
          oracle.query) ∧
      ∀ current,
        (truncatedMetropolisBallWalk q sigma2 steps current).StronglyMeasurable
          oracle.query := by
  intro steps
  induction steps with
  | zero =>
      constructor
      · simp only [truncatedMetropolisBallWalk,
          MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac
      · intro current
        trivial
  | succ steps ih =>
      have hstepMeas : Measurable fun current =>
          (truncatedMetropolisBallStep q sigma2 current).runEstimate
            oracle.query := by
        rw [show (fun current =>
            (truncatedMetropolisBallStep q sigma2 current).runEstimate
              oracle.query) =
          (fun current => truncatedMetropolisBallStepEstimateLaw
            q oracle.query sigma2 current) by
          funext current
          exact runEstimate_truncatedMetropolisBallStep
            q I oracle sigma2 current]
        exact measurable_truncatedMetropolisBallStepEstimateLaw q I oracle sigma2
      have hrun : (fun current =>
          (truncatedMetropolisBallWalk q sigma2 (steps + 1) current).runEstimate
            oracle.query) =
          (fun current =>
            ((truncatedMetropolisBallStep q sigma2 current).runEstimate
              oracle.query).bind fun point =>
                (truncatedMetropolisBallWalk q sigma2 steps point).runEstimate
                  oracle.query) := by
        funext current
        simp only [truncatedMetropolisBallWalk]
        exact MembershipOracleProgram.runEstimate_bind oracle.query
          (truncatedMetropolisBallStep q sigma2 current)
          (truncatedMetropolisBallWalk q sigma2 steps)
          (truncatedMetropolisBallStep_stronglyMeasurable
            q I oracle sigma2 current) ih.2 ih.1
      constructor
      · rw [hrun]
        exact (Measure.measurable_bind' ih.1).comp hstepMeas
      · intro current
        simp only [truncatedMetropolisBallWalk]
        exact (truncatedMetropolisBallStep_stronglyMeasurable
          q I oracle sigma2 current).bind ih.2 ih.1

/-- The body indicator cancels from a ratio at points known to be inside. -/
noncomputable def gaussianRatioWeight {n : ℕ} (sigma2 tau2 : ℝ)
    (x : AmbientSpace n) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (2 * tau2)) /
    Real.exp (-‖x‖ ^ 2 / (2 * sigma2))

noncomputable def uniformRatioWeight {n : ℕ} (sigma2 : ℝ)
    (x : AmbientSpace n) : ℝ :=
  Real.exp (‖x‖ ^ 2 / (2 * sigma2))

theorem measurable_gaussianRatioWeight {n : ℕ} (sigma2 tau2 : ℝ) :
    Measurable (gaussianRatioWeight (n := n) sigma2 tau2) := by
  unfold gaussianRatioWeight
  fun_prop

theorem measurable_uniformRatioWeight {n : ℕ} (sigma2 : ℝ) :
    Measurable (uniformRatioWeight (n := n) sigma2) := by
  unfold uniformRatioWeight
  fun_prop

/-- Collect fixed-many walk endpoints, sum their weights, and retain the last
endpoint as the warm state for the following phase. -/
noncomputable def collectWalkWeights (q : VolumeParams) (sigma2 : ℝ)
    (walkSteps : ℕ) (weight : AmbientSpace q.n → ℝ) :
    ℕ → AmbientSpace q.n → MembershipOracleProgram q.n (ℝ × AmbientSpace q.n)
  | 0, current => .pure (0, current)
  | samples + 1, current =>
      (truncatedMetropolisBallWalk q sigma2 walkSteps current).bind fun point =>
        (collectWalkWeights q sigma2 walkSteps weight samples point).bind fun tail =>
          .pure (weight point + tail.1, tail.2)

theorem collectWalkWeights_queryBound (q : VolumeParams) (sigma2 : ℝ)
    (walkSteps : ℕ) (weight : AmbientSpace q.n → ℝ) : ∀ samples current,
    (collectWalkWeights q sigma2 walkSteps weight samples current).QueryBound
      (samples * walkSteps) := by
  intro samples
  induction samples with
  | zero =>
      intro current
      simpa [collectWalkWeights] using
        (MembershipOracleProgram.QueryBound.pure (0, current) 0)
  | succ samples ih =>
      intro current
      simp only [collectWalkWeights]
      have htail : ∀ point,
          ((collectWalkWeights q sigma2 walkSteps weight samples point).bind fun tail =>
            .pure (weight point + tail.1, tail.2)).QueryBound
              (samples * walkSteps) := by
        intro point
        exact (ih point).bind fun tail => .pure _ 0
      have h := (truncatedMetropolisBallWalk_queryBound q sigma2 walkSteps current).bind htail
      simpa [Nat.succ_mul, Nat.add_comm] using h

theorem collectWalkWeights_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (walkSteps : ℕ) (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) : ∀ samples,
      Measurable (fun current =>
        (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
          oracle.query) ∧
      ∀ current,
        (collectWalkWeights q sigma2 walkSteps weight samples current).StronglyMeasurable
          oracle.query := by
  intro samples
  induction samples with
  | zero =>
      constructor
      · simp only [collectWalkWeights, MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          (measurable_const.prodMk measurable_id)
      · intro current
        trivial
  | succ samples ih =>
      have hwalk := truncatedMetropolisBallWalk_measurable_and_strong
        q I oracle sigma2 walkSteps
      let tailProgram : AmbientSpace q.n →
          MembershipOracleProgram q.n (ℝ × AmbientSpace q.n) := fun point =>
        (collectWalkWeights q sigma2 walkSteps weight samples point).bind fun tail =>
          .pure (weight point + tail.1, tail.2)
      have htailOutput : ∀ point, Measurable fun tail : ℝ × AmbientSpace q.n =>
          (.pure (weight point + tail.1, tail.2) :
            MembershipOracleProgram q.n (ℝ × AmbientSpace q.n)).runEstimate
              oracle.query := by
        intro point
        simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have htailStrong : ∀ point, (tailProgram point).StronglyMeasurable
          oracle.query := by
        intro point
        exact (ih.2 point).bind (fun tail => by trivial) (htailOutput point)
      have htailRun : Measurable fun point =>
          (tailProgram point).runEstimate oracle.query := by
        have hprob : ∀ point, IsProbabilityMeasure
            ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query) := fun point =>
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
            (ih.2 point).estimateMeasurable
        have htransform : Measurable fun p :
            AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
              (weight p.1 + p.2.1, p.2.2) :=
          ((hweight.comp measurable_fst).add
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)
        have hbind : Measurable fun point =>
            ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query).bind fun tail =>
                Measure.dirac (weight point + tail.1, tail.2) :=
          measurable_measure_bind_param_variable ih.1 hprob
            (Measure.measurable_dirac.comp htransform)
        rw [show (fun point => (tailProgram point).runEstimate oracle.query) =
            (fun point =>
              ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
                oracle.query).bind fun tail =>
                  Measure.dirac (weight point + tail.1, tail.2)) by
          funext point
          unfold tailProgram
          exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
            (ih.2 point) (fun tail => by trivial) (htailOutput point)]
        exact hbind
      have hrun : (fun current =>
          (collectWalkWeights q sigma2 walkSteps weight (samples + 1) current).runEstimate
            oracle.query) =
          (fun current =>
            ((truncatedMetropolisBallWalk q sigma2 walkSteps current).runEstimate
              oracle.query).bind fun point =>
                (tailProgram point).runEstimate oracle.query) := by
        funext current
        simp only [collectWalkWeights]
        exact MembershipOracleProgram.runEstimate_bind oracle.query _ tailProgram
          (hwalk.2 current) htailStrong htailRun
      constructor
      · rw [hrun]
        exact (Measure.measurable_bind' htailRun).comp hwalk.1
      · intro current
        simp only [collectWalkWeights]
        exact (hwalk.2 current).bind htailStrong htailRun

/-- The paper's sample count for accelerated phases and the terminal
Gaussian-to-uniform phase. -/
noncomputable def figureOneSampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (512 * protectedLog (terminalVariance q) / q.eps ^ 2)

/-- The all-epsilon starting variance lengthens the fixed-rate chain from
`O(n log n)` to `O(n log(n/eps))`; its empirical means therefore use the
matching logarithm. -/
noncomputable def figureOneFixedSampleCount (q : VolumeParams) : ℕ :=
  Nat.ceil
    (4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)

/-- Phase-sensitive sample count.  Accelerated phases keep the paper's
`log terminalVariance` count, avoiding an unnecessary runtime penalty. -/
noncomputable def figureOnePhaseSampleCount (q : VolumeParams)
    (sigma2 : ℝ) : ℕ :=
  if sigma2 ≤ 1 then figureOneFixedSampleCount q else figureOneSampleCount q

/-- The explicit fixed walk cap whose adequacy is the ball-walk mixing
obligation in the base-run proof. -/
noncomputable def figureOneWalkSteps (q : VolumeParams) (sigma2 : ℝ) : ℕ :=
  Nat.ceil
    (10 ^ 16 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
      protectedLog ((q.n : ℝ) / q.eps) ^ 2)

noncomputable def figureOneRatioEstimate (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (collectWalkWeights q sigma2 (figureOneWalkSteps q sigma2)
      (gaussianRatioWeight sigma2 tau2) (figureOnePhaseSampleCount q sigma2) current).bind
    fun total =>
      .pure (some (total.1 / (figureOnePhaseSampleCount q sigma2 : ℝ), total.2))

noncomputable def figureOneUniformRatioEstimate (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (collectWalkWeights q sigma2 (figureOneWalkSteps q sigma2)
      (uniformRatioWeight sigma2) (figureOneSampleCount q) current).bind
    fun total =>
      .pure (some (total.1 / (figureOneSampleCount q : ℝ)))

theorem figureOneRatioEstimate_queryBound (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    (figureOneRatioEstimate q sigma2 tau2 current).QueryBound
      (figureOnePhaseSampleCount q sigma2 * figureOneWalkSteps q sigma2) := by
  unfold figureOneRatioEstimate
  exact (collectWalkWeights_queryBound q sigma2 _ _ _ current).bind
    fun total => .pure _ 0

theorem figureOneUniformRatioEstimate_queryBound (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (figureOneUniformRatioEstimate q sigma2 current).QueryBound
      (figureOneSampleCount q * figureOneWalkSteps q sigma2) := by
  unfold figureOneUniformRatioEstimate
  exact (collectWalkWeights_queryBound q sigma2 _ _ _ current).bind
    fun total => .pure _ 0

theorem figureOneRatioEstimate_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 tau2 : ℝ) :
    Measurable (fun current =>
      (figureOneRatioEstimate q sigma2 tau2 current).runEstimate oracle.query) ∧
    ∀ current,
      (figureOneRatioEstimate q sigma2 tau2 current).StronglyMeasurable
        oracle.query := by
  have hcollect := collectWalkWeights_measurable_and_strong q I oracle sigma2
    (figureOneWalkSteps q sigma2) (gaussianRatioWeight sigma2 tau2)
    (measurable_gaussianRatioWeight sigma2 tau2)
      (figureOnePhaseSampleCount q sigma2)
  have hout : Measurable fun total : ℝ × AmbientSpace q.n =>
      (.pure (some (total.1 / (figureOnePhaseSampleCount q sigma2 : ℝ), total.2)) :
        MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))).runEstimate
          oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp <| measurable_some.comp <|
      (measurable_fst.div_const _).prodMk measurable_snd
  constructor
  · rw [show (fun current =>
        (figureOneRatioEstimate q sigma2 tau2 current).runEstimate oracle.query) =
      (fun current =>
        ((collectWalkWeights q sigma2 (figureOneWalkSteps q sigma2)
          (gaussianRatioWeight sigma2 tau2) (figureOnePhaseSampleCount q sigma2)
            current).runEstimate oracle.query).bind fun total =>
              Measure.dirac
                (some (total.1 / (figureOnePhaseSampleCount q sigma2 : ℝ), total.2))) by
      funext current
      unfold figureOneRatioEstimate
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (hcollect.2 current) (fun total => by trivial) hout]
    exact (Measure.measurable_bind' hout).comp hcollect.1
  · intro current
    unfold figureOneRatioEstimate
    exact (hcollect.2 current).bind (fun total => by trivial) hout

theorem figureOneUniformRatioEstimate_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) :
    Measurable (fun current =>
      (figureOneUniformRatioEstimate q sigma2 current).runEstimate oracle.query) ∧
    ∀ current,
      (figureOneUniformRatioEstimate q sigma2 current).StronglyMeasurable
        oracle.query := by
  have hcollect := collectWalkWeights_measurable_and_strong q I oracle sigma2
    (figureOneWalkSteps q sigma2) (uniformRatioWeight sigma2)
    (measurable_uniformRatioWeight sigma2) (figureOneSampleCount q)
  have hout : Measurable fun total : ℝ × AmbientSpace q.n =>
      (.pure (some (total.1 / (figureOneSampleCount q : ℝ))) :
        MembershipOracleProgram q.n (Option ℝ)).runEstimate oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp <| measurable_some.comp <|
      measurable_fst.div_const _
  constructor
  · rw [show (fun current =>
        (figureOneUniformRatioEstimate q sigma2 current).runEstimate oracle.query) =
      (fun current =>
        ((collectWalkWeights q sigma2 (figureOneWalkSteps q sigma2)
          (uniformRatioWeight sigma2) (figureOneSampleCount q)
            current).runEstimate oracle.query).bind fun total =>
              Measure.dirac (some (total.1 / (figureOneSampleCount q : ℝ)))) by
      funext current
      unfold figureOneUniformRatioEstimate
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (hcollect.2 current) (fun total => by trivial) hout]
    exact (Measure.measurable_bind' hout).comp hcollect.1
  · intro current
    unfold figureOneUniformRatioEstimate
    exact (hcollect.2 current).bind (fun total => by trivial) hout

/-- The concrete primitive package used by the base-run proof. -/
noncomputable def figureOnePrimitives : VolumeCoolingPrimitives where
  initialSample := figureOneInitialSample
  ratioEstimate := figureOneRatioEstimate
  uniformRatioEstimate := figureOneUniformRatioEstimate

/-- The complete Figure-1 computation after an initial point has been chosen.
Naming this continuation exposes the kernel needed to couple the executable
fallback start to the ideal restricted-Gaussian start. -/
noncomputable def figureOnePointContinuation
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (point : AmbientSpace q.n) :
    MembershipOracleProgram q.n ℝ :=
  (coolingProduct figureOnePrimitives q (S q).variances point).bind fun product =>
    match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (figureOneUniformRatioEstimate q (terminalVariance q) lastPoint).bind
          fun finalRatio => .pure <| match finalRatio with
            | some uniformRatio =>
                initialGaussianIntegral q * gaussianProduct * uniformRatio
            | none => 0

theorem figureOneCoolingProduct_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances,
      Measurable (fun point =>
        (coolingProduct figureOnePrimitives q variances point).runEstimate
          oracle.query) ∧
      ∀ point,
        (coolingProduct figureOnePrimitives q variances point).StronglyMeasurable
          oracle.query := by
  intro variances
  induction variances with
  | nil =>
      constructor
      · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp <| measurable_some.comp <|
          measurable_const.prodMk measurable_id
      · intro point
        simpa [coolingProduct] using
          (show (MembershipOracleProgram.pure (some (1, point)) :
            MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
              oracle.query from trivial)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          constructor
          · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_const.prodMk measurable_id
          · intro point
            simpa [coolingProduct] using
              (show (MembershipOracleProgram.pure (some (1, point)) :
                MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
                  oracle.query from trivial)
      | cons tau2 rest =>
          have hratio := figureOneRatioEstimate_measurable_and_strong
            q I oracle sigma2 tau2
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
            fun phase => match phase with
              | none => .pure none
              | some (ratio, nextPoint) =>
                  (coolingProduct figureOnePrimitives q (tau2 :: rest) nextPoint).bind
                    fun result => .pure <| match result with
                      | none => none
                      | some (product, lastPoint) =>
                          some (ratio * product, lastPoint)
          have htailOutput : ∀ ratio, Measurable fun result :
              Option (ℝ × AmbientSpace q.n) =>
              (.pure (match result with
                | none => none
                | some (product, lastPoint) => some (ratio * product, lastPoint)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
            intro ratio
            simp only [MembershipOracleProgram.runEstimate]
            apply Measure.measurable_dirac.comp
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                some (ratio * value.1, value.2) :=
              measurable_some.comp <|
                (measurable_const.mul measurable_fst).prodMk measurable_snd
            convert Measurable.optionElim
              (none : Option (ℝ × AmbientSpace q.n)) hsome using 1
            funext result
            cases result with
            | none => rfl
            | some value => cases value; rfl
          have hphaseStrong : ∀ phase,
              (phaseProgram phase).StronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value =>
                exact (ih.2 value.2).bind (fun result => by trivial)
                  (htailOutput value.1)
          have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
              (phaseProgram (some value)).runEstimate oracle.query := by
            have hsource : Measurable fun value : ℝ × AmbientSpace q.n =>
                (coolingProduct figureOnePrimitives q (tau2 :: rest) value.2).runEstimate
                  oracle.query := ih.1.comp measurable_snd
            have hprob : ∀ value : ℝ × AmbientSpace q.n, IsProbabilityMeasure
                ((coolingProduct figureOnePrimitives q (tau2 :: rest) value.2).runEstimate
                  oracle.query) := fun value =>
              MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
                (ih.2 value.2).estimateMeasurable
            have htransform : Measurable fun p :
                (ℝ × AmbientSpace q.n) × Option (ℝ × AmbientSpace q.n) =>
                match p.2 with
                | none => none
                | some (product, lastPoint) =>
                    some (p.1.1 * product, lastPoint) := by
              have hnone : Measurable fun _ : ℝ × AmbientSpace q.n =>
                  (none : Option (ℝ × AmbientSpace q.n)) := measurable_const
              have hsome : Measurable fun p :
                  (ℝ × AmbientSpace q.n) × (ℝ × AmbientSpace q.n) =>
                    some (p.1.1 * p.2.1, p.2.2) :=
                measurable_some.comp <|
                  ((measurable_fst.comp measurable_fst).mul
                    (measurable_fst.comp measurable_snd)).prodMk
                      (measurable_snd.comp measurable_snd)
              convert Measurable.optionCases
                ((0 : ℝ), (0 : AmbientSpace q.n)) hnone hsome using 1
              funext p
              cases p.2 with
              | none => rfl
              | some value => cases value; rfl
            have hbind : Measurable fun value : ℝ × AmbientSpace q.n =>
                ((coolingProduct figureOnePrimitives q (tau2 :: rest)
                  value.2).runEstimate oracle.query).bind fun result =>
                    Measure.dirac <| match result with
                      | none => none
                      | some (product, lastPoint) =>
                          some (value.1 * product, lastPoint) :=
              measurable_measure_bind_param_variable hsource hprob
                (Measure.measurable_dirac.comp htransform)
            rw [show (fun value : ℝ × AmbientSpace q.n =>
                (phaseProgram (some value)).runEstimate oracle.query) =
              (fun value =>
                ((coolingProduct figureOnePrimitives q (tau2 :: rest)
                  value.2).runEstimate oracle.query).bind fun result =>
                    Measure.dirac <| match result with
                      | none => none
                      | some (product, lastPoint) =>
                          some (value.1 * product, lastPoint)) by
              funext value
              unfold phaseProgram
              exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
                (ih.2 value.2) (fun result => by trivial)
                  (htailOutput value.1)]
            exact hbind
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).runEstimate oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsomeRun using 1
            funext phase
            cases phase <;> rfl
          have hcooling : ∀ point,
              coolingProduct figureOnePrimitives q (sigma2 :: tau2 :: rest) point =
                (figureOneRatioEstimate q sigma2 tau2 point).bind phaseProgram := by
            intro point
            rw [coolingProduct]
            change (figureOneRatioEstimate q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                cases value with
                | mk ratio nextPoint =>
                    unfold phaseProgram
                    simp only
                    congr 1
                    funext result
                    cases result with
                    | none => rfl
                    | some value => cases value; rfl
          have hrun : (fun point =>
              (coolingProduct figureOnePrimitives q (sigma2 :: tau2 :: rest)
                point).runEstimate oracle.query) =
              (fun point =>
                ((figureOneRatioEstimate q sigma2 tau2 point).runEstimate
                  oracle.query).bind fun phase =>
                    (phaseProgram phase).runEstimate oracle.query) := by
            funext point
            rw [hcooling point]
            exact MembershipOracleProgram.runEstimate_bind oracle.query _ phaseProgram
              (hratio.2 point) hphaseStrong hphaseRun
          constructor
          · rw [hrun]
            exact (Measure.measurable_bind' hphaseRun).comp hratio.1
          · intro point
            rw [hcooling point]
            exact (hratio.2 point).bind hphaseStrong hphaseRun

/-- The post-initialization Figure-1 law is a measurable probability kernel
of its starting point, and every continuation is strongly measurable. -/
theorem figureOnePointContinuation_measurable_and_strong
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    Measurable (fun point =>
      (figureOnePointContinuation S q point).runEstimate oracle.query) ∧
    ∀ point, (figureOnePointContinuation S q point).StronglyMeasurable
      oracle.query := by
  have hcooling := figureOneCoolingProduct_measurable_and_strong
    q I oracle (S q).variances
  have huniform := figureOneUniformRatioEstimate_measurable_and_strong
    q I oracle (terminalVariance q)
  let finalProgram : ℝ → Option ℝ → MembershipOracleProgram q.n ℝ :=
    fun gaussianProduct finalRatio => .pure <| match finalRatio with
      | none => 0
      | some uniformRatio =>
          initialGaussianIntegral q * gaussianProduct * uniformRatio
  have hfinalStrong : ∀ gaussianProduct finalRatio,
      (finalProgram gaussianProduct finalRatio).StronglyMeasurable oracle.query := by
    intro gaussianProduct finalRatio
    trivial
  have hfinalRun : ∀ gaussianProduct, Measurable fun finalRatio =>
      (finalProgram gaussianProduct finalRatio).runEstimate oracle.query := by
    intro gaussianProduct
    simp only [finalProgram, MembershipOracleProgram.runEstimate]
    apply Measure.measurable_dirac.comp
    have hsome : Measurable fun uniformRatio : ℝ =>
        initialGaussianIntegral q * gaussianProduct * uniformRatio :=
      measurable_const.mul measurable_id
    convert Measurable.optionElim 0 hsome using 1
    funext finalRatio
    cases finalRatio <;> rfl
  let productProgram : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ := fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (figureOneUniformRatioEstimate q (terminalVariance q) lastPoint).bind
          (finalProgram gaussianProduct)
  have hproductStrong : ∀ product,
      (productProgram product).StronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value =>
        exact (huniform.2 value.2).bind (hfinalStrong value.1)
          (hfinalRun value.1)
  have hsomeProductRun : Measurable fun value : ℝ × AmbientSpace q.n =>
      (productProgram (some value)).runEstimate oracle.query := by
    have hsource : Measurable fun value : ℝ × AmbientSpace q.n =>
        (figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query := huniform.1.comp measurable_snd
    have hprob : ∀ value : ℝ × AmbientSpace q.n, IsProbabilityMeasure
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query) := fun value =>
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        (huniform.2 value.2).estimateMeasurable
    have htransform : Measurable fun p :
        (ℝ × AmbientSpace q.n) × Option ℝ =>
          match p.2 with
          | none => 0
          | some uniformRatio =>
              initialGaussianIntegral q * p.1.1 * uniformRatio := by
      have hnone : Measurable fun _ : ℝ × AmbientSpace q.n => (0 : ℝ) :=
        measurable_const
      have hsome : Measurable fun p : (ℝ × AmbientSpace q.n) × ℝ =>
          initialGaussianIntegral q * p.1.1 * p.2 :=
        (measurable_const.mul (measurable_fst.comp measurable_fst)).mul
          measurable_snd
      convert Measurable.optionCases (0 : ℝ) hnone hsome using 1
      funext p
      cases p.2 <;> rfl
    have hbind : Measurable fun value : ℝ × AmbientSpace q.n =>
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query).bind fun finalRatio => Measure.dirac <| match finalRatio with
            | none => 0
            | some uniformRatio =>
                initialGaussianIntegral q * value.1 * uniformRatio :=
      measurable_measure_bind_param_variable hsource hprob
        (Measure.measurable_dirac.comp htransform)
    rw [show (fun value : ℝ × AmbientSpace q.n =>
        (productProgram (some value)).runEstimate oracle.query) =
      (fun value =>
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query).bind fun finalRatio => Measure.dirac <| match finalRatio with
            | none => 0
            | some uniformRatio =>
                initialGaussianIntegral q * value.1 * uniformRatio) by
      funext value
      unfold productProgram
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (huniform.2 value.2) (hfinalStrong value.1) (hfinalRun value.1)]
    exact hbind
  have hproductRun : Measurable fun product =>
      (productProgram product).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsomeProductRun using 1
    funext product
    cases product <;> rfl
  have hcontinuation : ∀ point,
      figureOnePointContinuation S q point =
        (coolingProduct figureOnePrimitives q (S q).variances point).bind
          productProgram := by
    intro point
    unfold figureOnePointContinuation productProgram finalProgram
    congr 1
    funext product
    cases product with
    | none => rfl
    | some value =>
        cases value with
        | mk gaussianProduct lastPoint =>
            simp only
            congr 1
            funext finalRatio
            cases finalRatio <;> rfl
  have hstrong : ∀ point,
      (figureOnePointContinuation S q point).StronglyMeasurable oracle.query :=
    fun point => by
      rw [hcontinuation point]
      exact (hcooling.2 point).bind hproductStrong hproductRun
  have hrun : Measurable fun point =>
      (figureOnePointContinuation S q point).runEstimate oracle.query := by
    rw [show (fun point =>
        (figureOnePointContinuation S q point).runEstimate oracle.query) =
      (fun point =>
        ((coolingProduct figureOnePrimitives q (S q).variances point).runEstimate
          oracle.query).bind fun product =>
            (productProgram product).runEstimate oracle.query) by
      funext point
      rw [hcontinuation point]
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ productProgram
        (hcooling.2 point) hproductStrong hproductRun]
    exact (Measure.measurable_bind' hproductRun).comp hcooling.1
  exact ⟨hrun, hstrong⟩

theorem figureOneBaseVolumeCooling_stronglyMeasurable
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (baseVolumeCooling figureOnePrimitives S q).StronglyMeasurable oracle.query := by
  have hcooling := figureOneCoolingProduct_measurable_and_strong
    q I oracle (S q).variances
  have huniform := figureOneUniformRatioEstimate_measurable_and_strong
    q I oracle (terminalVariance q)
  let finalProgram : ℝ → Option ℝ → MembershipOracleProgram q.n ℝ :=
    fun gaussianProduct finalRatio => .pure <| match finalRatio with
      | none => 0
      | some uniformRatio =>
          initialGaussianIntegral q * gaussianProduct * uniformRatio
  have hfinalStrong : ∀ gaussianProduct finalRatio,
      (finalProgram gaussianProduct finalRatio).StronglyMeasurable oracle.query := by
    intro gaussianProduct finalRatio
    trivial
  have hfinalRun : ∀ gaussianProduct, Measurable fun finalRatio =>
      (finalProgram gaussianProduct finalRatio).runEstimate oracle.query := by
    intro gaussianProduct
    simp only [finalProgram, MembershipOracleProgram.runEstimate]
    apply Measure.measurable_dirac.comp
    have hsome : Measurable fun uniformRatio : ℝ =>
        initialGaussianIntegral q * gaussianProduct * uniformRatio :=
      measurable_const.mul measurable_id
    convert Measurable.optionElim 0 hsome using 1
    funext finalRatio
    cases finalRatio <;> rfl
  let productProgram : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ := fun product => match product with
    | none => .pure 0
    | some (gaussianProduct, lastPoint) =>
        (figureOneUniformRatioEstimate q (terminalVariance q) lastPoint).bind
          (finalProgram gaussianProduct)
  have hproductStrong : ∀ product,
      (productProgram product).StronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value =>
        exact (huniform.2 value.2).bind (hfinalStrong value.1)
          (hfinalRun value.1)
  have hsomeProductRun : Measurable fun value : ℝ × AmbientSpace q.n =>
      (productProgram (some value)).runEstimate oracle.query := by
    have hsource : Measurable fun value : ℝ × AmbientSpace q.n =>
        (figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query := huniform.1.comp measurable_snd
    have hprob : ∀ value : ℝ × AmbientSpace q.n, IsProbabilityMeasure
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query) := fun value =>
      MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
        (huniform.2 value.2).estimateMeasurable
    have htransform : Measurable fun p :
        (ℝ × AmbientSpace q.n) × Option ℝ =>
          match p.2 with
          | none => 0
          | some uniformRatio =>
              initialGaussianIntegral q * p.1.1 * uniformRatio := by
      have hnone : Measurable fun _ : ℝ × AmbientSpace q.n => (0 : ℝ) :=
        measurable_const
      have hsome : Measurable fun p : (ℝ × AmbientSpace q.n) × ℝ =>
          initialGaussianIntegral q * p.1.1 * p.2 :=
        (measurable_const.mul (measurable_fst.comp measurable_fst)).mul
          measurable_snd
      convert Measurable.optionCases (0 : ℝ) hnone hsome using 1
      funext p
      cases p.2 <;> rfl
    have hbind : Measurable fun value : ℝ × AmbientSpace q.n =>
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query).bind fun finalRatio => Measure.dirac <| match finalRatio with
            | none => 0
            | some uniformRatio =>
                initialGaussianIntegral q * value.1 * uniformRatio :=
      measurable_measure_bind_param_variable hsource hprob
        (Measure.measurable_dirac.comp htransform)
    rw [show (fun value : ℝ × AmbientSpace q.n =>
        (productProgram (some value)).runEstimate oracle.query) =
      (fun value =>
        ((figureOneUniformRatioEstimate q (terminalVariance q) value.2).runEstimate
          oracle.query).bind fun finalRatio => Measure.dirac <| match finalRatio with
            | none => 0
            | some uniformRatio =>
                initialGaussianIntegral q * value.1 * uniformRatio) by
      funext value
      unfold productProgram
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (huniform.2 value.2) (hfinalStrong value.1) (hfinalRun value.1)]
    exact hbind
  have hproductRun : Measurable fun product =>
      (productProgram product).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsomeProductRun using 1
    funext product
    cases product <;> rfl
  let pointProgram : AmbientSpace q.n → MembershipOracleProgram q.n ℝ :=
    fun point =>
      (coolingProduct figureOnePrimitives q (S q).variances point).bind
        productProgram
  have hpointStrong : ∀ point,
      (pointProgram point).StronglyMeasurable oracle.query := fun point =>
    (hcooling.2 point).bind hproductStrong hproductRun
  have hpointRun : Measurable fun point =>
      (pointProgram point).runEstimate oracle.query := by
    rw [show (fun point => (pointProgram point).runEstimate oracle.query) =
        (fun point =>
          ((coolingProduct figureOnePrimitives q (S q).variances point).runEstimate
            oracle.query).bind fun product =>
              (productProgram product).runEstimate oracle.query) by
      funext point
      unfold pointProgram
      exact MembershipOracleProgram.runEstimate_bind oracle.query _ productProgram
        (hcooling.2 point) hproductStrong hproductRun]
    exact (Measure.measurable_bind' hproductRun).comp hcooling.1
  let initialProgram : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
      | none => .pure 0
      | some point => pointProgram point
  have hinitialStrong : ∀ initialPoint,
      (initialProgram initialPoint).StronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hpointStrong point
  have hinitialRun : Measurable fun initialPoint =>
      (initialProgram initialPoint).runEstimate oracle.query := by
    convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hpointRun using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have hbase : baseVolumeCooling figureOnePrimitives S q =
      (figureOneInitialSample q).bind initialProgram := by
    unfold baseVolumeCooling
    change (figureOneInitialSample q).bind _ = _
    congr 1
    funext initialPoint
    cases initialPoint with
    | none => rfl
    | some point =>
        unfold initialProgram pointProgram productProgram finalProgram
        simp only
        congr 1
        funext product
        cases product with
        | none => rfl
        | some value =>
            cases value with
            | mk gaussianProduct lastPoint =>
                simp only [figureOnePrimitives]
                congr 1
                funext finalRatio
                cases finalRatio <;> rfl
  rw [hbase]
  exact (figureOneInitialSample_stronglyMeasurable q I oracle).bind
    hinitialStrong hinitialRun

/-- The exact structural budget obtained by summing the fixed cap at every
adjacent Gaussian phase. -/
noncomputable def figureOneCoolingQueryBudget (q : VolumeParams) : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | sigma2 :: tau2 :: rest =>
      figureOnePhaseSampleCount q sigma2 * figureOneWalkSteps q sigma2 +
        figureOneCoolingQueryBudget q (tau2 :: rest)
termination_by variances => variances.length

theorem figureOneCoolingProduct_queryBound (q : VolumeParams) :
    ∀ variances point,
    (coolingProduct figureOnePrimitives q variances point).QueryBound
      (figureOneCoolingQueryBudget q variances) := by
  intro variances
  induction variances with
  | nil =>
      intro point
      simpa [coolingProduct, figureOneCoolingQueryBudget] using
        (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro point
          simpa [coolingProduct, figureOneCoolingQueryBudget] using
            (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
      | cons tau2 rest =>
          intro point
          simp only [coolingProduct, figureOnePrimitives]
          have htail : ∀ phase,
              ((match phase with
                | none => .pure none
                | some (ratio, nextPoint) =>
                    (coolingProduct figureOnePrimitives q (tau2 :: rest) nextPoint).bind
                      fun tail => .pure <| match tail with
                        | some (product, lastPoint) =>
                            some (ratio * product, lastPoint)
                        | none => none) :
                MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))).QueryBound
                  (figureOneCoolingQueryBudget q (tau2 :: rest)) := by
            intro phase
            cases phase with
            | none => exact .pure _ _
            | some value =>
                exact (ih value.2).bind fun tail => .pure _ 0
          have h := (figureOneRatioEstimate_queryBound q sigma2 tau2 point).bind htail
          convert h using 1
          · rfl
          · rw [figureOneCoolingQueryBudget]

/-- Complete worst-case query accounting for one concrete base run. -/
theorem figureOneBaseVolumeCooling_queryBound
    (S : (q : VolumeParams) → VolumeCoolingSchedule q) (q : VolumeParams) :
    (baseVolumeCooling figureOnePrimitives S q).QueryBound
      (1 + (figureOneCoolingQueryBudget q (S q).variances +
        figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q))) := by
  let finalBudget :=
    figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q)
  have hproduct : ∀ initialPoint,
      ((match initialPoint with
        | none => .pure 0
        | some point =>
            (coolingProduct figureOnePrimitives q (S q).variances point).bind
              fun product => match product with
                | none => .pure 0
                | some (gaussianProduct, lastPoint) =>
                    (figureOnePrimitives.uniformRatioEstimate q
                      (terminalVariance q) lastPoint).bind fun finalRatio =>
                        .pure <| match finalRatio with
                          | some uniformRatio =>
                              initialGaussianIntegral q * gaussianProduct * uniformRatio
                          | none => 0) : MembershipOracleProgram q.n ℝ).QueryBound
        (figureOneCoolingQueryBudget q (S q).variances + finalBudget) := by
    intro initialPoint
    cases initialPoint with
    | none => exact .pure _ _
    | some point =>
        apply (figureOneCoolingProduct_queryBound q (S q).variances point).bind
        intro product
        cases product with
        | none => exact .pure _ _
        | some value =>
            exact (figureOneUniformRatioEstimate_queryBound q
              (terminalVariance q) value.2).bind fun finalRatio => .pure _ 0
  unfold baseVolumeCooling
  have h := (figureOneInitialSample_queryBound q).bind hproduct
  convert h using 1
  congr 1

end ArlibCommunity.Algorithms.CV18
