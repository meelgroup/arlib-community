/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryKernel

/-! # Exact executable semantics of the scheduled proper step -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open Arlib.MarkovChains

theorem scheduledAccuracyMetropolisMarkedProposalProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).StronglyMeasurable
      oracle.query := by
  simp only [scheduledAccuracyMetropolisMarkedProposalProgram,
    MembershipOracleProgram.StronglyMeasurable]
  by_cases hproper : oracle.query proposal = true ∧
      ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2
  · simp only [if_pos hproper, MembershipOracleProgram.runEstimate,
      MembershipOracleProgram.StronglyMeasurable]
    constructor
    · apply Measure.measurable_dirac.comp
      exact measurable_const.prodMk <|
        Measurable.ite measurableSet_Iic measurable_const measurable_const
    · exact fun _ => trivial
  · simp only [if_neg hproper, MembershipOracleProgram.runEstimate,
      MembershipOracleProgram.StronglyMeasurable]
    exact ⟨Measure.measurable_dirac.comp measurable_const, fun _ => trivial⟩

theorem scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [scheduledAccuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.StronglyMeasurable]
  let output : AmbientSpace q.n → ℝ → Bool × AmbientSpace q.n :=
    fun point coin =>
      if oracle.query point = true ∧
          ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖point‖ ≤ figureOneScheduledPhaseRadius q sigma2 then
        (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current point
          then point else current)
      else (false, current)
  have horacle : Measurable fun p : AmbientSpace q.n × ℝ =>
      oracle.query p.1 := oracle.measurable_query.comp measurable_fst
  have hnorm : Measurable fun p : AmbientSpace q.n × ℝ => ‖p.1‖ := by fun_prop
  have haccept : Measurable fun p : AmbientSpace q.n × ℝ =>
      lazyGaussianMetropolisAcceptance sigma2 current p.1 := by
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  have hterminal : MeasurableSet {p : AmbientSpace q.n × ℝ |
      ‖p.1‖ ≤ Real.sqrt (terminalVariance q)} :=
    measurableSet_le hnorm measurable_const
  have hphase : MeasurableSet {p : AmbientSpace q.n × ℝ |
      ‖p.1‖ ≤ figureOneScheduledPhaseRadius q sigma2} :=
    measurableSet_le hnorm measurable_const
  have hout : Measurable fun p : AmbientSpace q.n × ℝ => output p.1 p.2 := by
    apply Measurable.ite
    · convert ((horacle (measurableSet_singleton true)).inter hterminal).inter
          hphase using 1
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_setOf_eq]
      tauto
    · apply measurable_const.prodMk
      exact Measurable.ite (measurableSet_le measurable_snd haccept)
        measurable_fst measurable_const
    · exact measurable_const
  constructor
  · rw [show (fun point =>
        (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current point).runEstimate
          oracle.query) =
        fun point => uniformUnitIntervalMeasure.map (output point) by
      funext point
      simp only [scheduledAccuracyMetropolisMarkedProposalProgram,
        MembershipOracleProgram.runEstimate]
      have hinner : (fun coin =>
          MembershipOracleProgram.runEstimate oracle.query
            (if oracle.query point = true ∧
                ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
                ‖point‖ ≤ figureOneScheduledPhaseRadius q sigma2 then
              .pure (true, if coin ≤
                lazyGaussianMetropolisAcceptance sigma2 current point
                then point else current)
            else .pure (false, current))) =
          fun coin => Measure.dirac (output point coin) := by
        funext coin
        by_cases hproper : oracle.query point = true ∧
            ‖point‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖point‖ ≤ figureOneScheduledPhaseRadius q sigma2
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
      rw [hinner]
      exact Measure.bind_dirac_eq_map uniformUnitIntervalMeasure
        (hout.comp (measurable_const.prodMk measurable_id))]
    exact measurable_measure_map_param uniformUnitIntervalMeasure hout
  · intro proposal
    exact scheduledAccuracyMetropolisMarkedProposalProgram_stronglyMeasurable
      q I oracle sigma2 current proposal

theorem map_snd_runEstimate_scheduledAccuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    ((scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
      oracle.query).map Prod.snd =
      ENNReal.ofReal (radialLazyMetropolisAcceptance
          (figureOneScheduledPhaseBody q I sigma2) sigma2 current proposal) •
        Measure.dirac proposal +
      ENNReal.ofReal (1 - radialLazyMetropolisAcceptance
          (figureOneScheduledPhaseBody q I sigma2) sigma2 current proposal) •
        Measure.dirac current := by
  by_cases hp : proposal ∈ figureOneScheduledPhaseBody q I sigma2
  · have heligible := (oracle_and_radii_iff_mem_scheduledPhaseBody
      q I oracle sigma2 proposal).mpr hp
    simp only [scheduledAccuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate, heligible, true_and, if_true]
    have hpair : Measurable fun coin : ℝ =>
        (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current) :=
      measurable_const.prodMk <|
        Measurable.ite measurableSet_Iic measurable_const measurable_const
    rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hpair,
      Measure.map_map measurable_snd hpair]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_mem hp]
    exact uniformUnitInterval_map_threshold
      (lazyGaussianMetropolisAcceptance_nonneg sigma2 current proposal)
      (lazyGaussianMetropolisAcceptance_le_one sigma2 current proposal)
      proposal current
  · have hineligible : ¬ (oracle.query proposal = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2) := by
      rwa [oracle_and_radii_iff_mem_scheduledPhaseBody]
    simp only [scheduledAccuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate, hineligible, if_false,
      Measure.map_dirac]
    unfold radialLazyMetropolisAcceptance
    rw [Set.indicator_of_notMem hp]
    simp

theorem map_snd_runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_radialLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    ((scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query).map Prod.snd =
      radialLazyMetropolisLaw (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 current := by
  let U := uniformClosedBallMeasure q.n current
    (figureOneScheduledProposalRadius q sigma2)
  have hproposal : AEMeasurable (fun proposal =>
      (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) U :=
    (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable.1
  have hradial := measurable_radialLazyMetropolisProposalLaw
    (figureOneScheduledPhaseBody_measurable q I sigma2) sigma2 current
  ext B hB
  simp only [scheduledAccuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.runEstimate]
  rw [Measure.map_apply measurable_snd hB,
    Measure.bind_apply (hB.preimage measurable_snd) hproposal]
  unfold radialLazyMetropolisLaw
  rw [Measure.bind_apply hB hradial.aemeasurable]
  apply lintegral_congr
  intro proposal
  have h := congrArg (fun mu : Measure (AmbientSpace q.n) => mu B)
    (map_snd_runEstimate_scheduledAccuracyMetropolisMarkedProposalProgram
      q I oracle sigma2 current proposal)
  rw [Measure.map_apply measurable_snd hB] at h
  exact h

theorem map_snd_runEstimate_scheduledAccuracyMetropolisMarkedBallStep
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    ((scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query).map Prod.snd =
      lazy (metropolisGaussian (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2) current := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  rw [map_snd_runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_radialLaw]
  exact radialLazyMetropolisLaw_eq_lazy_metropolisGaussian
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledProposalRadius_pos q hsigma2) sigma2 current

theorem uniformClosedBallMeasure_scheduledPhaseBody
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius
        (figureOneScheduledPhaseBody q I sigma2) =
      ell (figureOneScheduledPhaseBody q I sigma2) radius current := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  rw [uniformClosedBallMeasure_eq_openBall current hradius,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply
      (figureOneScheduledPhaseBody_measurable q I sigma2),
    ell_apply, ENNReal.div_eq_inv_mul]
  congr 1
  rw [Set.inter_comm]

theorem uniformClosedBallMeasure_scheduledPhaseBody_compl
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius
        (figureOneScheduledPhaseBody q I sigma2)ᶜ =
      1 - ell (figureOneScheduledPhaseBody q I sigma2) radius current := by
  rw [measure_compl (figureOneScheduledPhaseBody_measurable q I sigma2)
      (measure_ne_top _ _), measure_univ,
    uniformClosedBallMeasure_scheduledPhaseBody
      q I sigma2 current hradius]

theorem runEstimate_scheduledAccuracyMetropolisMarkedBallStep_apply_false_prod
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n)
    {t : Set (AmbientSpace q.n)} (ht : MeasurableSet t) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
        oracle.query ({false} ×ˢ t) =
      (1 - ell (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) current) *
          t.indicator 1 current := by
  let U := uniformClosedBallMeasure q.n current
    (figureOneScheduledProposalRadius q sigma2)
  have hset : MeasurableSet ({false} ×ˢ t) :=
    (measurableSet_singleton false).prod ht
  have hmeas : AEMeasurable (fun proposal =>
      (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) U :=
    (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable.1
  simp only [scheduledAccuracyMetropolisMarkedBallStep,
    MembershipOracleProgram.runEstimate]
  rw [Measure.bind_apply hset hmeas]
  have hinner : ∀ proposal : AmbientSpace q.n,
      (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
          oracle.query ({false} ×ˢ t) =
        (figureOneScheduledPhaseBody q I sigma2)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal := by
    intro proposal
    simp only [scheduledAccuracyMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate]
    by_cases hp : proposal ∈ figureOneScheduledPhaseBody q I sigma2
    · simp only [(oracle_and_radii_iff_mem_scheduledPhaseBody
          q I oracle sigma2 proposal).mpr hp]
      rw [Measure.bind_apply hset]
      · rw [Set.indicator_of_notMem (by simpa using hp)]
        change (∫⁻ coin, Measure.dirac
            (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
              then proposal else current) ({false} ×ˢ t)
          ∂uniformUnitIntervalMeasure) = 0
        simp [Measure.dirac_apply' _ hset]
      · exact (Measure.measurable_dirac.comp <|
          measurable_const.prodMk <|
            Measurable.ite measurableSet_Iic measurable_const
              measurable_const).aemeasurable
    · have hnot : ¬ (oracle.query proposal = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2) := by
        rwa [oracle_and_radii_iff_mem_scheduledPhaseBody]
      simp only [hnot, if_false, MembershipOracleProgram.runEstimate]
      rw [Measure.bind_const, measure_univ, one_smul]
      change Measure.dirac (false, current) ({false} ×ˢ t) =
        (figureOneScheduledPhaseBody q I sigma2)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal
      rw [Measure.dirac_apply' _ hset]
      by_cases hc : current ∈ t <;> simp [hp, hc]
  simp_rw [hinner]
  rw [lintegral_indicator
    (figureOneScheduledPhaseBody_measurable q I sigma2).compl]
  rw [setLIntegral_const]
  rw [uniformClosedBallMeasure_scheduledPhaseBody_compl
    q I sigma2 current (figureOneScheduledProposalRadius_pos q hsigma2)]
  ring

/-- Exact marked-kernel semantics of the executable scheduled proposal. -/
theorem runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
        oracle.query =
      lazyProperProposalGaussianAux
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 current := by
  let mu : Measure (Bool × AmbientSpace q.n) :=
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query
  let nu : Measure (Bool × AmbientSpace q.n) :=
    lazyProperProposalGaussianAux
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 current
  let _ : IsProbabilityMeasure mu :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current).estimateMeasurable
  let _ : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have hstate : mu.map Prod.snd = nu.map Prod.snd := by
    calc
      mu.map Prod.snd = lazy
          (metropolisGaussian (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2) current :=
        map_snd_runEstimate_scheduledAccuracyMetropolisMarkedBallStep
          q I oracle hsigma2 current
      _ = nu.map Prod.snd :=
        (map_snd_lazyProperProposalGaussianAux_apply
          (figureOneScheduledPhaseBody_measurable q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2 current).symm
  have hfalse : ∀ (t : Set (AmbientSpace q.n)), MeasurableSet t →
      mu ({false} ×ˢ t) = nu ({false} ×ˢ t) := by
    intro t ht
    rw [runEstimate_scheduledAccuracyMetropolisMarkedBallStep_apply_false_prod
      q I oracle hsigma2 current ht]
    dsimp [nu]
    rw [lazyProperProposalGaussianAux_apply_set
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 current
      ((measurableSet_singleton false).prod ht)]
    by_cases hc : current ∈ t <;> simp [hc]
  apply measure_bool_prod_ext
  intro b t ht
  cases b with
  | false => exact hfalse t ht
  | true =>
      have hpre : Prod.snd ⁻¹' t =
          ({false} ×ˢ t) ∪ ({true} ×ˢ t) := by
        ext p
        rcases p with ⟨b, x⟩
        cases b <;> simp
      have hdisj : Disjoint ({false} ×ˢ t) ({true} ×ˢ t) := by
        apply Set.disjoint_left.2
        rintro ⟨b, x⟩ hf ht'
        cases b <;> simp at hf ht'
      have hsumMu : mu ({false} ×ˢ t) + mu ({true} ×ˢ t) =
          mu.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hsumNu : nu ({false} ×ˢ t) + nu ({true} ×ˢ t) =
          nu.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hadd : mu ({false} ×ˢ t) + mu ({true} ×ˢ t) =
          nu ({false} ×ˢ t) + nu ({true} ×ˢ t) := by
        rw [hsumMu, hsumNu, hstate]
      rw [hfalse t ht] at hadd
      exact WithTop.add_left_cancel (measure_ne_top nu ({false} ×ˢ t)) hadd

theorem scheduledAccuracyZeroObservation_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).StronglyMeasurable
      oracle.query := by
  unfold scheduledAccuracyZeroObservation
  simp only [MembershipOracleProgram.StronglyMeasurable,
    MembershipOracleProgram.runEstimate]

theorem runEstimate_scheduledAccuracyZeroObservation
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).runEstimate oracle.query =
      Measure.dirac 0 := by
  simp [scheduledAccuracyZeroObservation, MembershipOracleProgram.runEstimate]

/-- A scheduled block with one query reserved for its endpoint observation
denotes the generic killed proper-step law with the advertised proposal cap. -/
theorem cappedScheduledAccuracyProperBlockAux_add_one_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (properStride : ℕ) :
    ∀ proposalCap remainingProper,
      (∀ current,
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          (proposalCap + 1) remainingProper current).StronglyMeasurable
            oracle.query) ∧
      ∀ current,
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          (proposalCap + 1) remainingProper current).runEstimate oracle.query =
        cappedProperCollectLawAux
          (lazyProperProposalGaussianAux
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledPhaseBody_measurable q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2)
          (fun _ => 0) properStride proposalCap remainingProper 1 0 current := by
  intro proposalCap
  induction proposalCap with
  | zero =>
      intro remainingProper
      cases remainingProper with
      | zero =>
          constructor
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            exact (scheduledAccuracyZeroObservation_stronglyMeasurable
              q I oracle sigma2 current).bind (fun _ => by trivial) <| by
                simp only [MembershipOracleProgram.runEstimate]
                exact Measure.measurable_dirac.comp <|
                  measurable_some.comp (measurable_id.prodMk measurable_const)
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux,
              cappedProperCollectLawAux]
            rw [MembershipOracleProgram.runEstimate_bind oracle.query]
            · rw [runEstimate_scheduledAccuracyZeroObservation]
              have hm : Measurable fun observed : ℝ =>
                  Measure.dirac (some (observed, current)) :=
                Measure.measurable_dirac.comp <|
                  measurable_some.comp (measurable_id.prodMk measurable_const)
              simp only [MembershipOracleProgram.runEstimate]
              rw [Measure.dirac_bind hm]
              norm_num
            · exact scheduledAccuracyZeroObservation_stronglyMeasurable
                q I oracle sigma2 current
            · intro observed; trivial
            · simp only [MembershipOracleProgram.runEstimate]
              exact Measure.measurable_dirac.comp <|
                measurable_some.comp (measurable_id.prodMk measurable_const)
      | succ remainingProper =>
          constructor
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            apply (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
              q I oracle sigma2 current).bind
            · intro result
              rcases result with ⟨mark, state⟩
              cases mark <;> cases remainingProper <;> trivial
            · cases remainingProper <;>
                simp [MembershipOracleProgram.runEstimate]
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux,
              cappedProperCollectLawAux]
            rw [MembershipOracleProgram.runEstimate_bind oracle.query]
            · rw [runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
                q I oracle hsigma2 current]
              cases remainingProper <;>
                simp [MembershipOracleProgram.runEstimate]
            · exact scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current
            · intro result
              rcases result with ⟨mark, state⟩
              cases mark <;> cases remainingProper <;> trivial
            · cases remainingProper <;>
                simp [MembershipOracleProgram.runEstimate]
  | succ proposalCap ih =>
      intro remainingProper
      cases remainingProper with
      | zero =>
          constructor
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            exact (scheduledAccuracyZeroObservation_stronglyMeasurable
              q I oracle sigma2 current).bind (fun _ => by trivial) <| by
                simp only [MembershipOracleProgram.runEstimate]
                exact Measure.measurable_dirac.comp <|
                  measurable_some.comp (measurable_id.prodMk measurable_const)
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux,
              cappedProperCollectLawAux]
            rw [MembershipOracleProgram.runEstimate_bind oracle.query]
            · rw [runEstimate_scheduledAccuracyZeroObservation]
              have hm : Measurable fun observed : ℝ =>
                  Measure.dirac (some (observed, current)) :=
                Measure.measurable_dirac.comp <|
                  measurable_some.comp (measurable_id.prodMk measurable_const)
              simp only [MembershipOracleProgram.runEstimate]
              rw [Measure.dirac_bind hm]
              norm_num
            · exact scheduledAccuracyZeroObservation_stronglyMeasurable
                q I oracle sigma2 current
            · intro observed; trivial
            · simp only [MembershipOracleProgram.runEstimate]
              exact Measure.measurable_dirac.comp <|
                measurable_some.comp (measurable_id.prodMk measurable_const)
      | succ remainingProper =>
          let next : Bool × AmbientSpace q.n →
              MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
            fun result =>
              if result.1 then
                match remainingProper with
                | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                    (proposalCap + 1) 0 result.2
                | nextRemaining + 1 =>
                    cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                      (proposalCap + 1) (nextRemaining + 1) result.2
              else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                (proposalCap + 1) (remainingProper + 1) result.2
          let nextLaw : Bool × AmbientSpace q.n →
              Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
            if result.1 then
              match remainingProper with
              | 0 => cappedProperCollectLawAux
                  (lazyProperProposalGaussianAux
                    (figureOneScheduledPhaseBody q I sigma2)
                    (figureOneScheduledPhaseBody_measurable q I sigma2)
                    (figureOneScheduledProposalRadius q sigma2) sigma2)
                  (fun _ => 0) properStride proposalCap 0 1 0 result.2
              | nextRemaining + 1 => cappedProperCollectLawAux
                  (lazyProperProposalGaussianAux
                    (figureOneScheduledPhaseBody q I sigma2)
                    (figureOneScheduledPhaseBody_measurable q I sigma2)
                    (figureOneScheduledProposalRadius q sigma2) sigma2)
                  (fun _ => 0) properStride proposalCap
                    (nextRemaining + 1) 1 0 result.2
            else cappedProperCollectLawAux
              (lazyProperProposalGaussianAux
                (figureOneScheduledPhaseBody q I sigma2)
                (figureOneScheduledPhaseBody_measurable q I sigma2)
                (figureOneScheduledProposalRadius q sigma2) sigma2)
              (fun _ => 0) properStride proposalCap
                (remainingProper + 1) 1 0 result.2
          have hnextStrong : ∀ result, (next result).StronglyMeasurable
              oracle.query := by
            rintro ⟨mark, state⟩
            cases mark with
            | false => exact (ih (remainingProper + 1)).1 state
            | true =>
                cases remainingProper with
                | zero => exact (ih 0).1 state
                | succ nextRemaining => exact (ih (nextRemaining + 1)).1 state
          have hnextEq : ∀ result,
              (next result).runEstimate oracle.query = nextLaw result := by
            rintro ⟨mark, state⟩
            cases mark with
            | false => exact (ih (remainingProper + 1)).2 state
            | true =>
                cases remainingProper with
                | zero => exact (ih 0).2 state
                | succ nextRemaining => exact (ih (nextRemaining + 1)).2 state
          have hnextLawMeasurable : Measurable nextLaw := by
            dsimp only [nextLaw]
            apply Measurable.ite
            · exact measurable_fst (measurableSet_singleton true)
            · cases remainingProper with
              | zero =>
                  exact (cappedProperCollectLawAux_measurable_and_probability
                    (lazyProperProposalGaussianAux
                      (figureOneScheduledPhaseBody q I sigma2)
                      (figureOneScheduledPhaseBody_measurable q I sigma2)
                      (figureOneScheduledProposalRadius q sigma2) sigma2)
                    measurable_const properStride proposalCap 0 1).1.comp
                      (measurable_const.prodMk measurable_snd)
              | succ nextRemaining =>
                  exact (cappedProperCollectLawAux_measurable_and_probability
                    (lazyProperProposalGaussianAux
                      (figureOneScheduledPhaseBody q I sigma2)
                      (figureOneScheduledPhaseBody_measurable q I sigma2)
                      (figureOneScheduledProposalRadius q sigma2) sigma2)
                    measurable_const properStride proposalCap
                      (nextRemaining + 1) 1).1.comp
                        (measurable_const.prodMk measurable_snd)
            · exact (cappedProperCollectLawAux_measurable_and_probability
                (lazyProperProposalGaussianAux
                  (figureOneScheduledPhaseBody q I sigma2)
                  (figureOneScheduledPhaseBody_measurable q I sigma2)
                  (figureOneScheduledProposalRadius q sigma2) sigma2)
                measurable_const properStride proposalCap
                  (remainingProper + 1) 1).1.comp
                    (measurable_const.prodMk measurable_snd)
          have hprogram : ∀ current,
              cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  ((proposalCap + 1) + 1) (remainingProper + 1) current =
                (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).bind
                  next := by
            intro current
            rw [cappedScheduledAccuracyProperBlockAux]
            congr 1
          have hlaw : ∀ current,
              cappedProperCollectLawAux
                  (lazyProperProposalGaussianAux
                    (figureOneScheduledPhaseBody q I sigma2)
                    (figureOneScheduledPhaseBody_measurable q I sigma2)
                    (figureOneScheduledProposalRadius q sigma2) sigma2)
                  (fun _ => 0) properStride (proposalCap + 1)
                    (remainingProper + 1) 1 0 current =
                (lazyProperProposalGaussianAux
                    (figureOneScheduledPhaseBody q I sigma2)
                    (figureOneScheduledPhaseBody_measurable q I sigma2)
                    (figureOneScheduledProposalRadius q sigma2) sigma2 current).bind
                  nextLaw := by
            intro current
            rw [cappedProperCollectLawAux]
            apply Measure.bind_congr_right
            filter_upwards with result
            rcases result with ⟨mark, state⟩
            cases mark <;> cases remainingProper <;>
              simp [nextLaw, cappedProperCollectLawAux]
          constructor
          · intro current
            rw [hprogram current]
            exact (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
              q I oracle sigma2 current).bind hnextStrong <| by
                simpa only [hnextEq] using hnextLawMeasurable
          · intro current
            rw [hprogram current, hlaw current]
            rw [MembershipOracleProgram.runEstimate_bind oracle.query _ next
              (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current) hnextStrong]
            · rw [runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
                q I oracle hsigma2 current]
              apply Measure.bind_congr_right
              filter_upwards with result
              exact hnextEq result
            · simpa only [hnextEq] using hnextLawMeasurable

theorem cappedScheduledAccuracyProperBlock_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
      properStride current).runEstimate oracle.query =
      scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
        properStride current := by
  exact (cappedScheduledAccuracyProperBlockAux_add_one_semantics
    q I oracle hsigma2 properStride proposalCap properStride).2 current

theorem cappedScheduledAccuracyProperBlock_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
      properStride current).StronglyMeasurable oracle.query :=
  (cappedScheduledAccuracyProperBlockAux_add_one_semantics
    q I oracle hsigma2 properStride proposalCap properStride).1 current

theorem scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [scheduledBalancedAccuracyGaussianRejectionAttempt,
    MembershipOracleProgram.StronglyMeasurable]
  let target : AmbientSpace q.n := (accuracyScaleFactor q)⁻¹ • current
  let output : ℝ → Bool × AmbientSpace q.n := fun coin =>
    if oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
        ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
          gaussianScaleAcceptance sigma2 (accuracyScaleFactor q) target then
      (true, target)
    else (false, target)
  have hout : Measurable output := by
    by_cases heligible : oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2
    · simp only [output, heligible.1, heligible.2.1, heligible.2.2, true_and]
      exact Measurable.ite
        (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_id)
          measurable_const) measurable_const measurable_const
    · have hfalse : ∀ coin : ℝ, ¬ (oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            gaussianScaleAcceptance sigma2 (accuracyScaleFactor q) target) := by
        intro coin h
        exact heligible ⟨h.1, h.2.1, h.2.2.1⟩
      simp only [output, hfalse, if_false]
      exact measurable_const
  constructor
  · rw [show (fun coin => MembershipOracleProgram.runEstimate oracle.query
        (if oracle.query target = true ∧
            ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
            ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
              gaussianScaleAcceptance sigma2 (accuracyScaleFactor q) target then
          .pure (true, target) else .pure (false, target))) =
        fun coin => Measure.dirac (output coin) by
      funext coin
      by_cases h : oracle.query target = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            gaussianScaleAcceptance sigma2 (accuracyScaleFactor q) target
      · simp [h, output, MembershipOracleProgram.runEstimate]
      · simp [h, output, MembershipOracleProgram.runEstimate]]
    exact Measure.measurable_dirac.comp hout
  · intro coin
    split <;> trivial

#print axioms runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
#print axioms cappedScheduledAccuracyProperBlock_semantics

end ArlibCommunity.Algorithms.CV18
