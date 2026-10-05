/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCappedDominance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledBranchMass
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCostBounds
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLocalCapPrefix

/-! # Cap-independent cost of one scheduled retry trial -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- One live retry trial: run one proper block and, on success, its balanced
rejection test.  The retained point is the pre-scaling mixed point used by
the executable retry recursion. -/
noncomputable def scheduledBalancedAccuracyLiveTrial
    (q : VolumeParams) (sigma2 : ℝ) (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (Bool × AmbientSpace q.n)) :=
  (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
    properStride current).bind fun block =>
      match block with
      | none => .pure none
      | some (_, mixed) =>
          (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
            fun result => .pure (some (result.1, mixed))

private noncomputable def scheduledBalancedAccuracyRejectionTail
    (q : VolumeParams) (sigma2 : ℝ) :
    Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (Bool × AmbientSpace q.n))
  | none => .pure none
  | some (_, mixed) =>
      (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
        fun result => .pure (some (result.1, mixed))

private theorem scheduledBalancedAccuracyRejectionTail_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun block =>
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).run oracle.query) ∧
    ∀ block,
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).CountedStronglyMeasurable
        oracle.query := by
  have htail : ∀ block,
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).CountedStronglyMeasurable
        oracle.query := by
    intro block
    cases block with
    | none => trivial
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        apply MembershipOracleProgram.CountedStronglyMeasurable.bind
          (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
            q I oracle sigma2 mixed) (fun _ => by trivial)
        simp only [MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp <|
          (measurable_some.comp <| measurable_fst.prodMk measurable_const).prodMk
            measurable_const
  have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
      (scheduledBalancedAccuracyRejectionTail q sigma2 (some value)).run
        oracle.query := by
    apply MembershipOracleProgram.measurable_run_bind_param
      oracle.query
      (fun value : ℝ × AmbientSpace q.n =>
        scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 value.2)
      (fun z : (ℝ × AmbientSpace q.n) × (Bool × AmbientSpace q.n) =>
        .pure (some (z.2.1, z.1.2)))
    · apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
        oracle.query _ 1
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
          q sigma2 value.2
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
          q I oracle sigma2 value.2
      · rw [show (fun value : ℝ × AmbientSpace q.n =>
              (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                value.2).runEstimate oracle.query) =
            fun value => scheduledBalancedAccuracyGaussianRejectionKernel
              q I sigma2 value.2 by
            funext value
            exact runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
              q I oracle hsigma2 value.2]
        exact (scheduledBalancedAccuracyGaussianRejectionKernel
          q I sigma2).measurable.comp measurable_snd
    · intro value
      exact scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
        q I oracle sigma2 value.2
    · simp only [MembershipOracleProgram.run]
      exact Measure.measurable_dirac.comp <|
        (measurable_some.comp <|
          (measurable_fst.comp measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_const
    · intro z
      trivial
  refine ⟨?_, htail⟩
  convert Measurable.optionElim
    (Measure.dirac ((none : Option (Bool × AmbientSpace q.n)), 0)) hsome using 1
  funext block
  cases block <;> rfl

private theorem MembershipOracleProgram.FixedQueryCount.countedQueryCost_eq
    {n : ℕ} {A : Type} [MeasurableSpace A]
    {program : MembershipOracleProgram n A} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (hstrong : program.StronglyMeasurable oracle) :
    countedQueryCost (program.run oracle) = count := by
  rw [hcount.run_eq_map_runEstimate oracle hstrong]
  unfold countedQueryCost
  letI : IsProbabilityMeasure (program.runEstimate oracle) :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle program
      hstrong.estimateMeasurable
  rw [lintegral_map]
  · simp
  · fun_prop
  · fun_prop

theorem scheduledBalancedAccuracyLiveTrial_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
      current).CountedStronglyMeasurable oracle.query := by
  have htail := scheduledBalancedAccuracyRejectionTail_countedMeasurable
    q I oracle hsigma2
  unfold scheduledBalancedAccuracyLiveTrial
  exact (cappedScheduledAccuracyProperBlock_countedMeasurable
    q I oracle hsigma2 (proposalCap + 1) properStride).2 current |>.bind
      htail.2 htail.1

/-- The counted execution law of one live trial varies measurably with its
input state. -/
theorem scheduledBalancedAccuracyLiveTrial_run_measurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    Measurable fun current =>
      (scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
        current).run oracle.query := by
  let source (current : AmbientSpace q.n) :=
    cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
      properStride current
  let tail (z : AmbientSpace q.n × Option (ℝ × AmbientSpace q.n)) :=
    scheduledBalancedAccuracyRejectionTail q sigma2 z.2
  have hsource := cappedScheduledAccuracyProperBlock_countedMeasurable
    q I oracle hsigma2 (proposalCap + 1) properStride
  have htail := scheduledBalancedAccuracyRejectionTail_countedMeasurable
    q I oracle hsigma2
  have h := MembershipOracleProgram.measurable_run_bind_param oracle.query
    source tail hsource.1 hsource.2 (htail.1.comp measurable_snd)
      (fun z => htail.2 z.2)
  simpa only [source, tail, scheduledBalancedAccuracyLiveTrial,
    scheduledBalancedAccuracyRejectionTail] using h

/-- A live trial inherits exactly the local block budget plus the one-query
balanced rejection decision. -/
theorem scheduledBalancedAccuracyLiveTrial_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
      current).QueryBound (proposalCap + 2) := by
  unfold scheduledBalancedAccuracyLiveTrial
  let tail : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (Bool × AmbientSpace q.n))
    | none => .pure none
    | some (_, mixed) =>
        (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
          fun result => .pure (some (result.1, mixed))
  have htail : ∀ block, (tail block).QueryBound 1 := by
    intro block
    cases block with
    | none =>
        exact (MembershipOracleProgram.QueryBound.pure
          (none : Option (Bool × AmbientSpace q.n)) 0).mono (by omega)
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        exact (scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
          q sigma2 mixed).bind (fun result =>
            MembershipOracleProgram.QueryBound.pure
              (some (result.1, mixed)) 0)
  have h := (cappedScheduledAccuracyProperBlock_queryBound q sigma2
    (proposalCap + 1) properStride current).bind htail
  simpa only [tail, Nat.add_assoc] using h

/-- Pointwise, adding the balanced rejection decision costs at most one query
beyond the cap-independent proper-block cost. -/
theorem scheduledBalancedAccuracyLiveTrial_countedQueryCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
          current).run oracle.query) ≤
      countedQueryCost
        ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
          properStride current).run oracle.query) + 1 := by
  let tail := scheduledBalancedAccuracyRejectionTail q sigma2
  have htail := scheduledBalancedAccuracyRejectionTail_countedMeasurable
    q I oracle hsigma2
  have htailCost : ∀ block,
      countedQueryCost ((tail block).run oracle.query) ≤ 1 := by
    intro block
    cases block with
    | none =>
        rw [show tail none = .pure none by rfl]
        have hfixed :
            (MembershipOracleProgram.pure (n := q.n)
              (none : Option (Bool × AmbientSpace q.n))).FixedQueryCount 0 :=
          MembershipOracleProgram.FixedQueryCount.pure _
        rw [hfixed.countedQueryCost_eq oracle.query (by trivial)]
        norm_num
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        have hfixed : (tail (some (ignored, mixed))).FixedQueryCount 1 := by
          change ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
            mixed).bind fun result =>
              .pure (some (result.1, mixed))).FixedQueryCount 1
          simpa using
            (scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
              q sigma2 mixed).bind
                (fun result => MembershipOracleProgram.FixedQueryCount.pure
                  (some (result.1, mixed)))
        have hstrong : (tail (some (ignored, mixed))).StronglyMeasurable
            oracle.query := by
          change ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
            mixed).bind fun result =>
              .pure (some (result.1, mixed))).StronglyMeasurable oracle.query
          apply (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
            q I oracle sigma2 mixed).bind (fun _ => by trivial)
          simp only [MembershipOracleProgram.runEstimate]
          exact Measure.measurable_dirac.comp <|
            measurable_some.comp (measurable_fst.prodMk measurable_const)
        exact le_of_eq (by
          simpa only [Nat.cast_one] using
            hfixed.countedQueryCost_eq oracle.query hstrong)
  unfold scheduledBalancedAccuracyLiveTrial
  change countedQueryCost
      (((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).bind tail).run oracle.query) ≤ _
  exact MembershipOracleProgram.countedQueryCost_bind_le_add oracle.query _ tail
    ((cappedScheduledAccuracyProperBlock_countedMeasurable
      q I oracle hsigma2 (proposalCap + 1) properStride).2 current)
    htail.2 htail.1 1 htailCost

/-- Integrated one-trial cost under an arbitrary warm subprobability law.
Crucially, the bound contains no `proposalCap`. -/
theorem lintegral_scheduledBalancedAccuracyLiveTrial_countedQueryCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
          current).run oracle.query) ∂mu ≤
      (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by
  calc
    _ ≤ ∫⁻ current, (countedQueryCost
          ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
            properStride current).run oracle.query) + 1) ∂mu :=
      lintegral_mono fun current =>
        scheduledBalancedAccuracyLiveTrial_countedQueryCost_le
          q I oracle hsigma2 proposalCap properStride current
    _ = (∫⁻ current, countedQueryCost
          ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
            properStride current).run oracle.query) ∂mu) + mu Set.univ := by
      rw [lintegral_add_left]
      · simp
      · exact (Measure.measurable_lintegral
          measurable_countedQueryCost_integrand).comp <|
            (cappedScheduledAccuracyProperBlock_countedMeasurable
              q I oracle hsigma2 (proposalCap + 1) properStride).1
    _ ≤ ((properStride : ENNReal) * (M * 2) + mu Set.univ) +
        mu Set.univ := by
      gcongr
      exact lintegral_cappedScheduledAccuracyProperBlock_countedQueryCost_le_of_isWarm_submeasure
        q I oracle hsigma2 hwarm (proposalCap + 1) properStride
    _ = (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by ring

/-- One-trial expected cost for a law split into a warm good submeasure and
an arbitrary error submeasure.  The error is charged only at the structural
local budget; the warm part retains the cap-independent proper-clock bound. -/
theorem lintegral_scheduledBalancedAccuracyLiveTrial_countedQueryCost_le_of_le_warm_add
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M error : ENNReal}
    {mu good bad : Measure (AmbientSpace q.n)}
    (hle : mu ≤ good + bad)
    (hwarm : _root_.Arlib.IsWarm M good
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hbad : bad Set.univ ≤ error)
    (proposalCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
          current).run oracle.query) ∂mu ≤
      ((properStride : ENNReal) * (M * 2) + 2 * good Set.univ) +
        (proposalCap + 2 : ℕ) * error := by
  let cost : AmbientSpace q.n → ENNReal := fun current => countedQueryCost
    ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
      current).run oracle.query)
  have hgood : ∫⁻ current, cost current ∂good ≤
      (properStride : ENNReal) * (M * 2) + 2 * good Set.univ := by
    simpa only [cost] using
      lintegral_scheduledBalancedAccuracyLiveTrial_countedQueryCost_le_of_isWarm
        q I oracle hsigma2 hwarm proposalCap properStride
  have hpoint : ∀ current, cost current ≤ (proposalCap : ENNReal) + 2 := by
    intro current
    dsimp only [cost]
    simpa only [countedQueryCost, Nat.cast_add, Nat.cast_ofNat] using
      (scheduledBalancedAccuracyLiveTrial_queryBound q sigma2 proposalCap
        properStride current).lintegral_queryCount_le
        (scheduledBalancedAccuracyLiveTrial_countedStronglyMeasurable
          q I oracle hsigma2 proposalCap properStride current)
  have hbadCost : ∫⁻ current, cost current ∂bad ≤
      ((proposalCap : ENNReal) + 2) * error := by
    calc
      (∫⁻ current, cost current ∂bad) ≤
          ∫⁻ _current, ((proposalCap : ENNReal) + 2) ∂bad :=
        lintegral_mono fun current => hpoint current
      _ = ((proposalCap : ENNReal) + 2) * bad Set.univ := by
        rw [lintegral_const]
      _ ≤ ((proposalCap : ENNReal) + 2) * error := by
        gcongr
  calc
    (∫⁻ current, cost current ∂mu) ≤
        ∫⁻ current, cost current ∂(good + bad) :=
      lintegral_mono' hle le_rfl
    _ = (∫⁻ current, cost current ∂good) +
        ∫⁻ current, cost current ∂bad := lintegral_add_measure _ _ _
    _ ≤ ((properStride : ENNReal) * (M * 2) + 2 * good Set.univ) +
        (proposalCap + 2 : ℕ) * error := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using add_le_add hgood hbadCost

/-- Acceptance filtering can only remove mass from a scheduled endpoint law. -/
theorem scheduledBalancedAcceptedStateMeasure_le
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) :
    scheduledBalancedAcceptedStateMeasure q I sigma2 mu ≤ mu := by
  unfold scheduledBalancedAcceptedStateMeasure
  apply Measure.le_iff.mpr
  intro A hA
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, scheduledBalancedAccuracyGaussianAcceptance
        q I sigma2 x ∂mu) ≤ ∫⁻ _x in A, (1 : ENNReal) ∂mu :=
      lintegral_mono fun x =>
        (scheduledBalancedAccuracyGaussianAcceptance_le_half
          q I hsigma2 x).trans (by norm_num)
    _ = mu A := by rw [setLIntegral_one]

/-- Any submeasure of a warm measure is warm with the same coefficient. -/
theorem isWarm_of_le_of_isWarm
    {S : Type*} [MeasurableSpace S]
    {M : ENNReal} {mu nu pi : Measure S}
    (hle : nu ≤ mu) (hwarm : _root_.Arlib.IsWarm M mu pi) :
    _root_.Arlib.IsWarm M nu pi := by
  intro A hA
  exact (Measure.le_iff.mp hle A hA).trans (hwarm A hA)

/-- Every scheduled lazy-speedy stride preserves its speedy stationary law. -/
theorem scheduledPhaseLazySpeedyPow_invariant
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (properStride : ℕ) :
    Kernel.Invariant
      ((lazy (speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) ^ properStride)
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2) := by
  let pi := ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hinvOne : Kernel.Invariant
      (lazy (speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) pi :=
    (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob
        (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)).invariant
  induction properStride with
  | zero =>
      rw [pow_zero, Kernel.Invariant]
      ext A hA
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
      change (∫⁻ a, (Kernel.id a) A ∂pi) = pi A
      simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
      exact lintegral_indicator_one hA
  | succ k ih =>
      rw [pow_succ]
      exact ih.comp hinvOne

/-- Both retry branches preserve the warmness of the successful block-endpoint
sublaw.  No normalization, TV error, or proposal-cap term is required. -/
theorem scheduledBalancedRetryBranches_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    let endpoint := successfulEndpointLaw
      (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
        proposalCap properStride))
    _root_.Arlib.IsWarm M
        (scheduledBalancedAcceptedStateMeasure q I sigma2 endpoint)
        (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2) ∧
      _root_.Arlib.IsWarm M
        (scheduledBalancedRejectedStateMeasure q I sigma2 endpoint)
        (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2) := by
  dsimp only
  let pi := ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hinv : Kernel.Invariant
      ((lazy (speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) ^ properStride) pi :=
    scheduledPhaseLazySpeedyPow_invariant q I sigma2 properStride
  have hend : _root_.Arlib.IsWarm M
      (successfulEndpointLaw
        (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
          proposalCap properStride))) pi :=
    successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_isWarm
      q I sigma2 proposalCap properStride hwarm hinv
  exact ⟨
    isWarm_of_le_of_isWarm
      (scheduledBalancedAcceptedStateMeasure_le q I hsigma2 _) hend,
    isWarm_of_le_of_isWarm
      (scheduledBalancedRejectedStateMeasure_le q I sigma2 _) hend⟩

end ArlibCommunity.Algorithms.CV18
