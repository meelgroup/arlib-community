/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperClock

/-!
# A capped executable proper-step walk for CV18

This file exposes the proper-proposal bit in the membership-oracle program
itself and uses it to run a requested number of proper steps subject to a
deterministic raw-query cap.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- The executable proposal program with the proper-proposal bit retained.
A proposal is proper exactly when it lies in the fixed truncated body. A
Metropolis rejection on that branch is still marked proper. -/
noncomputable def truncatedMetropolisMarkedProposalProgram (q : VolumeParams)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧ ‖proposal‖ ≤ Real.sqrt (terminalVariance q) then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

/-- One executable lazy Metropolis proposal with its proper bit retained. -/
noncomputable def truncatedMetropolisMarkedBallStep (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current (figureOneProposalRadius q sigma2))
    inferInstance fun proposal =>
      truncatedMetropolisMarkedProposalProgram q sigma2 current proposal

/-- Forgetting the mark in the proposal program is definitionally the
existing executable proposal program. -/
theorem truncatedMetropolisMarkedProposalProgram_map_snd
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).bind
        (fun p => .pure p.2) =
      truncatedMetropolisProposalProgram q sigma2 current proposal := by
  unfold truncatedMetropolisMarkedProposalProgram
    truncatedMetropolisProposalProgram
  simp only [MembershipOracleProgram.bind]
  congr 1
  funext inside
  congr 1
  funext coin
  by_cases hproper :
      inside = true ∧ ‖proposal‖ ≤ Real.sqrt (terminalVariance q)
  · simp [MembershipOracleProgram.bind, hproper]
  · have hfull : ¬ (inside = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
        coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal) := by
      intro h
      exact hproper ⟨h.1, h.2.1⟩
    simp [MembershipOracleProgram.bind, hproper, hfull]

/-- Forgetting the mark in a complete step is definitionally the existing
Figure-1 step. -/
theorem truncatedMetropolisMarkedBallStep_map_snd
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).bind
        (fun p => .pure p.2) =
      truncatedMetropolisBallStep q sigma2 current := by
  unfold truncatedMetropolisMarkedBallStep truncatedMetropolisBallStep
    MembershipOracleProgram.bind
  congr 1
  funext proposal
  exact truncatedMetropolisMarkedProposalProgram_map_snd
    q sigma2 current proposal

theorem truncatedMetropolisMarkedProposalProgram_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem truncatedMetropolisMarkedBallStep_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  exact truncatedMetropolisMarkedProposalProgram_queryBound
    q sigma2 current proposal

/-- Under the executable proposal law, the probability of landing in the
truncated body is exactly its abstract local conductance. -/
theorem uniformClosedBallMeasure_truncatedBody
    (q : VolumeParams) (I : VolumeInput q.n) (current : AmbientSpace q.n)
    {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius (truncatedBody q I) =
      Arlib.MarkovChains.ell (truncatedBody q I) radius current := by
  let _ : NeZero q.n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)⟩
  rw [uniformClosedBallMeasure_eq_openBall current hradius,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply
      (truncatedBody_measurable q I), Arlib.MarkovChains.ell_apply,
    ENNReal.div_eq_inv_mul]
  congr 1
  rw [Set.inter_comm]

theorem uniformClosedBallMeasure_truncatedBody_compl
    (q : VolumeParams) (I : VolumeInput q.n) (current : AmbientSpace q.n)
    {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure q.n current radius (truncatedBody q I)ᶜ =
      1 - Arlib.MarkovChains.ell (truncatedBody q I) radius current := by
  rw [measure_compl (truncatedBody_measurable q I) (measure_ne_top _ _),
    measure_univ, uniformClosedBallMeasure_truncatedBody q I current hradius]

theorem truncatedMetropolisMarkedProposalProgram_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).StronglyMeasurable
      oracle.query := by
  simp only [truncatedMetropolisMarkedProposalProgram,
    MembershipOracleProgram.StronglyMeasurable]
  by_cases hproper : oracle.query proposal = true ∧
      ‖proposal‖ ≤ Real.sqrt (terminalVariance q)
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

theorem truncatedMetropolisMarkedBallStep_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp only [truncatedMetropolisMarkedBallStep,
    MembershipOracleProgram.StronglyMeasurable]
  let output : AmbientSpace q.n → ℝ → Bool × AmbientSpace q.n :=
      fun point coin =>
        if oracle.query point = true ∧
            ‖point‖ ≤ Real.sqrt (terminalVariance q) then
          (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current point
            then point else current)
        else (false, current)
  have horacle : Measurable fun p : AmbientSpace q.n × ℝ =>
      oracle.query p.1 := oracle.measurable_query.comp measurable_fst
  have hnorm : Measurable fun p : AmbientSpace q.n × ℝ => ‖p.1‖ := by
    fun_prop
  have haccept : Measurable fun p : AmbientSpace q.n × ℝ =>
      lazyGaussianMetropolisAcceptance sigma2 current p.1 := by
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  have hout : Measurable fun p : AmbientSpace q.n × ℝ =>
      output p.1 p.2 := by
    apply Measurable.ite
    · exact (horacle (measurableSet_singleton true)).inter
        (measurableSet_le hnorm measurable_const)
    · apply measurable_const.prodMk
      exact Measurable.ite (measurableSet_le measurable_snd haccept)
        measurable_fst measurable_const
    · exact measurable_const
  constructor
  · rw [show (fun point =>
        (truncatedMetropolisMarkedProposalProgram q sigma2 current point).runEstimate
          oracle.query) =
        fun point => uniformUnitIntervalMeasure.map (output point) by
      funext point
      simp only [truncatedMetropolisMarkedProposalProgram,
        MembershipOracleProgram.runEstimate]
      have hinner : (fun coin =>
          MembershipOracleProgram.runEstimate oracle.query
            (if oracle.query point = true ∧
                ‖point‖ ≤ Real.sqrt (terminalVariance q) then
              .pure (true, if coin ≤
                lazyGaussianMetropolisAcceptance sigma2 current point
                then point else current)
            else .pure (false, current))) =
          fun coin => Measure.dirac (output point coin) := by
        funext coin
        by_cases hproper : oracle.query point = true ∧
            ‖point‖ ≤ Real.sqrt (terminalVariance q)
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
        · simp [hproper, output, MembershipOracleProgram.runEstimate]
      rw [hinner]
      exact Measure.bind_dirac_eq_map uniformUnitIntervalMeasure
        (hout.comp (measurable_const.prodMk measurable_id))]
    exact measurable_measure_map_param uniformUnitIntervalMeasure hout
  · intro proposal
    exact truncatedMetropolisMarkedProposalProgram_stronglyMeasurable
      q I oracle sigma2 current proposal

/-- The state marginal of the marked executable step is exactly the existing
Figure-1 kernel. -/
theorem map_snd_runEstimate_truncatedMetropolisMarkedBallStep
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    ((truncatedMetropolisMarkedBallStep q sigma2 current).runEstimate
      oracle.query).map Prod.snd =
        truncatedMetropolisKernel q I oracle sigma2 current := by
  have hrun := MembershipOracleProgram.runEstimate_bind oracle.query
    (truncatedMetropolisMarkedBallStep q sigma2 current)
    (fun p => .pure p.2)
    (truncatedMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current)
    (fun p => by trivial)
    (by
      simp only [MembershipOracleProgram.runEstimate]
      exact Measure.measurable_dirac.comp measurable_snd)
  rw [truncatedMetropolisMarkedBallStep_map_snd] at hrun
  simp only [MembershipOracleProgram.runEstimate] at hrun
  change _ = truncatedMetropolisBallStepEstimateLaw q oracle.query sigma2 current
  rw [← runEstimate_truncatedMetropolisBallStep q I oracle sigma2 current,
    hrun, Measure.bind_dirac_eq_map _ measurable_snd]

/-- The false-mark slice of the executable marked law is exactly the
improper-proposal self-loop of the abstract marked kernel. -/
theorem runEstimate_truncatedMetropolisMarkedBallStep_apply_false_prod
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n)
    {t : Set (AmbientSpace q.n)} (ht : MeasurableSet t) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query
        ({false} ×ˢ t) =
      (1 - Arlib.MarkovChains.ell (truncatedBody q I)
        (figureOneProposalRadius q sigma2) current) * t.indicator 1 current := by
  let U := uniformClosedBallMeasure q.n current
    (figureOneProposalRadius q sigma2)
  have hset : MeasurableSet ({false} ×ˢ t) :=
    (measurableSet_singleton false).prod ht
  have hmeas : AEMeasurable (fun proposal =>
      (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
        oracle.query) U :=
    (truncatedMetropolisMarkedBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable.1
  simp only [truncatedMetropolisMarkedBallStep,
    MembershipOracleProgram.runEstimate]
  rw [Measure.bind_apply hset hmeas]
  have hinner : ∀ proposal : AmbientSpace q.n,
      (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).runEstimate
          oracle.query ({false} ×ˢ t) =
        (truncatedBody q I)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal := by
    intro proposal
    simp only [truncatedMetropolisMarkedProposalProgram,
      MembershipOracleProgram.runEstimate]
    by_cases hp : proposal ∈ truncatedBody q I
    · simp only [
        (oracle_and_radius_iff_mem_truncatedBody q I oracle proposal).mpr hp]
      rw [Measure.bind_apply hset]
      · simp only [true_and, if_true,
          MembershipOracleProgram.runEstimate]
        rw [Set.indicator_of_notMem (by simpa using hp)]
        change (∫⁻ coin, Measure.dirac
            (true, if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
              then proposal else current) ({false} ×ˢ t)
          ∂uniformUnitIntervalMeasure) = 0
        simp [Measure.dirac_apply' _ hset]
      · exact (Measure.measurable_dirac.comp <|
          measurable_const.prodMk <|
            Measurable.ite measurableSet_Iic measurable_const measurable_const).aemeasurable
    · simp only [
        (oracle_and_radius_iff_mem_truncatedBody q I oracle proposal).not.mpr hp]
      simp only [if_false, MembershipOracleProgram.runEstimate]
      rw [Measure.bind_const, measure_univ, one_smul]
      change Measure.dirac (false, current) ({false} ×ˢ t) =
        (truncatedBody q I)ᶜ.indicator
          (fun _ => t.indicator 1 current) proposal
      rw [Measure.dirac_apply' _ hset]
      by_cases hc : current ∈ t <;> simp [hp, hc]
  simp_rw [hinner]
  rw [lintegral_indicator (truncatedBody_measurable q I).compl]
  rw [setLIntegral_const]
  rw [uniformClosedBallMeasure_truncatedBody_compl q I current
    (figureOneProposalRadius_pos q hsigma2)]
  ring

/-- Measures on `Bool × α` are determined by their two measurable
singleton slices. -/
theorem measure_bool_prod_ext {α : Type*} [MeasurableSpace α]
    {μ ν : Measure (Bool × α)}
    (hslice : ∀ (b : Bool) (t : Set α), MeasurableSet t →
      μ ({b} ×ˢ t) = ν ({b} ×ˢ t)) :
    μ = ν := by
  ext S hS
  let sf : Set α := (fun x => (false, x)) ⁻¹' S
  let st : Set α := (fun x => (true, x)) ⁻¹' S
  have hsf : MeasurableSet sf := hS.preimage (measurable_const.prodMk measurable_id)
  have hst : MeasurableSet st := hS.preimage (measurable_const.prodMk measurable_id)
  have hdecomp : S = ({false} ×ˢ sf) ∪ ({true} ×ˢ st) := by
    ext p
    rcases p with ⟨b, x⟩
    cases b <;> simp [sf, st]
  have hdisj : Disjoint ({false} ×ˢ sf) ({true} ×ˢ st) := by
    apply Set.disjoint_left.2
    rintro ⟨b, x⟩ hpFalse hpTrue
    cases b <;> simp at hpFalse hpTrue
  rw [hdecomp, measure_union hdisj ((measurableSet_singleton true).prod hst),
    measure_union hdisj ((measurableSet_singleton true).prod hst),
    hslice false sf hsf, hslice true st hst]

/-- The marked membership-oracle step has exactly the abstract marked-kernel
law used by the lazy proper-proposal clock. -/
theorem runEstimate_truncatedMetropolisMarkedBallStep_eq_lazyProperAux
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query =
      Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
        (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
        sigma2 current := by
  let μ : Measure (Bool × AmbientSpace q.n) :=
    (truncatedMetropolisMarkedBallStep q sigma2 current).runEstimate oracle.query
  let ν : Measure (Bool × AmbientSpace q.n) :=
    Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
      (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
      sigma2 current
  let _ : IsProbabilityMeasure μ :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      (truncatedMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current).estimateMeasurable
  let _ : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hstate : μ.map Prod.snd = ν.map Prod.snd := by
    calc
      μ.map Prod.snd = truncatedMetropolisKernel q I oracle sigma2 current :=
        map_snd_runEstimate_truncatedMetropolisMarkedBallStep
          q I oracle sigma2 current
      _ = ν.map Prod.snd :=
        (map_snd_lazyProperProposalGaussianAux_figureOne
          q I oracle hsigma2 current).symm
  have hfalse : ∀ (t : Set (AmbientSpace q.n)), MeasurableSet t →
      μ ({false} ×ˢ t) = ν ({false} ×ˢ t) := by
    intro t ht
    rw [runEstimate_truncatedMetropolisMarkedBallStep_apply_false_prod
      q I oracle hsigma2 current ht]
    dsimp [ν]
    rw [Arlib.MarkovChains.lazyProperProposalGaussianAux_apply_set
      (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
      sigma2 current ((measurableSet_singleton false).prod ht)]
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
      have hsumμ : μ ({false} ×ˢ t) + μ ({true} ×ˢ t) =
          μ.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hsumν : ν ({false} ×ˢ t) + ν ({true} ×ˢ t) =
          ν.map Prod.snd t := by
        rw [Measure.map_apply measurable_snd ht, hpre,
          measure_union hdisj ((measurableSet_singleton true).prod ht)]
      have hadd : μ ({false} ×ˢ t) + μ ({true} ×ˢ t) =
          ν ({false} ×ˢ t) + ν ({true} ×ˢ t) := by
        rw [hsumμ, hsumν, hstate]
      rw [hfalse t ht] at hadd
      exact WithTop.add_left_cancel (measure_ne_top ν ({false} ×ˢ t)) hadd

/-- Run until `properSteps` marked proposals have occurred, but abort with
`none` after `rawCap` raw proposals. -/
noncomputable def cappedProperMetropolisBallWalk (q : VolumeParams)
    (sigma2 : ℝ) : ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | _, 0, current => .pure (some current)
  | 0, _ + 1, _ => .pure none
  | rawCap + 1, properSteps + 1, current =>
      (truncatedMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        cappedProperMetropolisBallWalk q sigma2 rawCap
          (if result.1 then properSteps else properSteps + 1) result.2

/-- The capped proper-step walk makes at most `rawCap` membership queries,
independently of whether it succeeds. -/
theorem cappedProperMetropolisBallWalk_queryBound
    (q : VolumeParams) (sigma2 : ℝ) : ∀ rawCap properSteps current,
    (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).QueryBound
      rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps current
      cases properSteps <;> exact .pure _ 0
  | succ rawCap ih =>
      intro properSteps current
      cases properSteps with
      | zero => exact .pure _ (rawCap + 1)
      | succ properSteps =>
          simp only [cappedProperMetropolisBallWalk]
          simpa [Nat.add_comm] using
            (truncatedMetropolisMarkedBallStep_queryBound q sigma2 current).bind
              (fun result =>
                ih (if result.1 then properSteps else properSteps + 1) result.2)

open ProbabilityTheory

/-- The finite law obtained by consuming at most `rawCap` marked transitions
while waiting for `properSteps` true marks. -/
noncomputable def cappedProperMarkedLaw {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) : ℕ → ℕ → S → Measure (Option S)
  | _, 0, current => Measure.dirac (some current)
  | 0, _ + 1, _ => Measure.dirac none
  | rawCap + 1, properSteps + 1, current =>
      (Q current).bind fun result =>
        cappedProperMarkedLaw Q rawCap
          (if result.1 then properSteps else properSteps + 1) result.2

theorem measurable_cappedProperMarkedLaw {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) : ∀ rawCap properSteps,
    Measurable fun current => cappedProperMarkedLaw Q rawCap properSteps current := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps
      cases properSteps with
      | zero =>
          exact Measure.measurable_dirac.comp
            (measurable_some.comp measurable_id)
      | succ properSteps =>
          exact Measure.measurable_dirac.comp measurable_const
  | succ rawCap ih =>
      intro properSteps
      cases properSteps with
      | zero =>
          exact Measure.measurable_dirac.comp
            (measurable_some.comp measurable_id)
      | succ properSteps =>
          have hnext : Measurable fun result : Bool × S =>
              cappedProperMarkedLaw Q rawCap
                (if result.1 then properSteps else properSteps + 1) result.2 := by
            rw [show (fun result : Bool × S =>
                cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2) =
              fun result => if result.1 = true then
                cappedProperMarkedLaw Q rawCap properSteps result.2 else
                cappedProperMarkedLaw Q rawCap (properSteps + 1) result.2 by
              funext result
              rcases result with ⟨mark, state⟩
              cases mark <;> rfl]
            apply Measurable.ite
            · exact measurable_fst (measurableSet_singleton true)
            · exact (ih properSteps).comp measurable_snd
            · exact (ih (properSteps + 1)).comp measurable_snd
          exact (Measure.measurable_bind' hnext).comp Q.measurable

/-- The executable capped proper-step program realizes exactly the finite
marked-kernel law.  The first two conjuncts retain the measurability evidence
needed by subsequent program composition. -/
theorem cappedProperMetropolisBallWalk_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) : ∀ rawCap properSteps,
    (Measurable fun current =>
      (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).runEstimate
        oracle.query) ∧
    (∀ current,
      (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).StronglyMeasurable
        oracle.query) ∧
    (∀ current,
      (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).runEstimate
          oracle.query =
        cappedProperMarkedLaw
          (Arlib.MarkovChains.lazyProperProposalGaussianAux (truncatedBody q I)
            (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
            sigma2) rawCap properSteps current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps
      cases properSteps with
      | zero =>
          constructor
          · simp only [cappedProperMetropolisBallWalk,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp
              (measurable_some.comp measurable_id)
          constructor
          · intro current
            trivial
          · intro current
            rfl
      | succ properSteps =>
          constructor
          · simp only [cappedProperMetropolisBallWalk,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp measurable_const
          constructor
          · intro current
            trivial
          · intro current
            rfl
  | succ rawCap ih =>
      intro properSteps
      cases properSteps with
      | zero =>
          constructor
          · simp only [cappedProperMetropolisBallWalk,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp
              (measurable_some.comp measurable_id)
          constructor
          · intro current
            trivial
          · intro current
            rfl
      | succ properSteps =>
          let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
            (truncatedBody q I) (truncatedBody_measurable q I)
            (figureOneProposalRadius q sigma2) sigma2
          let next : Bool × AmbientSpace q.n →
              MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
            fun result => cappedProperMetropolisBallWalk q sigma2 rawCap
              (if result.1 then properSteps else properSteps + 1) result.2
          have hnextStrong : ∀ result, (next result).StronglyMeasurable oracle.query := by
            rintro ⟨mark, current⟩
            cases mark <;> exact (ih _).2.1 current
          have hnextRun : Measurable fun result => (next result).runEstimate oracle.query := by
            have heq : (fun result => (next result).runEstimate oracle.query) =
                fun result => cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2 := by
              funext result
              rcases result with ⟨mark, current⟩
              cases mark <;> exact (ih _).2.2 current
            rw [heq]
            rw [show (fun result : Bool × AmbientSpace q.n =>
                cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2) =
              fun result => if result.1 = true then
                cappedProperMarkedLaw Q rawCap properSteps result.2 else
                cappedProperMarkedLaw Q rawCap (properSteps + 1) result.2 by
              funext result
              rcases result with ⟨mark, state⟩
              cases mark <;> rfl]
            apply Measurable.ite
            · exact measurable_fst (measurableSet_singleton true)
            · exact (measurable_cappedProperMarkedLaw Q rawCap properSteps).comp
                measurable_snd
            · exact (measurable_cappedProperMarkedLaw Q rawCap (properSteps + 1)).comp
                measurable_snd
          have hstepStrong : ∀ current,
              (truncatedMetropolisMarkedBallStep q sigma2 current).StronglyMeasurable
                oracle.query :=
            fun current => truncatedMetropolisMarkedBallStep_stronglyMeasurable
              q I oracle sigma2 current
          constructor
          · have heq : (fun current =>
                (cappedProperMetropolisBallWalk q sigma2 (rawCap + 1)
                  (properSteps + 1) current).runEstimate oracle.query) =
              fun current => cappedProperMarkedLaw Q (rawCap + 1)
                (properSteps + 1) current := by
                funext current
                simp only [cappedProperMetropolisBallWalk]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _ next
                  (hstepStrong current) hnextStrong hnextRun]
                rw [runEstimate_truncatedMetropolisMarkedBallStep_eq_lazyProperAux
                  q I oracle hsigma2 current]
                simp_rw [show ∀ result, (next result).runEstimate oracle.query =
                    cappedProperMarkedLaw Q rawCap
                      (if result.1 then properSteps else properSteps + 1) result.2 by
                  intro result
                  rcases result with ⟨mark, state⟩
                  cases mark <;> exact (ih _).2.2 state]
                rfl
            rw [heq]
            exact measurable_cappedProperMarkedLaw Q _ _
          constructor
          · intro current
            simp only [cappedProperMetropolisBallWalk]
            exact (hstepStrong current).bind hnextStrong hnextRun
          · intro current
            simp only [cappedProperMetropolisBallWalk]
            rw [MembershipOracleProgram.runEstimate_bind oracle.query _ next
              (hstepStrong current) hnextStrong hnextRun]
            rw [runEstimate_truncatedMetropolisMarkedBallStep_eq_lazyProperAux
              q I oracle hsigma2 current]
            simp_rw [show ∀ result, (next result).runEstimate oracle.query =
                cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2 by
              intro result
              rcases result with ⟨mark, state⟩
              cases mark <;> exact (ih _).2.2 state]
            rfl

end ArlibCommunity.Algorithms.CV18
