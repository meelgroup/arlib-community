/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperFailure
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperExpectedCostSubmeasure
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperSemantics

/-! # Expected cost of the schedule-targeted proper block

This is the operational Bellman bound for the actual scheduled executable.
It is uniform in the syntactic proposal cap; the cap can therefore be chosen
later from the one global soft-O query budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

theorem scheduledAccuracyMetropolisMarkedProposalProgram_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).FixedQueryCount
      1 := by
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  apply MembershipOracleProgram.FixedQueryCount.randomReal
  intro coin
  split <;> exact .pure _

theorem scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).FixedQueryCount
      1 := by
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro proposal
  exact scheduledAccuracyMetropolisMarkedProposalProgram_fixedQueryCount
    q sigma2 current proposal

theorem scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  (scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount q sigma2 current).countedStronglyMeasurable
    oracle.query
      (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current)

theorem scheduledAccuracyZeroObservation_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).FixedQueryCount 1 := by
  unfold scheduledAccuracyZeroObservation
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  exact .pure _

private theorem scheduledAccuracyZeroObservation_stronglyMeasurable_for_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp [scheduledAccuracyZeroObservation,
    MembershipOracleProgram.StronglyMeasurable,
    MembershipOracleProgram.runEstimate]

theorem scheduledAccuracyZeroObservation_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  (scheduledAccuracyZeroObservation_fixedQueryCount q sigma2 current).countedStronglyMeasurable
    oracle.query
      (scheduledAccuracyZeroObservation_stronglyMeasurable_for_cost
        q I oracle sigma2 current)

/-- The scheduled capped proper block has a jointly measurable counted law.
The proof follows its raw-proposal recursion, so no deterministic local-cost
multiplier is introduced. -/
theorem cappedScheduledAccuracyProperBlockAux_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (properStride : ℕ) :
    ∀ rawCap remainingProper,
      (Measurable fun current =>
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          rawCap remainingProper current).run oracle.query) ∧
      (∀ current,
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          rawCap remainingProper current).CountedStronglyMeasurable
            oracle.query) := by
  let Q := lazyProperProposalGaussianAux
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper
      constructor
      · simp only [cappedScheduledAccuracyProperBlockAux,
          MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp
          (measurable_const.prodMk measurable_const)
      · intro current
        rw [cappedScheduledAccuracyProperBlockAux]
        trivial
  | succ rawCap ih =>
      intro remainingProper
      cases remainingProper with
      | zero =>
          let observation (current : AmbientSpace q.n) :=
            scheduledAccuracyZeroObservation q sigma2 current
          let next (z : AmbientSpace q.n × ℝ) : MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) :=
            .pure (some (z.2, z.1))
          have hobservationMeas : Measurable fun current =>
              (observation current).run oracle.query := by
            apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
              oracle.query observation 1
            · intro current
              exact scheduledAccuracyZeroObservation_fixedQueryCount
                q sigma2 current
            · intro current
              exact scheduledAccuracyZeroObservation_stronglyMeasurable
                q I oracle sigma2 current
            · rw [show (fun current =>
                    (observation current).runEstimate oracle.query) =
                  fun _ : AmbientSpace q.n => Measure.dirac 0 by
                    funext current
                    exact runEstimate_scheduledAccuracyZeroObservation
                      q I oracle sigma2 current]
              exact measurable_const
          have hnextMeas : Measurable fun z => (next z).run oracle.query := by
            simp only [next, MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <|
                measurable_snd.prodMk measurable_fst).prodMk measurable_const
          constructor
          · simpa only [observation, next,
                cappedScheduledAccuracyProperBlockAux] using
              MembershipOracleProgram.measurable_run_bind_param
                oracle.query observation next hobservationMeas
                (fun current =>
                  scheduledAccuracyZeroObservation_countedStronglyMeasurable
                    q I oracle sigma2 current)
                hnextMeas (fun _ => by trivial)
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            apply MembershipOracleProgram.CountedStronglyMeasurable.bind
              (scheduledAccuracyZeroObservation_countedStronglyMeasurable
                q I oracle sigma2 current)
              (fun _ => by trivial)
            have hnextAt : Measurable fun observed : ℝ =>
                (next (current, observed)).run oracle.query :=
              hnextMeas.comp
                ((measurable_const : Measurable fun _ : ℝ => current).prodMk
                  measurable_id)
            exact hnextAt
      | succ remainingProper =>
          let step (current : AmbientSpace q.n) :=
            scheduledAccuracyMetropolisMarkedBallStep q sigma2 current
          let next (z : AmbientSpace q.n × (Bool × AmbientSpace q.n)) :=
            if z.2.1 then
              match remainingProper with
              | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap 0 z.2.2
              | nextRemaining + 1 =>
                  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                    rawCap (nextRemaining + 1) z.2.2
            else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
              rawCap (remainingProper + 1) z.2.2
          have hstepMeas : Measurable fun current =>
              (step current).run oracle.query := by
            apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
              oracle.query step 1
            · intro current
              exact scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount
                q sigma2 current
            · intro current
              exact scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current
            · rw [show (fun current => (step current).runEstimate oracle.query) =
                  Q by
                    funext current
                    exact runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
                      q I oracle hsigma2 current]
              exact Q.measurable
          have hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query := by
            rintro ⟨current, mark, point⟩
            cases mark with
            | false => exact (ih (remainingProper + 1)).2 point
            | true =>
                cases remainingProper with
                | zero => exact (ih 0).2 point
                | succ nextRemaining => exact (ih (nextRemaining + 1)).2 point
          have hnextMeas : Measurable fun z => (next z).run oracle.query := by
            dsimp only [next]
            rw [show (fun z : AmbientSpace q.n ×
                    (Bool × AmbientSpace q.n) =>
                  (if z.2.1 = true then
                    match remainingProper with
                    | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                        properStride rawCap 0 z.2.2
                    | nextRemaining + 1 =>
                        cappedScheduledAccuracyProperBlockAux q sigma2
                          properStride rawCap (nextRemaining + 1) z.2.2
                  else cappedScheduledAccuracyProperBlockAux q sigma2
                    properStride rawCap (remainingProper + 1) z.2.2).run
                      oracle.query) =
                fun z => if z.2.1 = true then
                  (match remainingProper with
                  | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                      properStride rawCap 0 z.2.2
                  | nextRemaining + 1 =>
                      cappedScheduledAccuracyProperBlockAux q sigma2
                        properStride rawCap (nextRemaining + 1) z.2.2).run
                    oracle.query
                else (cappedScheduledAccuracyProperBlockAux q sigma2
                  properStride rawCap (remainingProper + 1) z.2.2).run
                    oracle.query by
                      funext z
                      split <;> rfl]
            apply Measurable.ite
            · exact (measurable_fst.comp measurable_snd)
                (measurableSet_singleton true)
            · cases remainingProper with
              | zero => exact (ih 0).1.comp (measurable_snd.comp measurable_snd)
              | succ nextRemaining =>
                  exact (ih (nextRemaining + 1)).1.comp
                    (measurable_snd.comp measurable_snd)
            · exact (ih (remainingProper + 1)).1.comp
                (measurable_snd.comp measurable_snd)
          constructor
          · simp only [cappedScheduledAccuracyProperBlockAux]
            change Measurable fun current =>
              ((step current).bind fun result => next (current, result)).run
                oracle.query
            exact MembershipOracleProgram.measurable_run_bind_param
              oracle.query step next hstepMeas
              (fun current =>
                scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                  q I oracle sigma2 current)
              hnextMeas hnext
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            apply MembershipOracleProgram.CountedStronglyMeasurable.bind
              (scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                q I oracle sigma2 current)
              (fun result => hnext (current, result))
            exact hnextMeas.comp (measurable_const.prodMk measurable_id)

theorem cappedScheduledAccuracyProperBlock_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rawCap properStride : ℕ) :
    (Measurable fun current =>
      (cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride current).run
        oracle.query) ∧
    (∀ current,
      (cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride current).CountedStronglyMeasurable
        oracle.query) :=
  cappedScheduledAccuracyProperBlockAux_countedMeasurable
    q I oracle hsigma2 properStride rawCap properStride

/-- Pointwise Bellman bound for the actual schedule-targeted proper block.
The bound is independent of `rawCap`: truncation only removes executions. -/
theorem cappedScheduledAccuracyProperBlockAux_countedQueryCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (properStride : ℕ) : ∀ rawCap remainingProper current,
    countedQueryCost
        ((cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          rawCap remainingProper current).run oracle.query) ≤
      totalLazyProperExpectedRawCost
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2
        remainingProper current + 1 := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let hK : MeasurableSet K := figureOneScheduledPhaseBody_measurable q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let E := totalLazyProperExpectedRawCost K hK delta sigma2
  let Q := lazyProperProposalGaussianAux K hK delta sigma2
  have hstep := one_add_lintegral_totalLazyProperExpectedRawCost_le
    K hK (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      (figureOneScheduledProposalRadius_pos q hsigma2) sigma2
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper current
      simp only [cappedScheduledAccuracyProperBlockAux,
        MembershipOracleProgram.run, countedQueryCost]
      rw [lintegral_dirac' _ measurable_countedQueryCost_integrand]
      simp
  | succ rawCap ih =>
      intro remainingProper current
      cases remainingProper with
      | zero =>
          let observation := scheduledAccuracyZeroObservation q sigma2 current
          let next : ℝ → MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) := fun observed =>
            .pure (some (observed, current))
          have hnext : ∀ observed,
              (next observed).CountedStronglyMeasurable oracle.query := by
            intro observed
            trivial
          have hnextRun : Measurable fun observed =>
              (next observed).run oracle.query := by
            simp only [next, MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <|
                measurable_id.prodMk measurable_const).prodMk measurable_const
          rw [show cappedScheduledAccuracyProperBlockAux q sigma2 properStride
              (rawCap + 1) 0 current = observation.bind next by
                simp [observation, next, cappedScheduledAccuracyProperBlockAux]]
          rw [(scheduledAccuracyZeroObservation_fixedQueryCount
            q sigma2 current).countedQueryCost_bind oracle.query next
              (scheduledAccuracyZeroObservation_stronglyMeasurable
                q I oracle sigma2 current)
              (scheduledAccuracyZeroObservation_countedStronglyMeasurable
                q I oracle sigma2 current) hnext hnextRun]
          have hzero : ∀ observed, countedQueryCost
              ((next observed).run oracle.query) = 0 := by
            intro observed
            simp only [next, MembershipOracleProgram.run, countedQueryCost]
            rw [lintegral_dirac' _ measurable_countedQueryCost_integrand]
            simp
          simp_rw [hzero]
          simp [E, totalLazyProperExpectedRawCost]
      | succ remainingProper =>
          let step := scheduledAccuracyMetropolisMarkedBallStep q sigma2 current
          let next : Bool × AmbientSpace q.n → MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) := fun result =>
            if result.1 then
              match remainingProper with
              | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap 0 result.2
              | nextRemaining + 1 =>
                  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                    rawCap (nextRemaining + 1) result.2
            else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
              rawCap (remainingProper + 1) result.2
          have hnext : ∀ result,
              (next result).CountedStronglyMeasurable oracle.query := by
            rintro ⟨mark, point⟩
            cases mark
            · exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                q I oracle hsigma2 properStride rawCap
                  (remainingProper + 1)).2 point
            · cases remainingProper with
              | zero =>
                  exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                    q I oracle hsigma2 properStride rawCap 0).2 point
              | succ nextRemaining =>
                  exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                    q I oracle hsigma2 properStride rawCap
                      (nextRemaining + 1)).2 point
          have hnextRun : Measurable fun result =>
              (next result).run oracle.query := by
            dsimp only [next]
            rw [show (fun result : Bool × AmbientSpace q.n =>
                (if result.1 = true then
                  match remainingProper with
                  | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                      properStride rawCap 0 result.2
                  | nextRemaining + 1 =>
                      cappedScheduledAccuracyProperBlockAux q sigma2
                        properStride rawCap (nextRemaining + 1) result.2
                else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap (remainingProper + 1) result.2).run oracle.query) =
              fun result => if result.1 = true then
                (match remainingProper with
                | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                    properStride rawCap 0 result.2
                | nextRemaining + 1 =>
                    cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                      rawCap (nextRemaining + 1) result.2).run oracle.query
              else (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                rawCap (remainingProper + 1) result.2).run oracle.query by
                funext result
                split <;> rfl]
            apply Measurable.ite
            · exact measurable_fst (measurableSet_singleton true)
            · cases remainingProper with
              | zero =>
                  exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                    q I oracle hsigma2 properStride rawCap 0).1.comp measurable_snd
              | succ nextRemaining =>
                  exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                    q I oracle hsigma2 properStride rawCap
                      (nextRemaining + 1)).1.comp measurable_snd
            · exact (cappedScheduledAccuracyProperBlockAux_countedMeasurable
                q I oracle hsigma2 properStride rawCap
                  (remainingProper + 1)).1.comp measurable_snd
          rw [show cappedScheduledAccuracyProperBlockAux q sigma2 properStride
              (rawCap + 1) (remainingProper + 1) current = step.bind next by
                rw [cappedScheduledAccuracyProperBlockAux]
                rfl]
          rw [(scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount
            q sigma2 current).countedQueryCost_bind oracle.query next
              (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current)
              (scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                q I oracle sigma2 current) hnext hnextRun]
          rw [runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
            q I oracle hsigma2 current]
          have hmono : (∫⁻ result, countedQueryCost ((next result).run oracle.query)
                ∂Q current) ≤
              ∫⁻ result, E (if result.1 then remainingProper else
                remainingProper + 1) result.2 + 1 ∂Q current := by
            apply lintegral_mono
            rintro ⟨mark, point⟩
            cases mark
            · exact ih (remainingProper + 1) point
            · cases remainingProper with
              | zero => exact ih 0 point
              | succ nextRemaining => exact ih (nextRemaining + 1) point
          have hEmeas : Measurable fun result : Bool × AmbientSpace q.n =>
              E (if result.1 then remainingProper else remainingProper + 1)
                result.2 := by
            rw [show (fun result : Bool × AmbientSpace q.n =>
                E (if result.1 then remainingProper else remainingProper + 1)
                  result.2) = fun result => if result.1 = true then
                    E remainingProper result.2 else
                    E (remainingProper + 1) result.2 by
              funext result
              rcases result with ⟨mark, point⟩
              cases mark <;> rfl]
            exact Measurable.ite (measurable_fst (measurableSet_singleton true))
              ((measurable_totalLazyProperExpectedRawCost K hK delta sigma2
                remainingProper).comp measurable_snd)
              ((measurable_totalLazyProperExpectedRawCost K hK delta sigma2
                (remainingProper + 1)).comp measurable_snd)
          have hresult : (1 : ENNReal) +
                ∫⁻ result, countedQueryCost ((next result).run oracle.query)
                  ∂Q current ≤ E (remainingProper + 1) current + 1 := by
            calc
              (1 : ENNReal) +
                  ∫⁻ result, countedQueryCost ((next result).run oracle.query)
                    ∂Q current ≤
                1 + ∫⁻ result, E (if result.1 then remainingProper else
                  remainingProper + 1) result.2 + 1 ∂Q current := by gcongr
              _ = (1 + ∫⁻ result,
                  E (if result.1 then remainingProper else remainingProper + 1)
                    result.2 ∂Q current) + 1 := by
                rw [lintegral_add_left hEmeas]
                simp only [lintegral_const, measure_univ, one_mul]
                ring
              _ ≤ E (remainingProper + 1) current + 1 := by
                gcongr
                exact hstep remainingProper current
          dsimp only [Q, E, K, delta] at hresult
          have hK_eq : hK = figureOneScheduledPhaseBody_measurable q I sigma2 :=
            Subsingleton.elim _ _
          rw [hK_eq] at hresult
          simpa only [Nat.cast_one] using hresult

theorem cappedScheduledAccuracyProperBlock_countedQueryCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rawCap properStride : ℕ) (current : AmbientSpace q.n) :
    countedQueryCost
        ((cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride
          current).run oracle.query) ≤
      totalLazyProperExpectedRawCost
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledPhaseBody_measurable q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2
        properStride current + 1 := by
  unfold cappedScheduledAccuracyProperBlock
  exact cappedScheduledAccuracyProperBlockAux_countedQueryCost_le
    q I oracle hsigma2 properStride rawCap properStride current

/-- The scheduled proposal remains below the Lovász--Vempala average local
conductance scale of its actual (possibly sub-unit) phase body. -/
theorem figureOneScheduledProposalRadius_le_phaseLVStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneScheduledProposalRadius q sigma2 ≤
      min (Real.sqrt sigma2) (figureOneScheduledPhaseInradius q sigma2) /
        (4096 * Real.sqrt q.n) := by
  let sigma : ℝ := Real.sqrt sigma2
  let L : ℝ := figureOneScheduledAccuracyLog q
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsigma2
  have hnR : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ L := by
    simpa [L] using figureOneScheduledAccuracyLog_one_le q
  have hnL : 1 ≤ (q.n : ℝ) * L := by nlinarith
  have hsqrt1 : 1 ≤ Real.sqrt ((q.n : ℝ) * L) := by
    simpa using Real.sqrt_le_sqrt hnL
  have hsigmaR : sigma ≤ figureOneScheduledPhaseRadius q sigma2 := by
    unfold figureOneScheduledPhaseRadius
    change sigma ≤ 32 * sigma * Real.sqrt ((q.n : ℝ) * L)
    nlinarith
  have hmin : min sigma (figureOneScheduledPhaseInradius q sigma2) =
      min sigma 1 := by
    apply le_antisymm
    · exact le_min (min_le_left _ _)
        ((min_le_right _ _).trans (min_le_left _ _))
    · apply le_min (min_le_left _ _)
      exact le_min (min_le_right _ _) ((min_le_left _ _).trans hsigmaR)
  rw [hmin]
  unfold figureOneScheduledProposalRadius
  change min sigma 1 / (4096 * Real.sqrt ((q.n : ℝ) * L)) ≤
    min sigma 1 / (4096 * Real.sqrt q.n)
  apply div_le_div_of_nonneg_left (le_min hsigma.le zero_le_one)
  · positivity
  · have hmul : (q.n : ℝ) ≤ (q.n : ℝ) * L := by nlinarith
    nlinarith [Real.sqrt_le_sqrt hmul]

theorem half_mul_gaussianWeight_le_scheduledPhaseEllGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ENNReal.ofReal (1 / 2) *
        (∫⁻ x in figureOneScheduledPhaseBody q I sigma2,
          gaussianWeight sigma2 x) ≤
      ellGaussianMeasure
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have h :=
    half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct_radius
      hn2 (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isClosed
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledPhaseInradius_pos q hsigma2)
      (ball_scheduledPhaseInradius_subset q I sigma2)
      hsigma hdelta (figureOneScheduledProposalRadius_le_phaseLVStep q hsigma2)
  simpa [Real.sq_sqrt hsigma2.le] using h

/-- Warm-subprobability cost bound for the executable scheduled block.  This
is the compositional form used by retry continuations. -/
theorem lintegral_cappedScheduledAccuracyProperBlock_countedQueryCost_le_of_isWarm_submeasure
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (rawCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride
          current).run oracle.query) ∂mu ≤
      (properStride : ENNReal) * (M * 2) + mu Set.univ := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let hKm : MeasurableSet K := figureOneScheduledPhaseBody_measurable q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hpoint : ∀ current, countedQueryCost
      ((cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride
        current).run oracle.query) ≤
      totalLazyProperExpectedRawCost K hKm delta sigma2 properStride current + 1 := by
    intro current
    simpa only [K, hKm, delta] using
      cappedScheduledAccuracyProperBlock_countedQueryCost_le
        q I oracle hsigma2 rawCap properStride current
  have hlocal : (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ 2 := by
    have hKc : Convex ℝ K := figureOneScheduledPhaseBody_convex q I sigma2
    have hKb : Bornology.IsBounded K :=
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
    have hK0 : volume K ≠ 0 :=
      figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2
    have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
    have hZ0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
      ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 hdelta sigma2
    have hZtop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
      ellGaussianMeasure_ne_top_cv18
        (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
    have hlambda : ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ x in K, gaussianWeight sigma2 x) ≤
          ellGaussianMeasure K delta sigma2 Set.univ := by
      simpa only [K, delta] using
        half_mul_gaussianWeight_le_scheduledPhaseEllGaussian q I hsigma2
    have hhalf := mul_lintegral_inv_ell_ellGaussianProb_le_one
      hKm hdelta sigma2 hZ0 hZtop hlambda
    have hhalfEq : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [hhalfEq] at hhalf
    calc
      (∫⁻ current, (ell K delta current)⁻¹ ∂pi) =
          2 * ((2 : ENNReal)⁻¹ *
            ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel]
        · simp
        · norm_num
        · norm_num
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := mul_one _
  have h := lintegral_blockCost_le_of_isWarm K hKm delta sigma2 pi
    (ellGaussianProb_compl_eq_zero hKm delta sigma2)
    (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hKm delta sigma2)).invariant
    hwarm properStride 1 2 hlocal
    (fun current => countedQueryCost
      ((cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride
        current).run oracle.query)) hpoint
  simpa [one_mul] using h

#print axioms cappedScheduledAccuracyProperBlock_countedQueryCost_le
#print axioms
  lintegral_cappedScheduledAccuracyProperBlock_countedQueryCost_le_of_isWarm_submeasure

end ArlibCommunity.Algorithms.CV18
