/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperFailure

/-!
# Expected executable cost of one capped proper block

The local raw-proposal cap only truncates a proper block.  Its expected query
count is therefore bounded by the Bellman potential of the untruncated proper
clock, plus the final one-query observation.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

theorem cappedAccuracyProperCollectOne_countedQueryCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (weight : AmbientSpace q.n → ℝ) (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper total current,
    countedQueryCost
        ((cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap remainingProper 1 total current).run oracle.query) ≤
      totalLazyProperExpectedRawCost
        (accuracyPhaseTruncatedBody q I sigma2)
        (accuracyPhaseTruncatedBody_measurable q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 remainingProper current + 1 := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let hK : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let E := totalLazyProperExpectedRawCost K hK delta sigma2
  let Q := lazyProperProposalGaussianAux K hK delta sigma2
  have hstep := one_add_lintegral_totalLazyProperExpectedRawCost_le
    K hK (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      (figureOneProposalRadius_pos q hsigma2) sigma2
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper total current
      simp only [cappedAccuracyProperCollectWeightsAux,
        MembershipOracleProgram.run, countedQueryCost]
      rw [lintegral_dirac' _ measurable_countedQueryCost_integrand]
      simp
  | succ rawCap ih =>
      intro remainingProper total current
      cases remainingProper with
      | zero =>
          let observation := accuracyImportanceObservation q sigma2 weight current
          let next : ℝ → MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) := fun observed =>
            cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
              rawCap properStride 0 (total + observed) current
          have hnext : ∀ observed,
              (next observed).CountedStronglyMeasurable oracle.query := by
            intro observed
            dsimp only [next]
            rw [cappedAccuracyProperCollectWeightsAux]
            trivial
          have hnextRun : Measurable fun observed =>
              (next observed).run oracle.query := by
            simp only [next, cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <|
                (measurable_const.add measurable_id).prodMk measurable_const).prodMk
                  measurable_const
          rw [show cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
              (rawCap + 1) 0 1 total current = observation.bind next by
                simp [observation, next, cappedAccuracyProperCollectWeightsAux]]
          rw [(accuracyImportanceObservation_fixedQueryCount
            q sigma2 weight current).countedQueryCost_bind oracle.query next
              (accuracyImportanceObservation_stronglyMeasurable
                q I oracle sigma2 weight current)
              (accuracyImportanceObservation_countedStronglyMeasurable
                q I oracle sigma2 weight current) hnext hnextRun]
          have hzero : ∀ observed, countedQueryCost
              ((next observed).run oracle.query) = 0 := by
            intro observed
            simp only [next, cappedAccuracyProperCollectWeightsAux,
              MembershipOracleProgram.run, countedQueryCost]
            rw [lintegral_dirac' _ measurable_countedQueryCost_integrand]
            simp
          simp_rw [hzero]
          simp [E, totalLazyProperExpectedRawCost]
      | succ remainingProper =>
          let step := accuracyMetropolisMarkedBallStep q sigma2 current
          let next : Bool × AmbientSpace q.n → MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) := fun result =>
            if result.1 then
              match remainingProper with
              | 0 => cappedAccuracyProperCollectWeightsAux q sigma2 weight
                  properStride rawCap 0 1 total result.2
              | nextRemaining + 1 =>
                  cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride rawCap (nextRemaining + 1) 1 total result.2
            else
              cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
                rawCap (remainingProper + 1) 1 total result.2
          have hnext : ∀ result,
              (next result).CountedStronglyMeasurable oracle.query := by
            rintro ⟨mark, point⟩
            cases mark
            · exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                q I oracle hsigma2 hweight properStride rawCap
                  (remainingProper + 1) 1).2 total point
            · cases remainingProper with
              | zero =>
                  exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                    q I oracle hsigma2 hweight properStride rawCap 0 1).2
                      total point
              | succ nextRemaining =>
                  exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                    q I oracle hsigma2 hweight properStride rawCap
                      (nextRemaining + 1) 1).2 total point
          have hnextRun : Measurable fun result =>
              (next result).run oracle.query := by
            dsimp only [next]
            rw [show (fun result : Bool × AmbientSpace q.n =>
                (if result.1 = true then
                  match remainingProper with
                  | 0 => cappedAccuracyProperCollectWeightsAux q sigma2 weight
                      properStride rawCap 0 1 total result.2
                  | nextRemaining + 1 =>
                      cappedAccuracyProperCollectWeightsAux q sigma2 weight
                        properStride rawCap (nextRemaining + 1) 1 total result.2
                else cappedAccuracyProperCollectWeightsAux q sigma2 weight
                  properStride rawCap (remainingProper + 1) 1 total
                    result.2).run oracle.query) =
              fun result => if result.1 = true then
                (match remainingProper with
                | 0 => cappedAccuracyProperCollectWeightsAux q sigma2 weight
                    properStride rawCap 0 1 total result.2
                | nextRemaining + 1 =>
                    cappedAccuracyProperCollectWeightsAux q sigma2 weight
                      properStride rawCap (nextRemaining + 1) 1 total
                        result.2).run oracle.query
              else (cappedAccuracyProperCollectWeightsAux q sigma2 weight
                properStride rawCap (remainingProper + 1) 1 total
                  result.2).run oracle.query by
                funext result
                split <;> rfl]
            apply Measurable.ite
            · exact measurable_fst (measurableSet_singleton true)
            · cases remainingProper with
              | zero =>
                  exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                    q I oracle hsigma2 hweight properStride rawCap 0 1).1.comp <|
                      measurable_const.prodMk measurable_snd
              | succ nextRemaining =>
                  exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                    q I oracle hsigma2 hweight properStride rawCap
                      (nextRemaining + 1) 1).1.comp <|
                        measurable_const.prodMk measurable_snd
            · exact (cappedAccuracyProperCollectWeightsAux_countedMeasurable
                q I oracle hsigma2 hweight properStride rawCap
                  (remainingProper + 1) 1).1.comp <|
                    measurable_const.prodMk measurable_snd
          rw [show cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
              (rawCap + 1) (remainingProper + 1) 1 total current = step.bind next by
                rw [cappedAccuracyProperCollectWeightsAux]
                rfl]
          rw [(accuracyMetropolisMarkedBallStep_fixedQueryCount
            q sigma2 current).countedQueryCost_bind oracle.query next
              (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current)
              (accuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                q I oracle sigma2 current) hnext hnextRun]
          rw [runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
            q I oracle hsigma2 current]
          have hmono : (∫⁻ result, countedQueryCost ((next result).run oracle.query)
                ∂Q current) ≤
              ∫⁻ result, E (if result.1 then remainingProper else
                remainingProper + 1) result.2 + 1 ∂Q current := by
            apply lintegral_mono
            rintro ⟨mark, point⟩
            cases mark
            · exact ih (remainingProper + 1) total point
            · cases remainingProper with
              | zero => exact ih 0 total point
              | succ nextRemaining => exact ih (nextRemaining + 1) total point
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
          have hK_eq : hK = accuracyPhaseTruncatedBody_measurable q I sigma2 :=
            Subsingleton.elim _ _
          rw [hK_eq] at hresult
          simpa only [Nat.cast_one] using hresult

/-- Warm-start integrated form.  The paper's average local-conductance bound
turns the proper-clock potential into at most two raw membership queries per
requested proper step, up to the warmness factor. -/
theorem lintegral_cappedAccuracyProperCollectOne_countedQueryCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (weight : AmbientSpace q.n → ℝ) (hweight : Measurable weight)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu]
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
          properStride 1 current).run oracle.query) ∂mu ≤
      (properStride : ENNReal) * (M * 2) + 1 := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let hK : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let E := totalLazyProperExpectedRawCost K hK delta sigma2
  have hpoint : ∀ current, countedQueryCost
        ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
          properStride 1 current).run oracle.query) ≤ E properStride current + 1 := by
    intro current
    unfold cappedAccuracyProperCollectWeights
    simpa only [E, K, hK, delta] using
      cappedAccuracyProperCollectOne_countedQueryCost_le
        q I oracle hsigma2 weight hweight properStride rawCap properStride 0 current
  have hfirst : (∫⁻ current, countedQueryCost
        ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
          properStride 1 current).run oracle.query) ∂mu) ≤
      ∫⁻ current, E properStride current + 1 ∂mu := by
    exact lintegral_mono hpoint
  have hEcost : (∫⁻ current, E properStride current ∂mu) ≤
      (properStride : ENNReal) *
        (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
    exact lintegral_totalLazyProperExpectedRawCost_le_of_isWarm
      K hK delta sigma2 pi
        (ellGaussianProb_compl_eq_zero hK delta sigma2)
        (isReversible_lazy
          (isReversible_speedyMetropolisGaussian_prob hK delta sigma2)).invariant
        hwarm properStride
  have hKc : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKb : Bornology.IsBounded K :=
    (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
  have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hZ0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hdelta sigma2
  have hZtop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  have hlambda : ENNReal.ofReal (1 / 2 : ℝ) *
      (∫⁻ x in K, gaussianWeight sigma2 x) ≤
        ellGaussianMeasure K delta sigma2 Set.univ := by
    simpa only [K, delta] using
      half_mul_gaussianWeight_le_accuracyPhaseEllGaussian q I hsigma2
  have hstationary : ENNReal.ofReal (1 / 2 : ℝ) *
      (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ 1 :=
    mul_lintegral_inv_ell_ellGaussianProb_le_one
      hK hdelta sigma2 hZ0 hZtop hlambda
  have hinv : (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ 2 := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [hhalf] at hstationary
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
  calc
    (∫⁻ current, countedQueryCost
        ((cappedAccuracyProperCollectWeights q sigma2 weight rawCap
          properStride 1 current).run oracle.query) ∂mu) ≤
      ∫⁻ current, E properStride current + 1 ∂mu := hfirst
    _ = (∫⁻ current, E properStride current ∂mu) + 1 := by
      rw [lintegral_add_left
        (measurable_totalLazyProperExpectedRawCost K hK delta sigma2 properStride)]
      simp only [lintegral_const, measure_univ, one_mul]
      rfl
    _ ≤ (properStride : ENNReal) *
        (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) + 1 := by
      gcongr
    _ ≤ (properStride : ENNReal) * (M * 2) + 1 := by
      gcongr

end ArlibCommunity.Algorithms.CV18
