/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportance

/-! # Finite executable importance phases for CV18

This module implements the Rao--Blackwellized KLS phase with the same marked
proper-proposal clock used by the faithful rejection implementation.  It
collects an importance numerator and acceptance denominator on two
unconditioned speedy trajectories and divides their sums.  Each trajectory
has its own deterministic raw-query cap.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- One deterministic (Rao--Blackwellized) KLS observation.  Membership of
the scaled target is obtained only through the oracle query. -/
noncomputable def accuracyImportanceObservation (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) : MembershipOracleProgram q.n ℝ :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .pure <| if inside = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2 then
      (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target).toReal *
        weight target
    else 0

theorem accuracyImportanceObservation_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (current : AmbientSpace q.n) :
    (accuracyImportanceObservation q sigma2 weight current).QueryBound 1 := by
  simp only [accuracyImportanceObservation]
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

theorem runEstimate_accuracyImportanceObservation
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) :
    (accuracyImportanceObservation q sigma2 weight current).runEstimate
        oracle.query =
      Measure.dirac (accuracyImportanceWeight q I sigma2 weight current) := by
  let c := accuracyScaleFactor q
  let target : AmbientSpace q.n := c⁻¹ • current
  have heligible :
      (oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2) ↔
      target ∈ accuracyPhaseTruncatedBody q I sigma2 :=
    oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody q I oracle sigma2 target
  simp only [accuracyImportanceObservation, MembershipOracleProgram.runEstimate]
  dsimp only [c, target] at heligible ⊢
  by_cases ht : (accuracyScaleFactor q)⁻¹ • current ∈
      accuracyPhaseTruncatedBody q I sigma2
  · have hcond := heligible.mpr ht
    simp only [hcond, if_true]
    congr 2
    unfold accuracyImportanceWeight accuracyAcceptanceWeight
      accuracyGaussianRejectionAcceptance
    rw [Set.indicator_of_mem ht]
    simp
  · have hcond : ¬ (oracle.query ((accuracyScaleFactor q)⁻¹ • current) = true ∧
        ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
          Real.sqrt (terminalVariance q) ∧
        ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
          accuracyPhaseRadius q sigma2) := fun h => ht (heligible.mp h)
    simp only [hcond, if_false]
    congr 2
    unfold accuracyImportanceWeight accuracyAcceptanceWeight
      accuracyGaussianRejectionAcceptance
    rw [Set.indicator_of_notMem ht, ENNReal.toReal_zero, zero_mul]

theorem accuracyImportanceObservation_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) :
    (accuracyImportanceObservation q sigma2 weight current).StronglyMeasurable
      oracle.query := by
  simp [accuracyImportanceObservation,
    MembershipOracleProgram.StronglyMeasurable]

/-- Accuracy-body version of the globally capped proper-step collector. -/
noncomputable def cappedAccuracyProperCollectWeightsAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, _, 0, total, current => .pure (some (total, current))
  | 0, _, _ + 1, _, _ => .pure none
  | rawCap + 1, 0, samples + 1, total, current =>
      (accuracyImportanceObservation q sigma2 weight current).bind fun observed =>
        cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap properStride samples (total + observed) current
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (accuracyMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        if result.1 then
          match remainingProper with
          | 0 =>
              cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
                rawCap 0 (samples + 1) total result.2
          | nextRemaining + 1 =>
              cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
                rawCap (nextRemaining + 1) (samples + 1) total result.2
        else
          cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
            rawCap (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedAccuracyProperCollectWeights (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
    rawCap properStride samples 0 current

theorem cappedAccuracyProperCollectWeightsAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
    (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
      rawCap remainingProper samples total current).QueryBound rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux]
          exact .pure _ 0
      | succ samples =>
          rw [cappedAccuracyProperCollectWeightsAux]
          exact .pure _ 0
  | succ rawCap ih =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux]
          exact .pure _ (rawCap + 1)
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux]
              have h := (accuracyImportanceObservation_queryBound
                q sigma2 weight current).bind (fun observed =>
                  ih properStride samples (total + observed) current)
              simpa [Nat.add_comm] using h
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectWeightsAux]
              simpa [Nat.add_comm] using
                (accuracyMetropolisMarkedBallStep_queryBound
                  q sigma2 current).bind (fun result => by
                    by_cases hmark : result.1 = true
                    · simp only [hmark, if_true]
                      cases remainingProper with
                      | zero =>
                          exact ih 0 (samples + 1) total result.2
                      | succ nextRemaining =>
                          exact ih (nextRemaining + 1) (samples + 1) total result.2
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hmark
                      simp only [hfalse, if_false]
                      exact ih (remainingProper + 1) (samples + 1) total result.2)

theorem cappedAccuracyProperCollectWeights_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (cappedAccuracyProperCollectWeights q sigma2 weight rawCap properStride
      samples current).QueryBound rawCap :=
  cappedAccuracyProperCollectWeightsAux_queryBound q sigma2 weight properStride
    rawCap properStride samples 0 current

/-- Two capped proper trajectories implementing a self-normalized KLS
importance estimate.  The sample-count factors cancel in the quotient. -/
noncomputable def accuracyImportanceRatioEstimate (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (cappedAccuracyProperCollectWeights q sigma2
      weight
      rawCap properStride samples current).bind fun numerator =>
    match numerator with
    | none => .pure none
    | some (num, middle) =>
        (cappedAccuracyProperCollectWeights q sigma2
          (fun _ => 1)
          rawCap properStride samples middle).bind fun denominator =>
          .pure <| match denominator with
          | none => none
          | some (den, last) => some (num / den, last)

theorem accuracyImportanceRatioEstimate_queryBound (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (accuracyImportanceRatioEstimate q sigma2 weight rawCap properStride
      samples current).QueryBound (2 * rawCap) := by
  unfold accuracyImportanceRatioEstimate
  have hfirst := (cappedAccuracyProperCollectWeights_queryBound
    q sigma2 weight rawCap properStride samples current).bind
      (fun numerator => by
        change (match numerator with
          | none => MembershipOracleProgram.pure none
          | some (num, middle) =>
              (cappedAccuracyProperCollectWeights q sigma2 (fun _ => 1)
                rawCap properStride samples middle).bind fun denominator =>
                MembershipOracleProgram.pure <| match denominator with
                | none => none
                | some (den, last) => some (num / den, last)).QueryBound rawCap
        cases numerator with
        | none => exact .pure _ rawCap
        | some value =>
            rcases value with ⟨num, middle⟩
            simpa using (cappedAccuracyProperCollectWeights_queryBound
              q sigma2 (fun _ => 1) rawCap properStride samples middle).bind
                (fun denominator => .pure
                  (match denominator with
                  | none => none
                  | some (den, last) => some (num / den, last)) 0))
  simpa [two_mul] using hfirst

end ArlibCommunity.Algorithms.CV18
