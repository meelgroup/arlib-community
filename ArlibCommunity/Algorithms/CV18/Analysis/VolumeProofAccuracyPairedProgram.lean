/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceConcentration
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceMoments

/-! # Paired Rao--Blackwell observations for CV18

The numerator and denominator of the KLS importance ratio must be accumulated
on the same speedy trajectory.  This module supplies that executable paired
collector and proves that every linear projection of its two sums is exactly
the already analysed scalar collector.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Associativity of the syntax-level oracle-program bind. -/
theorem MembershipOracleProgram.bind_assoc_cv18
    {n : ℕ} {A B C : Type}
    (program : MembershipOracleProgram n A)
    (next : A → MembershipOracleProgram n B)
    (last : B → MembershipOracleProgram n C) :
    (program.bind next).bind last =
      program.bind (fun value => (next value).bind last) := by
  induction program with
  | pure value => rfl
  | query point branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext answer
      exact ih answer
  | randomNat law branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext seed
      exact ih seed
  | randomPoint law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext point
      exact ih point
  | randomReal law hprob branch ih =>
      simp only [MembershipOracleProgram.bind]
      congr 1
      funext value
      exact ih value

/-- One membership query returns both the importance numerator contribution
and its matching acceptance denominator contribution. -/
noncomputable def accuracyImportancePairObservation (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) : MembershipOracleProgram q.n (ℝ × ℝ) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .pure <| if inside = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2 then
      let accept :=
        (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target).toReal
      (accept * weight target, accept)
    else (0, 0)

theorem accuracyImportancePairObservation_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (current : AmbientSpace q.n) :
    (accuracyImportancePairObservation q sigma2 weight current).QueryBound 1 := by
  simp only [accuracyImportancePairObservation]
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

theorem runEstimate_accuracyImportancePairObservation
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) :
    (accuracyImportancePairObservation q sigma2 weight current).runEstimate
        oracle.query =
      Measure.dirac
        (accuracyImportanceWeight q I sigma2 weight current,
          accuracyAcceptanceWeight q I sigma2 current) := by
  let c := accuracyScaleFactor q
  let target : AmbientSpace q.n := c⁻¹ • current
  have heligible :
      (oracle.query target = true ∧
        ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
        ‖target‖ ≤ accuracyPhaseRadius q sigma2) ↔
      target ∈ accuracyPhaseTruncatedBody q I sigma2 :=
    oracle_and_radii_iff_mem_accuracyPhaseTruncatedBody q I oracle sigma2 target
  simp only [accuracyImportancePairObservation,
    MembershipOracleProgram.runEstimate]
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
    · unfold accuracyImportanceWeight accuracyAcceptanceWeight
        accuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem ht, ENNReal.toReal_zero, zero_mul]
    · unfold accuracyAcceptanceWeight accuracyGaussianRejectionAcceptance
      rw [Set.indicator_of_notMem ht, ENNReal.toReal_zero]

theorem accuracyImportancePairObservation_stronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (current : AmbientSpace q.n) :
    (accuracyImportancePairObservation q sigma2 weight current).StronglyMeasurable
      oracle.query := by
  simp [accuracyImportancePairObservation,
    MembershipOracleProgram.StronglyMeasurable]

/-- Every linear functional of one paired observation is exactly the scalar
importance observation for the corresponding affine weight. -/
theorem accuracyImportancePairObservation_bind_linear
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (current : AmbientSpace q.n)
    (a b : ℝ) {R : Type} (next : ℝ → MembershipOracleProgram q.n R) :
    (accuracyImportancePairObservation q sigma2 weight current).bind
        (fun observed => next (a * observed.1 + b * observed.2)) =
      (accuracyImportanceObservation q sigma2
        (fun y => a * weight y + b) current).bind next := by
  unfold accuracyImportancePairObservation accuracyImportanceObservation
  simp only [MembershipOracleProgram.bind]
  congr 1
  funext inside
  by_cases h : inside = true ∧
      ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
        Real.sqrt (terminalVariance q) ∧
      ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
        accuracyPhaseRadius q sigma2
  · simp only [h, if_true]
    simp
    ring
  · simp only [h, if_false]
    congr 1
    ring

/-- Globally capped proper-step collector with a shared numerator-denominator
observation at each retained state. -/
noncomputable def cappedAccuracyProperCollectPairsAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℕ → (ℝ × ℝ) → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option ((ℝ × ℝ) × AmbientSpace q.n))
  | _, _, 0, total, current => .pure (some (total, current))
  | 0, _, _ + 1, _, _ => .pure none
  | rawCap + 1, 0, samples + 1, total, current =>
      (accuracyImportancePairObservation q sigma2 weight current).bind fun observed =>
        cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
          rawCap properStride samples
            (total.1 + observed.1, total.2 + observed.2) current
  | rawCap + 1, remainingProper + 1, samples + 1, total, current =>
      (accuracyMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        if result.1 then
          match remainingProper with
          | 0 =>
              cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
                rawCap 0 (samples + 1) total result.2
          | nextRemaining + 1 =>
              cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
                rawCap (nextRemaining + 1) (samples + 1) total result.2
        else
          cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
            rawCap (remainingProper + 1) (samples + 1) total result.2
termination_by rawCap remainingProper samples total current => (rawCap, samples)

noncomputable def cappedAccuracyProperCollectPairs (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ((ℝ × ℝ) × AmbientSpace q.n)) :=
  cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
    rawCap properStride samples (0, 0) current

theorem cappedAccuracyProperCollectPairsAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current,
    (cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
      rawCap remainingProper samples total current).QueryBound rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples total current
      cases samples <;>
        simp only [cappedAccuracyProperCollectPairsAux] <;> exact .pure _ 0
  | succ rawCap ih =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectPairsAux]
          exact .pure _ (rawCap + 1)
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectPairsAux]
              have h := (accuracyImportancePairObservation_queryBound
                q sigma2 weight current).bind (fun observed =>
                  ih properStride samples
                    (total.1 + observed.1, total.2 + observed.2) current)
              simpa [Nat.add_comm] using h
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectPairsAux]
              simpa [Nat.add_comm] using
                (accuracyMetropolisMarkedBallStep_queryBound
                  q sigma2 current).bind (fun result => by
                    by_cases hmark : result.1 = true
                    · simp only [hmark, if_true]
                      cases remainingProper with
                      | zero => exact ih 0 (samples + 1) total result.2
                      | succ nextRemaining =>
                          exact ih (nextRemaining + 1) (samples + 1) total result.2
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hmark
                      simp only [hfalse, if_false]
                      exact ih (remainingProper + 1) (samples + 1) total result.2)

theorem cappedAccuracyProperCollectPairs_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n) :
    (cappedAccuracyProperCollectPairs q sigma2 weight rawCap properStride
      samples current).QueryBound rawCap :=
  cappedAccuracyProperCollectPairsAux_queryBound q sigma2 weight properStride
    rawCap properStride samples (0, 0) current

/-- Parameterized measurability and pointwise interpreter measurability for
the paired collector. -/
theorem cappedAccuracyProperCollectPairsAux_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (properStride : ℕ) : ∀ rawCap remainingProper samples,
    (Measurable fun state : (ℝ × ℝ) × AmbientSpace q.n =>
      (cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
        rawCap remainingProper samples state.1 state.2).runEstimate oracle.query) ∧
    (∀ total current,
      (cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
        rawCap remainingProper samples total current).StronglyMeasurable
          oracle.query) := by
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
    (accuracyPhaseTruncatedBody q I sigma2)
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  have hpair : Measurable fun current : AmbientSpace q.n =>
      (accuracyImportanceWeight q I sigma2 weight current,
        accuracyAcceptanceWeight q I sigma2 current) :=
    (measurable_accuracyImportanceWeight q I sigma2 hweight).prodMk
      (measurable_accuracyAcceptanceWeight q I sigma2)
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyProperCollectPairsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            rw [cappedAccuracyProperCollectPairsAux]
            trivial
      | succ samples =>
          constructor
          · simp only [cappedAccuracyProperCollectPairsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp measurable_const
          · intro total current
            rw [cappedAccuracyProperCollectPairsAux]
            trivial
  | succ rawCap ih =>
      intro remainingProper samples
      cases samples with
      | zero =>
          constructor
          · simp only [cappedAccuracyProperCollectPairsAux,
              MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_fst.prodMk measurable_snd
          · intro total current
            rw [cappedAccuracyProperCollectPairsAux]
            trivial
      | succ samples =>
          cases remainingProper with
          | zero =>
              let next (total : ℝ × ℝ) (current : AmbientSpace q.n)
                  (observed : ℝ × ℝ) :=
                cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
                  rawCap properStride samples
                    (total.1 + observed.1, total.2 + observed.2) current
              have hnextStrong : ∀ total current observed,
                  (next total current observed).StronglyMeasurable oracle.query := by
                intro total current observed
                exact (ih properStride samples).2 _ _
              have hnextRun : ∀ total current, Measurable fun observed =>
                  (next total current observed).runEstimate oracle.query := by
                intro total current
                exact (ih properStride samples).1.comp <|
                  (((measurable_const : Measurable fun observed : ℝ × ℝ =>
                      total.1).add measurable_fst).prodMk
                    ((measurable_const : Measurable fun observed : ℝ × ℝ =>
                      total.2).add measurable_snd)).prodMk measurable_const
              have hsemantic : ∀ total current,
                  (cappedAccuracyProperCollectPairsAux q sigma2 weight
                    properStride (rawCap + 1) 0 (samples + 1)
                      total current).runEstimate oracle.query =
                    (next total current
                      (accuracyImportanceWeight q I sigma2 weight current,
                        accuracyAcceptanceWeight q I sigma2 current)).runEstimate
                          oracle.query := by
                intro total current
                simp only [cappedAccuracyProperCollectPairsAux]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total current)
                  (accuracyImportancePairObservation_stronglyMeasurable
                    q I oracle sigma2 weight current)
                  (hnextStrong total current) (hnextRun total current)]
                rw [runEstimate_accuracyImportancePairObservation
                  q I oracle sigma2 weight current]
                rw [Measure.dirac_bind (hnextRun total current)]
              constructor
              · rw [show (fun state : (ℝ × ℝ) × AmbientSpace q.n =>
                    (cappedAccuracyProperCollectPairsAux q sigma2 weight
                      properStride (rawCap + 1) 0 (samples + 1)
                        state.1 state.2).runEstimate oracle.query) =
                  fun state =>
                    (next state.1 state.2
                      (accuracyImportanceWeight q I sigma2 weight state.2,
                        accuracyAcceptanceWeight q I sigma2 state.2)).runEstimate
                          oracle.query by
                    funext state
                    exact hsemantic state.1 state.2]
                exact (ih properStride samples).1.comp <| by
                  exact ((((measurable_fst.comp measurable_fst).add
                        (measurable_fst.comp (hpair.comp measurable_snd))).prodMk
                      ((measurable_snd.comp measurable_fst).add
                        (measurable_snd.comp (hpair.comp measurable_snd)))).prodMk
                    measurable_snd)
              · intro total current
                simp only [cappedAccuracyProperCollectPairsAux]
                exact (accuracyImportancePairObservation_stronglyMeasurable
                  q I oracle sigma2 weight current).bind
                    (hnextStrong total current) (hnextRun total current)
          | succ remainingProper =>
              let next (total : ℝ × ℝ) : Bool × AmbientSpace q.n →
                  MembershipOracleProgram q.n
                    (Option ((ℝ × ℝ) × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  match remainingProper with
                  | 0 =>
                      cappedAccuracyProperCollectPairsAux q sigma2 weight
                        properStride rawCap 0 (samples + 1) total result.2
                  | nextRemaining + 1 =>
                      cappedAccuracyProperCollectPairsAux q sigma2 weight
                        properStride rawCap (nextRemaining + 1) (samples + 1)
                          total result.2
                else
                  cappedAccuracyProperCollectPairsAux q sigma2 weight
                    properStride rawCap (remainingProper + 1) (samples + 1)
                      total result.2
              have hnextStrong : ∀ total result,
                  (next total result).StronglyMeasurable oracle.query := by
                intro total
                rintro ⟨mark, state⟩
                cases mark with
                | false => exact (ih (remainingProper + 1)
                    (samples + 1)).2 _ _
                | true =>
                    cases remainingProper with
                    | zero => exact (ih 0 (samples + 1)).2 _ _
                    | succ nextRemaining =>
                        exact (ih (nextRemaining + 1) (samples + 1)).2 _ _
              have hnextJoint : Measurable fun p :
                  ((ℝ × ℝ) × AmbientSpace q.n) ×
                    (Bool × AmbientSpace q.n) =>
                  (next p.1.1 p.2).runEstimate oracle.query := by
                rw [show (fun p : ((ℝ × ℝ) × AmbientSpace q.n) ×
                      (Bool × AmbientSpace q.n) =>
                    (next p.1.1 p.2).runEstimate oracle.query) =
                    fun p => if p.2.1 = true then
                      match remainingProper with
                      | 0 =>
                          (cappedAccuracyProperCollectPairsAux q sigma2 weight
                            properStride rawCap 0 (samples + 1) p.1.1 p.2.2).runEstimate
                              oracle.query
                      | nextRemaining + 1 =>
                          (cappedAccuracyProperCollectPairsAux q sigma2 weight
                            properStride rawCap (nextRemaining + 1) (samples + 1)
                              p.1.1 p.2.2).runEstimate oracle.query
                    else
                      (cappedAccuracyProperCollectPairsAux q sigma2 weight
                        properStride rawCap (remainingProper + 1) (samples + 1)
                          p.1.1 p.2.2).runEstimate oracle.query by
                    funext p
                    by_cases hmark : p.2.1 = true
                    · simp only [next, hmark, if_true]
                      cases remainingProper <;> rfl
                    · have hfalse : p.2.1 = false :=
                        Bool.eq_false_of_not_eq_true hmark
                      simp only [next, hfalse, Bool.false_eq_true, if_false]]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (ih 0 (samples + 1)).1.comp <|
                        (measurable_fst.comp measurable_fst).prodMk
                          (measurable_snd.comp measurable_snd)
                  | succ nextRemaining =>
                      exact (ih (nextRemaining + 1) (samples + 1)).1.comp <|
                        (measurable_fst.comp measurable_fst).prodMk
                          (measurable_snd.comp measurable_snd)
                · exact (ih (remainingProper + 1) (samples + 1)).1.comp <|
                    (measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp measurable_snd)
              have hnextRun : ∀ total, Measurable fun result =>
                  (next total result).runEstimate oracle.query := by
                intro total
                exact hnextJoint.comp <|
                  (((show Measurable
                      (fun _result : Bool × AmbientSpace q.n => total) from
                        measurable_const).prodMk measurable_snd).prodMk measurable_id)
              have hstepRun : Measurable fun current =>
                  (accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
                    oracle.query := by
                rw [show (fun current =>
                    (accuracyMetropolisMarkedBallStep q sigma2 current).runEstimate
                      oracle.query) = fun current => Q current by
                  funext current
                  exact runEstimate_accuracyMetropolisMarkedBallStep_eq_lazyProperAux
                    q I oracle hsigma2 current]
                exact Q.measurable
              have hcombined : Measurable fun state :
                  (ℝ × ℝ) × AmbientSpace q.n =>
                  ((accuracyMetropolisMarkedBallStep q sigma2 state.2).runEstimate
                    oracle.query).bind fun result =>
                      (next state.1 result).runEstimate oracle.query := by
                exact measurable_measure_bind_param_variable
                  (hstepRun.comp measurable_snd)
                  (fun state =>
                    MembershipOracleProgram.runEstimate_isProbabilityMeasure
                      oracle.query _
                      (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                        q I oracle sigma2 state.2).estimateMeasurable)
                  hnextJoint
              constructor
              · rw [show (fun state : (ℝ × ℝ) × AmbientSpace q.n =>
                    (cappedAccuracyProperCollectPairsAux q sigma2 weight
                      properStride (rawCap + 1) (remainingProper + 1)
                        (samples + 1) state.1 state.2).runEstimate oracle.query) =
                  fun state =>
                    ((accuracyMetropolisMarkedBallStep q sigma2 state.2).runEstimate
                      oracle.query).bind fun result =>
                        (next state.1 result).runEstimate oracle.query by
                    funext state
                    simp only [cappedAccuracyProperCollectPairsAux]
                    exact MembershipOracleProgram.runEstimate_bind oracle.query _
                      (next state.1)
                      (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                        q I oracle sigma2 state.2)
                      (hnextStrong state.1) (hnextRun state.1)]
                exact hcombined
              · intro total current
                simp only [cappedAccuracyProperCollectPairsAux]
                exact (accuracyMetropolisMarkedBallStep_stronglyMeasurable
                  q I oracle sigma2 current).bind
                    (hnextStrong total) (hnextRun total)

theorem cappedAccuracyProperCollectPairs_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) :
    (Measurable fun current =>
      (cappedAccuracyProperCollectPairs q sigma2 weight rawCap properStride
        samples current).runEstimate oracle.query) ∧
    (∀ current,
      (cappedAccuracyProperCollectPairs q sigma2 weight rawCap properStride
        samples current).StronglyMeasurable oracle.query) := by
  have h := cappedAccuracyProperCollectPairsAux_measurable_and_strong
    q I oracle hsigma2 hweight properStride rawCap properStride samples
  exact ⟨h.1.comp (measurable_const.prodMk measurable_id),
    fun current => h.2 (0, 0) current⟩

/-- Apply a linear functional to the accumulated pair and keep its endpoint. -/
def accuracyPairLinearOutput {n : ℕ} (a b : ℝ) :
    Option ((ℝ × ℝ) × AmbientSpace n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some output => some (a * output.1.1 + b * output.1.2, output.2)

theorem measurable_accuracyPairLinearOutput {n : ℕ} (a b : ℝ) :
    Measurable (accuracyPairLinearOutput (n := n) a b) := by
  have hsome : Measurable fun output : (ℝ × ℝ) × AmbientSpace n =>
      some (a * output.1.1 + b * output.1.2, output.2) := by
    exact measurable_some.comp (by fun_prop)
  convert Measurable.optionElim none hsome using 1
  funext output
  cases output <;> rfl

theorem cappedAccuracyProperCollectPairsAux_bind_linear
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) (a b : ℝ) :
    ∀ rawCap remainingProper samples total current,
    (cappedAccuracyProperCollectPairsAux q sigma2 weight properStride
      rawCap remainingProper samples total current).bind
        (fun output => .pure (accuracyPairLinearOutput a b output)) =
      cappedAccuracyProperCollectWeightsAux q sigma2
        (fun y => a * weight y + b) properStride rawCap remainingProper samples
          (a * total.1 + b * total.2) current := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rcases total with ⟨num, den⟩
          simp [cappedAccuracyProperCollectPairsAux,
            cappedAccuracyProperCollectWeightsAux, accuracyPairLinearOutput,
            MembershipOracleProgram.bind]
      | succ samples =>
          rcases total with ⟨num, den⟩
          simp [cappedAccuracyProperCollectPairsAux,
            cappedAccuracyProperCollectWeightsAux,
            accuracyPairLinearOutput,
            MembershipOracleProgram.bind]
  | succ rawCap ih =>
      intro remainingProper samples total current
      cases samples with
      | zero =>
          rcases total with ⟨num, den⟩
          simp [cappedAccuracyProperCollectPairsAux,
            cappedAccuracyProperCollectWeightsAux, accuracyPairLinearOutput,
            MembershipOracleProgram.bind]
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectPairsAux,
                cappedAccuracyProperCollectWeightsAux]
              rw [MembershipOracleProgram.bind_assoc_cv18]
              simp_rw [ih]
              let next : ℝ → MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n)) := fun observed =>
                cappedAccuracyProperCollectWeightsAux q sigma2
                  (fun y => a * weight y + b) properStride rawCap properStride
                    samples (a * total.1 + b * total.2 + observed) current
              rw [show (fun observed : ℝ × ℝ =>
                    cappedAccuracyProperCollectWeightsAux q sigma2
                      (fun y => a * weight y + b) properStride rawCap
                        properStride samples
                        (a * (total.1 + observed.1) +
                          b * (total.2 + observed.2)) current) =
                  fun observed => next (a * observed.1 + b * observed.2) by
                    funext observed
                    dsimp only [next]
                    apply congrArg (fun total : ℝ =>
                      cappedAccuracyProperCollectWeightsAux q sigma2
                        (fun y => a * weight y + b) properStride rawCap
                          properStride samples total current)
                    ring]
              exact accuracyImportancePairObservation_bind_linear
                q sigma2 weight current a b next
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectPairsAux,
                cappedAccuracyProperCollectWeightsAux]
              rw [MembershipOracleProgram.bind_assoc_cv18]
              congr 1
              funext result
              by_cases hmark : result.1 = true
              · simp only [hmark, if_true]
                cases remainingProper with
                | zero => exact ih 0 (samples + 1) total result.2
                | succ nextRemaining =>
                    exact ih (nextRemaining + 1) (samples + 1) total result.2
              · have hfalse : result.1 = false :=
                  Bool.eq_false_of_not_eq_true hmark
                simp only [hfalse, if_false]
                exact ih (remainingProper + 1) (samples + 1) total result.2

theorem cappedAccuracyProperCollectPairs_bind_linear
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (rawCap properStride samples : ℕ)
    (current : AmbientSpace q.n) (a b : ℝ) :
    (cappedAccuracyProperCollectPairs q sigma2 weight rawCap properStride
      samples current).bind
        (fun output => .pure (accuracyPairLinearOutput a b output)) =
      cappedAccuracyProperCollectWeights q sigma2
        (fun y => a * weight y + b) rawCap properStride samples current := by
  simpa [cappedAccuracyProperCollectPairs,
    cappedAccuracyProperCollectWeights] using
      cappedAccuracyProperCollectPairsAux_bind_linear q sigma2 weight
        properStride a b rawCap properStride samples (0, 0) current

/-- Measure semantics of the syntax-level linear projection. -/
theorem runEstimate_cappedAccuracyProperCollectPairs_map_linear
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (rawCap properStride samples : ℕ) (current : AmbientSpace q.n)
    (a b : ℝ) :
    ((cappedAccuracyProperCollectPairs q sigma2 weight rawCap properStride
      samples current).runEstimate oracle.query).map
        (accuracyPairLinearOutput a b) =
      (cappedAccuracyProperCollectWeights q sigma2
        (fun y => a * weight y + b) rawCap properStride samples current).runEstimate
          oracle.query := by
  let pairProgram := cappedAccuracyProperCollectPairs q sigma2 weight rawCap
    properStride samples current
  let project := fun output =>
    (MembershipOracleProgram.pure (accuracyPairLinearOutput a b output) :
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)))
  have hpair := (cappedAccuracyProperCollectPairs_measurable_and_strong
    q I oracle hsigma2 hweight rawCap properStride samples).2 current
  have hprojectStrong : ∀ output, (project output).StronglyMeasurable
      oracle.query := by intro output; trivial
  have hprojectRun : Measurable fun output =>
      (project output).runEstimate oracle.query := by
    exact Measure.measurable_dirac.comp
      (measurable_accuracyPairLinearOutput a b)
  have hrun := MembershipOracleProgram.runEstimate_bind oracle.query
    pairProgram project hpair hprojectStrong hprojectRun
  rw [show pairProgram.bind project =
      cappedAccuracyProperCollectWeights q sigma2
        (fun y => a * weight y + b) rawCap properStride samples current by
    simpa [pairProgram, project] using
      cappedAccuracyProperCollectPairs_bind_linear q sigma2 weight rawCap
        properStride samples current a b] at hrun
  simp only [project, MembershipOracleProgram.runEstimate] at hrun
  rw [Measure.bind_dirac_eq_map _
    (measurable_accuracyPairLinearOutput a b)] at hrun
  exact hrun.symm

/-- Warm-start spectral concentration for any linear projection of the
successful paired collector.  Centered numerator-minus-mean-times-denominator
and the denominator itself are the two applications used by a phase. -/
theorem bind_accuracyImportancePairProgram_success_linear_deviation_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (a b : ℝ) (proposalCap samples : ℕ)
    {mu : Measure (AmbientSpace q.n)} {M : ENNReal}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (m : ℝ)
    (hmean : ∫ x,
        (accuracyImportanceWeight q I sigma2
          (fun y => a * weight y + b) x - m)
        ∂Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2 = 0)
    (hmem : MemLp (fun x =>
        accuracyImportanceWeight q I sigma2
          (fun y => a * weight y + b) x - m) 2
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x,
      |accuracyImportanceWeight q I sigma2
        (fun y => a * weight y + b) x - m| ≤ B)
    {c : ℝ} (hc : 0 < c) :
    (mu.bind fun current =>
      (cappedAccuracyProperCollectPairs q sigma2 weight
        (proposalCap + samples) 1 samples current).runEstimate oracle.query)
      (optionSomeEvent {output | c ≤
        |a * output.1.1 + b * output.1.2 - (samples : ℝ) * m|}) ≤
      M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((Arlib.MarkovChains.spectralGap
          (Arlib.MarkovChains.lazy
            (Arlib.MarkovChains.speedyMetropolisGaussian
              (accuracyPhaseTruncatedBody q I sigma2)
              (figureOneProposalRadius q sigma2) sigma2))
          (Arlib.MarkovChains.ellGaussianProb
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))⁻¹ *
          Arlib.MarkovChains.varianceReal
            (Arlib.MarkovChains.ellGaussianProb
              (accuracyPhaseTruncatedBody q I sigma2)
              (figureOneProposalRadius q sigma2) sigma2)
            (fun x => accuracyImportanceWeight q I sigma2
              (fun y => a * weight y + b) x - m)))) / c ^ 2) := by
  let pairLaw : AmbientSpace q.n →
      Measure (Option ((ℝ × ℝ) × AmbientSpace q.n)) := fun current =>
    (cappedAccuracyProperCollectPairs q sigma2 weight
      (proposalCap + samples) 1 samples current).runEstimate oracle.query
  let scalarLaw : AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun current =>
    (cappedAccuracyProperCollectWeights q sigma2
      (fun y => a * weight y + b) (proposalCap + samples) 1 samples current).runEstimate
        oracle.query
  let project := accuracyPairLinearOutput (n := q.n) a b
  let E : Set (Option (ℝ × AmbientSpace q.n)) :=
    optionSomeEvent {output | c ≤ |output.1 - (samples : ℝ) * m|}
  let Epair : Set (Option ((ℝ × ℝ) × AmbientSpace q.n)) :=
    optionSomeEvent {output | c ≤
      |a * output.1.1 + b * output.1.2 - (samples : ℝ) * m|}
  have hpairMeas : Measurable pairLaw := by
    exact (cappedAccuracyProperCollectPairs_measurable_and_strong
      q I oracle hsigma2 hweight (proposalCap + samples) 1 samples).1
  have hproject : Measurable project :=
    measurable_accuracyPairLinearOutput a b
  have hE : MeasurableSet E := by
    exact measurableSet_optionSomeEvent <|
      measurableSet_le measurable_const (by fun_prop)
  have hpre : project ⁻¹' E = Epair := by
    ext output
    cases output <;> rfl
  have hmap : (mu.bind pairLaw).map project = mu.bind scalarLaw := by
    rw [map_bind_eq_bind_map_of_measurable mu hpairMeas hproject]
    apply Measure.bind_congr_right
    filter_upwards with current
    exact runEstimate_cappedAccuracyProperCollectPairs_map_linear
      q I oracle hsigma2 hweight (proposalCap + samples) 1 samples current a b
  have hscalar :=
    bind_accuracyImportanceProgram_success_deviation_le_of_isWarm
      q I oracle hsigma2
      (weight := fun y => a * weight y + b) (by fun_prop)
      proposalCap samples hwarm m hmean hmem hB hbound hc
  change (mu.bind pairLaw) Epair ≤ _
  rw [← hpre, ← Measure.map_apply hproject hE, hmap]
  simpa [scalarLaw, E] using hscalar

end ArlibCommunity.Algorithms.CV18
