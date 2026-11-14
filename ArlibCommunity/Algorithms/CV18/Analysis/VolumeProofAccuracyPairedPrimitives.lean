/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPairedCost

/-! # Structural facts for the paired CV18 primitive package -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

theorem measurable_accuracyPairedRatioOutput {n : ℕ} :
    Measurable (accuracyPairedRatioOutput (n := n)) := by
  have hsome : Measurable fun output : (ℝ × ℝ) × AmbientSpace n =>
      if output.1.2 = 0 then none
      else some (output.1.1 / output.1.2, output.2) := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact measurable_const
    · exact measurable_some.comp (by fun_prop)
  convert Measurable.optionElim none hsome using 1
  funext output
  cases output <;> rfl

theorem measurable_accuracyPairedUniformOutput {n : ℕ} :
    Measurable (accuracyPairedUniformOutput (n := n)) := by
  have hsome : Measurable fun output : (ℝ × ℝ) × AmbientSpace n =>
      if output.1.2 = 0 then none else some (output.1.1 / output.1.2) := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact measurable_const
    · exact measurable_some.comp (by fun_prop)
  convert Measurable.optionElim none hsome using 1
  funext output
  cases output <;> rfl

theorem accuracyPairedRatioEstimate_eq_bind_output
    (q : VolumeParams) (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    accuracyPairedRatioEstimate q sigma2 tau2 current =
      (cappedAccuracyProperCollectPairs q sigma2
        (gaussianRatioWeight sigma2 tau2)
        (accuracyPairedProposalCap q
            (accuracyPairedPhaseSampleCount q sigma2) +
          accuracyPairedPhaseSampleCount q sigma2)
        1 (accuracyPairedPhaseSampleCount q sigma2) current).bind
          (fun result => .pure (accuracyPairedRatioOutput result)) := by
  rfl

theorem accuracyPairedUniformRatioEstimate_eq_bind_output
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    accuracyPairedUniformRatioEstimate q sigma2 current =
      (cappedAccuracyProperCollectPairs q sigma2
        (uniformRatioWeight sigma2)
        (accuracyPairedProposalCap q
            (accuracyPairedTerminalSampleCount q) +
          accuracyPairedTerminalSampleCount q)
        1 (accuracyPairedTerminalSampleCount q) current).bind
          (fun result => .pure (accuracyPairedUniformOutput result)) := by
  rfl

theorem accuracyPairedRatioEstimate_queryBound
    (q : VolumeParams) (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyPairedRatioEstimate q sigma2 tau2 current).QueryBound
      (accuracyPairedProposalCap q
          (accuracyPairedPhaseSampleCount q sigma2) +
        accuracyPairedPhaseSampleCount q sigma2) := by
  rw [accuracyPairedRatioEstimate_eq_bind_output]
  exact (cappedAccuracyProperCollectPairs_queryBound q sigma2
    (gaussianRatioWeight sigma2 tau2)
    (accuracyPairedProposalCap q (accuracyPairedPhaseSampleCount q sigma2) +
      accuracyPairedPhaseSampleCount q sigma2)
    1 (accuracyPairedPhaseSampleCount q sigma2) current).bind
      fun _ => .pure _ 0

theorem accuracyPairedUniformRatioEstimate_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (accuracyPairedUniformRatioEstimate q sigma2 current).QueryBound
      (accuracyPairedProposalCap q (accuracyPairedTerminalSampleCount q) +
        accuracyPairedTerminalSampleCount q) := by
  rw [accuracyPairedUniformRatioEstimate_eq_bind_output]
  exact (cappedAccuracyProperCollectPairs_queryBound q sigma2
    (uniformRatioWeight sigma2)
    (accuracyPairedProposalCap q (accuracyPairedTerminalSampleCount q) +
      accuracyPairedTerminalSampleCount q)
    1 (accuracyPairedTerminalSampleCount q) current).bind
      fun _ => .pure _ 0

theorem accuracyPairedRatioEstimate_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ) :
    Measurable (fun current =>
      (accuracyPairedRatioEstimate q sigma2 tau2 current).runEstimate
        oracle.query) ∧
    ∀ current,
      (accuracyPairedRatioEstimate q sigma2 tau2 current).StronglyMeasurable
        oracle.query := by
  let rawCap := accuracyPairedProposalCap q
    (accuracyPairedPhaseSampleCount q sigma2) +
      accuracyPairedPhaseSampleCount q sigma2
  let samples := accuracyPairedPhaseSampleCount q sigma2
  let collector := fun current => cappedAccuracyProperCollectPairs q sigma2
    (gaussianRatioWeight sigma2 tau2) rawCap 1 samples current
  have hcollector := cappedAccuracyProperCollectPairs_measurable_and_strong
    q I oracle hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
      rawCap 1 samples
  let outputProgram := fun result : Option ((ℝ × ℝ) × AmbientSpace q.n) =>
    (MembershipOracleProgram.pure (accuracyPairedRatioOutput result) :
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)))
  have houtStrong : ∀ result,
      (outputProgram result).StronglyMeasurable oracle.query := by
    intro result
    trivial
  have houtRun : Measurable fun result =>
      (outputProgram result).runEstimate oracle.query := by
    exact Measure.measurable_dirac.comp measurable_accuracyPairedRatioOutput
  constructor
  · rw [show (fun current =>
        (accuracyPairedRatioEstimate q sigma2 tau2 current).runEstimate
          oracle.query) =
      fun current => (collector current).runEstimate oracle.query |>.bind
        fun result => (outputProgram result).runEstimate oracle.query by
        funext current
        rw [accuracyPairedRatioEstimate_eq_bind_output]
        exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
          (hcollector.2 current) houtStrong houtRun]
    exact (Measure.measurable_bind' houtRun).comp hcollector.1
  · intro current
    rw [accuracyPairedRatioEstimate_eq_bind_output]
    exact (hcollector.2 current).bind houtStrong houtRun

theorem accuracyPairedUniformRatioEstimate_measurable_and_strong
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable (fun current =>
      (accuracyPairedUniformRatioEstimate q sigma2 current).runEstimate
        oracle.query) ∧
    ∀ current,
      (accuracyPairedUniformRatioEstimate q sigma2 current).StronglyMeasurable
        oracle.query := by
  let rawCap := accuracyPairedProposalCap q
    (accuracyPairedTerminalSampleCount q) + accuracyPairedTerminalSampleCount q
  let samples := accuracyPairedTerminalSampleCount q
  let collector := fun current => cappedAccuracyProperCollectPairs q sigma2
    (uniformRatioWeight sigma2) rawCap 1 samples current
  have hcollector := cappedAccuracyProperCollectPairs_measurable_and_strong
    q I oracle hsigma2 (measurable_uniformRatioWeight sigma2)
      rawCap 1 samples
  let outputProgram := fun result : Option ((ℝ × ℝ) × AmbientSpace q.n) =>
    (MembershipOracleProgram.pure (accuracyPairedUniformOutput result) :
      MembershipOracleProgram q.n (Option ℝ))
  have houtStrong : ∀ result,
      (outputProgram result).StronglyMeasurable oracle.query := by
    intro result
    trivial
  have houtRun : Measurable fun result =>
      (outputProgram result).runEstimate oracle.query := by
    exact Measure.measurable_dirac.comp measurable_accuracyPairedUniformOutput
  constructor
  · rw [show (fun current =>
        (accuracyPairedUniformRatioEstimate q sigma2 current).runEstimate
          oracle.query) =
      fun current => (collector current).runEstimate oracle.query |>.bind
        fun result => (outputProgram result).runEstimate oracle.query by
        funext current
        rw [accuracyPairedUniformRatioEstimate_eq_bind_output]
        exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
          (hcollector.2 current) houtStrong houtRun]
    exact (Measure.measurable_bind' houtRun).comp hcollector.1
  · intro current
    rw [accuracyPairedUniformRatioEstimate_eq_bind_output]
    exact (hcollector.2 current).bind houtStrong houtRun

/-! ## Finite syntax-level query bounds -/

noncomputable def accuracyPairedCoolingQueryBudget
    (q : VolumeParams) : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | sigma2 :: tau2 :: rest =>
      accuracyPairedProposalCap q
          (accuracyPairedPhaseSampleCount q sigma2) +
        accuracyPairedPhaseSampleCount q sigma2 +
        accuracyPairedCoolingQueryBudget q (tau2 :: rest)
termination_by variances => variances.length

theorem accuracyPairedCoolingProduct_queryBound (q : VolumeParams) :
    ∀ variances point,
    (coolingProduct accuracyPairedPrimitives q variances point).QueryBound
      (accuracyPairedCoolingQueryBudget q variances) := by
  intro variances
  induction variances with
  | nil =>
      intro point
      simpa [coolingProduct, accuracyPairedCoolingQueryBudget] using
        (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro point
          simpa [coolingProduct, accuracyPairedCoolingQueryBudget] using
            (MembershipOracleProgram.QueryBound.pure (some (1, point)) 0)
      | cons tau2 rest =>
          intro point
          simp only [coolingProduct, accuracyPairedPrimitives]
          have htail : ∀ phase,
              ((match phase with
                | none => .pure none
                | some (ratio, nextPoint) =>
                    (coolingProduct accuracyPairedPrimitives q
                      (tau2 :: rest) nextPoint).bind fun tail =>
                        .pure <| match tail with
                          | some (product, lastPoint) =>
                              some (ratio * product, lastPoint)
                          | none => none) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).QueryBound
                (accuracyPairedCoolingQueryBudget q (tau2 :: rest)) := by
            intro phase
            cases phase with
            | none => exact .pure _ _
            | some value =>
                exact (ih value.2).bind fun _tail => .pure _ 0
          have h := (accuracyPairedRatioEstimate_queryBound
            q sigma2 tau2 point).bind htail
          convert h using 1
          · rfl
          · rw [accuracyPairedCoolingQueryBudget]

theorem accuracyPairedBaseVolumeCooling_queryBound
    (S : (q : VolumeParams) → VolumeCoolingSchedule q) (q : VolumeParams) :
    (baseVolumeCooling accuracyPairedPrimitives S q).QueryBound
      (1 + (accuracyPairedCoolingQueryBudget q (S q).variances +
        (accuracyPairedProposalCap q (accuracyPairedTerminalSampleCount q) +
          accuracyPairedTerminalSampleCount q))) := by
  let finalBudget :=
    accuracyPairedProposalCap q (accuracyPairedTerminalSampleCount q) +
      accuracyPairedTerminalSampleCount q
  have hproduct : ∀ initialPoint,
      ((match initialPoint with
        | none => .pure 0
        | some point =>
            (coolingProduct accuracyPairedPrimitives q
              (S q).variances point).bind fun product =>
                match product with
                | none => .pure 0
                | some (gaussianProduct, lastPoint) =>
                    (accuracyPairedPrimitives.uniformRatioEstimate q
                      (terminalVariance q) lastPoint).bind fun finalRatio =>
                        .pure <| match finalRatio with
                          | some uniformRatio =>
                              initialGaussianIntegral q * gaussianProduct * uniformRatio
                          | none => 0) : MembershipOracleProgram q.n ℝ).QueryBound
        (accuracyPairedCoolingQueryBudget q (S q).variances + finalBudget) := by
    intro initialPoint
    cases initialPoint with
    | none => exact .pure _ _
    | some point =>
        apply (accuracyPairedCoolingProduct_queryBound q
          (S q).variances point).bind
        intro product
        cases product with
        | none => exact .pure _ _
        | some value =>
            exact (accuracyPairedUniformRatioEstimate_queryBound q
              (terminalVariance q) value.2).bind fun _ => .pure _ 0
  unfold baseVolumeCooling
  have h := (figureOneInitialSample_queryBound q).bind hproduct
  convert h using 1
  congr 1

end ArlibCommunity.Algorithms.CV18
