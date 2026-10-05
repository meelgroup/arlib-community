/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedMeasurability
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedFullHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedGlobalCap

/-!
# Counted semantics of the complete balanced Figure-One base program

This module carries the counted-measurability proofs for the variable-cost
balanced collector through the cooling phase wrappers.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- A parameterized measurable pure postprocessing can be composed with a
counted-measurable source program. -/
theorem MembershipOracleProgram.countedMeasurable_bind_pure
    {n : ℕ} {P : Type*} {A B : Type} [MeasurableSpace P]
    [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool) (program : P → MembershipOracleProgram n A)
    (f : P × A → B)
    (hprogramMeas : Measurable fun p => (program p).run oracle)
    (hprogram : ∀ p, (program p).CountedStronglyMeasurable oracle)
    (hf : Measurable f) :
    (Measurable fun p => ((program p).bind fun a => .pure (f (p, a))).run oracle) ∧
    ∀ p, ((program p).bind fun a => .pure (f (p, a))).CountedStronglyMeasurable
      oracle := by
  let finish (z : P × A) : MembershipOracleProgram n B := .pure (f z)
  have hfinishMeas : Measurable fun z => (finish z).run oracle := by
    simp only [finish, MembershipOracleProgram.run]
    exact Measure.measurable_dirac.comp <| hf.prodMk measurable_const
  have hfinish : ∀ z, (finish z).CountedStronglyMeasurable oracle := by
    intro z
    trivial
  constructor
  · exact MembershipOracleProgram.measurable_run_bind_param oracle program finish
      hprogramMeas hprogram hfinishMeas hfinish
  · intro p
    exact (hprogram p).bind (fun a => hfinish (p, a))
      (hfinishMeas.comp <| measurable_const.prodMk measurable_id)

theorem balancedCoolingRatioEstimate_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ) :
    (Measurable fun current =>
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).run
        oracle.query) ∧
    ∀ current,
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    balancedAccuracyRetryCollect q sigma2 (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)
  let average (z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n)) :=
    balancedCoolingAverage (figureOnePhaseSampleCount q sigma2) z.2
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsourceBase := balancedAccuracyRetryCollect_countedMeasurable
    q I oracle hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
  have hsourceMeas : Measurable fun current => (source current).run oracle.query :=
    hsourceBase.1.comp hscale
  have hsource : ∀ current,
      (source current).CountedStronglyMeasurable oracle.query :=
    fun current => hsourceBase.2 (accuracyScaleFactor q • current)
  have havg : Measurable average :=
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOnePhaseSampleCount q sigma2)).comp measurable_snd
  have h := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query source average hsourceMeas hsource havg
  simpa only [source, average, balancedCoolingRatioEstimate] using h

theorem balancedCoolingUniformEstimateWithState_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun current =>
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).run
        oracle.query) ∧
    ∀ current,
      (balancedCoolingUniformEstimateWithState parameters q sigma2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    balancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) (accuracyScaleFactor q • current)
  let average (z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n)) :=
    balancedCoolingAverage (figureOneSampleCount q) z.2
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsourceBase := balancedAccuracyRetryCollect_countedMeasurable
    q I oracle hsigma2 (measurable_uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2) (figureOneSampleCount q)
  have hsourceMeas : Measurable fun current => (source current).run oracle.query :=
    hsourceBase.1.comp hscale
  have hsource : ∀ current,
      (source current).CountedStronglyMeasurable oracle.query :=
    fun current => hsourceBase.2 (accuracyScaleFactor q • current)
  have havg : Measurable average :=
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOneSampleCount q)).comp measurable_snd
  have h := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query source average hsourceMeas hsource havg
  simpa only [source, average, balancedCoolingUniformEstimateWithState] using h

theorem balancedCoolingUniformRatioEstimate_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun current =>
      (balancedCoolingUniformRatioEstimate parameters q sigma2 current).run
        oracle.query) ∧
    ∀ current,
      (balancedCoolingUniformRatioEstimate parameters q sigma2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    balancedCoolingUniformEstimateWithState parameters q sigma2 current
  let forget (z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n)) := balancedCoolingForgetState z.2
  have hsource := balancedCoolingUniformEstimateWithState_countedMeasurable
    parameters q I oracle hsigma2
  have hforget : Measurable forget :=
    measurable_balancedCoolingForgetState.comp measurable_snd
  have h := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query source forget hsource.1 hsource.2 hforget
  simpa only [source, forget, balancedCoolingUniformRatioEstimate] using h

/-- The result-and-query-count interpreter of the complete Gaussian cooling
product is measurable.  This is the counted analogue of
`balancedCoolingProduct_measurable_and_strong`. -/
theorem balancedCoolingProduct_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      (Measurable fun point =>
        (coolingProduct (balancedCoolingPrimitives parameters) q variances point).run
          oracle.query) ∧
      ∀ point,
        (coolingProduct (balancedCoolingPrimitives parameters) q variances point).CountedStronglyMeasurable
          oracle.query := by
  intro variances
  induction variances with
  | nil =>
      intro _
      constructor
      · simp only [coolingProduct, MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp <|
          (measurable_some.comp <| measurable_const.prodMk measurable_id).prodMk
            measurable_const
      · intro point
        simpa [coolingProduct] using
          (show (MembershipOracleProgram.pure (some (1, point)) :
            MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n))).CountedStronglyMeasurable
                oracle.query from trivial)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _
          constructor
          · simp only [coolingProduct, MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <| measurable_const.prodMk measurable_id).prodMk
                measurable_const
          · intro point
            simpa [coolingProduct] using
              (show (MembershipOracleProgram.pure (some (1, point)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).CountedStronglyMeasurable
                    oracle.query from trivial)
      | cons tau2 rest =>
          intro hpositive
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htail := ih htailPositive
          have hratio := balancedCoolingRatioEstimate_countedMeasurable
            parameters q I oracle hsigma2 tau2
          let tailProgram (value : ℝ × AmbientSpace q.n) :=
            coolingProduct (balancedCoolingPrimitives parameters) q
              (tau2 :: rest) value.2
          let multiply (z : (ℝ × AmbientSpace q.n) ×
              Option (ℝ × AmbientSpace q.n)) :=
            balancedCoolingProductCons z.1.1 z.2
          have hmultiply : Measurable multiply :=
            measurable_balancedCoolingProductCons.comp <|
              (measurable_fst.comp measurable_fst).prodMk measurable_snd
          have htailBind := MembershipOracleProgram.countedMeasurable_bind_pure
            oracle.query tailProgram multiply
              (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
                hmultiply
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n
                (Option (ℝ × AmbientSpace q.n)) := fun phase =>
            match phase with
            | none => .pure none
            | some value =>
                (tailProgram value).bind fun result =>
                  .pure (multiply (value, result))
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).run oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac ((none : Option (ℝ × AmbientSpace q.n)), 0))
                htailBind.1 using 1
            funext phase
            cases phase <;> rfl
          have hphase : ∀ phase,
              (phaseProgram phase).CountedStronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value => exact htailBind.2 value
          let ratioProgram (point : AmbientSpace q.n) :=
            balancedCoolingRatioEstimate parameters q sigma2 tau2 point
          have hbound := MembershipOracleProgram.measurable_run_bind_param
            oracle.query ratioProgram (fun z => phaseProgram z.2)
              hratio.1 hratio.2 (hphaseRun.comp measurable_snd)
                (fun z => hphase z.2)
          have hcooling : ∀ point,
              coolingProduct (balancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (ratioProgram point).bind phaseProgram := by
            intro point
            rw [coolingProduct]
            change (balancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                rcases value with ⟨ratio, nextPoint⟩
                simp only [phaseProgram, tailProgram, multiply,
                  balancedCoolingProductCons]
                congr 1
                funext result
                cases result with
                | none => rfl
                | some value => rcases value with ⟨product, lastPoint⟩; rfl
          constructor
          · rw [show (fun point =>
                (coolingProduct (balancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point).run oracle.query) =
              fun point => ((ratioProgram point).bind phaseProgram).run
                oracle.query by
              funext point
              rw [hcooling point]]
            exact hbound
          · intro point
            rw [hcooling point]
            exact (hratio.2 point).bind hphase hphaseRun

/-- Counted semantics for the complete post-initial continuation, including
the terminal Gaussian-to-uniform estimator. -/
theorem balancedFigureOnePointContinuation_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun point =>
      (balancedFigureOnePointContinuation parameters q point).run oracle.query) ∧
    ∀ point,
      (balancedFigureOnePointContinuation parameters q point).CountedStronglyMeasurable
        oracle.query := by
  have hcooling := balancedCoolingProduct_countedMeasurable
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have hterminal := balancedCoolingUniformEstimateWithState_countedMeasurable
    parameters q I oracle (terminalVariance_pos' q)
  let terminalProgram (value : ℝ × AmbientSpace q.n) :=
    balancedCoolingUniformEstimateWithState parameters q
      (terminalVariance q) value.2
  let finish (z : (ℝ × AmbientSpace q.n) ×
      Option (ℝ × AmbientSpace q.n)) :=
    balancedFigureOneTerminalScalar q z.1.1 z.2
  have hfinish : Measurable finish :=
    (measurable_balancedFigureOneTerminalScalar q).comp <|
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hterminalBind := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query terminalProgram finish
      (hterminal.1.comp measurable_snd)
      (fun value => hterminal.2 value.2) hfinish
  let tail : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ := fun product =>
    match product with
    | none => .pure 0
    | some value =>
        (terminalProgram value).bind fun terminal =>
          .pure (finish (value, terminal))
  have htailRun : Measurable fun product => (tail product).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hterminalBind.1 using 1
    funext product
    cases product <;> rfl
  have htail : ∀ product,
      (tail product).CountedStronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value => exact hterminalBind.2 value
  let cooling (point : AmbientSpace q.n) :=
    coolingProduct (balancedCoolingPrimitives parameters) q
      (explicitVolumeCoolingSchedule q).variances point
  have hrun := MembershipOracleProgram.measurable_run_bind_param
    oracle.query cooling (fun z => tail z.2) hcooling.1 hcooling.2
      (htailRun.comp measurable_snd) (fun z => htail z.2)
  have hretained : ∀ point,
      balancedFigureOneRetainedPointContinuation parameters q point =
        (cooling point).bind tail := by
    intro point
    unfold balancedFigureOneRetainedPointContinuation cooling tail
      terminalProgram finish
    congr 1
    funext product
    cases product with
    | none => rfl
    | some value => rcases value with ⟨gaussianProduct, lastPoint⟩; rfl
  constructor
  · rw [show (fun point =>
        (balancedFigureOnePointContinuation parameters q point).run oracle.query) =
      fun point => ((cooling point).bind tail).run oracle.query by
        funext point
        rw [balancedFigureOnePointContinuation_eq_retained,
          hretained point]]
    exact hrun
  · intro point
    rw [balancedFigureOnePointContinuation_eq_retained, hretained point]
    exact (hcooling.2 point).bind htail htailRun

/-- The complete balanced Figure-One base program has a measurable joint law
of its scalar result and its actual membership-query count. -/
theorem balancedFigureOneBaseVolumeCooling_countedStronglyMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q).CountedStronglyMeasurable oracle.query := by
  have hpoint := balancedFigureOnePointContinuation_countedMeasurable
    parameters q I oracle
  let tail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => balancedFigureOnePointContinuation parameters q point
  have htailRun : Measurable fun initialPoint =>
      (tail initialPoint).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      hpoint.1 using 1
    funext initialPoint
    cases initialPoint <;> rfl
  have htail : ∀ initialPoint,
      (tail initialPoint).CountedStronglyMeasurable oracle.query := by
    intro initialPoint
    cases initialPoint with
    | none => trivial
    | some point => exact hpoint.2 point
  have hbase : baseVolumeCooling (balancedCoolingPrimitives parameters)
      explicitVolumeCoolingSchedule q = (figureOneInitialSample q).bind tail := by
    unfold baseVolumeCooling
    congr 1
  rw [hbase]
  exact (figureOneInitialSample_countedStronglyMeasurable q I oracle).bind
    htail htailRun

/-- The concrete finite syntax underlying the globally capped Figure-One
program has a measurable result-and-cost law. -/
theorem figureOneGlobalBalancedBaseProgram_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneGlobalBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query := by
  unfold figureOneGlobalBalancedBaseProgram
  exact balancedFigureOneBaseVolumeCooling_countedStronglyMeasurable
    figureOneGlobalBalancedParameters q I oracle

end ArlibCommunity.Algorithms.CV18
