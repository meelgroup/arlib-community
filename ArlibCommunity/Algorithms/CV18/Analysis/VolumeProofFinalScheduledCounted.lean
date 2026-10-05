/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedBaseCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryCounted

/-! # Counted measurability of the complete scheduled Figure-One base -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

theorem scheduledBalancedCoolingRatioEstimate_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ) :
    (Measurable fun current =>
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).run
        oracle.query) ∧
    ∀ current,
      (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q sigma2 (gaussianRatioWeight sigma2 tau2)
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
  have hsourceBase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
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
  simpa only [source, average, scheduledBalancedCoolingRatioEstimate] using h

theorem scheduledBalancedCoolingUniformEstimateWithState_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun current =>
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).run
        oracle.query) ∧
    ∀ current,
      (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
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
  have hsourceBase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
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
  simpa only [source, average, scheduledBalancedCoolingUniformEstimateWithState] using h

theorem scheduledBalancedCoolingUniformRatioEstimate_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun current =>
      (scheduledBalancedCoolingUniformRatioEstimate parameters q sigma2 current).run
        oracle.query) ∧
    ∀ current,
      (scheduledBalancedCoolingUniformRatioEstimate parameters q sigma2 current).CountedStronglyMeasurable
        oracle.query := by
  let source (current : AmbientSpace q.n) :=
    scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current
  let forget (z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n)) := balancedCoolingForgetState z.2
  have hsource := scheduledBalancedCoolingUniformEstimateWithState_countedMeasurable
    parameters q I oracle hsigma2
  have hforget : Measurable forget :=
    measurable_balancedCoolingForgetState.comp measurable_snd
  have h := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query source forget hsource.1 hsource.2 hforget
  simpa only [source, forget, scheduledBalancedCoolingUniformRatioEstimate] using h

/-- The result-and-query-count interpreter of the complete Gaussian cooling
product is measurable.  This is the counted analogue of
`balancedCoolingProduct_measurable_and_strong`. -/
theorem scheduledBalancedCoolingProduct_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      (Measurable fun point =>
        (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q variances point).run
          oracle.query) ∧
      ∀ point,
        (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q variances point).CountedStronglyMeasurable
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
          have hratio := scheduledBalancedCoolingRatioEstimate_countedMeasurable
            parameters q I oracle hsigma2 tau2
          let tailProgram (value : ℝ × AmbientSpace q.n) :=
            coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
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
            scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point
          have hbound := MembershipOracleProgram.measurable_run_bind_param
            oracle.query ratioProgram (fun z => phaseProgram z.2)
              hratio.1 hratio.2 (hphaseRun.comp measurable_snd)
                (fun z => hphase z.2)
          have hcooling : ∀ point,
              coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (ratioProgram point).bind phaseProgram := by
            intro point
            rw [coolingProduct]
            change (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
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
                (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point).run oracle.query) =
              fun point => ((ratioProgram point).bind phaseProgram).run
                oracle.query by
              funext point
              rw [hcooling point]]
            exact hbound
          · intro point
            rw [hcooling point]
            exact (hratio.2 point).bind hphase hphaseRun

/-- The exact post-initial continuation used by the scheduled primitive package. -/
noncomputable def scheduledBalancedFigureOnePointContinuation
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (point : AmbientSpace q.n) : MembershipOracleProgram q.n ℝ :=
  (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
    (explicitVolumeCoolingSchedule q).variances point).bind fun product =>
      match product with
      | none => .pure 0
      | some (gaussianProduct, lastPoint) =>
          (scheduledBalancedCoolingUniformRatioEstimate parameters q
            (terminalVariance q) lastPoint).bind fun finalRatio =>
              .pure <| match finalRatio with
              | some uniformRatio =>
                  initialGaussianIntegral q * gaussianProduct * uniformRatio
              | none => 0

/-- Counted semantics for the complete scheduled post-initial continuation. -/
theorem scheduledBalancedFigureOnePointContinuation_countedMeasurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun point =>
      (scheduledBalancedFigureOnePointContinuation parameters q point).run
        oracle.query) ∧
    ∀ point,
      (scheduledBalancedFigureOnePointContinuation parameters q point).CountedStronglyMeasurable
        oracle.query := by
  have hcooling := scheduledBalancedCoolingProduct_countedMeasurable
    parameters q I oracle (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive
  have huniform := scheduledBalancedCoolingUniformRatioEstimate_countedMeasurable
    parameters q I oracle (terminalVariance_pos' q)
  let uniformProgram (value : ℝ × AmbientSpace q.n) :=
    scheduledBalancedCoolingUniformRatioEstimate parameters q
      (terminalVariance q) value.2
  let finish (z : (ℝ × AmbientSpace q.n) × Option ℝ) : ℝ :=
    match z.2 with
    | some uniformRatio => initialGaussianIntegral q * z.1.1 * uniformRatio
    | none => 0
  have hfinish : Measurable finish := by
    have hnone : Measurable fun _ : ℝ × AmbientSpace q.n => (0 : ℝ) :=
      measurable_const
    have hsome : Measurable fun z : (ℝ × AmbientSpace q.n) × ℝ =>
        initialGaussianIntegral q * z.1.1 * z.2 := by fun_prop
    convert Measurable.optionElimParam hnone hsome using 1
    funext z
    rcases z with ⟨p, value⟩
    cases value <;> rfl
  have huniformBind := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query uniformProgram finish
      (huniform.1.comp measurable_snd)
      (fun value => huniform.2 value.2) hfinish
  let tail : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n ℝ := fun product =>
    match product with
    | none => .pure 0
    | some value =>
        (uniformProgram value).bind fun finalRatio =>
          .pure (finish (value, finalRatio))
  have htailRun : Measurable fun product => (tail product).run oracle.query := by
    convert Measurable.optionElim (Measure.dirac ((0 : ℝ), 0))
      huniformBind.1 using 1
    funext product
    cases product <;> rfl
  have htail : ∀ product,
      (tail product).CountedStronglyMeasurable oracle.query := by
    intro product
    cases product with
    | none => trivial
    | some value => exact huniformBind.2 value
  let cooling (point : AmbientSpace q.n) :=
    coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
      (explicitVolumeCoolingSchedule q).variances point
  have hrun := MembershipOracleProgram.measurable_run_bind_param
    oracle.query cooling (fun z => tail z.2) hcooling.1 hcooling.2
      (htailRun.comp measurable_snd) (fun z => htail z.2)
  have hprogram : ∀ point,
      scheduledBalancedFigureOnePointContinuation parameters q point =
        (cooling point).bind tail := by
    intro point
    unfold scheduledBalancedFigureOnePointContinuation cooling tail
      uniformProgram finish
    congr 1
    funext product
    cases product with
    | none => rfl
    | some value => rcases value with ⟨gaussianProduct, lastPoint⟩; rfl
  constructor
  · rw [show (fun point =>
        (scheduledBalancedFigureOnePointContinuation parameters q point).run
          oracle.query) =
      fun point => ((cooling point).bind tail).run oracle.query by
        funext point
        rw [hprogram point]]
    exact hrun
  · intro point
    rw [hprogram point]
    exact (hcooling.2 point).bind htail htailRun

/-- The actual final scheduled base program has a measurable joint result/cost law. -/
theorem figureOneFinalScheduledBalancedBaseProgram_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (figureOneFinalScheduledBalancedBaseProgram q).CountedStronglyMeasurable
      oracle.query := by
  have hpoint := scheduledBalancedFigureOnePointContinuation_countedMeasurable
    figureOneFinalScheduledBalancedParameters q I oracle
  let tail : Option (AmbientSpace q.n) → MembershipOracleProgram q.n ℝ :=
    fun initialPoint => match initialPoint with
    | none => .pure 0
    | some point => scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point
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
  have hbase : figureOneFinalScheduledBalancedBaseProgram q =
      (figureOneInitialSample q).bind tail := by
    unfold figureOneFinalScheduledBalancedBaseProgram baseVolumeCooling tail
      scheduledBalancedFigureOnePointContinuation
    congr 1
  rw [hbase]
  exact (figureOneInitialSample_countedStronglyMeasurable q I oracle).bind
    htail htailRun

end ArlibCommunity.Algorithms.CV18
