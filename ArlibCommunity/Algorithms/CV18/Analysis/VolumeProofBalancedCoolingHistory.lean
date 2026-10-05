/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule

/-!
# A balanced-retry implementation of the CV18 cooling history

This file packages the finite balanced/proper-step collector as the phase
primitive used by `coolingProduct`.  Its public state is always a point in the
target body; the homothetic speedy coordinate is introduced only when a phase
collector is called.

The history law below retains every phase estimate, their accumulated product,
and the last target-space state.  Thus it supplies a single probability space
on which the dependent-product argument can be instantiated, rather than a
separate marginal law for every phase.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Finite execution parameters for the balanced/proper-step phase collector.
The statistical sample counts are not configurable: they are the actual
Figure-One counts used by `VolumeProofDependentSchedule`. -/
structure BalancedCoolingParameters where
  proposalCap : (q : VolumeParams) → ℝ → ℕ
  properStride : (q : VolumeParams) → ℝ → ℕ
  retryLimit : (q : VolumeParams) → ℝ → ℕ

/-- The phase count is bounded by the common sample-count parameter appearing
in the dependent-product error budget. -/
theorem figureOnePhaseSampleCount_le_dependentMax
    (q : VolumeParams) (sigma2 : ℝ) :
    figureOnePhaseSampleCount q sigma2 ≤
      figureOneDependentMaxSampleCount q := by
  unfold figureOnePhaseSampleCount figureOneDependentMaxSampleCount
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem figureOneTerminalSampleCount_le_dependentMax (q : VolumeParams) :
    figureOneSampleCount q ≤ figureOneDependentMaxSampleCount q :=
  le_max_right _ _

/-- Average an accumulated phase observable without changing its retained
target-space state. -/
noncomputable def balancedCoolingAverage (samples : ℕ) :
    Option (ℝ × AmbientSpace n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some (total, current) => some (total / (samples : ℝ), current)

theorem measurable_balancedCoolingAverage (samples : ℕ) :
    Measurable (balancedCoolingAverage (n := n) samples) := by
  have hsome : Measurable fun value : ℝ × AmbientSpace n =>
      some (value.1 / (samples : ℝ), value.2) :=
    measurable_some.comp <| measurable_fst.div_const _ |>.prodMk measurable_snd
  convert Measurable.optionElim (none : Option (ℝ × AmbientSpace n)) hsome using 1
  funext value
  cases value <;> rfl

/-- A Gaussian cooling phase.  `current` is in target coordinates, whereas
the proper-step walk runs on the homothetically shrunken speedy body. -/
noncomputable def balancedCoolingRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (balancedAccuracyRetryCollect q sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2) result)

/-- The terminal Gaussian-to-uniform estimator, before forgetting the final
retained state. -/
noncomputable def balancedCoolingUniformEstimateWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (balancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOneSampleCount q) result)

/-- Forget only the terminal retained state, as required by
`VolumeCoolingPrimitives.uniformRatioEstimate`. -/
noncomputable def balancedCoolingForgetState :
    Option (ℝ × AmbientSpace n) → Option ℝ
  | none => none
  | some (estimate, _) => some estimate

theorem measurable_balancedCoolingForgetState :
    Measurable (balancedCoolingForgetState (n := n)) := by
  have hsome : Measurable fun value : ℝ × AmbientSpace n => some value.1 :=
    measurable_some.comp measurable_fst
  convert Measurable.optionElim (none : Option ℝ) hsome using 1
  funext value
  cases value <;> rfl

noncomputable def balancedCoolingUniformRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (balancedCoolingUniformEstimateWithState parameters q sigma2 current).bind
    fun result => .pure (balancedCoolingForgetState result)

/-- Paper-faithful cooling primitives whose phases use finite capped
balanced/proper-step retries and the Figure-One sample counts. -/
noncomputable def balancedCoolingPrimitives
    (parameters : BalancedCoolingParameters) : VolumeCoolingPrimitives where
  initialSample := figureOneInitialSample
  ratioEstimate := balancedCoolingRatioEstimate parameters
  uniformRatioEstimate := balancedCoolingUniformRatioEstimate parameters

/-- Exact target-coordinate law of one averaged Gaussian phase. -/
noncomputable def balancedCoolingRatioLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (balancedAccuracyTransitionCollectLaw q I sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2) 0
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2))

theorem balancedCoolingRatioEstimate_measurable_strong_and_law
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ) :
    Measurable (fun current =>
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
        oracle.query) ∧
    (∀ current,
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).StronglyMeasurable
        oracle.query) ∧
    ∀ current,
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
          oracle.query =
        balancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOnePhaseSampleCount q sigma2
  let weight : AmbientSpace q.n → ℝ := gaussianRatioWeight sigma2 tau2
  let scalePoint : AmbientSpace q.n → AmbientSpace q.n :=
    fun current => accuracyScaleFactor q • current
  have hweight : Measurable weight :=
    measurable_gaussianRatioWeight sigma2 tau2
  have htransition :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight cap stride retries samples
  have hscale : Measurable scalePoint :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (scalePoint current) :=
    htransition.1.comp (measurable_const.prodMk hscale)
  have hsourceProb : ∀ current, IsProbabilityMeasure
      (balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (scalePoint current)) :=
    fun current => htransition.2 0 (scalePoint current)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  have hlaw : Measurable fun current =>
      balancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
    unfold balancedCoolingRatioLaw
    exact (Measure.measurable_map _ havg).comp hsource
  have hcollectorStrong : ∀ current,
      (balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
        (scalePoint current)).StronglyMeasurable oracle.query := by
    intro current
    have haux := balancedAccuracyRetryCollectAux_semantics q I oracle hsigma2
      hweight cap stride retries retries samples
    let output : Option (ℝ × AmbientSpace q.n) →
        MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
      fun result => .pure (balancedAccuracyRetryOutput q result)
    have houtputRun : Measurable fun result =>
        (output result).runEstimate oracle.query := by
      simp only [output, MembershipOracleProgram.runEstimate]
      exact Measure.measurable_dirac.comp
        (measurable_balancedAccuracyRetryOutput q)
    unfold balancedAccuracyRetryCollect
    exact (haux.1 0 (scalePoint current)).bind (fun _ => by trivial) houtputRun
  have havgRun : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (.pure (balancedCoolingAverage samples result) :
        MembershipOracleProgram q.n
          (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp havg
  have hstrong : ∀ current,
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).StronglyMeasurable
        oracle.query := by
    intro current
    unfold balancedCoolingRatioEstimate
    change (balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
      (scalePoint current)).bind _ |>.StronglyMeasurable oracle.query
    exact (hcollectorStrong current).bind (fun _ => by trivial) havgRun
  have hrun : ∀ current,
      (balancedCoolingRatioEstimate parameters q sigma2 tau2 current).runEstimate
          oracle.query =
        balancedCoolingRatioLaw parameters q I sigma2 tau2 current := by
    intro current
    unfold balancedCoolingRatioEstimate balancedCoolingRatioLaw
    change ((balancedAccuracyRetryCollect q sigma2 weight cap stride retries samples
      (scalePoint current)).bind fun result =>
        .pure (balancedCoolingAverage samples result)).runEstimate oracle.query = _
    rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
      (hcollectorStrong current) (fun _ => by trivial) havgRun]
    rw [balancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
      q I oracle hsigma2 hweight]
    exact Measure.bind_dirac_eq_map _ havg
  refine ⟨?_, hstrong, hrun⟩
  simpa only [hrun] using hlaw

/-- A complete Gaussian-phase history: the estimates in chronological order,
their accumulated product, and the retained target-space point. -/
abbrev BalancedCoolingHistory (n : ℕ) :=
  (ℕ → ℝ) × (ℕ × (ℝ × AmbientSpace n))

/-- Insert the current phase at the front of a tail history. -/
noncomputable def balancedCoolingHistoryCons (ratio : ℝ) :
    Option (BalancedCoolingHistory n) → Option (BalancedCoolingHistory n)
  | none => none
  | some (ratios, count, product, lastPoint) =>
      some ((fun k => if k = 0 then ratio else ratios (k - 1)),
        count + 1, ratio * product, lastPoint)

theorem measurable_balancedCoolingHistoryCons :
    Measurable fun value : ℝ × Option (BalancedCoolingHistory n) =>
      balancedCoolingHistoryCons value.1 value.2 := by
  have hnone : Measurable fun _ : ℝ =>
      (none : Option (BalancedCoolingHistory n)) := measurable_const
  have hsome : Measurable fun value : ℝ × BalancedCoolingHistory n =>
      some ((fun k => if k = 0 then value.1 else value.2.1 (k - 1)),
        value.2.2.1 + 1, value.1 * value.2.2.2.1, value.2.2.2.2) := by
    apply measurable_some.comp
    have hsequence : Measurable fun value : ℝ × BalancedCoolingHistory n =>
        fun k => if k = 0 then value.1 else value.2.1 (k - 1) := by
      refine measurable_pi_lambda _ fun k => ?_
      split_ifs
      · exact measurable_fst
      · exact (measurable_pi_apply (k - 1)).comp
          (measurable_fst.comp measurable_snd)
    exact hsequence.prodMk (by fun_prop)
  convert Measurable.optionCases
    ((fun _ => 0), 0, (1 : ℝ), (0 : AmbientSpace n)) hnone hsome using 1
  funext value
  cases value.2 <;> rfl

/-- Project a history to the accumulated product and retained state consumed
by `coolingProduct`. -/
noncomputable def balancedCoolingHistoryOutput :
    Option (BalancedCoolingHistory n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some (_, _, product, lastPoint) => some (product, lastPoint)

theorem measurable_balancedCoolingHistoryOutput :
    Measurable (balancedCoolingHistoryOutput (n := n)) := by
  have hsome : Measurable fun value : BalancedCoolingHistory n =>
      some value.2.2 := measurable_some.comp (measurable_snd.comp measurable_snd)
  convert Measurable.optionElim
    (none : Option (ℝ × AmbientSpace n)) hsome using 1
  funext value
  cases value <;> rfl

/-- Multiply a completed tail product by the current phase estimate. -/
noncomputable def balancedCoolingProductCons (ratio : ℝ) :
    Option (ℝ × AmbientSpace n) → Option (ℝ × AmbientSpace n)
  | none => none
  | some (product, lastPoint) => some (ratio * product, lastPoint)

theorem measurable_balancedCoolingProductCons :
    Measurable fun value : ℝ × Option (ℝ × AmbientSpace n) =>
      balancedCoolingProductCons value.1 value.2 := by
  have hnone : Measurable fun _ : ℝ =>
      (none : Option (ℝ × AmbientSpace n)) := measurable_const
  have hsome : Measurable fun value : ℝ × (ℝ × AmbientSpace n) =>
      some (value.1 * value.2.1, value.2.2) :=
    measurable_some.comp <|
      (measurable_fst.mul (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
  convert Measurable.optionCases
    ((0 : ℝ), (0 : AmbientSpace n)) hnone hsome using 1
  funext value
  cases value.2 <;> rfl

theorem balancedCoolingHistoryOutput_cons (ratio : ℝ)
    (history : Option (BalancedCoolingHistory n)) :
    balancedCoolingHistoryOutput (balancedCoolingHistoryCons ratio history) =
      balancedCoolingProductCons ratio
        (balancedCoolingHistoryOutput history) := by
  cases history <;> rfl

/-- The joint law of all Gaussian cooling phases.  It is deliberately defined
from the exact transition law of the executable balanced collector. -/
noncomputable def balancedCoolingHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    List ℝ → AmbientSpace q.n →
      Measure (Option (BalancedCoolingHistory q.n))
  | [], point => Measure.dirac (some ((fun _ => 0), 0, 1, point))
  | [_], point => Measure.dirac (some ((fun _ => 0), 0, 1, point))
  | sigma2 :: tau2 :: rest, point =>
      (balancedCoolingRatioLaw parameters q I sigma2 tau2 point).bind fun phase =>
        match phase with
        | none => Measure.dirac none
        | some (ratio, nextPoint) =>
            (balancedCoolingHistoryLaw parameters q I (tau2 :: rest) nextPoint).map
              (balancedCoolingHistoryCons ratio)
termination_by variances => variances.length

theorem balancedCoolingRatioLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) :
    Measurable (balancedCoolingRatioLaw parameters q I sigma2 tau2) ∧
    ∀ current, IsProbabilityMeasure
      (balancedCoolingRatioLaw parameters q I sigma2 tau2 current) := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOnePhaseSampleCount q sigma2
  let weight : AmbientSpace q.n → ℝ := gaussianRatioWeight sigma2 tau2
  have htransition :=
    balancedAccuracyTransitionCollectLaw_measurable_and_probability
      q I hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
        cap stride retries samples
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (accuracyScaleFactor q • current) :=
    htransition.1.comp (measurable_const.prodMk hscale)
  have hsourceProb : ∀ current, IsProbabilityMeasure
      (balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (accuracyScaleFactor q • current)) :=
    fun current => htransition.2 0 (accuracyScaleFactor q • current)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  constructor
  · unfold balancedCoolingRatioLaw
    exact (Measure.measurable_map _ havg).comp hsource
  · intro current
    unfold balancedCoolingRatioLaw
    let _ : IsProbabilityMeasure
        (balancedAccuracyTransitionCollectLaw q I sigma2 weight cap stride retries
          samples 0 (accuracyScaleFactor q • current)) := hsourceProb current
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- The cooling history is a measurable probability kernel of its initial
target-space point. -/
theorem balancedCoolingHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      Measurable (balancedCoolingHistoryLaw parameters q I variances) ∧
      ∀ point, IsProbabilityMeasure
        (balancedCoolingHistoryLaw parameters q I variances point) := by
  intro variances
  induction variances with
  | nil =>
      intro _
      constructor
      · rw [show balancedCoolingHistoryLaw parameters q I [] =
            fun point => Measure.dirac
              (some ((fun _ : ℕ => (0 : ℝ)), 0, 1, point)) by
          funext point
          rw [balancedCoolingHistoryLaw]]
        exact Measure.measurable_dirac.comp <| measurable_some.comp <|
          measurable_const.prodMk <| measurable_const.prodMk <|
            measurable_const.prodMk measurable_id
      · intro point
        rw [balancedCoolingHistoryLaw]
        infer_instance
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _
          constructor
          · rw [show balancedCoolingHistoryLaw parameters q I [sigma2] =
                fun point => Measure.dirac
                  (some ((fun _ : ℕ => (0 : ℝ)), 0, 1, point)) by
              funext point
              rw [balancedCoolingHistoryLaw]]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_const.prodMk <| measurable_const.prodMk <|
                measurable_const.prodMk measurable_id
          · intro point
            rw [balancedCoolingHistoryLaw]
            infer_instance
      | cons tau2 rest =>
          intro hpositive
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htail := ih htailPositive
          have hphase := balancedCoolingRatioLaw_measurable_and_probability
            parameters q I hsigma2 tau2
          let continuation : Option (ℝ × AmbientSpace q.n) →
              Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
            match phase with
            | none => Measure.dirac none
            | some (ratio, nextPoint) =>
                (balancedCoolingHistoryLaw parameters q I
                  (tau2 :: rest) nextPoint).map
                    (balancedCoolingHistoryCons ratio)
          have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
              (balancedCoolingHistoryLaw parameters q I
                (tau2 :: rest) value.2).map
                  (balancedCoolingHistoryCons value.1) := by
            apply measurable_measure_map_param_variable
              (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
            exact measurable_balancedCoolingHistoryCons.comp <|
              (measurable_fst.comp measurable_fst).prodMk measurable_snd
          have hcontinuation : Measurable continuation := by
            dsimp only [continuation]
            convert Measurable.optionElim
              (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
                hsome using 1
            funext phase
            cases phase <;> rfl
          have hcontinuationProb : ∀ phase,
              IsProbabilityMeasure (continuation phase) := by
            intro phase
            cases phase with
            | none =>
                dsimp only [continuation]
                infer_instance
            | some value =>
                dsimp only [continuation]
                let _ : IsProbabilityMeasure
                    (balancedCoolingHistoryLaw parameters q I
                      (tau2 :: rest) value.2) := htail.2 value.2
                exact Measure.isProbabilityMeasure_map <|
                  (measurable_balancedCoolingHistoryCons (n := q.n)).comp
                    (measurable_const.prodMk measurable_id) |>.aemeasurable
          have hlaw : balancedCoolingHistoryLaw parameters q I
                (sigma2 :: tau2 :: rest) =
              fun point =>
                (balancedCoolingRatioLaw parameters q I sigma2 tau2 point).bind
                  continuation := by
            funext point
            simp only [balancedCoolingHistoryLaw]
            apply Measure.bind_congr_right
            filter_upwards with phase
            cases phase <;> rfl
          constructor
          · rw [hlaw]
            exact (Measure.measurable_bind' hcontinuation).comp hphase.1
          · intro point
            rw [congrFun hlaw point]
            let _ : IsProbabilityMeasure
                (balancedCoolingRatioLaw parameters q I sigma2 tau2 point) :=
              hphase.2 point
            exact MeasureTheory.isProbabilityMeasure_bind
              hcontinuation.aemeasurable
                (ae_of_all _ hcontinuationProb)

/-- The executable balanced cooling product is a measurable kernel, with no
extra analytic hypothesis beyond positivity of the variances. -/
theorem balancedCoolingProduct_measurable_and_strong
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      Measurable (fun point =>
        (coolingProduct (balancedCoolingPrimitives parameters) q variances point).runEstimate
          oracle.query) ∧
      ∀ point,
        (coolingProduct (balancedCoolingPrimitives parameters) q variances point).StronglyMeasurable
          oracle.query := by
  intro variances
  induction variances with
  | nil =>
      intro _
      constructor
      · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp <| measurable_some.comp <|
          measurable_const.prodMk measurable_id
      · intro point
        simpa [coolingProduct] using
          (show (MembershipOracleProgram.pure (some (1, point)) :
            MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
                oracle.query from trivial)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _
          constructor
          · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_const.prodMk measurable_id
          · intro point
            simpa [coolingProduct] using
              (show (MembershipOracleProgram.pure (some (1, point)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
                    oracle.query from trivial)
      | cons tau2 rest =>
          intro hpositive
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htail := ih htailPositive
          have hratio :=
            balancedCoolingRatioEstimate_measurable_strong_and_law
              parameters q I oracle hsigma2 tau2
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n
                (Option (ℝ × AmbientSpace q.n)) := fun phase =>
            match phase with
            | none => .pure none
            | some (ratio, nextPoint) =>
                (coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) nextPoint).bind fun result =>
                    .pure <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (ratio * product, lastPoint)
          have htailOutput : ∀ ratio, Measurable fun result :
              Option (ℝ × AmbientSpace q.n) =>
              (.pure (match result with
                | none => none
                | some (product, lastPoint) =>
                    some (ratio * product, lastPoint)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
            intro ratio
            simp only [MembershipOracleProgram.runEstimate]
            apply Measure.measurable_dirac.comp
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                some (ratio * value.1, value.2) :=
              measurable_some.comp <|
                (measurable_const.mul measurable_fst).prodMk measurable_snd
            convert Measurable.optionElim
              (none : Option (ℝ × AmbientSpace q.n)) hsome using 1
            funext result
            cases result with
            | none => rfl
            | some value => cases value; rfl
          have hphaseStrong : ∀ phase,
              (phaseProgram phase).StronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value =>
                exact (htail.2 value.2).bind (fun _ => by trivial)
                  (htailOutput value.1)
          have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
              (phaseProgram (some value)).runEstimate oracle.query := by
            have hsource : Measurable fun value : ℝ × AmbientSpace q.n =>
                (coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query :=
              htail.1.comp measurable_snd
            have hprob : ∀ value : ℝ × AmbientSpace q.n,
                IsProbabilityMeasure
                  ((coolingProduct (balancedCoolingPrimitives parameters) q
                    (tau2 :: rest) value.2).runEstimate oracle.query) :=
              fun value =>
                MembershipOracleProgram.runEstimate_isProbabilityMeasure
                  oracle.query _ (htail.2 value.2).estimateMeasurable
            have htransform : Measurable fun p :
                (ℝ × AmbientSpace q.n) ×
                  Option (ℝ × AmbientSpace q.n) =>
                match p.2 with
                | none => none
                | some (product, lastPoint) =>
                    some (p.1.1 * product, lastPoint) := by
              have hnone : Measurable fun _ : ℝ × AmbientSpace q.n =>
                  (none : Option (ℝ × AmbientSpace q.n)) := measurable_const
              have hsome : Measurable fun p :
                  (ℝ × AmbientSpace q.n) × (ℝ × AmbientSpace q.n) =>
                  some (p.1.1 * p.2.1, p.2.2) :=
                measurable_some.comp <|
                  ((measurable_fst.comp measurable_fst).mul
                    (measurable_fst.comp measurable_snd)).prodMk
                      (measurable_snd.comp measurable_snd)
              convert Measurable.optionCases
                ((0 : ℝ), (0 : AmbientSpace q.n)) hnone hsome using 1
              funext p
              cases p.2 with
              | none => rfl
              | some value => cases value; rfl
            have hbind : Measurable fun value : ℝ × AmbientSpace q.n =>
                ((coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).bind
                    fun result => Measure.dirac <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (value.1 * product, lastPoint) :=
              measurable_measure_bind_param_variable hsource hprob
                (Measure.measurable_dirac.comp htransform)
            rw [show (fun value : ℝ × AmbientSpace q.n =>
                (phaseProgram (some value)).runEstimate oracle.query) =
              (fun value =>
                ((coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).bind
                    fun result => Measure.dirac <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (value.1 * product, lastPoint)) by
              funext value
              unfold phaseProgram
              exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
                (htail.2 value.2) (fun _ => by trivial)
                  (htailOutput value.1)]
            exact hbind
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).runEstimate oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                hsomeRun using 1
            funext phase
            cases phase <;> rfl
          have hcooling : ∀ point,
              coolingProduct (balancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (balancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind
                  phaseProgram := by
            intro point
            rw [coolingProduct]
            change (balancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                cases value with
                | mk ratio nextPoint =>
                    unfold phaseProgram
                    simp only
                    congr 1
                    funext result
                    cases result with
                    | none => rfl
                    | some value => cases value; rfl
          have hrun : (fun point =>
              (coolingProduct (balancedCoolingPrimitives parameters) q
                (sigma2 :: tau2 :: rest) point).runEstimate oracle.query) =
              fun point =>
                ((balancedCoolingRatioEstimate parameters q sigma2 tau2 point).runEstimate
                  oracle.query).bind fun phase =>
                    (phaseProgram phase).runEstimate oracle.query := by
            funext point
            rw [hcooling point]
            exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
              (hratio.2.1 point) hphaseStrong hphaseRun
          constructor
          · rw [hrun]
            exact (Measure.measurable_bind' hphaseRun).comp hratio.1
          · intro point
            rw [hcooling point]
            exact (hratio.2.1 point).bind hphaseStrong hphaseRun

/-- The executable continuation is exactly the output map of the one joint
history law.  In particular, the accumulated product and retained point are
not merely distributionally postulated phase by phase. -/
theorem balancedCoolingProduct_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      ∀ point,
        (coolingProduct (balancedCoolingPrimitives parameters) q variances point).runEstimate
            oracle.query =
          (balancedCoolingHistoryLaw parameters q I variances point).map
            balancedCoolingHistoryOutput := by
  intro variances
  induction variances with
  | nil =>
      intro _ point
      simp only [coolingProduct, MembershipOracleProgram.runEstimate]
      rw [balancedCoolingHistoryLaw, Measure.map_dirac'
        measurable_balancedCoolingHistoryOutput]
      rfl
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _ point
          simp only [coolingProduct, MembershipOracleProgram.runEstimate]
          rw [balancedCoolingHistoryLaw, Measure.map_dirac'
            measurable_balancedCoolingHistoryOutput]
          rfl
      | cons tau2 rest =>
          intro hpositive point
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htailMS := balancedCoolingProduct_measurable_and_strong
            parameters q I oracle (tau2 :: rest) htailPositive
          have htailLaw := balancedCoolingHistoryLaw_measurable_and_probability
            parameters q I (tau2 :: rest) htailPositive
          have hratio :=
            balancedCoolingRatioEstimate_measurable_strong_and_law
              parameters q I oracle hsigma2 tau2
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n
                (Option (ℝ × AmbientSpace q.n)) := fun phase =>
            match phase with
            | none => .pure none
            | some (ratio, nextPoint) =>
                (coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) nextPoint).bind fun result =>
                    .pure (balancedCoolingProductCons ratio result)
          have hproductCons (ratio : ℝ) :
              Measurable (balancedCoolingProductCons
                (n := q.n) ratio) :=
            measurable_balancedCoolingProductCons.comp
              (measurable_const.prodMk measurable_id)
          have hpureRun (ratio : ℝ) : Measurable fun result :
              Option (ℝ × AmbientSpace q.n) =>
              (.pure (balancedCoolingProductCons ratio result) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
            simp only [MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp (hproductCons ratio)
          have hphaseStrong : ∀ phase,
              (phaseProgram phase).StronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value =>
                exact (htailMS.2 value.2).bind (fun _ => by trivial)
                  (hpureRun value.1)
          have hsomeLaw : ∀ value : ℝ × AmbientSpace q.n,
              (phaseProgram (some value)).runEstimate oracle.query =
                ((coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).map
                    (balancedCoolingProductCons value.1) := by
            intro value
            unfold phaseProgram
            rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
              (htailMS.2 value.2) (fun _ => by trivial) (hpureRun value.1)]
            exact Measure.bind_dirac_eq_map _ (hproductCons value.1)
          have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
              (phaseProgram (some value)).runEstimate oracle.query := by
            rw [show (fun value : ℝ × AmbientSpace q.n =>
                (phaseProgram (some value)).runEstimate oracle.query) =
              fun value =>
                ((coolingProduct (balancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).map
                    (balancedCoolingProductCons value.1) by
              funext value
              exact hsomeLaw value]
            apply measurable_measure_map_param_variable
              (htailMS.1.comp measurable_snd)
            · intro value
              exact MembershipOracleProgram.runEstimate_isProbabilityMeasure
                oracle.query _ (htailMS.2 value.2).estimateMeasurable
            · exact measurable_balancedCoolingProductCons.comp <|
                (measurable_fst.comp measurable_fst).prodMk measurable_snd
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).runEstimate oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                hsomeRun using 1
            funext phase
            cases phase <;> rfl
          have hcooling :
              coolingProduct (balancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (balancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind
                  phaseProgram := by
            rw [coolingProduct]
            change (balancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                rcases value with ⟨ratio, nextPoint⟩
                change
                  (coolingProduct (balancedCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind (fun result =>
                      .pure <| match result with
                      | some (product, lastPoint) =>
                          some (ratio * product, lastPoint)
                      | none => none) =
                  (coolingProduct (balancedCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind (fun result =>
                      .pure (balancedCoolingProductCons ratio result))
                congr 1
                funext result
                cases result <;> rfl
          have hcontinuation : Measurable fun phase :
              Option (ℝ × AmbientSpace q.n) =>
              match phase with
              | none => Measure.dirac
                  (none : Option (BalancedCoolingHistory q.n))
              | some (ratio, nextPoint) =>
                  (balancedCoolingHistoryLaw parameters q I
                    (tau2 :: rest) nextPoint).map
                      (balancedCoolingHistoryCons ratio) := by
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                (balancedCoolingHistoryLaw parameters q I
                  (tau2 :: rest) value.2).map
                    (balancedCoolingHistoryCons value.1) := by
              apply measurable_measure_map_param_variable
                (htailLaw.1.comp measurable_snd)
                (fun value => htailLaw.2 value.2)
              exact measurable_balancedCoolingHistoryCons.comp <|
                (measurable_fst.comp measurable_fst).prodMk measurable_snd
            convert Measurable.optionElim
              (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
                hsome using 1
            funext phase
            cases phase <;> rfl
          rw [hcooling]
          rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
            (hratio.2.1 point) hphaseStrong hphaseRun]
          rw [hratio.2.2 point]
          rw [balancedCoolingHistoryLaw]
          rw [map_bind_eq_bind_map_of_measurable _ hcontinuation
            measurable_balancedCoolingHistoryOutput]
          apply Measure.bind_congr_right
          filter_upwards with phase
          cases phase with
          | none =>
              simp only [phaseProgram, MembershipOracleProgram.runEstimate]
              rw [Measure.map_dirac' measurable_balancedCoolingHistoryOutput]
              rfl
          | some value =>
              rw [hsomeLaw value, ih htailPositive value.2]
              rw [Measure.map_map
                (hproductCons value.1)
                measurable_balancedCoolingHistoryOutput]
              let mu := balancedCoolingHistoryLaw parameters q I
                (tau2 :: rest) value.2
              have hhistoryCons : Measurable
                  (balancedCoolingHistoryCons (n := q.n) value.1) :=
                measurable_balancedCoolingHistoryCons.comp
                  (measurable_const.prodMk measurable_id)
              calc
                Measure.map (balancedCoolingProductCons value.1 ∘
                    balancedCoolingHistoryOutput) mu =
                    Measure.map (balancedCoolingHistoryOutput ∘
                      balancedCoolingHistoryCons value.1) mu := by
                  apply Measure.map_congr
                  filter_upwards with history
                  exact (balancedCoolingHistoryOutput_cons
                    value.1 history).symm
                _ = (mu.map (balancedCoolingHistoryCons value.1)).map
                    balancedCoolingHistoryOutput :=
                  (Measure.map_map
                    (μ := mu)
                    (g := balancedCoolingHistoryOutput)
                    (f := balancedCoolingHistoryCons value.1)
                    measurable_balancedCoolingHistoryOutput
                    hhistoryCons).symm

/-- The single joint Gaussian-cooling history law for the explicit Figure-One
schedule.  Its sequence coordinates are the phase variables `W_j` consumed by
the dependent-product argument. -/
noncomputable def balancedFigureOneCoolingHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  balancedCoolingHistoryLaw parameters q I
    (explicitVolumeCoolingSchedule q).variances point

theorem balancedFigureOneCoolingHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (balancedFigureOneCoolingHistoryLaw parameters q I) ∧
    ∀ point, IsProbabilityMeasure
      (balancedFigureOneCoolingHistoryLaw parameters q I point) := by
  exact balancedCoolingHistoryLaw_measurable_and_probability parameters q I
    (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive

theorem balancedFigureOneCoolingProduct_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (coolingProduct (balancedCoolingPrimitives parameters) q
        (explicitVolumeCoolingSchedule q).variances point).runEstimate
          oracle.query =
      (balancedFigureOneCoolingHistoryLaw parameters q I point).map
        balancedCoolingHistoryOutput := by
  exact balancedCoolingProduct_runEstimate_eq_history_map parameters q I oracle
    (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive point

#print axioms balancedCoolingRatioEstimate_measurable_strong_and_law
#print axioms balancedCoolingHistoryLaw_measurable_and_probability
#print axioms balancedCoolingProduct_runEstimate_eq_history_map
#print axioms balancedFigureOneCoolingProduct_runEstimate_eq_history_map

end ArlibCommunity.Algorithms.CV18
