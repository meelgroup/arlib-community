/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceMomentTransfer
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProductAccuracy
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFuture

/-!
# Raw phase-mean comparison for the executable scheduled trace

The CV18 product argument only needs the marginal mean of each phase average.
It does not require replacing a complete Markov phase by an IID phase law.
This file records that weaker, paper-faithful interface: bounded scalar-law
TV comparisons give additive mean bounds, and sufficiently small phasewise
relative errors multiply to the exact `hrawApprox` premise of the trace
capstone.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal

/-! ## The raw coordinate as an immediate phase output -/

/-- Read a live phase average, sending a failed phase to zero and clamping
the otherwise nonnegative executable observation at zero. -/
def figureOneScheduledTraceLiveRawOutput
    (result : Option (ℝ × AmbientSpace n)) : ℝ :=
  match result with
  | none => 0
  | some value => max 0 value.1

theorem measurable_figureOneScheduledTraceLiveRawOutput :
    Measurable (figureOneScheduledTraceLiveRawOutput (n := n)) := by
  unfold figureOneScheduledTraceLiveRawOutput
  convert Measurable.optionElim (0 : ℝ)
    (measurable_const.max measurable_fst) using 1
  funext result
  cases result <;> rfl

/-- A trace which was already dead appends the neutral raw coordinate `1`;
a live trace appends the nonnegative phase observation (or zero on failure). -/
theorem scheduledBalancedTracePhaseVariable_append_eq_rawOutput
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid phase trace)
    (result : Option (ℝ × AmbientSpace q.n)) :
    scheduledBalancedTracePhaseVariable q (phase + 1)
        (scheduledBalancedCoolingTraceAppend trace result) =
      if trace.2 then figureOneScheduledTraceLiveRawOutput result else 1 := by
  unfold scheduledBalancedTracePhaseVariable
    scheduledBalancedTraceChronologicalPhaseVariable
    figureOneScheduledTraceLiveRawOutput
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q phase hphase]
  rcases trace with ⟨history, live⟩
  change history.2.1 = phase ∧ _ at hvalid
  cases live <;> cases result <;>
    simp [scheduledBalancedCoolingTraceAppend, balancedCoolingHistoryAppend,
      hvalid.1]

/-- At the instant a phase is appended, its mapped raw-coordinate law is
exactly the corresponding trace-dependent scalar output law. -/
theorem bind_scheduledBalancedTraceRawPhaseOutput_eq_forwardTrace_succ
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    let rho := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase
    let outK := scheduledBalancedTracePhaseOutputLaw
      figureOneFinalScheduledBalancedParameters q I phase
      figureOneScheduledTraceLiveRawOutput 1
    rho.bind outK =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
        (scheduledBalancedTracePhaseVariable q (phase + 1)) := by
  dsimp only
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I phase
    figureOneScheduledTraceLiveRawOutput 1
  let traceK := scheduledBalancedTracePhaseKernel
    figureOneFinalScheduledBalancedParameters q I phase
  let Y := scheduledBalancedTracePhaseVariable q (phase + 1)
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
    figureOneScheduledTraceLiveRawOutput 1
    measurable_figureOneScheduledTraceLiveRawOutput
  have htraceK := scheduledBalancedTracePhaseKernel_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
  have hY : Measurable Y :=
    measurable_scheduledBalancedTracePhaseVariable q (phase + 1)
  rw [show scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1) =
      rho.bind traceK by rfl,
    map_bind_eq_bind_map_of_measurable rho htraceK.1 hY]
  apply Measure.bind_congr_right
  filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
    figureOneFinalScheduledBalancedParameters q I phase] with trace hvalid
  unfold scheduledBalancedTracePhaseOutputLaw
    scheduledBalancedTracePhaseKernel
  have hconditional : Measurable
      (if trace.2 then
        (figureOneScheduledTraceLiveRawOutput (n := q.n)) else
        fun _ : Option (ℝ × AmbientSpace q.n) => (1 : ℝ)) := by
    cases trace.2
    · exact measurable_const
    · exact measurable_figureOneScheduledTraceLiveRawOutput
  have happend : Measurable (scheduledBalancedCoolingTraceAppend trace) :=
    (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
      (measurable_const.prodMk measurable_id)
  calc
    (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase trace).map
          (if trace.2 then
            (figureOneScheduledTraceLiveRawOutput (n := q.n)) else
            fun _ : Option (ℝ × AmbientSpace q.n) => (1 : ℝ)) =
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase trace).map
          (Y ∘ scheduledBalancedCoolingTraceAppend trace) := by
      apply Measure.map_congr
      filter_upwards with result
      simp only [Function.comp_apply]
      rw [show (if trace.2 = true then
          (figureOneScheduledTraceLiveRawOutput (n := q.n)) else
          fun _ : Option (ℝ × AmbientSpace q.n) => (1 : ℝ)) result =
        if trace.2 = true then
          figureOneScheduledTraceLiveRawOutput result else 1 by
          by_cases h : trace.2 = true <;> simp [h]]
      exact (scheduledBalancedTracePhaseVariable_append_eq_rawOutput
        q phase hphase trace hvalid result).symm
    _ = ((scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase trace).map
          (scheduledBalancedCoolingTraceAppend trace)).map Y :=
      (Measure.map_map hY happend).symm

/-- Later phases preserve the already-created raw coordinate law. -/
theorem map_scheduledBalancedForwardTraceLaw_rawPhase_eq_prefix
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase future : ℕ)
    (horizon : phase + 1 + future ≤ figureOneDependentPhaseCount q) :
    (scheduledBalancedForwardTraceLaw parameters q I
      (phase + 1 + future)).map
        (scheduledBalancedTracePhaseVariable q (phase + 1)) =
      (scheduledBalancedForwardTraceLaw parameters q I (phase + 1)).map
        (scheduledBalancedTracePhaseVariable q (phase + 1)) := by
  let Y := scheduledBalancedTracePhaseVariable q (phase + 1)
  have hY : Measurable Y :=
    measurable_scheduledBalancedTracePhaseVariable q (phase + 1)
  induction future with
  | zero => rfl
  | succ future ih =>
      let m := phase + 1 + future
      let law := scheduledBalancedForwardTraceLaw parameters q I m
      let K := scheduledBalancedTracePhaseKernel parameters q I m
      have hmphase : m ≤ figureOneDependentPhaseCount q := by
        dsimp only [m]
        omega
      have hK := scheduledBalancedTracePhaseKernel_measurable_and_probability
        parameters q I m
      have hpreserve : ∀ᵐ trace ∂law, ∀ᵐ next ∂K trace,
          Y next = Y trace := by
        filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
          parameters q I m] with trace hvalid
        unfold K scheduledBalancedTracePhaseKernel
        let append := scheduledBalancedCoolingTraceAppend trace
        have happend : Measurable append :=
          (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
            (measurable_const.prodMk measurable_id)
        let good : Set (ScheduledBalancedCoolingTrace q.n) :=
          {next | Y next = Y trace}
        have hgood : MeasurableSet good :=
          measurableSet_eq_fun hY measurable_const
        apply (ae_map_iff happend.aemeasurable hgood).2
        filter_upwards with result
        exact scheduledBalancedTracePhaseVariable_append_eq q hvalid hmphase
          (by omega) (by dsimp only [m]; omega) result
      have hstep : (law.bind K).map Y = law.map Y := by
        rw [map_bind_eq_bind_map_of_measurable law hK.1 hY]
        calc
          law.bind (fun trace => (K trace).map Y) =
              law.bind (fun trace => Measure.dirac (Y trace)) := by
            apply Measure.bind_congr_right
            filter_upwards [hpreserve] with trace htrace
            calc
              (K trace).map Y =
                  (K trace).map (fun _ => Y trace) :=
                Measure.map_congr htrace
              _ = Measure.dirac (Y trace) := by
                let _ : IsProbabilityMeasure (K trace) := hK.2 trace
                simp
          _ = law.map Y := Measure.bind_dirac_eq_map law hY
      have hsuccLaw : scheduledBalancedForwardTraceLaw parameters q I
          (phase + 1 + (future + 1)) = law.bind K := by rfl
      rw [hsuccLaw, hstep]
      exact ih (by omega)

/-! ## Concrete scalar `MeasureLeUpTo` comparisons -/

/-- Any immediate complete-phase comparison transports unchanged to the raw
coordinate of the final trace. -/
theorem scheduledBalancedFinalTraceRawPhase_leUpTo_of_immediate
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (target : Measure (Option (ℝ × AmbientSpace q.n)))
    {error : ENNReal}
    (himmediate :
      let rho := scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phase
      let outK := scheduledBalancedTracePhaseOutputLaw
        figureOneFinalScheduledBalancedParameters q I phase
        figureOneScheduledTraceLiveRawOutput 1
      MeasureLeUpTo (rho.bind outK)
        (target.map figureOneScheduledTraceLiveRawOutput) error) :
    MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q (phase + 1)))
      (target.map figureOneScheduledTraceLiveRawOutput) error := by
  have himmediateLaw :=
    bind_scheduledBalancedTraceRawPhaseOutput_eq_forwardTrace_succ
      q I phase hphase
  have hfuture := map_scheduledBalancedForwardTraceLaw_rawPhase_eq_prefix
    figureOneFinalScheduledBalancedParameters q I phase
      (figureOneDependentPhaseCount q - (phase + 1)) (by omega)
  have hhorizon : phase + 1 +
      (figureOneDependentPhaseCount q - (phase + 1)) =
        figureOneDependentPhaseCount q := by omega
  rw [hhorizon] at hfuture
  rw [hfuture, ← himmediateLaw]
  exact himmediate

/-- For every noninitial Gaussian phase, the final raw trace coordinate is
within the accumulated retained loss plus one fresh transition budget of the
paper-faithful complete-phase target (first point exact, common Markov tail). -/
theorem scheduledBalancedFinalTraceRawGaussianPhase_leUpTo_target
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase0 : 0 < phase) (hphase : phase < terminalPhaseSteps q) :
    MeasureLeUpTo
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q (phase + 1)))
      ((figureOneScheduledGaussianPhaseTarget q I phase).map
        figureOneScheduledTraceLiveRawOutput)
      (figureOneCorrectedTransitionBudget q +
        figureOneScheduledRetainedError q phase) := by
  let previous := phase - 1
  have hprevious : previous < terminalPhaseSteps q := by
    dsimp only [previous]
    omega
  have hpreviousSucc : previous + 1 = phase := by
    dsimp only [previous]
    omega
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I previous).map scale
  let eta := figureOneScheduledRetainedError q phase
  obtain ⟨bad, hlive, herror⟩ :=
    exists_figureOneScheduledTraceScaledLive_good_bad
      q I previous hprevious
  have hetaTop : eta ≠ ⊤ := by
    dsimp only [eta]
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun index _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure bad :=
    { measure_univ_lt_top := by
        apply lt_of_le_of_lt
        · exact le_trans (le_add_right le_rfl) herror
        · exact lt_top_iff_ne_top.mpr <| by
            simpa [eta, hpreviousSucc] using hetaTop }
  let _ : IsProbabilityMeasure rho :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I phase
  have hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I phase) := by
    simpa [good, scale, previous, hpreviousSucc,
      figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
        q I previous
  have hM8 : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM8M16 : ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  apply scheduledBalancedFinalTraceRawPhase_leUpTo_of_immediate
    q I phase (by rw [figureOneDependentPhaseCount]; omega)
      (figureOneScheduledGaussianPhaseTarget q I phase)
  apply bind_scheduledBalancedTracePhaseOutputLaw_leUpTo_of_live_good_bad
    q I phase hphase rho good bad hM8 ENNReal.ofReal_ne_top hM8M16
  · simpa [rho, good, scale, previous, hpreviousSucc] using hlive
  · exact hgood
  · simpa [rho, scale, eta, previous, hpreviousSucc] using herror
  · exact measurable_figureOneScheduledTraceLiveRawOutput

/-- Total variation transfers the first moment when the scalar observable is
bounded only almost everywhere under the two probability measures. -/
theorem Arlib.TVLe.integral_le_of_ae_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0mu : ∀ᵐ x ∂mu, 0 ≤ f x)
    (hfBmu : ∀ᵐ x ∂mu, f x ≤ B)
    (hf0nu : ∀ᵐ x ∂nu, 0 ≤ f x)
    (hfBnu : ∀ᵐ x ∂nu, f x ≤ B) :
    |(∫ x, f x ∂mu) - ∫ x, f x ∂nu| ≤ B * epsilon.toReal := by
  let g : S → ℝ := fun x => min (max 0 (f x)) B
  have hg : Measurable g := (measurable_const.max hf).min measurable_const
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    exact le_min (le_max_left _ _) hB.le
  have hgB : ∀ x, g x ≤ B := fun x => min_le_right _ _
  have hgeqmu : ∀ᵐ x ∂mu, g x = f x := by
    filter_upwards [hf0mu, hfBmu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  have hgeqnu : ∀ᵐ x ∂nu, g x = f x := by
    filter_upwards [hf0nu, hfBnu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  rw [← integral_congr_ae hgeqmu, ← integral_congr_ae hgeqnu]
  exact Arlib.TVLe.integral_le_of_nonnegative_le
    h hepsilon hg hB hg0 hgB

/-- A mapped scalar-law comparison gives the explicit additive error between
an executable trace raw mean and its chronological ideal phase mean. -/
theorem scheduledFigureOneTraceRawMean_abs_sub_ideal_le_of_mapped_tv
    (q : VolumeParams) (I : VolumeInput q.n) (j : Nat)
    {epsilon : ENNReal} (hepsilonTop : epsilon ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    (hscalar : Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q j))
      ((figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j)).map
        (figureOneIdealPhaseEstimator q
          (figureOneChronologicalPhaseAt q j))) epsilon)
    (hWB : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      scheduledBalancedTracePhaseVariable q j trace <= B)
    (hidealB : ∀ᵐ samples
        ∂figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j),
      figureOneIdealPhaseEstimator q (figureOneChronologicalPhaseAt q j)
        samples <= B) :
    |scheduledFigureOneTraceRawMean q I j -
        figureOneIdealPhaseMean q I (figureOneChronologicalPhaseAt q j)| <=
      B * epsilon.toReal := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let phase := figureOneChronologicalPhaseAt q j
  let idealLaw := figureOneIdealPhaseLaw q I phase
  let W := scheduledBalancedTracePhaseVariable q j
  let estimator := figureOneIdealPhaseEstimator q phase
  let actualScalar := mu.map W
  let idealScalar := idealLaw.map estimator
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure idealLaw :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure actualScalar :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
  let _ : IsProbabilityMeasure idealScalar :=
    Measure.isProbabilityMeasure_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
  have hactual0 : ∀ᵐ y ∂actualScalar, 0 ≤ y := by
    exact (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (scheduledBalancedTracePhaseVariable_nonnegative q j)
  have hactualB : ∀ᵐ y ∂actualScalar, y ≤ B := by
    exact (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Iic).2 hWB
  have hideal0 : ∀ᵐ y ∂idealScalar, 0 ≤ y := by
    exact (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (figureOneIdealPhaseEstimator_nonneg q phase)
  have hidealScalarB : ∀ᵐ y ∂idealScalar, y ≤ B := by
    exact (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Iic).2 hidealB
  have htransfer := Arlib.TVLe.integral_le_of_ae_nonnegative_le
    (show Arlib.TVLe actualScalar idealScalar epsilon from hscalar)
    hepsilonTop measurable_id hB hactual0 hactualB hideal0 hidealScalarB
  have hactual : (∫ y, y ∂actualScalar) =
      scheduledFigureOneTraceRawMean q I j := by
    change (∫ y, id y ∂actualScalar) = _
    rw [integral_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurable_id.aestronglyMeasurable]
    rfl
  have hideal : (∫ y, y ∂idealScalar) =
      figureOneIdealPhaseMean q I phase := by
    change (∫ y, id y ∂idealScalar) = _
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurable_id.aestronglyMeasurable]
    exact (figureOneIdealPhase_moments q I
      (figureOneSharpAcceleratedMoments q I) phase).1
  simpa [hactual, hideal, phase] using htransfer

/-- Phasewise multiplicative raw-mean errors multiply without asking for an
IID coupling of the phase histories.  The deliberately tiny `eps/128`
aggregate budget leaves exactly the `eps/64` product slack used downstream. -/
theorem scheduledFigureOneTraceRawMeanProduct_relativeApprox_ideal_of_phasewise
    (q : VolumeParams) (I : VolumeInput q.n) {delta : ℝ}
    (hdelta0 : 0 <= delta) (hdelta1 : delta <= 1)
    (hbudget : (figureOneDependentPhaseCount q : ℝ) * delta ≤ q.eps / 128)
    (hphase : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      |scheduledFigureOneTraceRawMean q I j -
          figureOneChronologicalRawMean q I j| <=
        delta * figureOneChronologicalRawMean q I j) :
    RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q)) := by
  let m := figureOneDependentPhaseCount q
  let ideal := dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) m
  let actual := dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) m
  have honeSub : 0 <= 1 - delta := by linarith
  have hidealTerms : ∀ j, 0 ≤ figureOneChronologicalRawMean q I j :=
    fun j => (figureOneChronologicalRawMean_pos q I j).le
  have hlowerTerms : ∀ j, 1 ≤ j → j ≤ m →
      (1 - delta) * figureOneChronologicalRawMean q I j <=
        scheduledFigureOneTraceRawMean q I j := by
    intro j hj1 hjm
    have hb := (abs_le.mp (hphase j hj1 hjm)).1
    linarith
  have hupperTerms : ∀ j, 1 ≤ j → j ≤ m →
      scheduledFigureOneTraceRawMean q I j <=
        (1 + delta) * figureOneChronologicalRawMean q I j := by
    intro j hj1 hjm
    have hb := (abs_le.mp (hphase j hj1 hjm)).2
    linarith
  have hlowerProduct : (1 - delta) ^ m * ideal ≤ actual := by
    change (1 - delta) ^ m *
        dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) m ≤
      dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) m
    rw [dependentPhaseMeanProduct, dependentPhaseMeanProduct]
    calc
      (1 - delta) ^ m *
          ∏ j ∈ Finset.range m, figureOneChronologicalRawMean q I (j + 1) =
          ∏ j ∈ Finset.range m,
            ((1 - delta) * figureOneChronologicalRawMean q I (j + 1)) := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro j hj
          exact mul_nonneg honeSub (hidealTerms (j + 1))
        · intro j hj
          exact hlowerTerms (j + 1) (by omega)
            (by have := Finset.mem_range.mp hj; omega)
  have hupperProduct : actual ≤ (1 + delta) ^ m * ideal := by
    change dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) m ≤
      (1 + delta) ^ m *
        dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) m
    rw [dependentPhaseMeanProduct, dependentPhaseMeanProduct]
    calc
      (∏ j ∈ Finset.range m,
          scheduledFigureOneTraceRawMean q I (j + 1)) ≤
          ∏ j ∈ Finset.range m,
            ((1 + delta) * figureOneChronologicalRawMean q I (j + 1)) := by
        apply Finset.prod_le_prod
        · intro j hj
          unfold scheduledFigureOneTraceRawMean
          exact integral_nonneg fun trace =>
            scheduledBalancedTracePhaseVariable_nonnegative q (j + 1) trace
        · intro j hj
          exact hupperTerms (j + 1) (by omega)
            (by have := Finset.mem_range.mp hj; omega)
      _ = (1 + delta) ^ m *
          ∏ j ∈ Finset.range m,
            figureOneChronologicalRawMean q I (j + 1) := by
        rw [Finset.prod_mul_distrib]
        simp
  have hpowLower : 1 - q.eps / 64 <= (1 - delta) ^ m := by
    have hbern : 1 - (m : Real) * delta <= (1 - delta) ^ m := by
      have := one_add_mul_le_pow (a := -delta) (by linarith) m
      simpa [sub_eq_add_neg] using this
    calc
      1 - q.eps / 64 ≤ 1 - (m : ℝ) * delta := by
        have hepsScale : q.eps / 128 ≤ q.eps / 64 := by
          nlinarith [q.heps.1]
        linarith
      _ ≤ (1 - delta) ^ m := hbern
  have hmdelta0 : 0 <= (m : Real) * delta := mul_nonneg (by positivity) hdelta0
  have hmdeltaHalf : (m : Real) * delta <= 1 / 2 := by
    calc
      (m : Real) * delta <= q.eps / 128 := hbudget
      _ <= 1 / 2 := by nlinarith [q.heps.2]
  have hexp : Real.exp ((m : Real) * delta) <=
      1 + 2 * ((m : Real) * delta) := by
    have hden : 0 < 1 - (m : Real) * delta := by linarith
    have hinv : Real.exp ((m : Real) * delta) <=
        (1 - (m : Real) * delta) ^ (-1 : Int) := by
      rw [zpow_neg_one, le_inv_comm₀ (Real.exp_pos _) hden, <- Real.exp_neg]
      linarith [Real.add_one_le_exp (-((m : Real) * delta))]
    have hinvLinear : (1 - (m : Real) * delta) ^ (-1 : Int) <=
        1 + 2 * ((m : Real) * delta) := by
      rw [zpow_neg_one, inv_le_iff_one_le_mul₀ hden]
      nlinarith
    exact hinv.trans hinvLinear
  have hpowUpper : (1 + delta) ^ m <= 1 + q.eps / 64 := by
    calc
      (1 + delta) ^ m <= Real.exp ((m : Real) * delta) := by
        calc
          _ <= (Real.exp delta) ^ m :=
            pow_le_pow_left₀ (by positivity) (by
              simpa [add_comm] using Real.add_one_le_exp delta) m
          _ = _ := by rw [<- Real.exp_nat_mul]
      _ <= 1 + 2 * ((m : Real) * delta) := hexp
      _ <= 1 + q.eps / 64 := by linarith
  have hideal0 : 0 <= ideal :=
    dependentPhaseMeanProduct_nonneg _ hidealTerms m
  rw [<- figureOneChronologicalRawMean_product q I]
  unfold RelativeApprox Arlib.relErr
  change (1 - q.eps / 64) * ideal <= actual /\
    actual <= (1 + q.eps / 64) * ideal
  constructor
  · exact (mul_le_mul_of_nonneg_right hpowLower hideal0).trans hlowerProduct
  · exact hupperProduct.trans
      (mul_le_mul_of_nonneg_right hpowUpper hideal0)

#print axioms Arlib.TVLe.integral_le_of_ae_nonnegative_le
#print axioms scheduledFigureOneTraceRawMean_abs_sub_ideal_le_of_mapped_tv
#print axioms scheduledFigureOneTraceRawMeanProduct_relativeApprox_ideal_of_phasewise

end ArlibCommunity.Algorithms.CV18
