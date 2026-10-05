import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLossPreservingTrace

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable def scheduledBalancedTracePhaseVariable
    (q : VolumeParams) (j : ℕ) : ScheduledBalancedCoolingTrace q.n → ℝ :=
  fun trace => max 0 (scheduledBalancedTraceChronologicalPhaseVariable q j trace)

theorem measurable_scheduledBalancedTracePhaseVariable
    (q : VolumeParams) (j : ℕ) :
    Measurable (scheduledBalancedTracePhaseVariable q j) :=
  measurable_const.max
    (measurable_scheduledBalancedTraceChronologicalPhaseVariable q j)

theorem scheduledBalancedTracePhaseVariable_nonnegative
    (q : VolumeParams) (j : ℕ) (trace : ScheduledBalancedCoolingTrace q.n) :
    0 ≤ scheduledBalancedTracePhaseVariable q j trace :=
  le_max_left _ _

noncomputable def scheduledFigureOneTraceRawMean
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ trace, scheduledBalancedTracePhaseVariable q j trace
    ∂scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)

noncomputable def scheduledFigureOneTraceTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) :
    ℕ → ScheduledBalancedCoolingTrace q.n → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (scheduledFigureOneTraceRawMean q I)
    (scheduledBalancedTracePhaseVariable q)

noncomputable def scheduledFigureOneTraceTruncatedMean
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ trace, scheduledFigureOneTraceTruncatedPhase q I j trace
    ∂scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)

noncomputable def scheduledFigureOneTraceTruncatedSecond
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ trace, scheduledFigureOneTraceTruncatedPhase q I j trace ^ 2
    ∂scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)

theorem ScheduledBalancedCoolingTraceValid.hasProduct_project
    {n m : ℕ} {trace : ScheduledBalancedCoolingTrace n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace) :
    BalancedCoolingHistoryHasProduct m
      (scheduledBalancedCoolingTraceProject trace) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false => trivial
  | true => exact ⟨hvalid.1, hvalid.2.1⟩

theorem balancedFigureOneHistoryEstimate_traceProject_eq
    (q : VolumeParams) (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid
      (figureOneDependentPhaseCount q) trace) :
    balancedFigureOneHistoryEstimate q
        (scheduledBalancedCoolingTraceProject trace) =
      initialGaussianIntegral q * trace.1.2.2.1 := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      simp only [scheduledBalancedCoolingTraceProject,
        balancedFigureOneHistoryEstimate]
      rw [hvalid.2.2 rfl, mul_zero]
  | true => rfl

/-- Corrected Lemma 7.15-to-base-failure capstone over the loss-preserving
trace.  Later failure no longer changes earlier phase variables.  Structural
support, product, projection, and nonnegativity premises are discharged; the
remaining hypotheses are exactly finite executable moments, phasewise Lemma
7.17(c), and the product-center estimates. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_trace_lemma717bc
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hpoint : ∀ point,
      MembershipOracleProgram.runEstimate oracle.query
          (scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point) =
        (scheduledBalancedForwardHistoryLawFromPoint
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q) point).map
            (balancedFigureOneHistoryEstimate q))
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (scheduledBalancedTracePhaseVariable q j)
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hmeanPos : ∀ j, 0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j,
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j,
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j,
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    FigureOnePostInitialDirectFailureBoundFor q I fun point =>
      (scheduledBalancedFigureOnePointContinuation
        figureOneFinalScheduledBalancedParameters q point).runEstimate
          oracle.query := by
  let parameters := figureOneFinalScheduledBalancedParameters
  let mu := scheduledBalancedForwardTraceLaw parameters q I
    (figureOneDependentPhaseCount q)
  let W := scheduledBalancedTracePhaseVariable q
  let rawMean := scheduledFigureOneTraceRawMean q I
  let V := scheduledFigureOneTraceTruncatedPhase q I
  let mean := scheduledFigureOneTraceTruncatedMean q I
  let second := scheduledFigureOneTraceTruncatedSecond q I
  let continuation : AmbientSpace q.n → Measure ℝ := fun point =>
    (scheduledBalancedFigureOnePointContinuation parameters q point).runEstimate
      oracle.query
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure parameters q I _
  have hWmeas : ∀ j, Measurable (W j) := fun j =>
    measurable_scheduledBalancedTracePhaseVariable q j
  have hW0 : ∀ j trace, 0 ≤ W j trace := fun j trace =>
    scheduledBalancedTracePhaseVariable_nonnegative q j trace
  have hVmeas : ∀ j, Measurable (V j) := fun j =>
    (hWmeas j).min measurable_const
  have hV0 : ∀ j trace, 0 ≤ V j trace := by
    intro j trace
    exact le_min (hW0 j trace)
      (mul_nonneg (figureOneDependentAlpha_pos q).le
        (hrawMeanPos j).le)
  have hVcap : ∀ j trace,
      V j trace ≤ figureOneDependentAlpha q * rawMean j := fun j trace =>
    min_le_right _ _
  have htail := measure_dependentPhaseSampleProduct_figureOne_le
    q mu mean rawMean second V W
      (fun j => (hmeanPos j).le) hmeanPos
      (fun j => (hrawMeanPos j).le) hrawMeanPos hrawMean_le
      (fun j => (sq_nonneg (mean j)).trans (hmeanSecond j))
      hmeanSecond hrawSecond hVmeas hV0 hVcap
      (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
      (fun j _ _ => hWmeas j) (fun j _ _ => hW0 j)
      hWint (fun _ _ _ => rfl) hind hrelative htailSecond
  have hhistory :=
    bind_scheduledBalancedFigureOnePointContinuation_eq_forwardHistory_map_of_pointwise
      parameters q I oracle hpoint
  have htraceProjection := map_scheduledBalancedForwardTraceLaw_project
    parameters q I (figureOneDependentPhaseCount q)
  have hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        mu.map fun trace => initialGaussianIntegral q *
          dependentPhaseSampleProduct W
            (figureOneDependentPhaseCount q) trace := by
    rw [hhistory, ← htraceProjection]
    rw [Measure.map_map (measurable_balancedFigureOneHistoryEstimate q)
      measurable_scheduledBalancedCoolingTraceProject]
    apply Measure.map_congr
    filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
      parameters q I (figureOneDependentPhaseCount q),
      scheduledBalancedForwardTraceLaw_ae_coordinatesNonnegative
        parameters q I (figureOneDependentPhaseCount q)]
      with trace hvalid hnonnegative
    change balancedFigureOneHistoryEstimate q
      (scheduledBalancedCoolingTraceProject trace) = _
    rw [balancedFigureOneHistoryEstimate_traceProject_eq q trace hvalid]
    congr 1
    rw [← dependentPhaseSampleProduct_scheduledBalancedTrace_eq q trace hvalid]
    unfold dependentPhaseSampleProduct
    apply Finset.prod_congr rfl
    intro j hj
    simp only [W, scheduledBalancedTracePhaseVariable]
    rw [max_eq_right]
    unfold ScheduledBalancedCoolingTraceCoordinatesNonnegative at hnonnegative
    have hjraw := hnonnegative.2 j (Finset.mem_range.mp hj)
    simpa [scheduledBalancedTraceChronologicalPhaseVariable,
      balancedCoolingChronologicalPhaseVariable_apply_succ q j
        (Finset.mem_range.mp hj)] using hjraw
  have hX : Measurable
      (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q)) := by
    unfold dependentPhaseSampleProduct
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j _ => hWmeas (j + 1)
  have hpost := figureOnePostInitialDirectFailureBoundFor_of_dependentProduct
    q I continuation (figureOneRadialTruncationBound q I hrounded) mu
      (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      hX hmeanApprox hlaw htail
  exact hpost

/-- The direct trace argument, followed by the legacy non-aborting base
transport.  The direct theorem above is also reusable by the faithful
aborting implementation. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_trace_lemma717bc
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hpoint : ∀ point,
      MembershipOracleProgram.runEstimate oracle.query
          (scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point) =
        (scheduledBalancedForwardHistoryLawFromPoint
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q) point).map
            (balancedFigureOneHistoryEstimate q))
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (scheduledBalancedTracePhaseVariable q j)
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hmeanPos : ∀ j, 0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j,
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j,
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j,
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledBalancedBase_failure_le_of_directPostInitial
    q I oracle
  exact figureOnePostInitialDirectFailureBoundFor_of_trace_lemma717bc
    q I oracle hrounded hpoint hWint hmeanPos hrawMeanPos hrawMean_le
      hmeanSecond hrawSecond hind hrelative htailSecond hmeanApprox

#print axioms figureOnePostInitialDirectFailureBoundFor_of_trace_lemma717bc
#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_lemma717bc

end ArlibCommunity.Algorithms.CV18
