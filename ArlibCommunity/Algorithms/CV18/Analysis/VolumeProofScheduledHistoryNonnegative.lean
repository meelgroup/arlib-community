import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalPhase
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledConcreteTransition

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A failed phase is harmless for support statements; a successful phase has
nonnegative accumulated weight. -/
def ScheduledCollectedTotalNonnegative {n : ℕ} :
    Option (ℝ × AmbientSpace n) → Prop
  | none => True
  | some result => 0 ≤ result.1

theorem measurableSet_scheduledCollectedTotalNonnegative :
    MeasurableSet {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalNonnegative result} := by
  let A : Set (ℝ × AmbientSpace n) := {result | 0 ≤ result.1}
  have hA : MeasurableSet A :=
    (measurable_fst : Measurable fun result : ℝ × AmbientSpace n =>
      result.1) measurableSet_Ici
  rw [show {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalNonnegative result} =
      {none} ∪ optionSomeEvent A by
    ext result
    cases result <;> simp [ScheduledCollectedTotalNonnegative,
      optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

/-- Nonnegative sample weights make every successful accumulated total
nonnegative.  This is a support property of the exact scheduled transition
recursion and uses no mixing approximation. -/
theorem scheduledBalancedTransitionCollectLaw_ae_total_nonnegative
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples total current, 0 ≤ total →
      ∀ᵐ result ∂scheduledBalancedTransitionCollectLaw q I sigma2 weight
          proposalCap properStride retryLimit samples total current,
        ScheduledCollectedTotalNonnegative result := by
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  intro samples
  induction samples with
  | zero =>
      intro total current htotal
      unfold scheduledBalancedTransitionCollectLaw
      apply (ae_dirac_iff
        measurableSet_scheduledCollectedTotalNonnegative).2
      simpa [ScheduledCollectedTotalNonnegative] using htotal
  | succ samples ih =>
      intro total current htotal
      let tail : Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
        match result with
        | none => Measure.dirac none
        | some target =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target)
      have htail : Measurable tail := by
        dsimp only [tail]
        have hcollect :=
          (scheduledBalancedTransitionCollectLaw_measurable_and_probability
            q I hsigma2 hweight proposalCap properStride retryLimit samples).1
        have hsome : Measurable fun target : AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target) :=
          hcollect.comp <|
            (measurable_const.add hweight).prodMk <|
              (measurable_const : Measurable fun _ : AmbientSpace q.n =>
                accuracyScaleFactor q).smul measurable_id
        convert Measurable.optionElim
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
            hsome using 1
        ext result
        cases result <;> rfl
      let good : Set (Option (ℝ × AmbientSpace q.n)) :=
        {result | ScheduledCollectedTotalNonnegative result}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledCollectedTotalNonnegative
      change ∀ᵐ result ∂
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit current).bind tail,
        ScheduledCollectedTotalNonnegative result
      apply MeasureTheory.mem_ae_iff.mpr
      change ((scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit current).bind tail) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl htail.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with result
      cases result with
      | none =>
          change (Measure.dirac
            (none : Option (ℝ × AmbientSpace q.n))) goodᶜ = 0
          rw [Measure.dirac_apply' _ hgood.compl]
          simp [good, ScheduledCollectedTotalNonnegative]
      | some target =>
          exact MeasureTheory.mem_ae_iff.mp <|
            ih (total + weight target) (accuracyScaleFactor q • target)
              (add_nonneg htotal (hweight0 target))

theorem gaussianRatioWeight_nonnegative (sigma2 tau2 : ℝ)
    (x : AmbientSpace n) :
    0 ≤ gaussianRatioWeight sigma2 tau2 x := by
  unfold gaussianRatioWeight
  exact div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem uniformRatioWeight_nonnegative (sigma2 : ℝ)
    (x : AmbientSpace n) :
    0 ≤ uniformRatioWeight sigma2 x :=
  (Real.exp_pos _).le

/-- Every successful scheduled Gaussian phase returns a nonnegative sample
average. -/
theorem scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_nonnegative
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedCoolingRatioTransitionLaw parameters q I
        sigma2 tau2 current,
      ScheduledCollectedTotalNonnegative result := by
  unfold scheduledBalancedCoolingRatioTransitionLaw
  apply (ae_map_iff
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOnePhaseSampleCount q sigma2)).aemeasurable
    measurableSet_scheduledCollectedTotalNonnegative).2
  filter_upwards [scheduledBalancedTransitionCollectLaw_ae_total_nonnegative
    q I hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
      (gaussianRatioWeight_nonnegative sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2) 0
      (accuracyScaleFactor q • current) (by positivity)] with result hresult
  cases result with
  | none => trivial
  | some result =>
      simpa [balancedCoolingAverage, ScheduledCollectedTotalNonnegative] using
        div_nonneg hresult (Nat.cast_nonneg _)

/-- Every successful scheduled terminal phase returns a nonnegative sample
average. -/
theorem scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_nonnegative
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedCoolingUniformTransitionLaw parameters q I
        sigma2 current,
      ScheduledCollectedTotalNonnegative result := by
  unfold scheduledBalancedCoolingUniformTransitionLaw
  apply (ae_map_iff
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOneSampleCount q)).aemeasurable
    measurableSet_scheduledCollectedTotalNonnegative).2
  filter_upwards [scheduledBalancedTransitionCollectLaw_ae_total_nonnegative
    q I hsigma2 (measurable_uniformRatioWeight sigma2)
      (uniformRatioWeight_nonnegative sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) 0
      (accuracyScaleFactor q • current) (by positivity)] with result hresult
  cases result with
  | none => trivial
  | some result =>
      simpa [balancedCoolingAverage, ScheduledCollectedTotalNonnegative] using
        div_nonneg hresult (Nat.cast_nonneg _)

/-- A chronological history has the expected finite length and every stored
phase ratio in that prefix is nonnegative. -/
def BalancedCoolingHistoryHasNonnegativeCoordinates (m : ℕ) :
    Option (BalancedCoolingHistory n) → Prop
  | none => True
  | some history =>
      history.2.1 = m ∧ ∀ j, j < m → 0 ≤ history.1 j

theorem measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates
    (m : ℕ) :
    MeasurableSet {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasNonnegativeCoordinates m history} := by
  let A : Set (BalancedCoolingHistory n) := {history |
    history.2.1 = m ∧ ∀ j, j < m → 0 ≤ history.1 j}
  let B : Set (BalancedCoolingHistory n) :=
    ⋂ j ∈ Finset.range m, {history | 0 ≤ history.1 j}
  have hB : MeasurableSet B := by
    dsimp only [B]
    apply Finset.measurableSet_biInter
    intro j hj
    exact ((measurable_pi_apply j).comp
      (measurable_fst : Measurable fun history : BalancedCoolingHistory n =>
        history.1)) measurableSet_Ici
  have hAB : A =
      {history : BalancedCoolingHistory n | history.2.1 = m} ∩ B := by
    ext history
    simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.mem_range]
  have hA : MeasurableSet A := by
    rw [hAB]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter hB
  rw [show {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasNonnegativeCoordinates m history} =
      {none} ∪ optionSomeEvent A by
    ext history
    cases history <;> simp [BalancedCoolingHistoryHasNonnegativeCoordinates,
      optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

theorem BalancedCoolingHistoryHasNonnegativeCoordinates.snocTerminal
    {history : BalancedCoolingHistory n}
    (hcoordinates :
      BalancedCoolingHistoryHasNonnegativeCoordinates m (some history))
    {terminal : Option (ℝ × AmbientSpace n)}
    (hterminal : ScheduledCollectedTotalNonnegative terminal) :
    BalancedCoolingHistoryHasNonnegativeCoordinates (m + 1)
      (balancedCoolingHistorySnocTerminal history terminal) := by
  cases terminal with
  | none => trivial
  | some terminal =>
      simp only [BalancedCoolingHistoryHasNonnegativeCoordinates,
        balancedCoolingHistorySnocTerminal] at hcoordinates ⊢
      constructor
      · omega
      · intro j hj
        by_cases heq : j = history.2.1
        · change 0 ≤ terminal.1 at hterminal
          simpa [heq] using hterminal
        · simp only [heq, if_false]
          exact hcoordinates.2 j (by omega)

/-- One scheduled phase preserves nonnegativity of every chronological
coordinate while extending the finite prefix by one. -/
theorem scheduledBalancedForwardPhaseKernel_ae_nonnegativeCoordinates
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (history : Option (BalancedCoolingHistory q.n))
    (hcoordinates :
      BalancedCoolingHistoryHasNonnegativeCoordinates m history) :
    ∀ᵐ next ∂scheduledBalancedForwardPhaseKernel parameters q I phase history,
      BalancedCoolingHistoryHasNonnegativeCoordinates (m + 1) next := by
  cases history with
  | none =>
      unfold scheduledBalancedForwardPhaseKernel
      apply (ae_dirac_iff
        (measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates _)).2
      trivial
  | some history =>
      unfold scheduledBalancedForwardPhaseKernel
      split_ifs
      · apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates _)).2
        filter_upwards [
          scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_nonnegative
            parameters q I (scheduleValue_pos q phase)
              (scheduleValue q (phase + 1)) history.2.2.2] with result hresult
        exact hcoordinates.snocTerminal hresult
      · apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates _)).2
        filter_upwards [
          scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_nonnegative
            parameters q I (terminalVariance_pos' q) history.2.2.2]
          with result hresult
        exact hcoordinates.snocTerminal hresult

/-- The complete scheduled forward law is supported on histories whose
consumed chronological coordinates are all nonnegative. -/
theorem scheduledBalancedForwardHistoryLaw_ae_nonnegativeCoordinates
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ history ∂scheduledBalancedForwardHistoryLaw parameters q I phases,
      BalancedCoolingHistoryHasNonnegativeCoordinates phases history := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardHistoryLaw
      apply (ae_map_iff measurable_balancedCoolingInitialHistory.aemeasurable
        (measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates 0)).2
      filter_upwards with point
      simp [balancedCoolingInitialHistory,
        BalancedCoolingHistoryHasNonnegativeCoordinates]
  | succ phases ih =>
      let prefixLaw :=
        scheduledBalancedForwardHistoryLaw parameters q I phases
      let kernel := scheduledBalancedForwardPhaseKernel parameters q I phases
      let good : Set (Option (BalancedCoolingHistory q.n)) :=
        {history |
          BalancedCoolingHistoryHasNonnegativeCoordinates (phases + 1) history}
      have hgood : MeasurableSet good :=
        measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates _
      have hkernel : Measurable kernel :=
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phases).1
      change ∀ᵐ history ∂prefixLaw.bind kernel,
        BalancedCoolingHistoryHasNonnegativeCoordinates (phases + 1) history
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with history hhistory
      exact MeasureTheory.mem_ae_iff.mp
        (scheduledBalancedForwardPhaseKernel_ae_nonnegativeCoordinates
          parameters q I phases phases history hhistory)

/-- The exact finite-horizon support premise consumed by the scheduled
Lemma 7.15 capstone. -/
theorem figureOneFinalScheduledForwardHistoryLaw_ae_phaseVariable_nonnegative
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ history ∂scheduledBalancedForwardHistoryLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
        0 ≤ balancedCoolingChronologicalPhaseVariable q j history := by
  filter_upwards [
    scheduledBalancedForwardHistoryLaw_ae_nonnegativeCoordinates
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)] with history hhistory
  intro j hj1 hjm
  cases history with
  | none =>
      simp [balancedCoolingChronologicalPhaseVariable,
        balancedCoolingHistoryPhaseCoordinate]
  | some history =>
      have hjrepr : j = (j - 1) + 1 := by omega
      rw [hjrepr, balancedCoolingChronologicalPhaseVariable_apply_succ q
        (j - 1) (by omega) (some history)]
      exact hhistory.2 (j - 1) (by omega)

/-- Cap-aware, schedule-instantiated form of CV18 Lemma 7.17(c) for one
complete phase.  All transition-level analytic, retry, and local-cap premises
are discharged; the sole probabilistic input is the paper's warmness of the
retained phase-start marginal relative to the scheduled speedy law. -/
theorem approxIndepFun_figureOneFinalScheduledCompletePhase_of_warm
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (hbaseWarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (history.map state)
      (Arlib.MarkovChains.ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight
            (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
            (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
            (samples + 1) 0 current) ∘ state)) := by
  let target : Measure (Option (AmbientSpace q.n)) :=
    (truncatedGaussianProbability q I sigma2 hsigma2 :
      Measure (AmbientSpace q.n)).map some
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let _ : IsProbabilityMeasure (history.map state) :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  let delta := figureOneCorrectedTransitionBudget q
  have hdelta : delta ≠ ⊤ := by
    simp [delta, figureOneCorrectedTransitionBudget]
  have hfirst : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu (history.map state) →
      MeasureLeUpTo
        (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
        target delta := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    let transition := scheduledBalancedAccuracyTransitionLawAux q I sigma2
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
    have htransition :=
      scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
        q I hsigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
    let _ : IsProbabilityMeasure (mu.bind transition) :=
      MeasureTheory.isProbabilityMeasure_bind htransition.1.aemeasurable
        (ae_of_all _ htransition.2)
    exact MeasureLeUpTo.of_tvLe <|
      bind_figureOneFinalScheduledBalancedTransition_tvLe
        q I hsigma2 (history.map state) hbaseWarm mu hmu hwarm
  have hbudget : (delta + delta).toReal ≤
      3 * (figureOneDependentMaxSampleCount q : ℝ) *
        (figureOneDependentPhaseCount q : ℝ) *
          figureOnePerSampleMixingError q := by
    have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
      exact_mod_cast figureOneDependentMaxSampleCount_pos q
    have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
      exact_mod_cast figureOneDependentPhaseCount_pos q
    have hnu := figureOnePerSampleMixingError_pos q
    rw [ENNReal.toReal_add hdelta hdelta]
    simp only [delta, figureOneCorrectedTransitionBudget,
      ENNReal.toReal_ofReal hnu.le]
    have hkm : (1 : ℝ) ≤
        figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ figureOneDependentMaxSampleCount q *
            figureOneDependentPhaseCount q :=
          mul_le_mul hk hm (by positivity) (by positivity)
    have hcoef : (2 : ℝ) ≤
        3 * figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q := by nlinarith
    calc
      figureOnePerSampleMixingError q +
          figureOnePerSampleMixingError q =
        2 * figureOnePerSampleMixingError q := by ring
      _ ≤ (3 * figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q) *
            figureOnePerSampleMixingError q :=
        mul_le_mul_of_nonneg_right hcoef hnu.le
      _ = _ := by ring
  have hresult :=
    approxIndepFun_scheduledBalancedCompletePhase_of_warm_first
      q I hsigma2 hweight
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
      samples history state hstate target hdelta hfirst pastProduct
      nextEstimator hpastProduct hnextEstimator
      (figureOneDependentMaxSampleCount q)
      (figureOneDependentPhaseCount q)
      (figureOnePerSampleMixingError q) hbudget
  rw [figureOne_lemma717c_budget q] at hresult
  exact hresult

#print axioms scheduledBalancedTransitionCollectLaw_ae_total_nonnegative
#print axioms figureOneFinalScheduledForwardHistoryLaw_ae_phaseVariable_nonnegative
#print axioms approxIndepFun_figureOneFinalScheduledCompletePhase_of_warm

end ArlibCommunity.Algorithms.CV18
