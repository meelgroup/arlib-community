/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGoodBadIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFuture

/-! # Full retained-state good/bad decomposition for the scheduled trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open _root_.Arlib _root_.Arlib.MarkovChains

/-! ## The asymmetric form of Lemma 7.17(b) -/

/-- In the good/bad trace argument the conditioned next-phase law pays twice
the accumulated bad mass, whereas the unconditional law pays it only once.
Keeping those two errors separate is essential: replacing both by the larger
one loses a factor four and no longer fits CV18's `3 k m nu` allocation. -/
theorem approxIndepFun_sequentialPairLaw_of_asymmetric_leUpTo
    {H T : Type*} [MeasurableSpace H] [MeasurableSpace T]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (K : H → Measure T) (hK : Measurable K)
    (hKprob : ∀ h, IsProbabilityMeasure (K h))
    (target : Measure T) [IsProbabilityMeasure target]
    {conditionedError baseError : ENNReal}
    (hconditionedTop : conditionedError ≠ ⊤)
    (hbaseTop : baseError ≠ ⊤)
    (hconditioned : ∀ mu : Measure H, IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo (mu.bind K) target conditionedError)
    (hbase : MeasureLeUpTo (rho.bind K) target baseError) :
    ApproxIndepFun (conditionedError + baseError).toReal
      Prod.fst Prod.snd (sequentialPairLaw rho K) := by
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
    rho hK hKprob (ENNReal.add_ne_top.mpr
      ⟨hconditionedTop, hbaseTop⟩)
  intro A hA hhalf
  have hAposReal : 0 < rho.real A :=
    lt_of_lt_of_le (by norm_num) hhalf
  have hA0 : rho A ≠ 0 := by
    intro hzero
    rw [measureReal_def, hzero] at hAposReal
    simp at hAposReal
  let hcondProb : IsProbabilityMeasure (Arlib.condOn rho A) :=
    Arlib.isProbabilityMeasure_condOn rho hA0 (measure_ne_top rho A)
  let _ : IsProbabilityMeasure (Arlib.condOn rho A) := hcondProb
  let _ : IsProbabilityMeasure ((Arlib.condOn rho A).bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  have hleft := hconditioned (Arlib.condOn rho A) hcondProb
    (isWarm_condOn_two_of_half rho hA hhalf)
  exact hleft.to_tvLe.trans hbase.to_tvLe.symm

/-! ## Exact arithmetic of the accumulated retained error -/

theorem figureOneScheduledRetainedError_toReal_le
    (q : VolumeParams) (phases : ℕ) :
    (figureOneScheduledRetainedError q phases).toReal ≤
      figureOnePerSampleMixingError q / 4 +
        (phases : ℝ) * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q := by
  have hnu : 0 ≤ figureOnePerSampleMixingError q :=
    (figureOnePerSampleMixingError_pos q).le
  have htarget := scheduledBalancedStationaryTargetError_le_targetBudget q
  have htargetBudgetTop : figureOneCorrectedTargetBudget q ≠ ⊤ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have htargetTop : scheduledBalancedStationaryTargetError q ≠ ⊤ :=
    ne_top_of_le_ne_top htargetBudgetTop htarget
  have htermTop : ∀ phase,
      figureOnePhaseSampleCount q (scheduleValue q phase) •
          figureOneCorrectedTransitionBudget q ≠ ⊤ := by
    intro phase
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top
  have hsumTop : (∑ phase ∈ Finset.range phases,
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 fun phase _ => htermTop phase
  rw [figureOneScheduledRetainedError,
    ENNReal.toReal_add htargetTop hsumTop]
  calc
    (scheduledBalancedStationaryTargetError q).toReal +
        (∑ phase ∈ Finset.range phases,
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q).toReal ≤
      (figureOneCorrectedTargetBudget q).toReal +
        ∑ phase ∈ Finset.range phases,
          (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) *
            figureOnePerSampleMixingError q := by
      apply add_le_add
      · exact ENNReal.toReal_mono htargetBudgetTop htarget
      · rw [ENNReal.toReal_sum fun phase _ => htermTop phase]
        apply Finset.sum_le_sum
        intro phase hphase
        rw [ENNReal.toReal_nsmul,
          figureOneCorrectedTransitionBudget,
          ENNReal.toReal_ofReal hnu]
        simp [nsmul_eq_mul]
    _ ≤ figureOnePerSampleMixingError q / 4 +
        ∑ _phase ∈ Finset.range phases,
          (figureOneDependentMaxSampleCount q : ℝ) *
            figureOnePerSampleMixingError q := by
      apply add_le_add
      · simp [figureOneCorrectedTargetBudget,
          figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
          ENNReal.toReal_ofReal hnu]
      · apply Finset.sum_le_sum
        intro phase hphase
        have hcount :
            (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) ≤
              (figureOneDependentMaxSampleCount q : ℝ) := by
          exact_mod_cast figureOnePhaseSampleCount_le_dependentMax
            q (scheduleValue q phase)
        exact mul_le_mul_of_nonneg_right hcount hnu
    _ = figureOnePerSampleMixingError q / 4 +
        (phases : ℝ) * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The asymmetric conditioned/unconditioned comparison fits exactly inside
the paper's dependence budget at every noninitial chronological phase. -/
theorem figureOneScheduledRetained_asymmetric_budget
    (q : VolumeParams) (phases : ℕ)
    (hphases : phases < figureOneDependentPhaseCount q) :
    ((figureOneCorrectedTransitionBudget q +
          2 * figureOneScheduledRetainedError q phases) +
        (figureOneCorrectedTransitionBudget q +
          figureOneScheduledRetainedError q phases)).toReal ≤
      figureOneDependentEpsilon q := by
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have herrTop : figureOneScheduledRetainedError q phases ≠ ⊤ := by
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun phase _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  have hbudgetReal := figureOneScheduledRetainedError_toReal_le q phases
  have htransitionTop : figureOneCorrectedTransitionBudget q ≠ ⊤ := by
    simp [figureOneCorrectedTransitionBudget]
  have htwoErrorTop : 2 * figureOneScheduledRetainedError q phases ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) herrTop
  have hreal :
      ((figureOneCorrectedTransitionBudget q +
            2 * figureOneScheduledRetainedError q phases) +
          (figureOneCorrectedTransitionBudget q +
            figureOneScheduledRetainedError q phases)).toReal =
        2 * figureOnePerSampleMixingError q +
          3 * (figureOneScheduledRetainedError q phases).toReal := by
    rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨htransitionTop, htwoErrorTop⟩)
        (ENNReal.add_ne_top.mpr ⟨htransitionTop, herrTop⟩),
      ENNReal.toReal_add htransitionTop htwoErrorTop,
      ENNReal.toReal_add htransitionTop herrTop,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      figureOneCorrectedTransitionBudget,
      ENNReal.toReal_ofReal hnu.le]
    ring
  rw [hreal]
  have hphaseCast : (phases : ℝ) + 1 ≤
      figureOneDependentPhaseCount q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hphases)
  have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hphaseProduct := mul_le_mul_of_nonneg_right hphaseCast
    (mul_nonneg
      (show 0 ≤ (figureOneDependentMaxSampleCount q : ℝ) by positivity)
      hnu.le)
  have hnuProduct := mul_le_mul_of_nonneg_right hk hnu.le
  rw [← figureOne_lemma717c_budget q]
  nlinarith [hphaseProduct, hnuProduct]

/-! ## Completing only the live subprobability -/

/-- A subprobability dominated by a warm good part and a bad part can be
completed to a warm probability measure while charging only the bad part.
Unlike completing the full live/dead state marginal, this leaves the dead
mass available for its actual absorbing output. -/
theorem exists_warm_probability_of_submeasure_le_good_add_bad
    {Omega : Type*} [MeasurableSpace Omega]
    (sub good bad pi : Measure Omega)
    [IsFiniteMeasure sub] [IsFiniteMeasure bad] [IsProbabilityMeasure pi]
    {M : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hsubMass : sub Set.univ ≤ 1)
    (hsub : sub ≤ good + bad) (hgood : Arlib.IsWarm M good pi) :
    ∃ nu : Measure Omega, IsProbabilityMeasure nu ∧
      Arlib.IsWarm M nu pi ∧ sub ≤ nu + bad := by
  let residual := sub - bad
  have hresidualLeGood : residual ≤ good :=
    Measure.sub_le_of_le_add hsub
  have hgoodLe : good ≤ M • pi :=
    (isWarm_iff_le_smul good pi).1 hgood
  have hresidualLe : residual ≤ M • pi :=
    hresidualLeGood.trans hgoodLe
  have hresidualMass : residual Set.univ ≤ 1 :=
    (Measure.le_iff'.mp (Measure.sub_le (μ := sub) (ν := bad))
      Set.univ).trans hsubMass
  let missing := 1 - residual Set.univ
  let capacity := M • pi - residual
  have hcapacityMass : capacity Set.univ = M - residual Set.univ := by
    rw [show capacity = M • pi - residual by rfl,
      Measure.sub_apply MeasurableSet.univ hresidualLe,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have hmissingLeCapacity : missing ≤ capacity Set.univ := by
    rw [hcapacityMass]
    exact tsub_le_tsub_right hM (residual Set.univ)
  by_cases hmissing0 : missing = 0
  · refine ⟨residual, ?_, ?_, ?_⟩
    · refine ⟨?_⟩
      apply le_antisymm hresidualMass
      exact (tsub_eq_zero_iff_le).mp hmissing0
    · exact (isWarm_iff_le_smul residual pi).2 hresidualLe
    · exact (Measure.sub_le_iff_le_add (μ := sub) (ν := bad)
        (ξ := residual)).mp le_rfl
  · have hcapacity0 : capacity Set.univ ≠ 0 := by
      intro hzero
      apply hmissing0
      apply bot_unique
      simpa [hzero] using hmissingLeCapacity
    have hcapacityTop : capacity Set.univ ≠ ⊤ := by
      rw [hcapacityMass]
      exact ne_top_of_le_ne_top hMtop tsub_le_self
    let coefficient := missing / capacity Set.univ
    have hcoefficientLe : coefficient ≤ 1 :=
      ENNReal.div_le_iff_le_mul (Or.inl hcapacity0)
        (Or.inl hcapacityTop) |>.2 <| by
          simpa using hmissingLeCapacity
    let filler := coefficient • capacity
    let nu := residual + filler
    have hfillerLe : filler ≤ capacity := by
      apply Measure.le_iff'.mpr
      intro S
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact mul_le_of_le_one_left bot_le hcoefficientLe
    have hnuLe : nu ≤ M • pi := by
      calc
        nu = residual + filler := rfl
        _ ≤ residual + capacity := by gcongr
        _ = M • pi := by
          rw [show capacity = M • pi - residual by rfl, add_comm,
            Measure.sub_add_cancel_of_le hresidualLe]
    have hfillerMass : filler Set.univ = missing := by
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact ENNReal.div_mul_cancel hcapacity0 hcapacityTop
    have hnuMass : nu Set.univ = 1 := by
      rw [show nu = residual + filler by rfl, Measure.add_apply,
        hfillerMass, show missing = 1 - residual Set.univ by rfl]
      exact add_tsub_cancel_of_le hresidualMass
    let hnuProb : IsProbabilityMeasure nu := ⟨hnuMass⟩
    refine ⟨nu, hnuProb, (isWarm_iff_le_smul nu pi).2 hnuLe, ?_⟩
    calc
      sub ≤ residual + bad :=
        (Measure.sub_le_iff_le_add (μ := sub) (ν := bad)
          (ξ := residual)).mp le_rfl
      _ ≤ nu + bad := by
        gcongr
        exact Measure.le_add_right le_rfl

/-- Run a common transition on the live submeasure and emit an arbitrary
probability output on the absorbing dead mass.  The warm completion above
shows that the total additive loss is the transition budget plus the sum of
the live bad mass and dead mass, with neither charged twice. -/
theorem measureLeUpTo_live_dead_bind_of_good_bad
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (live dead good bad pi : Measure S)
    [IsFiniteMeasure live] [IsFiniteMeasure dead] [IsFiniteMeasure bad]
    [IsProbabilityMeasure pi]
    {M eta budget : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hmass : live Set.univ + dead Set.univ = 1)
    (hlive : live ≤ good + bad) (hgood : Arlib.IsWarm M good pi)
    (herror : bad Set.univ + dead Set.univ ≤ eta)
    (K : S → Measure T) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (deadOutput target : Measure T) [IsProbabilityMeasure deadOutput]
    [IsProbabilityMeasure target]
    (hmix : ∀ nu : Measure S, IsProbabilityMeasure nu →
      Arlib.IsWarm M nu pi →
      MeasureLeUpTo (nu.bind K) target budget) :
    MeasureLeUpTo
      (live.bind K + dead Set.univ • deadOutput) target (budget + eta) := by
  have hliveMass : live Set.univ ≤ 1 := by
    calc
      live Set.univ ≤ live Set.univ + dead Set.univ := le_add_right le_rfl
      _ = 1 := hmass
  obtain ⟨nu, hnuProb, hnuWarm, hliveNu⟩ :=
    exists_warm_probability_of_submeasure_le_good_add_bad
      live good bad pi hM hMtop hliveMass hlive hgood
  let _ : IsProbabilityMeasure nu := hnuProb
  obtain ⟨mixError, hmixDom, hmixMass⟩ := hmix nu hnuProb hnuWarm
  let error := mixError + bad.bind K + dead Set.univ • deadOutput
  refine ⟨error, ?_, ?_⟩
  · have hbind := measure_bind_mono_left hliveNu hK
    rw [measure_bind_add_left nu bad hK] at hbind
    calc
      live.bind K + dead Set.univ • deadOutput ≤
          (nu.bind K + bad.bind K) + dead Set.univ • deadOutput := by
        gcongr
      _ ≤ (target + mixError + bad.bind K) +
          dead Set.univ • deadOutput := by
        gcongr
      _ = target + error := by
        simp only [error]
        ac_rfl
  · rw [show error = mixError + bad.bind K +
        dead Set.univ • deadOutput by rfl,
      Measure.add_apply, Measure.add_apply,
      measure_bind_apply_univ bad hK hKprob,
      Measure.smul_apply, smul_eq_mul]
    have hdeadOutputMass : deadOutput Set.univ = 1 := measure_univ
    rw [hdeadOutputMass, mul_one]
    calc
      mixError Set.univ + bad Set.univ + dead Set.univ =
          mixError Set.univ + (bad Set.univ + dead Set.univ) := by
        ac_rfl
      _ ≤ budget + eta := add_le_add hmixMass herror

/-! ## The actual live/dead phase law -/

/-- A Gaussian phase kernel whose input is already in the speedy (scaled)
coordinates used by the scheduled walk. -/
noncomputable def figureOneScheduledScaledGaussianPhaseLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    AmbientSpace q.n → Measure (Option (ℝ × AmbientSpace q.n)) :=
  fun current =>
    (scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
      (gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase)) 0 current).map
        (balancedCoolingAverage
          (figureOnePhaseSampleCount q (scheduleValue q phase)))

theorem figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (figureOneScheduledScaledGaussianPhaseLaw q I phase) ∧
    ∀ current, IsProbabilityMeasure
      (figureOneScheduledScaledGaussianPhaseLaw q I phase current) := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) count
  have havg := measurable_balancedCoolingAverage (n := q.n) count
  constructor
  · unfold figureOneScheduledScaledGaussianPhaseLaw
    exact (Measure.measurable_map _ havg).comp <|
      hcollect.1.comp (measurable_const.prodMk measurable_id)
  · intro current
    unfold figureOneScheduledScaledGaussianPhaseLaw
    let _ : IsProbabilityMeasure
        (scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase)) count 0 current) := hcollect.2 0 current
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- Common ideal output law for a complete Gaussian phase: its first point
is exactly stationary and all remaining scheduled collector steps are common
postprocessing. -/
noncomputable def figureOneScheduledGaussianPhaseTarget
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let first := (truncatedGaussianProbability q I (scheduleValue q phase)
    (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase))
          (count - 1) (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)) point)
          (accuracyScaleFactor q • point)
  (first.bind tail).map (balancedCoolingAverage count)

theorem figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure
      (figureOneScheduledGaussianPhaseTarget q I phase) := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let first := (truncatedGaussianProbability q I (scheduleValue q phase)
    (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase))
          (count - 1) (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)) point)
          (accuracyScaleFactor q • point)
  have htailCollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) (count - 1)
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase))
          (count - 1) (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)) point)
          (accuracyScaleFactor q • point) := by
      exact htailCollect.1.comp <|
        (measurable_gaussianRatioWeight _ _).prodMk
          ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
            accuracyScaleFactor q).smul measurable_id)
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none => infer_instance
    | some point => exact htailCollect.2 _ _
  let _ : IsProbabilityMeasure first :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let _ : IsProbabilityMeasure (first.bind tail) :=
    isProbabilityMeasure_bind htail.aemeasurable (ae_of_all _ htailProb)
  unfold figureOneScheduledGaussianPhaseTarget
  exact Measure.isProbabilityMeasure_map
    (measurable_balancedCoolingAverage count).aemeasurable

/-- A warm speedy start is replaced only at the first transition of the
complete phase; the collector tail and average are common postprocessing. -/
theorem bind_figureOneScheduledScaledGaussianPhaseLaw_leUpTo_target_of_warmSixteen
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    (hwarm : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) mu
      (figureOneScheduledSpeedyPiAt q I phase)) :
    MeasureLeUpTo
      (mu.bind (figureOneScheduledScaledGaussianPhaseLaw q I phase))
      (figureOneScheduledGaussianPhaseTarget q I phase)
      (figureOneCorrectedTransitionBudget q) := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let collect := fun current =>
    scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
      (gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) count 0 current
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) count
  have hcollectCurrent : Measurable collect :=
    hcollect.1.comp (measurable_const.prodMk measurable_id)
  let transition := scheduledBalancedAccuracyTransitionLawAux q I
    (scheduleValue q phase)
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (scheduleValue q phase))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (scheduleValue q phase))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (scheduleValue q phase))
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I (scheduleValue_pos q phase)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
  let _ : IsProbabilityMeasure (mu.bind transition) :=
    isProbabilityMeasure_bind htransition.1.aemeasurable
      (ae_of_all _ htransition.2)
  let _ : IsProbabilityMeasure
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hfirst : MeasureLeUpTo
      (mu.bind transition)
      ((truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q) := by
    apply MeasureLeUpTo.of_tvLe
    simpa [transition, figureOneScheduledSpeedyPiAt] using
      bind_figureOneFinalScheduledBalancedTransition_tvLe_of_warmSixteen
        q I (scheduleValue_pos q phase) mu hwarm
  have hcomplete :=
    MeasureLeUpTo.bind_scheduledBalancedTransitionCollectLaw_of_first
      q I (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) (count - 1) mu _ hfirst
  have hcount : 0 < count := by
    dsimp only [count]
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  rw [Nat.sub_add_cancel hcount] at hcomplete
  have hmapped := hcomplete.map
    (measurable_balancedCoolingAverage (n := q.n) count)
  rw [map_bind_eq_bind_map_of_measurable mu hcollectCurrent
    (measurable_balancedCoolingAverage (n := q.n) count)] at hmapped
  change MeasureLeUpTo
    (mu.bind fun current => (collect current).map
      (balancedCoolingAverage count))
    (figureOneScheduledGaussianPhaseTarget q I phase)
    (figureOneCorrectedTransitionBudget q)
  convert hmapped using 1 <;>
    simp [figureOneScheduledGaussianPhaseTarget, count, collect]
  congr 1

/-- Splitting a trace law into live and dead restrictions identifies its
next Gaussian observation law exactly.  Live states run the scaled complete
phase kernel; dead states emit `none` and consume no randomness. -/
theorem bind_scheduledBalancedTracePhaseObservationLaw_eq_live_dead
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n)) :
    law.bind (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase) =
      (scheduledBalancedTraceLiveStateLaw law
          (fun x => accuracyScaleFactor q • x)).bind
        (figureOneScheduledScaledGaussianPhaseLaw q I phase) +
      (scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x)) Set.univ •
        Measure.dirac none := by
  let liveSet := scheduledBalancedTraceLiveSet q.n
  let deadSet := scheduledBalancedTraceDeadSet q.n
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let state : ScheduledBalancedCoolingTrace q.n → AmbientSpace q.n :=
    scale ∘ scheduledBalancedTraceRetainedState
  let obs := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let K := figureOneScheduledScaledGaussianPhaseLaw q I phase
  have hobs := scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
  have hK := figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    q I phase
  have hstate : Measurable state := by
    dsimp only [state, scale]
    exact ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id).comp
        measurable_scheduledBalancedTraceRetainedState
  have hsplit : law = law.restrict liveSet + law.restrict deadSet := by
    rw [show deadSet = liveSetᶜ by
      exact scheduledBalancedTraceDeadSet_eq_compl,
      Measure.restrict_add_restrict_compl
        measurableSet_scheduledBalancedTraceLiveSet]
  have hlive : (law.restrict liveSet).bind obs =
      ((law.restrict liveSet).map state).bind K := by
    rw [map_bind_eq_bind_comp_state (law.restrict liveSet) hstate hK.1]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem
      (measurableSet_scheduledBalancedTraceLiveSet (n := q.n))]
      with trace htrace
    rcases trace with ⟨history, live⟩
    cases live with
    | false =>
        simp [liveSet, scheduledBalancedTraceLiveSet] at htrace
    | true =>
        simp only [obs, scheduledBalancedTracePhaseObservationLaw,
          if_true, hphase, K, state, scale, Function.comp_apply,
          scheduledBalancedTraceRetainedState]
        rfl
  have hdead : (law.restrict deadSet).bind obs =
      (law.restrict deadSet) Set.univ • Measure.dirac none := by
    have heq : ∀ᵐ trace ∂(law.restrict deadSet),
        obs trace = Measure.dirac none := by
      filter_upwards [ae_restrict_mem
        (measurableSet_scheduledBalancedTraceDeadSet (n := q.n))]
        with trace htrace
      rcases trace with ⟨history, live⟩
      cases live with
      | false => simp [obs, scheduledBalancedTracePhaseObservationLaw]
      | true => simp [deadSet, scheduledBalancedTraceDeadSet] at htrace
    rw [Measure.bind_congr_right heq, Measure.bind_const]
  calc
    law.bind obs =
        (law.restrict liveSet + law.restrict deadSet).bind obs :=
      congrArg (fun mu => mu.bind obs) hsplit
    _ = (law.restrict liveSet).bind obs +
        (law.restrict deadSet).bind obs :=
      measure_bind_add_left _ _ hobs.1
    _ = ((law.restrict liveSet).map state).bind K +
        (law.restrict deadSet) Set.univ • Measure.dirac none := by
      rw [hlive, hdead]
    _ = _ := by
      congr 2
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      symm
      exact scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop)

/-- One full trace phase is close to the common stationary complete-phase
target when its live retained marginal has a warm good/bad decomposition.
The dead mass is charged once and emits the executable absorbing result. -/
theorem bind_scheduledBalancedTracePhaseObservationLaw_leUpTo_of_live_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure law]
    (good bad : Measure (AmbientSpace q.n)) [IsFiniteMeasure bad]
    {M eta : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hM16 : M ≤ ENNReal.ofReal (16 * speedyAdjacentWarmConstant q))
    (hlive : scheduledBalancedTraceLiveStateLaw law
      (fun x => accuracyScaleFactor q • x) ≤ good + bad)
    (hgood : Arlib.IsWarm M good (figureOneScheduledSpeedyPiAt q I phase))
    (herror : bad Set.univ +
        scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x) Set.univ ≤ eta) :
    MeasureLeUpTo
      (law.bind (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase))
      (figureOneScheduledGaussianPhaseTarget q I phase)
      (figureOneCorrectedTransitionBudget q + eta) := by
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let live := scheduledBalancedTraceLiveStateLaw law scale
  let dead := scheduledBalancedTraceDeadStateLaw law scale
  let pi := figureOneScheduledSpeedyPiAt q I phase
  let K := figureOneScheduledScaledGaussianPhaseLaw q I phase
  let target := figureOneScheduledGaussianPhaseTarget q I phase
  have hscale : Measurable scale := by
    dsimp only [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hstate : Measurable
      (scale ∘ scheduledBalancedTraceRetainedState) :=
    hscale.comp measurable_scheduledBalancedTraceRetainedState
  let _ : IsProbabilityMeasure pi :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure target :=
    figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I phase
  have hK := figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    q I phase
  have hmass : live Set.univ + dead Set.univ = 1 := by
    rw [← Measure.add_apply,
      ← scheduledBalancedTraceStateLaw_eq_live_add_dead law scale hscale]
    unfold scheduledBalancedTraceStateLaw
    rw [Measure.map_apply hstate MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  have hliveMass : live Set.univ ≤ 1 := by
    rw [← hmass]
    exact le_add_right le_rfl
  have hdeadMass : dead Set.univ ≤ 1 := by
    rw [← hmass]
    exact le_add_left le_rfl
  let _ : IsFiniteMeasure live :=
    ⟨hliveMass.trans_lt ENNReal.one_lt_top⟩
  let _ : IsFiniteMeasure dead :=
    ⟨hdeadMass.trans_lt ENNReal.one_lt_top⟩
  have hmlu := measureLeUpTo_live_dead_bind_of_good_bad
    live dead good bad pi hM hMtop hmass
    (by simpa [live, scale] using hlive)
    (by simpa [pi] using hgood)
    (by simpa [dead, scale] using herror)
    K hK.1 hK.2 (Measure.dirac none) target
    (fun nu hnu hwarm => by
      let _ : IsProbabilityMeasure nu := hnu
      apply bind_figureOneScheduledScaledGaussianPhaseLaw_leUpTo_target_of_warmSixteen
      exact hwarm.mono hM16)
  rw [bind_scheduledBalancedTracePhaseObservationLaw_eq_live_dead
    q I phase hphase law]
  simpa [live, dead, K, target, scale] using hmlu

/-! ## Trace-dependent phase outputs -/

/-- Map a phase observation to a value while retaining the distinction
between a previously dead trace and a live phase that fails now. -/
noncomputable def scheduledBalancedTracePhaseOutputLaw
    {T : Type*} [MeasurableSpace T]
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) :
    ScheduledBalancedCoolingTrace q.n → Measure T := fun trace =>
  (scheduledBalancedTracePhaseObservationLaw parameters q I phase trace).map
    (if trace.2 then liveOutput else fun _ => deadOutput)

theorem scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    {T : Type*} [MeasurableSpace T]
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) (hliveOutput : Measurable liveOutput) :
    Measurable (scheduledBalancedTracePhaseOutputLaw parameters q I phase
      liveOutput deadOutput) ∧
    ∀ trace, IsProbabilityMeasure
      (scheduledBalancedTracePhaseOutputLaw parameters q I phase
        liveOutput deadOutput trace) := by
  have hobs := scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
    parameters q I phase
  have hout : Measurable fun value : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
      if value.1.2 then liveOutput value.2 else deadOutput := by
    apply Measurable.ite
    · exact (measurable_snd.comp measurable_fst)
        (measurableSet_singleton true)
    · exact hliveOutput.comp measurable_snd
    · exact measurable_const
  constructor
  · unfold scheduledBalancedTracePhaseOutputLaw
    apply measurable_measure_map_param_variable hobs.1 hobs.2
    convert hout using 1
    funext value
    cases value.1.2 <;> rfl
  · intro trace
    unfold scheduledBalancedTracePhaseOutputLaw
    let _ : IsProbabilityMeasure
        (scheduledBalancedTracePhaseObservationLaw parameters q I phase trace) :=
      hobs.2 trace
    rcases trace with ⟨history, live⟩
    cases live with
    | false =>
        exact Measure.isProbabilityMeasure_map measurable_const.aemeasurable
    | true =>
        exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable

/-- Exact live/dead decomposition after applying a trace-dependent phase
observable. -/
theorem bind_scheduledBalancedTracePhaseOutputLaw_eq_live_dead
    {T : Type*} [MeasurableSpace T]
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n))
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) (hliveOutput : Measurable liveOutput) :
    law.bind (scheduledBalancedTracePhaseOutputLaw
        figureOneFinalScheduledBalancedParameters q I phase
        liveOutput deadOutput) =
      (scheduledBalancedTraceLiveStateLaw law
          (fun x => accuracyScaleFactor q • x)).bind
        (fun current =>
          (figureOneScheduledScaledGaussianPhaseLaw q I phase current).map
            liveOutput) +
      (scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x)) Set.univ •
        Measure.dirac deadOutput := by
  let liveSet := scheduledBalancedTraceLiveSet q.n
  let deadSet := scheduledBalancedTraceDeadSet q.n
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let state : ScheduledBalancedCoolingTrace q.n → AmbientSpace q.n :=
    scale ∘ scheduledBalancedTraceRetainedState
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I phase liveOutput deadOutput
  let K : AmbientSpace q.n → Measure T := fun current =>
    (figureOneScheduledScaledGaussianPhaseLaw q I phase current).map liveOutput
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase liveOutput deadOutput
      hliveOutput
  have hrawK := figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    q I phase
  have hK : Measurable K :=
    (Measure.measurable_map _ hliveOutput).comp hrawK.1
  have hstate : Measurable state := by
    dsimp only [state, scale]
    exact ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id).comp
        measurable_scheduledBalancedTraceRetainedState
  have hsplit : law = law.restrict liveSet + law.restrict deadSet := by
    rw [show deadSet = liveSetᶜ by
      exact scheduledBalancedTraceDeadSet_eq_compl,
      Measure.restrict_add_restrict_compl
        measurableSet_scheduledBalancedTraceLiveSet]
  have hlive : (law.restrict liveSet).bind outK =
      ((law.restrict liveSet).map state).bind K := by
    rw [map_bind_eq_bind_comp_state (law.restrict liveSet) hstate hK]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem
      (measurableSet_scheduledBalancedTraceLiveSet (n := q.n))]
      with trace htrace
    rcases trace with ⟨history, live⟩
    cases live with
    | false => simp [liveSet, scheduledBalancedTraceLiveSet] at htrace
    | true =>
        simp only [outK, scheduledBalancedTracePhaseOutputLaw, if_true,
          K, state, scale, Function.comp_apply,
          scheduledBalancedTraceRetainedState]
        rw [show scheduledBalancedTracePhaseObservationLaw
            figureOneFinalScheduledBalancedParameters q I phase
              (history, true) =
            figureOneScheduledScaledGaussianPhaseLaw q I phase
              (accuracyScaleFactor q • history.2.2.2) by
          simp only [scheduledBalancedTracePhaseObservationLaw, if_true,
            hphase, figureOneScheduledScaledGaussianPhaseLaw,
            scheduledBalancedCoolingRatioTransitionLaw]
          ]
  have hdead : (law.restrict deadSet).bind outK =
      (law.restrict deadSet) Set.univ • Measure.dirac deadOutput := by
    have heq : ∀ᵐ trace ∂(law.restrict deadSet),
        outK trace = Measure.dirac deadOutput := by
      filter_upwards [ae_restrict_mem
        (measurableSet_scheduledBalancedTraceDeadSet (n := q.n))]
        with trace htrace
      rcases trace with ⟨history, live⟩
      cases live with
      | false =>
          simp [outK, scheduledBalancedTracePhaseOutputLaw,
            scheduledBalancedTracePhaseObservationLaw]
      | true => simp [deadSet, scheduledBalancedTraceDeadSet] at htrace
    rw [Measure.bind_congr_right heq, Measure.bind_const]
  calc
    law.bind outK =
        (law.restrict liveSet + law.restrict deadSet).bind outK :=
      congrArg (fun mu => mu.bind outK) hsplit
    _ = (law.restrict liveSet).bind outK +
        (law.restrict deadSet).bind outK :=
      measure_bind_add_left _ _ houtK.1
    _ = ((law.restrict liveSet).map state).bind K +
        (law.restrict deadSet) Set.univ • Measure.dirac deadOutput := by
      rw [hlive, hdead]
    _ = _ := by
      congr 2
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      symm
      exact scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop)

/-- Mapped form of the live/dead complete-phase bound, suitable for the
actual next truncated phase coordinate. -/
theorem bind_scheduledBalancedTracePhaseOutputLaw_leUpTo_of_live_good_bad
    {T : Type*} [MeasurableSpace T]
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure law]
    (good bad : Measure (AmbientSpace q.n)) [IsFiniteMeasure bad]
    {M eta : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hM16 : M ≤ ENNReal.ofReal (16 * speedyAdjacentWarmConstant q))
    (hlive : scheduledBalancedTraceLiveStateLaw law
      (fun x => accuracyScaleFactor q • x) ≤ good + bad)
    (hgood : Arlib.IsWarm M good (figureOneScheduledSpeedyPiAt q I phase))
    (herror : bad Set.univ +
        scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x) Set.univ ≤ eta)
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) (hliveOutput : Measurable liveOutput) :
    MeasureLeUpTo
      (law.bind (scheduledBalancedTracePhaseOutputLaw
        figureOneFinalScheduledBalancedParameters q I phase
        liveOutput deadOutput))
      ((figureOneScheduledGaussianPhaseTarget q I phase).map liveOutput)
      (figureOneCorrectedTransitionBudget q + eta) := by
  let rawK := figureOneScheduledScaledGaussianPhaseLaw q I phase
  let K : AmbientSpace q.n → Measure T := fun current =>
    (rawK current).map liveOutput
  have hrawK := figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    q I phase
  have hK : Measurable K :=
    (Measure.measurable_map _ hliveOutput).comp hrawK.1
  have hKprob : ∀ current, IsProbabilityMeasure (K current) := by
    intro current
    let _ : IsProbabilityMeasure (rawK current) := hrawK.2 current
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  let target := (figureOneScheduledGaussianPhaseTarget q I phase).map liveOutput
  let _ : IsProbabilityMeasure target := by
    let _ := figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I phase
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let live := scheduledBalancedTraceLiveStateLaw law scale
  let dead := scheduledBalancedTraceDeadStateLaw law scale
  let pi := figureOneScheduledSpeedyPiAt q I phase
  let _ : IsProbabilityMeasure pi :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I phase
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hmass : live Set.univ + dead Set.univ = 1 := by
    rw [← Measure.add_apply,
      ← scheduledBalancedTraceStateLaw_eq_live_add_dead law scale hscale]
    unfold scheduledBalancedTraceStateLaw
    rw [Measure.map_apply
      (hscale.comp measurable_scheduledBalancedTraceRetainedState)
      MeasurableSet.univ, Set.preimage_univ, measure_univ]
  let _ : IsFiniteMeasure live :=
    ⟨(by
      apply lt_of_le_of_lt (show live Set.univ ≤ 1 by
        rw [← hmass]
        exact le_add_right le_rfl)
      exact ENNReal.one_lt_top)⟩
  let _ : IsFiniteMeasure dead :=
    ⟨(by
      apply lt_of_le_of_lt (show dead Set.univ ≤ 1 by
        rw [← hmass]
        exact le_add_left le_rfl)
      exact ENNReal.one_lt_top)⟩
  have hmlu := measureLeUpTo_live_dead_bind_of_good_bad
    live dead good bad pi hM hMtop hmass
    (by simpa [live, scale] using hlive)
    (by simpa [pi] using hgood)
    (by simpa [dead, scale] using herror)
    K hK hKprob (Measure.dirac deadOutput) target
    (fun nu hnu hwarm => by
      let _ : IsProbabilityMeasure nu := hnu
      have hraw :=
        bind_figureOneScheduledScaledGaussianPhaseLaw_leUpTo_target_of_warmSixteen
          q I phase nu (hwarm.mono hM16)
      have hmapped := hraw.map hliveOutput
      rw [map_bind_eq_bind_map_of_measurable nu hrawK.1 hliveOutput] at hmapped
      simpa [K, rawK, target] using hmapped)
  rw [bind_scheduledBalancedTracePhaseOutputLaw_eq_live_dead
    q I phase hphase law liveOutput deadOutput hliveOutput]
  simpa [live, dead, K, rawK, target, scale] using hmlu

/-! ## Immediate-phase scalar interface -/

noncomputable def figureOneScheduledTraceLiveTruncatedOutput
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    Option (ℝ × AmbientSpace q.n) → ℝ
  | none => min 0
      (figureOneDependentAlpha q * scheduledFigureOneTraceRawMean q I j)
  | some result => min (max 0 result.1)
      (figureOneDependentAlpha q * scheduledFigureOneTraceRawMean q I j)

theorem measurable_figureOneScheduledTraceLiveTruncatedOutput
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    Measurable (figureOneScheduledTraceLiveTruncatedOutput q I j) := by
  unfold figureOneScheduledTraceLiveTruncatedOutput
  convert Measurable.optionElim
    (min 0 (figureOneDependentAlpha q *
      scheduledFigureOneTraceRawMean q I j))
    (measurable_const.max measurable_fst |>.min measurable_const) using 1
  funext result
  cases result <;> rfl

noncomputable def figureOneScheduledTraceDeadTruncatedOutput
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  min 1 (figureOneDependentAlpha q * scheduledFigureOneTraceRawMean q I j)

/-- The trace-dependent scalar kernel reads exactly the new truncated
coordinate after appending the phase observation. -/
theorem scheduledFigureOneTraceTruncatedPhase_append_eq_output
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid phase trace)
    (result : Option (ℝ × AmbientSpace q.n)) :
    scheduledFigureOneTraceTruncatedPhase q I (phase + 1)
        (scheduledBalancedCoolingTraceAppend trace result) =
      if trace.2 then
        figureOneScheduledTraceLiveTruncatedOutput q I (phase + 1) result
      else figureOneScheduledTraceDeadTruncatedOutput q I (phase + 1) := by
  unfold scheduledFigureOneTraceTruncatedPhase dependentTruncatedPhase
    figureOneScheduledTraceLiveTruncatedOutput
    figureOneScheduledTraceDeadTruncatedOutput
    scheduledBalancedTracePhaseVariable
    scheduledBalancedTraceChronologicalPhaseVariable
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q phase hphase]
  rcases trace with ⟨history, live⟩
  change history.2.1 = phase ∧ _ at hvalid
  cases live <;> cases result <;>
    simp [scheduledBalancedCoolingTraceAppend, balancedCoolingHistoryAppend,
      hvalid.1]

/-- Joint-law identification at the instant phase `i` is created.  This is
the bridge from the sequential-pair Lemma 7.17(b) calculation to the trace
law after `i+1` completed phases. -/
theorem map_pair_sequentialTracePhaseOutput_eq_forwardTrace_succ
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) :
    let rho := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I i
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
    let outK := scheduledBalancedTracePhaseOutputLaw
      figureOneFinalScheduledBalancedParameters q I i
      (figureOneScheduledTraceLiveTruncatedOutput q I (i + 1))
      (figureOneScheduledTraceDeadTruncatedOutput q I (i + 1))
    (sequentialPairLaw rho outK).map
        (fun pair => (X pair.1, pair.2)) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (i + 1)).map
        (fun trace => (X trace, Y trace)) := by
  dsimp only
  let rho : Measure (ScheduledBalancedCoolingTrace q.n) :=
    scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I i
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
  let outK : ScheduledBalancedCoolingTrace q.n → Measure ℝ :=
    scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
  let traceK : ScheduledBalancedCoolingTrace q.n →
      Measure (ScheduledBalancedCoolingTrace q.n) :=
    scheduledBalancedTracePhaseKernel
    figureOneFinalScheduledBalancedParameters q I i
  have hV : ∀ j, Measurable
      (scheduledFigureOneTraceTruncatedPhase q I j) := fun j =>
    (measurable_scheduledBalancedTracePhaseVariable q j).min measurable_const
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) hV i
  have hY : Measurable Y := hV (i + 1)
  have hliveOutput : Measurable liveOutput :=
    measurable_figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
      hliveOutput
  have htraceK := scheduledBalancedTracePhaseKernel_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I i
  have hpair : Measurable fun pair :
      ScheduledBalancedCoolingTrace q.n × ℝ => (X pair.1, pair.2) :=
    (hX.comp measurable_fst).prodMk measurable_snd
  have htracePair : Measurable fun trace => (X trace, Y trace) :=
    hX.prodMk hY
  unfold sequentialPairLaw
  rw [map_bind_eq_bind_map_of_measurable rho
    (measurable_sequentialPairKernel houtK.1 houtK.2) hpair]
  rw [show (rho.bind fun trace =>
        ((outK trace).map fun value => (trace, value)).map
          (fun pair => (X pair.1, pair.2))) =
      rho.bind fun trace =>
        (outK trace).map fun value => (X trace, value) by
    apply Measure.bind_congr_right
    apply ae_of_all
    intro trace
    calc
      ((outK trace).map fun value => (trace, value)).map
          (fun pair => (X pair.1, pair.2)) =
        (outK trace).map
          ((fun pair => (X pair.1, pair.2)) ∘ fun value => (trace, value)) :=
        Measure.map_map hpair (measurable_const.prodMk measurable_id)
      _ = (outK trace).map fun value => (X trace, value) := by rfl]
  rw [show scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (i + 1) =
      rho.bind traceK by rfl,
    map_bind_eq_bind_map_of_measurable rho htraceK.1 htracePair]
  apply Measure.bind_congr_right
  filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
    figureOneFinalScheduledBalancedParameters q I i] with trace hvalid
  unfold outK scheduledBalancedTracePhaseOutputLaw
    scheduledBalancedTracePhaseKernel
  have hscalarPair : Measurable fun value : ℝ => (X trace, value) :=
    measurable_const.prodMk measurable_id
  have hconditional : Measurable
      (if trace.2 then liveOutput else fun _ => deadOutput) := by
    cases trace.2
    · exact measurable_const
    · exact hliveOutput
  have happend : Measurable (scheduledBalancedCoolingTraceAppend trace) :=
    (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
      (measurable_const.prodMk measurable_id)
  calc
    ((scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I i trace).map
          (if trace.2 then liveOutput else fun _ => deadOutput)).map
            (fun value => (X trace, value)) =
      (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I i trace).map
          ((fun value => (X trace, value)) ∘
            (if trace.2 then liveOutput else fun _ => deadOutput)) :=
      Measure.map_map hscalarPair hconditional
    _ = (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I i trace).map
          ((fun next => (X next, Y next)) ∘
            scheduledBalancedCoolingTraceAppend trace) := by
      refine Measure.map_congr
        (μ := scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I i trace) ?_
      apply ae_of_all
      intro result
      simp only [Function.comp_apply]
      apply Prod.ext
      · exact (scheduledFigureOneTraceTruncatedProduct_append_eq
          q I hvalid (Nat.le_of_lt hi) le_rfl result).symm
      · rw [show (if trace.2 = true then liveOutput else
            fun _ => deadOutput) result =
          if trace.2 = true then liveOutput result else deadOutput by
            by_cases h : trace.2 = true <;> simp [h]]
        exact (scheduledFigureOneTraceTruncatedPhase_append_eq_output
          q I i hi trace hvalid result).symm
    _ = ((scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I i trace).map
          (scheduledBalancedCoolingTraceAppend trace)).map
            (fun next => (X next, Y next)) :=
      (Measure.map_map htracePair happend).symm
  all_goals exact rho

/-- The dead trace mass is bounded by the same optional-retained exact-chance
error: the ideal accepted target is supported on `some`. -/
theorem figureOneScheduledTrace_deadState_mass_le_retainedError
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I (phase + 1))
        transform Set.univ ≤
      figureOneScheduledRetainedError q (phase + 1) := by
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  have hmlu := scheduledBalancedForwardTraceLaw_retained_leUpTo_target
    q I phase hphase
  have hevent := hmlu.event_le ({none} : Set (Option (AmbientSpace q.n)))
  have hnone :
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
          ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
    rw [Measure.map_apply measurable_some measurableSet_option_none]
    have hemp : some ⁻¹' ({none} : Set (Option (AmbientSpace q.n))) =
        (∅ : Set (AmbientSpace q.n)) := by
      ext point
      simp
    rw [hemp, measure_empty]
  rw [hnone, zero_add] at hevent
  calc
    scheduledBalancedTraceDeadStateLaw law transform Set.univ =
        (law.map scheduledBalancedCoolingTraceProject) {none} :=
      scheduledBalancedTraceDeadStateLaw_mass_eq_project_none
        law transform htransform
    _ = (law.map scheduledBalancedTraceRetainedOption) {none} := by
      rw [Measure.map_apply measurable_scheduledBalancedCoolingTraceProject
          measurableSet_option_none,
        Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
          measurableSet_option_none]
      congr 1
      ext trace
      rcases trace with ⟨history, live⟩
      cases live <;> simp [scheduledBalancedCoolingTraceProject,
        scheduledBalancedTraceRetainedOption]
    _ ≤ figureOneScheduledRetainedError q (phase + 1) := by
      simpa [law] using hevent

/-- The shared retained-error witness split in the form needed by the
live/dead transition lemma: the live marginal is good plus `liveBad`, and
`liveBad` together with the absorbing dead mass costs only the one retained
error budget. -/
theorem exists_figureOneScheduledTraceScaledLive_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
    ∃ liveBad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceLiveStateLaw law scale ≤ good + liveBad ∧
      liveBad Set.univ +
          scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
        figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
  obtain ⟨error, herrorDom, herrorMass⟩ :=
    scheduledBalancedForwardTraceLaw_retained_leUpTo_target
      q I phase hphase
  let someSet := scheduledRetainedSomeSet q.n
  let get := scheduledRetainedGetDZero (n := q.n)
  let liveBad0 := (error.restrict someSet).map get
  let liveBad := liveBad0.map scale
  refine ⟨liveBad, ?_, ?_⟩
  · have hrestrict :
        ((law.map scheduledBalancedTraceRetainedOption).restrict someSet) ≤
          ((((figureOneScheduledAcceptedTargetAt q I phase).map some) +
            error).restrict someSet) :=
      Measure.restrict_mono Set.Subset.rfl herrorDom
    have hmapped := Measure.map_mono hrestrict
      (measurable_scheduledRetainedGetDZero (n := q.n))
    rw [Measure.restrict_add,
      Measure.map_add _ _
        (measurable_scheduledRetainedGetDZero (n := q.n)),
      map_some_restrict_extract_eq] at hmapped
    have hlive0 : scheduledBalancedTraceLiveStateLaw law id ≤
        figureOneScheduledAcceptedTargetAt q I phase + liveBad0 := by
      rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome]
      exact hmapped
    have hlive := Measure.map_mono hlive0 (by fun_prop : Measurable scale)
    rw [Measure.map_add _ _ (by fun_prop : Measurable scale)] at hlive
    unfold scheduledBalancedTraceLiveStateLaw at hlive ⊢
    rw [Measure.map_map (by fun_prop : Measurable scale)
      ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
        (measurable_scheduledBalancedTraceRetainedState (n := q.n)))] at hlive
    simpa [good, liveBad, liveBad0, Function.comp_def] using hlive
  · have hliveBadMass : liveBad Set.univ = error someSet := by
      rw [show liveBad = liveBad0.map scale by rfl,
        Measure.map_apply (by fun_prop : Measurable scale) MeasurableSet.univ,
        Set.preimage_univ]
      rw [show liveBad0 = (error.restrict someSet).map get by rfl,
        Measure.map_apply
          (measurable_scheduledRetainedGetDZero (n := q.n))
          MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    have hnone :
        ((figureOneScheduledAcceptedTargetAt q I phase).map some)
            ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
      rw [Measure.map_apply measurable_some measurableSet_option_none]
      have hpreSome : (some : AmbientSpace q.n →
          Option (AmbientSpace q.n)) ⁻¹'
            ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
        ext point
        simp
      rw [hpreSome, measure_empty]
    have hdeadMass :
        scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
          error ({none} : Set (Option (AmbientSpace q.n))) := by
      have hevent := Measure.le_iff'.mp herrorDom
        ({none} : Set (Option (AmbientSpace q.n)))
      rw [Measure.add_apply, hnone, zero_add] at hevent
      rw [scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop : Measurable scale)]
      rw [Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
        measurableSet_option_none] at hevent
      have hpre : scheduledBalancedTraceRetainedOption ⁻¹'
          ({none} : Set (Option (AmbientSpace q.n))) =
            scheduledBalancedTraceDeadSet q.n := by
        ext trace
        rcases trace with ⟨history, live⟩
        cases live <;> simp [scheduledBalancedTraceRetainedOption,
          scheduledBalancedTraceDeadSet]
      simpa [law, hpre] using hevent
    calc
      liveBad Set.univ +
          scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
        error someSet + error ({none} : Set (Option (AmbientSpace q.n))) := by
          rw [hliveBadMass]
          exact add_le_add le_rfl hdeadMass
      _ = error Set.univ := by
        rw [show someSet =
            ({none} : Set (Option (AmbientSpace q.n)))ᶜ by rfl,
          add_comm,
          measure_add_measure_compl measurableSet_option_none]
      _ ≤ figureOneScheduledRetainedError q (phase + 1) := herrorMass

/-- Fold the absorbing dead-state marginal into the additive bad witness.
The resulting full retained-state law, rather than merely its live
restriction, is dominated by the scaled accepted target plus at most twice
the retained exact-chance error. -/
theorem exists_figureOneScheduledTraceScaledState_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
    ∃ bad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceStateLaw law scale ≤ good + bad ∧
      bad Set.univ ≤ figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
  obtain ⟨error, herrorDom, herrorMass⟩ :=
    scheduledBalancedForwardTraceLaw_retained_leUpTo_target
      q I phase hphase
  let someSet := scheduledRetainedSomeSet q.n
  let get := scheduledRetainedGetDZero (n := q.n)
  let liveBad0 := (error.restrict someSet).map get
  let liveBad := liveBad0.map scale
  let dead := scheduledBalancedTraceDeadStateLaw law scale
  let bad := liveBad + dead
  refine ⟨bad, ?_, ?_⟩
  · rw [scheduledBalancedTraceStateLaw_eq_live_add_dead law scale (by fun_prop)]
    have hlive0 : scheduledBalancedTraceLiveStateLaw law id ≤
        figureOneScheduledAcceptedTargetAt q I phase + liveBad0 := by
      rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome]
      have hrestrict :
          ((law.map scheduledBalancedTraceRetainedOption).restrict someSet) ≤
            ((((figureOneScheduledAcceptedTargetAt q I phase).map some) +
              error).restrict someSet) :=
        Measure.restrict_mono Set.Subset.rfl herrorDom
      have hmapped := Measure.map_mono hrestrict
        (measurable_scheduledRetainedGetDZero (n := q.n))
      rw [Measure.restrict_add,
        Measure.map_add _ _
          (measurable_scheduledRetainedGetDZero (n := q.n)),
        map_some_restrict_extract_eq] at hmapped
      exact hmapped
    have hlive := Measure.map_mono hlive0 (by fun_prop : Measurable scale)
    rw [Measure.map_add _ _ (by fun_prop : Measurable scale)] at hlive
    unfold scheduledBalancedTraceLiveStateLaw at hlive ⊢
    rw [Measure.map_map (by fun_prop : Measurable scale)
      ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
        (measurable_scheduledBalancedTraceRetainedState (n := q.n)))] at hlive
    calc
      scheduledBalancedTraceLiveStateLaw law scale + dead ≤
          (good + liveBad) + dead := by
            gcongr
            change
              (law.restrict (scheduledBalancedTraceLiveSet q.n)).map
                  (scale ∘ scheduledBalancedTraceRetainedState) ≤ _
            simpa [good, liveBad, liveBad0, Function.comp_def] using hlive
      _ = good + bad := by
        simp only [bad]
        ac_rfl
  · rw [show bad = liveBad + dead by rfl, Measure.add_apply]
    have hliveBadMass : liveBad Set.univ = error someSet := by
      rw [show liveBad = liveBad0.map scale by rfl,
        Measure.map_apply (by fun_prop : Measurable scale) MeasurableSet.univ,
        Set.preimage_univ]
      rw [show liveBad0 = (error.restrict someSet).map get by rfl,
        Measure.map_apply
          (measurable_scheduledRetainedGetDZero (n := q.n))
          MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    have hnone :
        ((figureOneScheduledAcceptedTargetAt q I phase).map some)
            ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
      rw [Measure.map_apply measurable_some measurableSet_option_none]
      have hpreSome : (some : AmbientSpace q.n →
          Option (AmbientSpace q.n)) ⁻¹'
            ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
        ext point
        simp
      rw [hpreSome, measure_empty]
    have hdeadMass : dead Set.univ ≤
        error ({none} : Set (Option (AmbientSpace q.n))) := by
      have hevent := Measure.le_iff'.mp herrorDom
        ({none} : Set (Option (AmbientSpace q.n)))
      rw [Measure.add_apply, hnone, zero_add] at hevent
      rw [show dead = scheduledBalancedTraceDeadStateLaw law scale by rfl,
        scheduledBalancedTraceDeadStateLaw_apply_univ law scale
          (by fun_prop : Measurable scale)]
      rw [Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
        measurableSet_option_none] at hevent
      have hpre : scheduledBalancedTraceRetainedOption ⁻¹'
          ({none} : Set (Option (AmbientSpace q.n))) =
            scheduledBalancedTraceDeadSet q.n := by
        ext trace
        rcases trace with ⟨history, live⟩
        cases live <;> simp [scheduledBalancedTraceRetainedOption,
          scheduledBalancedTraceDeadSet]
      simpa [law, hpre] using hevent
    calc
      liveBad Set.univ + dead Set.univ ≤
          error someSet + error ({none} : Set (Option (AmbientSpace q.n))) := by
        rw [hliveBadMass]
        exact add_le_add le_rfl hdeadMass
      _ = error Set.univ := by
        rw [show someSet =
            ({none} : Set (Option (AmbientSpace q.n)))ᶜ by
          rfl,
          add_comm,
          measure_add_measure_compl measurableSet_option_none]
      _ ≤ figureOneScheduledRetainedError q (phase + 1) := herrorMass

/-! ## Conditioning the retained live/dead split -/

theorem scheduledBalancedTraceLiveStateLaw_mono_smul
    (q : VolumeParams)
    (mu rho : Measure (ScheduledBalancedCoolingTrace q.n))
    (c : ENNReal) (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform)
    (h : mu ≤ c • rho) :
    scheduledBalancedTraceLiveStateLaw mu transform ≤
      c • scheduledBalancedTraceLiveStateLaw rho transform := by
  unfold scheduledBalancedTraceLiveStateLaw
  rw [← Measure.map_smul, ← Measure.restrict_smul]
  exact Measure.map_mono
    (Measure.restrict_mono Set.Subset.rfl h)
    (htransform.comp measurable_scheduledBalancedTraceRetainedState)

theorem scheduledBalancedTraceDeadStateLaw_mass_mono_smul
    (q : VolumeParams)
    (mu rho : Measure (ScheduledBalancedCoolingTrace q.n))
    (c : ENNReal) (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform)
    (h : mu ≤ c • rho) :
    scheduledBalancedTraceDeadStateLaw mu transform Set.univ ≤
      c * scheduledBalancedTraceDeadStateLaw rho transform Set.univ := by
  have hmeasure : scheduledBalancedTraceDeadStateLaw mu transform ≤
      c • scheduledBalancedTraceDeadStateLaw rho transform := by
    unfold scheduledBalancedTraceDeadStateLaw
    rw [← Measure.map_smul, ← Measure.restrict_smul]
    exact Measure.map_mono
      (Measure.restrict_mono Set.Subset.rfl h)
      (htransform.comp measurable_scheduledBalancedTraceRetainedState)
  have := Measure.le_iff'.mp hmeasure Set.univ
  simpa [Measure.smul_apply, smul_eq_mul] using this

/-- The asymmetric Lemma 7.17(b) estimate for a noninitial Gaussian phase,
before transporting the newly created coordinate through later trace phases. -/
theorem approxIndepFun_figureOneScheduledTrace_gaussianPhaseOutput
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q) :
    let i := previous + 1
    let rho := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I i
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
    let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
    let outK := scheduledBalancedTracePhaseOutputLaw
      figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
    ApproxIndepFun (figureOneDependentEpsilon q)
      (X ∘ Prod.fst) Prod.snd (sequentialPairLaw rho outK) := by
  dsimp only
  let i := previous + 1
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I i
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I previous).map scale
  let eta := figureOneScheduledRetainedError q i
  let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
  let target := (figureOneScheduledGaussianPhaseTarget q I i).map liveOutput
  have hprevious : previous < terminalPhaseSteps q := by omega
  obtain ⟨bad, hlive, herror⟩ :=
    exists_figureOneScheduledTraceScaledLive_good_bad q I previous hprevious
  have hetaTop : eta ≠ ⊤ := by
    dsimp only [eta, i]
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun phase _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure bad :=
    { measure_univ_lt_top := by
        apply lt_of_le_of_lt
        · exact le_trans (le_add_right le_rfl) herror
        · exact lt_top_iff_ne_top.mpr hetaTop }
  let _ : IsProbabilityMeasure rho :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I i
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hliveOutput : Measurable liveOutput :=
    measurable_figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
      hliveOutput
  let _ : IsProbabilityMeasure target := by
    let _ := figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I i
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  have hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I i) := by
    simpa [good, scale, i, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous
  have hM8 : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM8M16 : ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM16 : (1 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) :=
    hM8.trans hM8M16
  have hbase : MeasureLeUpTo (rho.bind outK) target
      (figureOneCorrectedTransitionBudget q + eta) := by
    apply bind_scheduledBalancedTracePhaseOutputLaw_leUpTo_of_live_good_bad
      q I i hnext rho good bad hM8 ENNReal.ofReal_ne_top hM8M16
    · simpa [rho, good, scale, i] using hlive
    · exact hgood
    · simpa [rho, scale, eta, i] using herror
    · exact hliveOutput
  have hconditioned : ∀ mu : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo (mu.bind outK) target
        (figureOneCorrectedTransitionBudget q + 2 * eta) := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    have hmule : mu ≤ (2 : ENNReal) • rho :=
      (isWarm_iff_le_smul mu rho).1 hwarm
    let good2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • good
    let bad2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • bad
    let _ : IsFiniteMeasure bad2 :=
      { measure_univ_lt_top := by
          rw [show bad2 = (2 : ENNReal) • bad by rfl,
            Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top bad Set.univ) }
    have hlive2 : scheduledBalancedTraceLiveStateLaw mu scale ≤
        good2 + bad2 := by
      calc
        scheduledBalancedTraceLiveStateLaw mu scale ≤
            (2 : ENNReal) • scheduledBalancedTraceLiveStateLaw rho scale :=
          scheduledBalancedTraceLiveStateLaw_mono_smul q mu rho 2 scale
            hscale hmule
        _ ≤ (2 : ENNReal) • (good + bad) := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
            smul_eq_mul]
          gcongr
        _ = good2 + bad2 := by
          simp only [good2, bad2, smul_add]
    have hgood2 : Arlib.IsWarm
        (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) good2
        (figureOneScheduledSpeedyPiAt q I i) := by
      intro S hS
      rw [show good2 = (2 : ENNReal) • good by rfl,
        Measure.smul_apply, smul_eq_mul]
      have hg := hgood S hS
      have hcoef : (2 : ENNReal) *
          ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) =
            ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      calc
        2 * good S ≤ 2 *
            (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) *
              (figureOneScheduledSpeedyPiAt q I i) S) := by gcongr
        _ = ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) *
              (figureOneScheduledSpeedyPiAt q I i) S := by
          rw [← mul_assoc, hcoef]
    have hdead2 := scheduledBalancedTraceDeadStateLaw_mass_mono_smul
      q mu rho 2 scale hscale hmule
    have herror2 : bad2 Set.univ +
        scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤ 2 * eta := by
      rw [show bad2 = (2 : ENNReal) • bad by rfl,
        Measure.smul_apply, smul_eq_mul]
      calc
        2 * bad Set.univ +
            scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤
          2 * bad Set.univ +
            2 * scheduledBalancedTraceDeadStateLaw rho scale Set.univ := by
              gcongr
        _ = 2 * (bad Set.univ +
            scheduledBalancedTraceDeadStateLaw rho scale Set.univ) := by ring
        _ ≤ 2 * eta := by gcongr
    apply bind_scheduledBalancedTracePhaseOutputLaw_leUpTo_of_live_good_bad
      q I i hnext mu good2 bad2 hM16 ENNReal.ofReal_ne_top le_rfl
    · exact hlive2
    · exact hgood2
    · exact herror2
    · exact hliveOutput
  have hraw := approxIndepFun_sequentialPairLaw_of_asymmetric_leUpTo
    rho outK houtK.1 houtK.2 target
    (ENNReal.add_ne_top.mpr ⟨by simp [figureOneCorrectedTransitionBudget],
      ENNReal.mul_ne_top (by norm_num) hetaTop⟩)
    (ENNReal.add_ne_top.mpr
      ⟨by simp [figureOneCorrectedTransitionBudget], hetaTop⟩)
    hconditioned hbase
  have hX : Measurable (dependentTruncatedProduct
      (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i) :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I)
      (fun j => (measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const) i
  apply (hraw.comp hX measurable_id).mono
  exact figureOneScheduledRetained_asymmetric_budget q i (by
    rw [figureOneDependentPhaseCount]
    omega)

/-- The same Gaussian-phase estimate on the trace immediately after the
coordinate has been appended. -/
theorem approxIndepFun_figureOneScheduledForwardTrace_gaussian_succ
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q) :
    let i := previous + 1
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
    ApproxIndepFun (figureOneDependentEpsilon q) X Y
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (i + 1)) := by
  dsimp only
  let i := previous + 1
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I i
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
  have hV : ∀ j, Measurable
      (scheduledFigureOneTraceTruncatedPhase q I j) := fun j =>
    (measurable_scheduledBalancedTracePhaseVariable q j).min measurable_const
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) hV i
  have hY : Measurable Y := hV (i + 1)
  have himmediate := approxIndepFun_figureOneScheduledTrace_gaussianPhaseOutput
    q I previous hnext
  apply ApproxIndepFun.of_map_pair_eq
    (hX.comp measurable_fst) measurable_snd hX hY
  · simpa [i, rho, X, Y, outK, liveOutput, deadOutput,
      Function.comp_def] using
        map_pair_sequentialTracePhaseOutput_eq_forwardTrace_succ
          q I i (by
            rw [figureOneDependentPhaseCount]
            omega)
  · simpa [i, rho, X, outK, liveOutput, deadOutput] using himmediate

/-- Later trace phases preserve the Gaussian Lemma 7.17(c) joint law. -/
theorem approxIndepFun_figureOneScheduledFinalTrace_gaussian
    (q : VolumeParams) (I : VolumeInput q.n) (previous : ℕ)
    (hnext : previous + 1 < terminalPhaseSteps q) :
    let i := previous + 1
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
    ApproxIndepFun (figureOneDependentEpsilon q) X Y
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) := by
  dsimp only
  let i := previous + 1
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let future := figureOneDependentPhaseCount q - (i + 1)
  have hcount : i + 1 ≤ figureOneDependentPhaseCount q := by
    dsimp only [i]
    rw [figureOneDependentPhaseCount]
    omega
  have hhorizon : i + 1 + future = figureOneDependentPhaseCount q := by
    dsimp only [future]
    omega
  have hV : ∀ j, Measurable
      (scheduledFigureOneTraceTruncatedPhase q I j) := fun j =>
    (measurable_scheduledBalancedTracePhaseVariable q j).min measurable_const
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) hV i
  have hY : Measurable Y := hV (i + 1)
  have hpref := approxIndepFun_figureOneScheduledForwardTrace_gaussian_succ
    q I previous hnext
  have hlaw :
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (i + 1)).map
          (fun trace => (X trace, Y trace)) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
          (fun trace => (X trace, Y trace)) := by
    rw [← hhorizon]
    symm
    exact map_pair_scheduledBalancedForwardTraceLaw_eq_prefix
      figureOneFinalScheduledBalancedParameters q I i future (by omega)
  exact ApproxIndepFun.of_map_pair_eq hX hY hX hY hlaw
    (by simpa [i, X, Y] using hpref)

theorem approxIndepFun_const_left_of_nonneg
    {Omega S T : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    [MeasurableSpace T] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (c : S) (Y : Omega → T) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    ApproxIndepFun epsilon (fun _ => c) Y mu := by
  intro A hA B hB
  by_cases hc : c ∈ A
  · have hpre : (fun _ : Omega => c) ⁻¹' A = Set.univ := by
      ext omega
      simp [hc]
    rw [hpre, Set.univ_inter]
    simp only [probReal_univ, one_mul, sub_self, abs_zero]
    exact hepsilon
  · have hpre : (fun _ : Omega => c) ⁻¹' A = ∅ := by
      ext omega
      simp [hc]
    rw [hpre, Set.empty_inter]
    simp only [measureReal_empty, zero_mul, sub_zero, abs_zero]
    exact hepsilon

/-- The `i=0` instance of Lemma 7.17(c) is exact because the empty prefix
product is the constant one. -/
theorem approxIndepFun_figureOneScheduledFinalTrace_zero
    (q : VolumeParams) (I : VolumeInput q.n) :
    ApproxIndepFun (figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) 0)
      (scheduledFigureOneTraceTruncatedPhase q I 1)
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) := by
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure law :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)
  change ApproxIndepFun (figureOneDependentEpsilon q) (fun _ => (1 : ℝ))
    (scheduledFigureOneTraceTruncatedPhase q I 1) law
  exact approxIndepFun_const_left_of_nonneg law (1 : ℝ)
    (scheduledFigureOneTraceTruncatedPhase q I 1)
    (figureOneDependentEpsilon_nonneg q)

/-! ## The final uniform-ratio phase -/

noncomputable def figureOneScheduledScaledTerminalPhaseLaw
    (q : VolumeParams) (I : VolumeInput q.n) :
    AmbientSpace q.n → Measure (Option (ℝ × AmbientSpace q.n)) :=
  fun current =>
    (scheduledBalancedTransitionCollectLaw q I (terminalVariance q)
      (uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q) 0 current).map
        (balancedCoolingAverage (figureOneSampleCount q))

theorem figureOneScheduledScaledTerminalPhaseLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measurable (figureOneScheduledScaledTerminalPhaseLaw q I) ∧
    ∀ current, IsProbabilityMeasure
      (figureOneScheduledScaledTerminalPhaseLaw q I current) := by
  have hcollect := scheduledBalancedTransitionCollectLaw_measurable_and_probability
    q I (terminalVariance_pos' q)
    (measurable_uniformRatioWeight (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (terminalVariance q)) (figureOneSampleCount q)
  have havg := measurable_balancedCoolingAverage (n := q.n)
    (figureOneSampleCount q)
  constructor
  · unfold figureOneScheduledScaledTerminalPhaseLaw
    exact (Measure.measurable_map _ havg).comp
      (hcollect.1.comp (measurable_const.prodMk measurable_id))
  · intro current
    unfold figureOneScheduledScaledTerminalPhaseLaw
    let _ := hcollect.2 0 current
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

noncomputable def figureOneScheduledTerminalPhaseTarget
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  let count := figureOneSampleCount q
  let first := (truncatedGaussianProbability q I (terminalVariance q)
    (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I (terminalVariance q)
          (uniformRatioWeight (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (terminalVariance q))
          (count - 1) (uniformRatioWeight (terminalVariance q) point)
          (accuracyScaleFactor q • point)
  (first.bind tail).map (balancedCoolingAverage count)

theorem figureOneScheduledTerminalPhaseTarget_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) :
    IsProbabilityMeasure (figureOneScheduledTerminalPhaseTarget q I) := by
  let count := figureOneSampleCount q
  let first := (truncatedGaussianProbability q I (terminalVariance q)
    (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I (terminalVariance q)
          (uniformRatioWeight (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (terminalVariance q))
          (count - 1) (uniformRatioWeight (terminalVariance q) point)
          (accuracyScaleFactor q • point)
  have htailCollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q)) (count - 1)
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I (terminalVariance q)
          (uniformRatioWeight (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (terminalVariance q))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (terminalVariance q))
          (count - 1) (uniformRatioWeight (terminalVariance q) point)
          (accuracyScaleFactor q • point) :=
      htailCollect.1.comp <|
        (measurable_uniformRatioWeight _).prodMk
          ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
            accuracyScaleFactor q).smul measurable_id)
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none => infer_instance
    | some point => exact htailCollect.2 _ _
  let _ : IsProbabilityMeasure first :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let _ : IsProbabilityMeasure (first.bind tail) :=
    isProbabilityMeasure_bind htail.aemeasurable (ae_of_all _ htailProb)
  unfold figureOneScheduledTerminalPhaseTarget
  exact Measure.isProbabilityMeasure_map
    (measurable_balancedCoolingAverage count).aemeasurable

theorem bind_figureOneScheduledScaledTerminalPhaseLaw_leUpTo_target_of_warmSixteen
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    (hwarm : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) mu
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q))) :
    MeasureLeUpTo
      (mu.bind (figureOneScheduledScaledTerminalPhaseLaw q I))
      (figureOneScheduledTerminalPhaseTarget q I)
      (figureOneCorrectedTransitionBudget q) := by
  let count := figureOneSampleCount q
  let collect := fun current =>
    scheduledBalancedTransitionCollectLaw q I (terminalVariance q)
      (uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q)) count 0 current
  have hcollect := scheduledBalancedTransitionCollectLaw_measurable_and_probability
    q I (terminalVariance_pos' q)
    (measurable_uniformRatioWeight (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (terminalVariance q)) count
  have hcollectCurrent : Measurable collect :=
    hcollect.1.comp (measurable_const.prodMk measurable_id)
  let transition := scheduledBalancedAccuracyTransitionLawAux q I
    (terminalVariance q)
    (figureOneFinalScheduledBalancedParameters.proposalCap q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.properStride q
      (terminalVariance q))
    (figureOneFinalScheduledBalancedParameters.retryLimit q
      (terminalVariance q))
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I (terminalVariance_pos' q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
  let _ : IsProbabilityMeasure (mu.bind transition) :=
    isProbabilityMeasure_bind htransition.1.aemeasurable
      (ae_of_all _ htransition.2)
  let _ : IsProbabilityMeasure
      ((truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hfirst : MeasureLeUpTo (mu.bind transition)
      ((truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q) := by
    apply MeasureLeUpTo.of_tvLe
    simpa [transition, figureOneScheduledSpeedyPiAt,
      scheduleValue_terminalPhaseSteps] using
      bind_figureOneFinalScheduledBalancedTransition_tvLe_of_warmSixteen
        q I (terminalVariance_pos' q) mu (by
          simpa [figureOneScheduledSpeedyPiAt,
            scheduleValue_terminalPhaseSteps] using hwarm)
  have hcomplete :=
    MeasureLeUpTo.bind_scheduledBalancedTransitionCollectLaw_of_first
      q I (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q)) (count - 1) mu _ hfirst
  have hcount : 0 < count := figureOneSampleCount_pos q
  rw [Nat.sub_add_cancel hcount] at hcomplete
  have hmapped := hcomplete.map
    (measurable_balancedCoolingAverage (n := q.n) count)
  rw [map_bind_eq_bind_map_of_measurable mu hcollectCurrent
    (measurable_balancedCoolingAverage (n := q.n) count)] at hmapped
  change MeasureLeUpTo
    (mu.bind fun current => (collect current).map
      (balancedCoolingAverage count))
    (figureOneScheduledTerminalPhaseTarget q I)
    (figureOneCorrectedTransitionBudget q)
  convert hmapped using 1 <;>
    simp [figureOneScheduledTerminalPhaseTarget, count, collect]
  congr 1

theorem bind_scheduledBalancedTerminalTracePhaseOutputLaw_eq_live_dead
    {T : Type*} [MeasurableSpace T]
    (q : VolumeParams) (I : VolumeInput q.n)
    (law : Measure (ScheduledBalancedCoolingTrace q.n))
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) (hliveOutput : Measurable liveOutput) :
    law.bind (scheduledBalancedTracePhaseOutputLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q) liveOutput deadOutput) =
      (scheduledBalancedTraceLiveStateLaw law
          (fun x => accuracyScaleFactor q • x)).bind
        (fun current =>
          (figureOneScheduledScaledTerminalPhaseLaw q I current).map liveOutput) +
      (scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x)) Set.univ •
        Measure.dirac deadOutput := by
  let liveSet := scheduledBalancedTraceLiveSet q.n
  let deadSet := scheduledBalancedTraceDeadSet q.n
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let state : ScheduledBalancedCoolingTrace q.n → AmbientSpace q.n :=
    scale ∘ scheduledBalancedTraceRetainedState
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
      liveOutput deadOutput
  let K : AmbientSpace q.n → Measure T := fun current =>
    (figureOneScheduledScaledTerminalPhaseLaw q I current).map liveOutput
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I (terminalPhaseSteps q)
      liveOutput deadOutput hliveOutput
  have hrawK :=
    figureOneScheduledScaledTerminalPhaseLaw_measurable_and_probability q I
  have hK : Measurable K :=
    (Measure.measurable_map _ hliveOutput).comp hrawK.1
  have hstate : Measurable state := by
    dsimp only [state, scale]
    exact ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id).comp
        measurable_scheduledBalancedTraceRetainedState
  have hsplit : law = law.restrict liveSet + law.restrict deadSet := by
    rw [show deadSet = liveSetᶜ by
      exact scheduledBalancedTraceDeadSet_eq_compl,
      Measure.restrict_add_restrict_compl
        measurableSet_scheduledBalancedTraceLiveSet]
  have hlive : (law.restrict liveSet).bind outK =
      ((law.restrict liveSet).map state).bind K := by
    rw [map_bind_eq_bind_comp_state (law.restrict liveSet) hstate hK]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem
      (measurableSet_scheduledBalancedTraceLiveSet (n := q.n))]
      with trace htrace
    rcases trace with ⟨history, live⟩
    cases live with
    | false => simp [liveSet, scheduledBalancedTraceLiveSet] at htrace
    | true =>
        simp only [outK, scheduledBalancedTracePhaseOutputLaw, if_true,
          K, state, scale, Function.comp_apply,
          scheduledBalancedTraceRetainedState]
        simp only [scheduledBalancedTracePhaseObservationLaw,
          lt_self_iff_false, if_false,
          scheduledBalancedCoolingUniformTransitionLaw,
          figureOneScheduledScaledTerminalPhaseLaw]
        simp only [if_true]
  have hdead : (law.restrict deadSet).bind outK =
      (law.restrict deadSet) Set.univ • Measure.dirac deadOutput := by
    have heq : ∀ᵐ trace ∂(law.restrict deadSet),
        outK trace = Measure.dirac deadOutput := by
      filter_upwards [ae_restrict_mem
        (measurableSet_scheduledBalancedTraceDeadSet (n := q.n))]
        with trace htrace
      rcases trace with ⟨history, live⟩
      cases live with
      | false =>
          simp [outK, scheduledBalancedTracePhaseOutputLaw,
            scheduledBalancedTracePhaseObservationLaw]
      | true => simp [deadSet, scheduledBalancedTraceDeadSet] at htrace
    rw [Measure.bind_congr_right heq, Measure.bind_const]
  calc
    law.bind outK =
        (law.restrict liveSet + law.restrict deadSet).bind outK :=
      congrArg (fun mu => mu.bind outK) hsplit
    _ = (law.restrict liveSet).bind outK +
        (law.restrict deadSet).bind outK :=
      measure_bind_add_left _ _ houtK.1
    _ = ((law.restrict liveSet).map state).bind K +
        (law.restrict deadSet) Set.univ • Measure.dirac deadOutput := by
      rw [hlive, hdead]
    _ = _ := by
      congr 2
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      symm
      exact scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop)

theorem bind_scheduledBalancedTerminalTracePhaseOutputLaw_leUpTo_of_live_good_bad
    {T : Type*} [MeasurableSpace T]
    (q : VolumeParams) (I : VolumeInput q.n)
    (law : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure law]
    (good bad : Measure (AmbientSpace q.n)) [IsFiniteMeasure bad]
    {M eta : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hM16 : M ≤ ENNReal.ofReal (16 * speedyAdjacentWarmConstant q))
    (hlive : scheduledBalancedTraceLiveStateLaw law
      (fun x => accuracyScaleFactor q • x) ≤ good + bad)
    (hgood : Arlib.IsWarm M good
      (figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)))
    (herror : bad Set.univ +
        scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x) Set.univ ≤ eta)
    (liveOutput : Option (ℝ × AmbientSpace q.n) → T)
    (deadOutput : T) (hliveOutput : Measurable liveOutput) :
    MeasureLeUpTo
      (law.bind (scheduledBalancedTracePhaseOutputLaw
        figureOneFinalScheduledBalancedParameters q I
          (terminalPhaseSteps q) liveOutput deadOutput))
      ((figureOneScheduledTerminalPhaseTarget q I).map liveOutput)
      (figureOneCorrectedTransitionBudget q + eta) := by
  let rawK := figureOneScheduledScaledTerminalPhaseLaw q I
  let K : AmbientSpace q.n → Measure T := fun current =>
    (rawK current).map liveOutput
  have hrawK :=
    figureOneScheduledScaledTerminalPhaseLaw_measurable_and_probability q I
  have hK : Measurable K :=
    (Measure.measurable_map _ hliveOutput).comp hrawK.1
  have hKprob : ∀ current, IsProbabilityMeasure (K current) := by
    intro current
    let _ := hrawK.2 current
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  let target := (figureOneScheduledTerminalPhaseTarget q I).map liveOutput
  let _ : IsProbabilityMeasure target := by
    let _ := figureOneScheduledTerminalPhaseTarget_isProbabilityMeasure q I
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let live := scheduledBalancedTraceLiveStateLaw law scale
  let dead := scheduledBalancedTraceDeadStateLaw law scale
  let pi := figureOneScheduledSpeedyPiAt q I (terminalPhaseSteps q)
  let _ : IsProbabilityMeasure pi :=
    figureOneScheduledSpeedyPiAt_isProbabilityMeasure q I
      (terminalPhaseSteps q)
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hmass : live Set.univ + dead Set.univ = 1 := by
    rw [← Measure.add_apply,
      ← scheduledBalancedTraceStateLaw_eq_live_add_dead law scale hscale]
    unfold scheduledBalancedTraceStateLaw
    rw [Measure.map_apply
      (hscale.comp measurable_scheduledBalancedTraceRetainedState)
      MeasurableSet.univ, Set.preimage_univ, measure_univ]
  let _ : IsFiniteMeasure live :=
    ⟨(le_add_right (le_refl (live Set.univ)) |>.trans_eq hmass).trans_lt
      ENNReal.one_lt_top⟩
  let _ : IsFiniteMeasure dead :=
    ⟨(le_add_left (le_refl (dead Set.univ)) |>.trans_eq hmass).trans_lt
      ENNReal.one_lt_top⟩
  have hmlu := measureLeUpTo_live_dead_bind_of_good_bad
    live dead good bad pi hM hMtop hmass
    (by simpa [live, scale] using hlive)
    (by simpa [pi] using hgood)
    (by simpa [dead, scale] using herror)
    K hK hKprob (Measure.dirac deadOutput) target
    (fun nu hnu hwarm => by
      let _ : IsProbabilityMeasure nu := hnu
      have hraw :=
        bind_figureOneScheduledScaledTerminalPhaseLaw_leUpTo_target_of_warmSixteen
          q I nu (hwarm.mono hM16)
      have hmapped := hraw.map hliveOutput
      rw [map_bind_eq_bind_map_of_measurable nu hrawK.1 hliveOutput] at hmapped
      simpa [K, rawK, target] using hmapped)
  rw [bind_scheduledBalancedTerminalTracePhaseOutputLaw_eq_live_dead
    q I law liveOutput deadOutput hliveOutput]
  simpa [live, dead, K, rawK, target, scale] using hmlu

theorem approxIndepFun_figureOneScheduledTrace_terminalPhaseOutput
    (q : VolumeParams) (I : VolumeInput q.n) :
    let i := terminalPhaseSteps q
    let rho := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I i
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
    let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
    let outK := scheduledBalancedTracePhaseOutputLaw
      figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
    ApproxIndepFun (figureOneDependentEpsilon q)
      (X ∘ Prod.fst) Prod.snd (sequentialPairLaw rho outK) := by
  dsimp only
  let i := terminalPhaseSteps q
  have hiPos : 0 < i := terminalPhaseSteps_pos q
  let previous := i - 1
  have hprevious : previous < terminalPhaseSteps q := by
    dsimp only [previous, i]
    omega
  have hpreviousSucc : previous + 1 = i := by
    dsimp only [previous]
    omega
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I i
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I previous).map scale
  let eta := figureOneScheduledRetainedError q i
  let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
  let target := (figureOneScheduledTerminalPhaseTarget q I).map liveOutput
  obtain ⟨bad, hlive, herror⟩ :=
    exists_figureOneScheduledTraceScaledLive_good_bad q I previous hprevious
  have hliveRho : scheduledBalancedTraceLiveStateLaw rho scale ≤ good + bad := by
    simpa [rho, good, scale, i, hpreviousSucc] using hlive
  have herrorEta : bad Set.univ +
      scheduledBalancedTraceDeadStateLaw rho scale Set.univ ≤ eta := by
    simpa [rho, scale, eta, i, hpreviousSucc] using herror
  have hetaTop : eta ≠ ⊤ := by
    dsimp only [eta]
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun phase _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure bad :=
    { measure_univ_lt_top := by
        apply lt_of_le_of_lt
        · exact le_trans (le_add_right le_rfl) herrorEta
        · exact lt_top_iff_ne_top.mpr hetaTop }
  let _ : IsProbabilityMeasure rho :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I i
  have hscale : Measurable scale := by
    dsimp only [scale]
    fun_prop
  have hliveOutput : Measurable liveOutput :=
    measurable_figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  have houtK := scheduledBalancedTracePhaseOutputLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
      hliveOutput
  let _ : IsProbabilityMeasure target := by
    let _ := figureOneScheduledTerminalPhaseTarget_isProbabilityMeasure q I
    exact Measure.isProbabilityMeasure_map hliveOutput.aemeasurable
  have hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) good
      (figureOneScheduledSpeedyPiAt q I i) := by
    simpa [good, scale, i, figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt, hpreviousSucc] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous
  have hM8 : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM8M16 : ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hM16 : (1 : ENNReal) ≤
      ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) :=
    hM8.trans hM8M16
  have hbase : MeasureLeUpTo (rho.bind outK) target
      (figureOneCorrectedTransitionBudget q + eta) := by
    simpa [outK, target, i] using
      (bind_scheduledBalancedTerminalTracePhaseOutputLaw_leUpTo_of_live_good_bad
        q I rho good bad hM8 ENNReal.ofReal_ne_top hM8M16
        hliveRho (by simpa [i] using hgood) herrorEta
        liveOutput deadOutput hliveOutput)
  have hconditioned : ∀ mu : Measure (ScheduledBalancedCoolingTrace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo (mu.bind outK) target
        (figureOneCorrectedTransitionBudget q + 2 * eta) := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    have hmule : mu ≤ (2 : ENNReal) • rho :=
      (isWarm_iff_le_smul mu rho).1 hwarm
    let good2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • good
    let bad2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • bad
    let _ : IsFiniteMeasure bad2 :=
      { measure_univ_lt_top := by
          rw [show bad2 = (2 : ENNReal) • bad by rfl,
            Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top bad Set.univ) }
    have hlive2 : scheduledBalancedTraceLiveStateLaw mu scale ≤
        good2 + bad2 := by
      calc
        scheduledBalancedTraceLiveStateLaw mu scale ≤
            (2 : ENNReal) • scheduledBalancedTraceLiveStateLaw rho scale :=
          scheduledBalancedTraceLiveStateLaw_mono_smul q mu rho 2 scale
            hscale hmule
        _ ≤ (2 : ENNReal) • (good + bad) := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
            smul_eq_mul]
          gcongr
        _ = good2 + bad2 := by simp only [good2, bad2, smul_add]
    have hgood2 : Arlib.IsWarm
        (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) good2
        (figureOneScheduledSpeedyPiAt q I i) := by
      intro S hS
      rw [show good2 = (2 : ENNReal) • good by rfl,
        Measure.smul_apply, smul_eq_mul]
      have hg := hgood S hS
      have hcoef : (2 : ENNReal) *
          ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) =
            ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      calc
        2 * good S ≤ 2 *
            (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q) *
              (figureOneScheduledSpeedyPiAt q I i) S) := by gcongr
        _ = ENNReal.ofReal (16 * speedyAdjacentWarmConstant q) *
              (figureOneScheduledSpeedyPiAt q I i) S := by
          rw [← mul_assoc, hcoef]
    have hdead2 := scheduledBalancedTraceDeadStateLaw_mass_mono_smul
      q mu rho 2 scale hscale hmule
    have herror2 : bad2 Set.univ +
        scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤ 2 * eta := by
      rw [show bad2 = (2 : ENNReal) • bad by rfl,
        Measure.smul_apply, smul_eq_mul]
      calc
        2 * bad Set.univ +
            scheduledBalancedTraceDeadStateLaw mu scale Set.univ ≤
          2 * bad Set.univ +
            2 * scheduledBalancedTraceDeadStateLaw rho scale Set.univ := by
              gcongr
        _ = 2 * (bad Set.univ +
            scheduledBalancedTraceDeadStateLaw rho scale Set.univ) := by ring
        _ ≤ 2 * eta := by gcongr
    simpa [outK, target, i] using
      (bind_scheduledBalancedTerminalTracePhaseOutputLaw_leUpTo_of_live_good_bad
        q I mu good2 bad2 hM16 ENNReal.ofReal_ne_top le_rfl
        hlive2 (by simpa [i] using hgood2) herror2
        liveOutput deadOutput hliveOutput)
  have hraw := approxIndepFun_sequentialPairLaw_of_asymmetric_leUpTo
    rho outK houtK.1 houtK.2 target
    (ENNReal.add_ne_top.mpr ⟨by simp [figureOneCorrectedTransitionBudget],
      ENNReal.mul_ne_top (by norm_num) hetaTop⟩)
    (ENNReal.add_ne_top.mpr
      ⟨by simp [figureOneCorrectedTransitionBudget], hetaTop⟩)
    hconditioned hbase
  have hX : Measurable (dependentTruncatedProduct
      (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i) :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I)
      (fun j => (measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const) i
  apply (hraw.comp hX measurable_id).mono
  exact figureOneScheduledRetained_asymmetric_budget q i (by
    simp [i, figureOneDependentPhaseCount])

theorem approxIndepFun_figureOneScheduledFinalTrace_terminal
    (q : VolumeParams) (I : VolumeInput q.n) :
    let i := terminalPhaseSteps q
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
    ApproxIndepFun (figureOneDependentEpsilon q) X Y
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) := by
  dsimp only
  let i := terminalPhaseSteps q
  let rho := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I i
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  let liveOutput := figureOneScheduledTraceLiveTruncatedOutput q I (i + 1)
  let deadOutput := figureOneScheduledTraceDeadTruncatedOutput q I (i + 1)
  let outK := scheduledBalancedTracePhaseOutputLaw
    figureOneFinalScheduledBalancedParameters q I i liveOutput deadOutput
  have hV : ∀ j, Measurable
      (scheduledFigureOneTraceTruncatedPhase q I j) := fun j =>
    (measurable_scheduledBalancedTracePhaseVariable q j).min measurable_const
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) hV i
  have hY : Measurable Y := hV (i + 1)
  have himmediate :=
    approxIndepFun_figureOneScheduledTrace_terminalPhaseOutput q I
  have hlaw := map_pair_sequentialTracePhaseOutput_eq_forwardTrace_succ
    q I i (by simp [i, figureOneDependentPhaseCount])
  have htransported := ApproxIndepFun.of_map_pair_eq
    (hX.comp measurable_fst) measurable_snd hX hY
    (by simpa [i, rho, X, Y, outK, liveOutput, deadOutput,
      Function.comp_def] using hlaw)
    (by simpa [i, rho, X, outK, liveOutput, deadOutput] using himmediate)
  simpa [i, figureOneDependentPhaseCount] using htransported

/-- Fully concrete CV18 Lemma 7.17(c) for every finite phase of the final
loss-preserving executable trace. -/
theorem figureOneScheduledTrace_lemma717c
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) := by
  intro i hi
  cases i with
  | zero => exact approxIndepFun_figureOneScheduledFinalTrace_zero q I
  | succ previous =>
      by_cases hgaussian : previous + 1 < terminalPhaseSteps q
      · exact approxIndepFun_figureOneScheduledFinalTrace_gaussian
          q I previous hgaussian
      · have hterminal : previous + 1 = terminalPhaseSteps q := by
          rw [figureOneDependentPhaseCount] at hi
          omega
        simpa [hterminal] using
          approxIndepFun_figureOneScheduledFinalTrace_terminal q I

#print axioms figureOneScheduledTrace_deadState_mass_le_retainedError
#print axioms exists_figureOneScheduledTraceScaledState_good_bad

end ArlibCommunity.Algorithms.CV18
