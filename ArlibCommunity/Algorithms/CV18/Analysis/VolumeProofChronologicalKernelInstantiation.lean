/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalDependentAssembly

/-!
# Concrete chronological ideal coordinates for the CV18 exact-chance argument

This module instantiates the ideal side of the chronological dependent-product
argument on the existing finite Figure-One product law.  The explicit phase
equivalence ensures that the first `figureOneDependentPhaseCount q` coordinates
are distinct and hence independent.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Reindex the existing independent ideal phase experiment chronologically. -/
noncomputable def figureOneChronologicalIdealCoordinate
    (q : VolumeParams) (j : ℕ) : FigureOneIdealExperimentSpace q → ℝ :=
  figureOneIdealCoordinate q (figureOneChronologicalPhaseAt q j)

theorem figureOneChronologicalIdealCoordinate_measurable
    (q : VolumeParams) (j : ℕ) :
    Measurable (figureOneChronologicalIdealCoordinate q j) :=
  figureOneIdealCoordinate_measurable q _

theorem figureOneChronologicalIdealCoordinate_memLp
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) (p : ENNReal) :
    MemLp (figureOneChronologicalIdealCoordinate q j) p
      (figureOneIdealExperimentLaw q I) :=
  figureOneIdealCoordinate_memLp q I _ p

theorem figureOneChronologicalIdealCoordinate_mean
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) (j : ℕ) :
    (∫ samples, figureOneChronologicalIdealCoordinate q j samples
      ∂figureOneIdealExperimentLaw q I) =
        figureOneChronologicalRawMean q I j :=
  figureOneIdealCoordinate_mean q I hsharp _

theorem figureOneChronologicalIdealCoordinate_secondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) (j : ℕ) :
    (∫ samples, figureOneChronologicalIdealCoordinate q j samples ^ 2
      ∂figureOneIdealExperimentLaw q I) ≤
        figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2 :=
  figureOneIdealCoordinate_secondMoment_le q I hsharp _

theorem figureOneIdealPhaseEstimator_nonneg
    (q : VolumeParams) (phase : FigureOneIdealPhase q)
    (samples : FigureOneIdealPhaseSampleSpace q phase) :
    0 ≤ figureOneIdealPhaseEstimator q phase samples := by
  cases phase with
  | fixed k =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage gaussianRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => div_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le
      · positivity
  | accelerated k =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage gaussianRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => div_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le
      · positivity
  | terminal =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage uniformRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
      · positivity

theorem figureOneChronologicalIdealCoordinate_nonneg
    (q : VolumeParams) (j : ℕ) (samples : FigureOneIdealExperimentSpace q) :
    0 ≤ figureOneChronologicalIdealCoordinate q j samples :=
  figureOneIdealPhaseEstimator_nonneg q _ _

/-- Chronological coordinates are mutually independent inside their finite
horizon.  The bound is essential because `figureOneChronologicalPhaseAt` is
defined periodically outside that horizon. -/
theorem figureOneChronologicalIdealCoordinate_indepFun
    (q : VolumeParams) (I : VolumeInput q.n) {j k : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ figureOneDependentPhaseCount q)
    (hk : 1 ≤ k) (hk' : k ≤ figureOneDependentPhaseCount q)
    (hjk : j ≠ k) :
    IndepFun (figureOneChronologicalIdealCoordinate q j)
      (figureOneChronologicalIdealCoordinate q k)
      (figureOneIdealExperimentLaw q I) := by
  apply (figureOneIdealCoordinates_iIndepFun q I).indepFun
  intro heq
  apply hjk
  have hjmod : (j - 1) % figureOneDependentPhaseCount q = j - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hkmod : (k - 1) % figureOneDependentPhaseCount q = k - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hfin : (⟨j - 1, by omega⟩ : Fin (figureOneDependentPhaseCount q)) =
      ⟨k - 1, by omega⟩ := by
    apply (figureOneChronologicalPhaseOrder q).injective
    simpa [figureOneChronologicalPhaseAt, hjmod, hkmod] using heq
  have : j - 1 = k - 1 := congrArg Fin.val hfin
  omega

/-- The finite family actually consumed by Figure One is mutually
independent, not merely pairwise independent. -/
theorem figureOneChronologicalIdealFinCoordinates_iIndepFun
    (q : VolumeParams) (I : VolumeInput q.n) :
    iIndepFun
      (fun i : Fin (figureOneDependentPhaseCount q) =>
        figureOneChronologicalIdealCoordinate q (i.1 + 1))
      (figureOneIdealExperimentLaw q I) := by
  have h := iIndepFun.precomp (figureOneChronologicalPhaseOrder q).injective
    (figureOneIdealCoordinates_iIndepFun q I)
  rw [show (fun i : Fin (figureOneDependentPhaseCount q) =>
      figureOneChronologicalIdealCoordinate q (i.1 + 1)) =
      fun i => figureOneIdealCoordinate q
        (figureOneChronologicalPhaseOrder q i) by
    funext i
    unfold figureOneChronologicalIdealCoordinate figureOneChronologicalPhaseAt
    congr 2
    apply Fin.ext
    simp only
    rw [show i.1 + 1 - 1 = i.1 by omega, Nat.mod_eq_of_lt i.isLt]]
  exact h

set_option maxHeartbeats 800000 in
/-- First-truncated chronological coordinates retain mutual independence. -/
theorem figureOneChronologicalIdealTruncatedFinCoordinates_iIndepFun
    (q : VolumeParams) (I : VolumeInput q.n) :
    iIndepFun
      (fun i : Fin (figureOneDependentPhaseCount q) =>
        figureOneChronologicalTruncatedPhase q I
          (figureOneChronologicalIdealCoordinate q) (i.1 + 1))
      (figureOneIdealExperimentLaw q I) := by
  have h := figureOneChronologicalIdealFinCoordinates_iIndepFun q I
  let truncate : ∀ _i : Fin (figureOneDependentPhaseCount q), ℝ → ℝ :=
    fun i value => min value
      (figureOneDependentAlpha q *
        figureOneChronologicalRawMean q I (i.1 + 1))
  have htruncate : ∀ i, Measurable (truncate i) := fun _ =>
    measurable_id.min measurable_const
  have hc := h.comp truncate htruncate
  change iIndepFun (fun (i : Fin (figureOneDependentPhaseCount q)) samples => min
      (figureOneChronologicalIdealCoordinate q (i.1 + 1) samples)
      (figureOneDependentAlpha q *
        figureOneChronologicalRawMean q I (i.1 + 1)))
    (figureOneIdealExperimentLaw q I)
  convert hc using 1 <;> rfl

noncomputable def figureOneChronologicalPrefixIndices
    (q : VolumeParams) (i : ℕ) :
    Finset (Fin (figureOneDependentPhaseCount q)) :=
  Finset.univ.filter fun k => k.1 < i

noncomputable def figureOneChronologicalPrefixValue
    (q : VolumeParams) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q)
    (values : (k : figureOneChronologicalPrefixIndices q i) → ℝ)
    (j : ℕ) : ℝ :=
  if hj : 1 ≤ j ∧ j ≤ i then
    values ⟨⟨j - 1, by omega⟩, by
      simp only [figureOneChronologicalPrefixIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega⟩
  else 0

theorem measurable_figureOneChronologicalPrefixValue
    (q : VolumeParams) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) (j : ℕ) :
    Measurable (fun values =>
      figureOneChronologicalPrefixValue q i hi values j) := by
  unfold figureOneChronologicalPrefixValue
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

noncomputable def figureOneChronologicalTruncatedProductFromPrefix
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) :
    ((k : figureOneChronologicalPrefixIndices q i) → ℝ) → ℝ :=
  dependentTruncatedProduct (figureOneDependentAlpha q)
    (figureOneChronologicalTruncatedMean q I
      (figureOneIdealExperimentLaw q I)
      (figureOneChronologicalIdealCoordinate q))
    (fun j values => figureOneChronologicalPrefixValue q i hi values j) i

theorem measurable_figureOneChronologicalTruncatedProductFromPrefix
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) :
    Measurable (figureOneChronologicalTruncatedProductFromPrefix q I i hi) := by
  exact measurable_dependentTruncatedProduct _ _ _
    (measurable_figureOneChronologicalPrefixValue q i hi) i

theorem figureOneChronologicalTruncatedProductFromPrefix_apply
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q)
    (samples : FigureOneIdealExperimentSpace q) :
    figureOneChronologicalTruncatedProductFromPrefix q I i hi
        (fun k => figureOneChronologicalTruncatedPhase q I
          (figureOneChronologicalIdealCoordinate q) (k.1.1 + 1) samples) =
      dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I
          (figureOneIdealExperimentLaw q I)
          (figureOneChronologicalIdealCoordinate q))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneChronologicalIdealCoordinate q)) i samples := by
  let mean := figureOneChronologicalTruncatedMean q I
    (figureOneIdealExperimentLaw q I)
    (figureOneChronologicalIdealCoordinate q)
  let V := figureOneChronologicalTruncatedPhase q I
    (figureOneChronologicalIdealCoordinate q)
  have haux : ∀ m, m ≤ i →
      dependentTruncatedProduct (figureOneDependentAlpha q) mean
          (fun j values => figureOneChronologicalPrefixValue q i hi values j) m
          (fun k => V (k.1.1 + 1) samples) =
        dependentTruncatedProduct (figureOneDependentAlpha q) mean V m samples := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [dependentTruncatedProduct_succ,
          dependentTruncatedProduct_succ, ih (by omega)]
        congr 2
        simp only [figureOneChronologicalPrefixValue]
        rw [dif_pos ⟨by omega, hm⟩]
        congr 2
  exact haux i le_rfl

theorem figureOneChronologicalIdealTruncatedProduct_indepFun
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) :
    IndepFun
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I
          (figureOneIdealExperimentLaw q I)
          (figureOneChronologicalIdealCoordinate q))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneChronologicalIdealCoordinate q)) i)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneChronologicalIdealCoordinate q) (i + 1))
      (figureOneIdealExperimentLaw q I) := by
  let V := figureOneChronologicalTruncatedPhase q I
    (figureOneChronologicalIdealCoordinate q)
  let S := figureOneChronologicalPrefixIndices q i
  let next : Fin (figureOneDependentPhaseCount q) := ⟨i, hi⟩
  have hind := figureOneChronologicalIdealTruncatedFinCoordinates_iIndepFun q I
  have hdisjoint : Disjoint S ({next} : Finset _) := by
    rw [Finset.disjoint_singleton_right]
    simp only [S, next, figureOneChronologicalPrefixIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_irrefl i
  have hvectors := hind.indepFun_finset S {next} hdisjoint fun k =>
    figureOneChronologicalTruncatedPhase_measurable q I
      (figureOneChronologicalIdealCoordinate q)
      (figureOneChronologicalIdealCoordinate_measurable q) (k.1 + 1)
  have hcomp := hvectors.comp
    (measurable_figureOneChronologicalTruncatedProductFromPrefix q I i hi)
    (measurable_pi_apply
      (⟨next, Finset.mem_singleton_self next⟩ : ({next} : Finset _) ))
  have hleft :
      figureOneChronologicalTruncatedProductFromPrefix q I i hi ∘
          (fun samples (k : S) => V (k.1.1 + 1) samples) =
        dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I
            (figureOneIdealExperimentLaw q I)
            (figureOneChronologicalIdealCoordinate q)) V i := by
    funext samples
    exact figureOneChronologicalTruncatedProductFromPrefix_apply
      q I i hi samples
  have hright :
      (fun values : (k : ({next} : Finset _)) → ℝ =>
          values ⟨next, Finset.mem_singleton_self next⟩) ∘
          (fun samples (k : ({next} : Finset _)) => V (k.1.1 + 1) samples) =
        V (i + 1) := by
    rfl
  rw [hleft, hright] at hcomp
  exact hcomp

theorem IndepFun.approxIndepFun_zero
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → S} {Y : Omega → T} (h : IndepFun X Y mu) :
    ApproxIndepFun 0 X Y mu := by
  intro A hA B hB
  have heq := h.measure_inter_preimage_eq_mul A B hA hB
  have hreal := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_mul] at hreal
  change |(mu (X ⁻¹' A ∩ Y ⁻¹' B)).toReal -
    (mu (X ⁻¹' A)).toReal * (mu (Y ⁻¹' B)).toReal| ≤ 0
  rw [hreal]
  norm_num

theorem figureOneChronologicalIdeal_exactIndependence
    (q : VolumeParams) (I : VolumeInput q.n) (i : ℕ)
    (hi : i < figureOneDependentPhaseCount q) :
    ApproxIndepFun 0
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I
          (figureOneIdealExperimentLaw q I)
          (figureOneChronologicalIdealCoordinate q))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneChronologicalIdealCoordinate q)) i)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneChronologicalIdealCoordinate q) (i + 1))
      (figureOneIdealExperimentLaw q I) := by
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  exact IndepFun.approxIndepFun_zero
    (figureOneChronologicalIdealTruncatedProduct_indepFun q I i hi)

/-! ## Concrete ideal iterated law -/

/-- The ideal comparison history is stationary while executable coordinates
are replaced.  Thus its exact-chance kernel is the identity kernel. -/
noncomputable def figureOneChronologicalIdealKernel (q : VolumeParams) :
    ℕ → FigureOneIdealExperimentSpace q →
      Measure (FigureOneIdealExperimentSpace q) :=
  fun _ samples => Measure.dirac samples

theorem figureOneChronologicalIdealKernel_measurable
    (q : VolumeParams) (i : ℕ) :
    Measurable (figureOneChronologicalIdealKernel q i) :=
  Measure.measurable_dirac

theorem figureOneChronologicalIdealKernel_isProbabilityMeasure
    (q : VolumeParams) (i : ℕ) (samples : FigureOneIdealExperimentSpace q) :
    IsProbabilityMeasure (figureOneChronologicalIdealKernel q i samples) := by
  unfold figureOneChronologicalIdealKernel
  infer_instance

theorem iteratedKernelLaw_figureOneChronologicalIdealKernel
    (q : VolumeParams) (I : VolumeInput q.n) (t : ℕ) :
    iteratedKernelLaw (figureOneChronologicalIdealKernel q)
        (figureOneIdealExperimentLaw q I) t =
      figureOneIdealExperimentLaw q I := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iteratedKernelLaw_succ, ih]
      exact Measure.bind_dirac

/-! ## Concrete balanced post-initial history law -/

theorem measurableSet_balancedCoolingHistoryHasProduct (m : ℕ) :
    MeasurableSet {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasProduct m history} := by
  let A : Set (BalancedCoolingHistory n) := {history |
    history.2.1 = m ∧
      history.2.2.1 = ∏ j ∈ Finset.range m, history.1 j}
  have hcount : Measurable fun history : BalancedCoolingHistory n =>
      history.2.1 := by fun_prop
  have hproduct : Measurable fun history : BalancedCoolingHistory n =>
      history.2.2.1 := by fun_prop
  have hsequence : Measurable fun history : BalancedCoolingHistory n =>
      ∏ j ∈ Finset.range m, history.1 j := by fun_prop
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun hcount measurable_const).inter
      (measurableSet_eq_fun hproduct hsequence)
  rw [show {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasProduct m history} =
      {none} ∪ optionSomeEvent A by
    ext history
    cases history <;> simp [BalancedCoolingHistoryHasProduct,
      optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

/-- Every history produced by the recursive Gaussian cooling law stores the
exact product of precisely the phases it contains. -/
theorem balancedCoolingHistoryLaw_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      ∀ point, ∀ᵐ history ∂balancedCoolingHistoryLaw parameters q I variances point,
        BalancedCoolingHistoryHasProduct (variances.length - 1) history := by
  intro variances
  induction variances with
  | nil =>
      intro _ point
      rw [balancedCoolingHistoryLaw]
      apply (ae_dirac_iff
        (measurableSet_balancedCoolingHistoryHasProduct 0)).2
      simp [BalancedCoolingHistoryHasProduct]
  | cons sigma2 rest ih =>
      cases rest with
      | nil =>
          intro _ point
          rw [balancedCoolingHistoryLaw]
          apply (ae_dirac_iff
            (measurableSet_balancedCoolingHistoryHasProduct 0)).2
          simp [BalancedCoolingHistoryHasProduct]
      | cons tau2 tail =>
          intro hpositive point
          have htailPositive : ∀ s ∈ tau2 :: tail, 0 < s := by
            intro s hs
            exact hpositive s (by simp [hs])
          let continuation : Option (ℝ × AmbientSpace q.n) →
              Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
            match phase with
            | none => Measure.dirac none
            | some (ratio, nextPoint) =>
                (balancedCoolingHistoryLaw parameters q I
                  (tau2 :: tail) nextPoint).map
                    (balancedCoolingHistoryCons ratio)
          have hcontinuation : Measurable continuation := by
            have htailLaw := balancedCoolingHistoryLaw_measurable_and_probability
              parameters q I (tau2 :: tail) htailPositive
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                (balancedCoolingHistoryLaw parameters q I
                  (tau2 :: tail) value.2).map
                    (balancedCoolingHistoryCons value.1) := by
              apply measurable_measure_map_param_variable
              · exact htailLaw.1.comp measurable_snd
              · intro value
                exact htailLaw.2 value.2
              · exact measurable_balancedCoolingHistoryCons.comp
                  ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
            convert Measurable.optionElim
              (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
                hsome using 1
            funext phase
            cases phase <;> rfl
          let source := balancedCoolingRatioLaw parameters q I sigma2 tau2 point
          let good : Set (Option (BalancedCoolingHistory q.n)) :=
            {history | BalancedCoolingHistoryHasProduct
              ((sigma2 :: tau2 :: tail).length - 1) history}
          have hgood : MeasurableSet good :=
            measurableSet_balancedCoolingHistoryHasProduct _
          rw [balancedCoolingHistoryLaw]
          apply MeasureTheory.mem_ae_iff.mpr
          change (source.bind continuation) goodᶜ = 0
          rw [Measure.bind_apply hgood.compl hcontinuation.aemeasurable]
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards with phase
          cases phase with
          | none =>
              rw [Measure.dirac_apply' _ hgood.compl]
              simp [good, BalancedCoolingHistoryHasProduct]
          | some value =>
              have htail := ih htailPositive value.2
              have htarget : ∀ᵐ history ∂
                  (balancedCoolingHistoryLaw parameters q I
                    (tau2 :: tail) value.2).map
                      (balancedCoolingHistoryCons value.1),
                  BalancedCoolingHistoryHasProduct
                    ((sigma2 :: tau2 :: tail).length - 1) history := by
                apply (ae_map_iff
                  (measurable_balancedCoolingHistoryCons.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable
                  (measurableSet_balancedCoolingHistoryHasProduct
                    ((sigma2 :: tau2 :: tail).length - 1))).2
                filter_upwards [htail] with history hhistory
                simpa using hhistory.cons value.1
              exact MeasureTheory.mem_ae_iff.mp htarget

theorem balancedFigureOneFullHistoryLaw_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    ∀ᵐ history ∂balancedFigureOneFullHistoryLaw parameters q I point,
      BalancedCoolingHistoryHasProduct
        (figureOneDependentPhaseCount q) history := by
  let m := terminalPhaseSteps q
  have hcooling0 := balancedCoolingHistoryLaw_ae_hasProduct
    parameters q I (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive point
  have hcooling : ∀ᵐ history ∂
      balancedFigureOneCoolingHistoryLaw parameters q I point,
      BalancedCoolingHistoryHasProduct m history := by
    simpa [balancedFigureOneCoolingHistoryLaw, explicitVolumeCoolingSchedule,
      explicitScheduleVariances, m] using hcooling0
  let continuation : Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun history =>
    match history with
    | none => Measure.dirac none
    | some value =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value)
  have hcontinuation : Measurable continuation := by
    have hterminal := balancedCoolingUniformLawWithState_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
    have hsome : Measurable fun value : BalancedCoolingHistory q.n =>
        (balancedCoolingUniformLawWithState parameters q I
          (terminalVariance q) value.2.2.2).map
            (balancedCoolingHistorySnocTerminal value) := by
      apply measurable_measure_map_param_variable
      · exact hterminal.1.comp <|
          measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp measurable_id))
      · intro value
        exact hterminal.2 value.2.2.2
      · exact measurable_balancedCoolingHistorySnocTerminal.comp
          (measurable_fst.prodMk measurable_snd)
    convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext history
    cases history <;> rfl
  let source := balancedFigureOneCoolingHistoryLaw parameters q I point
  let good : Set (Option (BalancedCoolingHistory q.n)) :=
    {history | BalancedCoolingHistoryHasProduct
      (figureOneDependentPhaseCount q) history}
  have hgood : MeasurableSet good :=
    measurableSet_balancedCoolingHistoryHasProduct _
  unfold balancedFigureOneFullHistoryLaw
  apply MeasureTheory.mem_ae_iff.mpr
  change (source.bind continuation) goodᶜ = 0
  rw [Measure.bind_apply hgood.compl hcontinuation.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hcooling] with history hhistory
  cases history with
  | none =>
      rw [Measure.dirac_apply' _ hgood.compl]
      simp [good, BalancedCoolingHistoryHasProduct]
  | some value =>
      have htarget : ∀ᵐ result ∂
          (balancedCoolingUniformLawWithState parameters q I
            (terminalVariance q) value.2.2.2).map
              (balancedCoolingHistorySnocTerminal value),
          BalancedCoolingHistoryHasProduct
            (figureOneDependentPhaseCount q) result := by
        apply (ae_map_iff
          (measurable_balancedCoolingHistorySnocTerminal.comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasProduct _)).2
        filter_upwards with terminal
        simpa [figureOneDependentPhaseCount, m] using
          hhistory.snocTerminal terminal
      exact MeasureTheory.mem_ae_iff.mp htarget

/-- Complete balanced history after a genuinely restricted-Gaussian initial
point.  This is the actual post-initial probability space used by the direct
failure argument. -/
noncomputable def balancedFigureOnePostInitialHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : Measure (Option (BalancedCoolingHistory q.n)) :=
  (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
    (balancedFigureOneFullHistoryLaw parameters q I)

theorem balancedFigureOnePostInitialHistoryLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    IsProbabilityMeasure
      (balancedFigureOnePostInitialHistoryLaw parameters q I) := by
  unfold balancedFigureOnePostInitialHistoryLaw
  exact MeasureTheory.isProbabilityMeasure_bind
    (balancedFigureOneFullHistoryLaw_measurable_and_probability
      parameters q I).1.aemeasurable
    (ae_of_all _ (balancedFigureOneFullHistoryLaw_measurable_and_probability
      parameters q I).2)

theorem balancedFigureOnePostInitialHistoryLaw_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ∀ᵐ history ∂balancedFigureOnePostInitialHistoryLaw parameters q I,
      BalancedCoolingHistoryHasProduct
        (figureOneDependentPhaseCount q) history := by
  let source := (truncatedGaussianProbability q I (initialVariance q)
    (initialVariance_pos q) : Measure (AmbientSpace q.n))
  let kernel := balancedFigureOneFullHistoryLaw parameters q I
  let good : Set (Option (BalancedCoolingHistory q.n)) :=
    {history | BalancedCoolingHistoryHasProduct
      (figureOneDependentPhaseCount q) history}
  have hgood : MeasurableSet good :=
    measurableSet_balancedCoolingHistoryHasProduct _
  have hkernel : Measurable kernel :=
    (balancedFigureOneFullHistoryLaw_measurable_and_probability
      parameters q I).1
  unfold balancedFigureOnePostInitialHistoryLaw
  apply MeasureTheory.mem_ae_iff.mpr
  change (source.bind kernel) goodᶜ = 0
  rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with point
  exact MeasureTheory.mem_ae_iff.mp
    (balancedFigureOneFullHistoryLaw_ae_hasProduct parameters q I point)

/-- The interpreter law of the balanced continuation is exactly the scalar
map of the complete chronological history law. -/
theorem bind_balancedFigureOnePointContinuation_eq_postInitialHistory_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (fun point =>
          (balancedFigureOnePointContinuation parameters q point).runEstimate
            oracle.query) =
      (balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (balancedFigureOneHistoryEstimate q) := by
  have hfull := balancedFigureOneFullHistoryLaw_measurable_and_probability
    parameters q I
  have hestimate := measurable_balancedFigureOneHistoryEstimate q
  rw [show (fun point =>
      (balancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query) = fun point =>
      (balancedFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) by
    funext point
    exact balancedFigureOnePointContinuation_runEstimate_eq_history_map
      parameters q I oracle point]
  unfold balancedFigureOnePostInitialHistoryLaw
  exact (map_bind_eq_bind_map_of_measurable _ hfull.1 hestimate).symm

/-- Once the structural product invariant is known almost surely, the actual
balanced scalar law is exactly the chronological sample-product law. -/
theorem bind_balancedFigureOnePointContinuation_eq_sampleProduct_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hproduct : ∀ᵐ history ∂balancedFigureOnePostInitialHistoryLaw parameters q I,
      BalancedCoolingHistoryHasProduct
        (figureOneDependentPhaseCount q) history) :
    (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (fun point =>
          (balancedFigureOnePointContinuation parameters q point).runEstimate
            oracle.query) =
      (balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history) := by
  rw [bind_balancedFigureOnePointContinuation_eq_postInitialHistory_map]
  apply Measure.map_congr
  filter_upwards [hproduct] with history hhistory
  exact balancedFigureOneHistoryEstimate_eq_sampleProduct q history hhistory

/-- Balanced-continuation specialization of the cross-history event-transfer
wrapper.  The executable output law is identified exactly; the sole remaining
comparison premise is the finite mapped-product domination `htransfer`. -/
theorem balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
    {Ideal : Type*} [MeasurableSpace Ideal]
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (idealLaw : Measure Ideal) [IsProbabilityMeasure idealLaw]
    (idealProduct : Ideal → ℝ) (hidealMeas : Measurable idealProduct)
    (mean : ℝ)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ i, figureOneIdealPhaseMean q I i) mean)
    (hidealTail : idealLaw {state | (5 * q.eps / 8) * mean ≤
      |idealProduct state - mean|} ≤ ENNReal.ofReal (11 / 64 : ℝ))
    (hproduct : ∀ᵐ history ∂balancedFigureOnePostInitialHistoryLaw parameters q I,
      BalancedCoolingHistoryHasProduct
        (figureOneDependentPhaseCount q) history)
    (htransfer : MeasureLeUpTo
      ((balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history))
      (idealLaw.map
        (fun state => initialGaussianIntegral q * idealProduct state))
      (ENNReal.ofReal (1 / 64 : ℝ))) :
    FigureOnePostInitialDirectFailureBoundFor q I
      (fun point =>
        (balancedFigureOnePointContinuation parameters q point).runEstimate
          oracle.query) := by
  apply figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
    q I (fun point =>
      (balancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query)
    htrunc (balancedFigureOnePostInitialHistoryLaw parameters q I) idealLaw
    (dependentPhaseSampleProduct
      (balancedCoolingChronologicalPhaseVariable q)
      (figureOneDependentPhaseCount q))
    idealProduct
  · unfold dependentPhaseSampleProduct
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j _ => measurable_balancedCoolingChronologicalPhaseVariable q (j + 1)
  · exact hidealMeas
  · exact hmeanApprox
  · exact hidealTail
  · exact htransfer
  · exact bind_balancedFigureOnePointContinuation_eq_sampleProduct_map
      parameters q I oracle hproduct

/-- All ideal-coordinate moment, truncation, product-center, and finite
independence obligations are discharged here.  For the concrete balanced
continuation, only its structural product invariant and the finite mapped-law
replacement estimate remain. -/
theorem balancedFigureOnePostInitialDirectFailureBound_of_idealMappedProductLe
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (hproduct : ∀ᵐ history ∂balancedFigureOnePostInitialHistoryLaw parameters q I,
      BalancedCoolingHistoryHasProduct
        (figureOneDependentPhaseCount q) history)
    (htransfer : MeasureLeUpTo
      ((balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ))) :
    FigureOnePostInitialDirectFailureBoundFor q I
      (fun point =>
        (balancedFigureOnePointContinuation parameters q point).runEstimate
          oracle.query) := by
  let W := figureOneChronologicalIdealCoordinate q
  let mu := figureOneIdealExperimentLaw q I
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  have hmeas : ∀ j, Measurable (W j) :=
    fun j => figureOneChronologicalIdealCoordinate_measurable q j
  have hnonneg : ∀ j samples, 0 ≤ W j samples :=
    fun j samples => figureOneChronologicalIdealCoordinate_nonneg q j samples
  have hmem : ∀ j, MemLp (W j) 2 mu :=
    fun j => figureOneChronologicalIdealCoordinate_memLp q I j 2
  have hmean : ∀ j, (∫ samples, W j samples ∂mu) =
      figureOneChronologicalRawMean q I j :=
    fun j => figureOneChronologicalIdealCoordinate_mean q I hsharp j
  have hsecond : ∀ j, (∫ samples, W j samples ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2 :=
    fun j => figureOneChronologicalIdealCoordinate_secondMoment_le q I hsharp j
  have hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I mu W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) mu := by
    intro i hi
    exact (figureOneChronologicalIdeal_exactIndependence q I i hi).mono
      (figureOneDependentEpsilon_nonneg q)
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I mu W hmeas hnonneg hmem hmean hsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I mu W hmeas hnonneg hmem hmean hsecond
  apply balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
    parameters q I oracle htrunc mu
      (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      (by
        unfold dependentPhaseSampleProduct
        exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
          fun j _ => hmeas (j + 1))
      mean hmeanApprox htail hproduct
  simpa [W, mu] using htransfer

/-- End-user form: the geometric and ideal-moment hypotheses are supplied by
the already-proved CV18 analytic theorems. -/
theorem balancedFigureOnePostInitialDirectFailureBound_of_mappedLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (htransfer : MeasureLeUpTo
      ((balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ))) :
    FigureOnePostInitialDirectFailureBoundFor q I
      (fun point =>
        (balancedFigureOnePointContinuation parameters q point).runEstimate
          oracle.query) :=
  balancedFigureOnePostInitialDirectFailureBound_of_idealMappedProductLe
    parameters q I oracle (figureOneRadialTruncationBound q I hrounded)
      (figureOneSharpAcceleratedMoments q I)
      (balancedFigureOnePostInitialHistoryLaw_ae_hasProduct parameters q I)
      htransfer

/-- The initial fallback costs at most `eps / 64`; hence the balanced base
run fails with probability at most `13/64` once the direct post-initial
contract has been established. -/
theorem balancedFigureOneBase_failure_le_of_directPostInitial
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hpost : FigureOnePostInitialDirectFailureBoundFor q I
      (fun point =>
        (balancedFigureOnePointContinuation parameters q point).runEstimate
          oracle.query)) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let K : AmbientSpace q.n → Measure ℝ := fun point =>
    (balancedFigureOnePointContinuation parameters q point).runEstimate
      oracle.query
  have hfull := balancedFigureOneFullHistoryLaw_measurable_and_probability
    parameters q I
  have hestimate := measurable_balancedFigureOneHistoryEstimate q
  have hK : Measurable K := by
    rw [show K = fun point =>
        (balancedFigureOneFullHistoryLaw parameters q I point).map
          (balancedFigureOneHistoryEstimate q) by
      funext point
      exact balancedFigureOnePointContinuation_runEstimate_eq_history_map
        parameters q I oracle point]
    exact (Measure.measurable_map _ hestimate).comp hfull.1
  have hKprob : ∀ point, IsProbabilityMeasure (K point) := by
    intro point
    rw [show K point =
        (balancedFigureOneFullHistoryLaw parameters q I point).map
          (balancedFigureOneHistoryEstimate q) by
      exact balancedFigureOnePointContinuation_runEstimate_eq_history_map
        parameters q I oracle point]
    let _ : IsProbabilityMeasure
        (balancedFigureOneFullHistoryLaw parameters q I point) := hfull.2 point
    exact Measure.isProbabilityMeasure_map hestimate.aemeasurable
  have hbaseLaw :
      (baseVolumeCooling (balancedCoolingPrimitives parameters)
          explicitVolumeCoolingSchedule q).runEstimate oracle.query =
        ((initialGaussianSamplingMeasure q).map
          (initialTruncatedFallback q I)).bind K := by
    rw [balancedFigureOneBaseVolumeCooling_runEstimate_eq_history_map]
    unfold balancedFigureOneBaseHistoryLaw
    calc
      Measure.map (balancedFigureOneHistoryEstimate q)
          ((initialGaussianSamplingMeasure q).bind (fun proposal =>
            balancedFigureOneFullHistoryLaw parameters q I
              (initialTruncatedFallback q I proposal))) =
          (initialGaussianSamplingMeasure q).bind (fun proposal =>
            (balancedFigureOneFullHistoryLaw parameters q I
              (initialTruncatedFallback q I proposal)).map
                (balancedFigureOneHistoryEstimate q)) :=
        map_bind_eq_bind_map_of_measurable _
          (hfull.1.comp (measurable_initialTruncatedFallback q I)) hestimate
      _ = (initialGaussianSamplingMeasure q).bind
          (K ∘ initialTruncatedFallback q I) := by
        congr 1
        funext proposal
        exact (balancedFigureOnePointContinuation_runEstimate_eq_history_map
          parameters q I oracle (initialTruncatedFallback q I proposal)).symm
      _ = ((initialGaussianSamplingMeasure q).map
          (initialTruncatedFallback q I)).bind K :=
        (map_bind_eq_bind_comp _ (initialTruncatedFallback q I)
          (measurable_initialTruncatedFallback q I) K hK).symm
  have hinitial := initialTruncatedFallback_bind_apply_le q I K hK hKprob
    (accurateOutcome q I)ᶜ (accurateOutcome_measurable q I).compl
  unfold FigureOnePostInitialDirectFailureBoundFor at hpost
  rw [hbaseLaw]
  calc
    ((initialGaussianSamplingMeasure q).map
        (initialTruncatedFallback q I)).bind K (accurateOutcome q I)ᶜ ≤
      ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind K)
          (accurateOutcome q I)ᶜ + ENNReal.ofReal (q.eps / 64) := hinitial
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) := by
      exact add_le_add hpost (ENNReal.ofReal_le_ofReal (by
        have := q.heps.2
        linarith))
    _ = ENNReal.ofReal (13 / 64 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 16)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

/-- Concrete base-run failure theorem: after the analytic and history
assembly, the only remaining probabilistic premise is the finite mapped-law
replacement bound. -/
theorem balancedFigureOneBase_failure_le_of_mappedLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (htransfer : MeasureLeUpTo
      ((balancedFigureOnePostInitialHistoryLaw parameters q I).map
        (fun history => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (balancedCoolingChronologicalPhaseVariable q)
            (figureOneDependentPhaseCount q) history))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ))) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) :=
  balancedFigureOneBase_failure_le_of_directPostInitial parameters q I oracle
    (balancedFigureOnePostInitialDirectFailureBound_of_mappedLaw
      parameters q I oracle hrounded htransfer)

#print axioms figureOneChronologicalIdealTruncatedFinCoordinates_iIndepFun
#print axioms figureOneChronologicalIdeal_exactIndependence
#print axioms iteratedKernelLaw_figureOneChronologicalIdealKernel
#print axioms balancedCoolingHistoryLaw_ae_hasProduct
#print axioms balancedFigureOneFullHistoryLaw_ae_hasProduct
#print axioms balancedFigureOnePostInitialHistoryLaw_ae_hasProduct
#print axioms bind_balancedFigureOnePointContinuation_eq_sampleProduct_map
#print axioms balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
#print axioms balancedFigureOnePostInitialDirectFailureBound_of_idealMappedProductLe
#print axioms balancedFigureOnePostInitialDirectFailureBound_of_mappedLaw
#print axioms balancedFigureOneBase_failure_le_of_directPostInitial
#print axioms balancedFigureOneBase_failure_le_of_mappedLaw

#print axioms figureOneChronologicalIdealCoordinate_mean
#print axioms figureOneChronologicalIdealCoordinate_secondMoment_le
#print axioms figureOneChronologicalIdealCoordinate_indepFun
#print axioms figureOneChronologicalIdealFinCoordinates_iIndepFun

end

end ArlibCommunity.Algorithms.CV18
