/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRejection
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceLaw

/-!
# Finite executable balanced KLS retries

Each trial first advances a capped block of proper speedy steps, then performs
one balanced KLS rejection test.  Rejection retains the unscaled speedy state
and consumes one retry; acceptance records the transformed target, resets the
retry budget, and begins the next sample.  Exhausting either a proposal cap or
a retry budget returns `none`.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Parameterized measurable elimination for the local `Option` measurable
space used by membership-oracle programs. -/
theorem Measurable.optionElimParam
    {P A B : Type*} [MeasurableSpace P] [MeasurableSpace A]
    [MeasurableSpace B] {noneValue : P → B} {someValue : P × A → B}
    (hnone : Measurable noneValue) (hsome : Measurable someValue) :
    Measurable fun z : P × Option A =>
      match z.2 with
      | none => noneValue z.1
      | some a => someValue (z.1, a) := by
  let encode : P × Option A → (P × Unit) ⊕ (P × A) := fun z =>
    MeasurableEquiv.prodSumDistrib P Unit A (z.1, optionToSum z.2)
  have hencode : Measurable encode := by
    exact (MeasurableEquiv.prodSumDistrib P Unit A).measurable.comp
      (measurable_fst.prodMk (measurable_optionToSum.comp measurable_snd))
  have hout : Measurable
      (Sum.elim (fun z : P × Unit => noneValue z.1) someValue) :=
    (hnone.comp measurable_fst).sumElim hsome
  convert hout.comp hencode using 1
  funext z
  rcases z with ⟨p, value⟩
  cases value <;> rfl

/-- A finite, globally bounded collector of balanced KLS samples.  The
`attempts` argument is the retry budget remaining for the current sample;
`retryLimit` is restored after every success. -/
noncomputable def balancedAccuracyRetryCollectAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, current => .pure (some (total, current))
  | 0, _ + 1, _, _ => .pure none
  | attempts + 1, samples + 1, total, current =>
      (cappedAccuracyProperCollectWeights q sigma2 (fun _ => 0)
        (proposalCap + 1) properStride 1 current).bind fun block =>
        match block with
        | none => .pure none
        | some (_, mixed) =>
            (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
              fun result =>
                if result.1 then
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit retryLimit samples
                    (total + weight result.2) mixed
                else
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit attempts (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

/-- Convert the retained speedy state of the last accepted trial into its
Gaussian target, while preserving failure and the accumulated observable. -/
noncomputable def balancedAccuracyRetryOutput (q : VolumeParams) :
    Option (ℝ × AmbientSpace q.n) → Option (ℝ × AmbientSpace q.n)
  | none => none
  | some (total, speedy) =>
      some (total, (accuracyScaleFactor q)⁻¹ • speedy)

theorem measurable_balancedAccuracyRetryOutput (q : VolumeParams) :
    Measurable (balancedAccuracyRetryOutput q) := by
  convert Measurable.optionElim none
    (measurable_some.comp <|
      measurable_fst.prodMk <|
        (measurable_const : Measurable fun _ : ℝ × AmbientSpace q.n =>
          (accuracyScaleFactor q)⁻¹).smul measurable_snd) using 1
  ext value
  cases value <;> rfl

noncomputable def balancedAccuracyRetryCollect (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
    retryLimit retryLimit samples 0 current).bind fun result =>
      .pure (balancedAccuracyRetryOutput q result)

/-- Number of queries reserved for all full future samples and the attempts
remaining for the current sample. -/
def balancedRetryQueryBudget (proposalCap retryLimit attempts samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | future + 1 => (future * retryLimit + attempts) * (proposalCap + 2)

theorem balancedRetryQueryBudget_full
    (proposalCap retryLimit samples : ℕ) :
    balancedRetryQueryBudget proposalCap retryLimit retryLimit samples =
      samples * retryLimit * (proposalCap + 2) := by
  cases samples with
  | zero => simp [balancedRetryQueryBudget]
  | succ samples =>
      simp [balancedRetryQueryBudget, Nat.succ_mul]

theorem balancedRetryQueryBudget_step
    (proposalCap retryLimit attempts future : ℕ) :
    (proposalCap + 2) +
        balancedRetryQueryBudget proposalCap retryLimit attempts (future + 1) =
      balancedRetryQueryBudget proposalCap retryLimit (attempts + 1)
        (future + 1) := by
  simp only [balancedRetryQueryBudget, Nat.add_mul]
  omega

/-- Every trial uses at most `proposalCap + 1` queries for the capped proper
block (including its harmless zero observation) and one query for KLS. -/
theorem balancedAccuracyRetryCollectAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples total current,
    (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
      retryLimit attempts samples total current).QueryBound
        (balancedRetryQueryBudget proposalCap retryLimit attempts samples) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro total current
          rw [balancedAccuracyRetryCollectAux]
          exact .pure _ _
      | succ future =>
          induction attempts with
          | zero =>
              intro total current
              rw [balancedAccuracyRetryCollectAux]
              exact .pure _ _
          | succ attempts ihAttempts =>
              intro total current
              simp only [balancedAccuracyRetryCollectAux]
              let block := cappedAccuracyProperCollectWeights q sigma2
                (fun _ => 0) (proposalCap + 1) properStride 1 current
              let tail : Option (ℝ × AmbientSpace q.n) →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun value =>
                match value with
                | none => .pure none
                | some (_, mixed) =>
                    (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
                      fun result =>
                        if result.1 then
                          balancedAccuracyRetryCollectAux q sigma2 weight
                            proposalCap properStride retryLimit retryLimit future
                            (total + weight result.2) mixed
                        else
                          balancedAccuracyRetryCollectAux q sigma2 weight
                            proposalCap properStride retryLimit attempts
                            (future + 1) total mixed
              have hblock : block.QueryBound (proposalCap + 1) := by
                dsimp [block]
                exact cappedAccuracyProperCollectWeights_queryBound q sigma2
                  (fun _ => 0) (proposalCap + 1) properStride 1 current
              have htail : ∀ value, (tail value).QueryBound
                  (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                    (future + 1)) := by
                intro value
                cases value with
                | none => exact .pure _ _
                | some value =>
                    rcases value with ⟨ignored, mixed⟩
                    dsimp only [tail]
                    apply MembershipOracleProgram.QueryBound.bind
                      (balancedAccuracyGaussianRejectionAttempt_queryBound
                        q sigma2 mixed)
                    intro result
                    by_cases hresult : result.1 = true
                    · simp only [hresult, if_true]
                      have hrec := ihSamples future (by omega) retryLimit
                        (total + weight result.2) mixed
                      rw [balancedRetryQueryBudget_full] at hrec
                      exact hrec.mono <| Nat.mul_le_mul_right
                        (proposalCap + 2) (Nat.le_add_right _ attempts)
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hresult
                      simp only [hfalse, Bool.false_eq_true, if_false]
                      exact ihAttempts total mixed
              have hbound := hblock.bind htail
              change (block.bind tail).QueryBound
                (balancedRetryQueryBudget proposalCap retryLimit
                  (attempts + 1) (future + 1))
              rw [← balancedRetryQueryBudget_step]
              have heq : proposalCap + 1 +
                    (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1)) =
                  proposalCap + 2 +
                    balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1) := by omega
              rw [← heq]
              exact hbound

theorem balancedAccuracyRetryCollect_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
      retryLimit samples current).QueryBound
        (samples * retryLimit * (proposalCap + 2)) :=
  by
    unfold balancedAccuracyRetryCollect
    have h := balancedAccuracyRetryCollectAux_queryBound q sigma2 weight
      proposalCap properStride retryLimit retryLimit samples 0 current
    rw [balancedRetryQueryBudget_full] at h
    exact h.bind fun result => .pure _ 0

/-- Measure-level counterpart of the balanced retry collector.  `B` is one
capped proper-step block and `R` is the balanced KLS kernel. -/
noncomputable def balancedRetryCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (B : Kernel S (Option (ℝ × S))) (R : Kernel S (Bool × S))
    (weight : S → ℝ) (retryLimit : ℕ) :
    ℕ → ℕ → ℝ → S → Measure (Option (ℝ × S))
  | _, 0, total, current => Measure.dirac (some (total, current))
  | 0, _ + 1, _, _ => Measure.dirac none
  | attempts + 1, samples + 1, total, current =>
      (B current).bind fun block =>
        match block with
        | none => Measure.dirac none
        | some (_, mixed) =>
            (R mixed).bind fun result =>
              if result.1 then
                balancedRetryCollectLawAux B R weight retryLimit retryLimit
                  samples (total + weight result.2) mixed
              else
                balancedRetryCollectLawAux B R weight retryLimit attempts
                  (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

theorem balancedRetryCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (B : Kernel S (Option (ℝ × S))) (R : Kernel S (Bool × S))
    [IsMarkovKernel B] [IsMarkovKernel R]
    {weight : S → ℝ} (hweight : Measurable weight) (retryLimit : ℕ) :
    ∀ attempts samples,
      Measurable (fun state : ℝ × S =>
        balancedRetryCollectLawAux B R weight retryLimit attempts samples
          state.1 state.2) ∧
      ∀ total current, IsProbabilityMeasure
        (balancedRetryCollectLawAux B R weight retryLimit attempts samples
          total current) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          simp only [balancedRetryCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <|
              measurable_some.comp (measurable_fst.prodMk measurable_snd)
          · intro total current
            infer_instance
      | succ future =>
          induction attempts with
          | zero =>
              simp only [balancedRetryCollectLawAux]
              constructor
              · exact Measure.measurable_dirac.comp measurable_const
              · intro total current
                infer_instance
          | succ attempts ihAttempts =>
              let nextResult : ((ℝ × S) × S) × (Bool × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                if value.2.1 then
                  balancedRetryCollectLawAux B R weight retryLimit retryLimit
                    future (value.1.1.1 + weight value.2.2) value.1.2
                else
                  balancedRetryCollectLawAux B R weight retryLimit attempts
                    (future + 1) value.1.1.1 value.1.2
              have hnextResult : Measurable nextResult := by
                dsimp only [nextResult]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (ihSamples future (by omega) retryLimit).1.comp <|
                    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
                      (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                        (measurable_snd.comp measurable_fst))
                · exact ihAttempts.1.comp <|
                    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
                      (measurable_snd.comp measurable_fst))
              let someTail : (ℝ × S) × (ℝ × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                (R value.2.2).bind fun result =>
                  nextResult ((value.1, value.2.2), result)
              have hsomeTail : Measurable someTail := by
                dsimp only [someTail]
                exact measurable_measure_bind_param_variable
                  (R.measurable.comp (measurable_snd.comp measurable_snd))
                  (fun value => IsMarkovKernel.isProbabilityMeasure value.2.2)
                  (hnextResult.comp <|
                    (((measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp
                        (measurable_snd.comp measurable_fst))).prodMk
                          measurable_snd))
              let tail : (ℝ × S) × Option (ℝ × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                match value.2 with
                | none => Measure.dirac none
                | some block => someTail (value.1, block)
              have htail : Measurable tail := by
                dsimp only [tail]
                convert Measurable.optionElimParam
                  (noneValue := fun _ : ℝ × S =>
                    Measure.dirac (none : Option (ℝ × S)))
                  (someValue := someTail)
                  (Measure.measurable_dirac.comp measurable_const) hsomeTail using 1
                ext value
                cases value.2 <;> rfl
              have hlaw : (fun state : ℝ × S =>
                    balancedRetryCollectLawAux B R weight retryLimit
                      (attempts + 1) (future + 1) state.1 state.2) =
                  fun state => (B state.2).bind fun block =>
                    tail (state, block) := by
                funext state
                simp only [balancedRetryCollectLawAux]
                apply Measure.bind_congr_right
                filter_upwards with block
                cases block with
                | none => rfl
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    dsimp only [tail, someTail]
              constructor
              · rw [hlaw]
                exact measurable_measure_bind_param_variable
                  (B.measurable.comp measurable_snd)
                  (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
                  htail
              · intro total current
                have hlawPoint :
                    balancedRetryCollectLawAux B R weight retryLimit
                        (attempts + 1) (future + 1) total current =
                      (B current).bind fun block =>
                        tail ((total, current), block) := by
                  simp only [balancedRetryCollectLawAux]
                  apply Measure.bind_congr_right
                  filter_upwards with block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      dsimp only [tail, someTail]
                rw [hlawPoint]
                apply MeasureTheory.isProbabilityMeasure_bind
                  (htail.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable
                filter_upwards with block
                cases block with
                | none =>
                    change IsProbabilityMeasure
                      (Measure.dirac (none : Option (ℝ × S)))
                    infer_instance
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    dsimp only [tail, someTail]
                    apply MeasureTheory.isProbabilityMeasure_bind
                      (hnextResult.comp
                        (measurable_const.prodMk measurable_id)).aemeasurable
                    filter_upwards with result
                    change IsProbabilityMeasure
                      (if result.1 then
                        balancedRetryCollectLawAux B R weight retryLimit
                          retryLimit future (total + weight result.2) mixed
                       else
                        balancedRetryCollectLawAux B R weight retryLimit
                          attempts (future + 1) total mixed)
                    cases hresult : result.1
                    · simpa only [hresult, Bool.false_eq_true, if_false] using
                        ihAttempts.2 total mixed
                    · simpa only [hresult, if_true] using
                        (ihSamples future (by omega) retryLimit).2
                          (total + weight result.2) mixed

/-- The one-sample capped proper-speedy block used by a balanced retry. -/
noncomputable def balancedAccuracyRetryBlockKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) :
    Kernel (AmbientSpace q.n) (Option (ℝ × AmbientSpace q.n)) where
  toFun current :=
    cappedProperCollectLaw
      (Arlib.MarkovChains.lazyProperProposalGaussianAux
        (accuracyPhaseTruncatedBody q I sigma2)
        (accuracyPhaseTruncatedBody_measurable q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      (accuracyImportanceWeight q I sigma2 (fun _ => 0))
      proposalCap properStride 1 current
  measurable' := by
    let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
      (accuracyPhaseTruncatedBody q I sigma2)
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
    change Measurable fun current =>
      cappedProperCollectLaw Q f proposalCap properStride 1 current
    unfold cappedProperCollectLaw
    exact (cappedProperCollectLawAux_measurable_and_probability Q
      (measurable_accuracyImportanceWeight q I sigma2 measurable_const)
      properStride proposalCap properStride 1).1.comp
        (measurable_const.prodMk measurable_id)

instance balancedAccuracyRetryBlockKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) [Fact (0 < sigma2)] :
    IsMarkovKernel
      (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride) := by
  constructor
  intro current
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux
    (accuracyPhaseTruncatedBody q I sigma2)
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
  change IsProbabilityMeasure
    (cappedProperCollectLaw Q f proposalCap properStride 1 current)
  unfold cappedProperCollectLaw
  exact (cappedProperCollectLawAux_measurable_and_probability Q
    (measurable_accuracyImportanceWeight q I sigma2 measurable_const)
    properStride proposalCap properStride 1).2 0 current

/-- Concrete probability law of the finite executable balanced collector. -/
noncomputable def balancedAccuracyRetryCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (balancedRetryCollectLawAux
    (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)
    (balancedAccuracyGaussianRejectionKernel q I sigma2)
    weight retryLimit retryLimit samples 0 current).map
      (balancedAccuracyRetryOutput q)

/-- Exact interpreter semantics of every internal balanced-retry state. -/
theorem balancedAccuracyRetryCollectAux_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples,
      (∀ total current,
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
          properStride retryLimit attempts samples total current).StronglyMeasurable
            oracle.query) ∧
      (∀ total current,
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
          properStride retryLimit attempts samples total current).runEstimate
            oracle.query =
          balancedRetryCollectLawAux
            (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
              properStride)
            (balancedAccuracyGaussianRejectionKernel q I sigma2)
            weight retryLimit attempts samples total current) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
  let R := balancedAccuracyGaussianRejectionKernel q I sigma2
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          constructor
          · intro total current
            simp only [balancedAccuracyRetryCollectAux,
              MembershipOracleProgram.StronglyMeasurable]
          · intro total current
            simp only [balancedAccuracyRetryCollectAux,
              MembershipOracleProgram.runEstimate,
              balancedRetryCollectLawAux]
      | succ future =>
          induction attempts with
          | zero =>
              constructor
              · intro total current
                simp only [balancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.StronglyMeasurable]
              · intro total current
                simp only [balancedAccuracyRetryCollectAux,
                  MembershipOracleProgram.runEstimate,
                  balancedRetryCollectLawAux]
          | succ attempts ihAttempts =>
              let next (total : ℝ) (mixed : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n → MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit retryLimit future
                    (total + weight result.2) mixed
                else
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit attempts (future + 1) total mixed
              let nextLaw (total : ℝ) (mixed : AmbientSpace q.n) :
                  Bool × AmbientSpace q.n →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
                if result.1 then
                  balancedRetryCollectLawAux B R weight retryLimit retryLimit
                    future (total + weight result.2) mixed
                else
                  balancedRetryCollectLawAux B R weight retryLimit attempts
                    (future + 1) total mixed
              have hnextStrong : ∀ total mixed result,
                  (next total mixed result).StronglyMeasurable oracle.query := by
                intro total mixed
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact ihAttempts.1 total mixed
                | true =>
                    exact (ihSamples future (by omega) retryLimit).1
                      (total + weight target) mixed
              have hnextEq : ∀ total mixed result,
                  (next total mixed result).runEstimate oracle.query =
                    nextLaw total mixed result := by
                intro total mixed
                rintro ⟨mark, target⟩
                cases mark with
                | false => exact ihAttempts.2 total mixed
                | true =>
                    exact (ihSamples future (by omega) retryLimit).2
                      (total + weight target) mixed
              have hnextLawMeasurable : ∀ total mixed,
                  Measurable (nextLaw total mixed) := by
                intro total mixed
                dsimp only [nextLaw]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · exact (balancedRetryCollectLawAux_measurable_and_probability
                    B R hweight retryLimit retryLimit future).1.comp <|
                      (measurable_const.add (hweight.comp measurable_snd)).prodMk
                        measurable_const
                · exact (balancedRetryCollectLawAux_measurable_and_probability
                    B R hweight retryLimit attempts (future + 1)).1.comp <|
                      measurable_const.prodMk measurable_const
              have hnextRun : ∀ total mixed, Measurable fun result =>
                  (next total mixed result).runEstimate oracle.query := by
                intro total mixed
                rw [show (fun result =>
                    (next total mixed result).runEstimate oracle.query) =
                  nextLaw total mixed by
                    funext result
                    exact hnextEq total mixed result]
                exact hnextLawMeasurable total mixed
              let someTail (total : ℝ) (current : AmbientSpace q.n)
                  (block : ℝ × AmbientSpace q.n) :=
                (balancedAccuracyGaussianRejectionAttempt q sigma2 block.2).bind
                  (next total block.2)
              let someTailLaw (total : ℝ) (current : AmbientSpace q.n)
                  (block : ℝ × AmbientSpace q.n) :
                  Measure (Option (ℝ × AmbientSpace q.n)) :=
                (R block.2).bind (nextLaw total block.2)
              have hsomeTailStrong : ∀ total current block,
                  (someTail total current block).StronglyMeasurable
                    oracle.query := by
                intro total current block
                exact (balancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                  q I oracle sigma2 block.2).bind
                    (hnextStrong total block.2) (hnextRun total block.2)
              have hsomeTailEq : ∀ total current block,
                  (someTail total current block).runEstimate oracle.query =
                    someTailLaw total current block := by
                intro total current block
                dsimp only [someTail, someTailLaw]
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (next total block.2)
                  (balancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
                    q I oracle sigma2 block.2)
                  (hnextStrong total block.2) (hnextRun total block.2)]
                rw [runEstimate_balancedAccuracyGaussianRejectionAttempt
                  q I oracle hsigma2 block.2]
                simp_rw [hnextEq total block.2]
                rfl
              have hsomeTailLawMeasurable : ∀ total current,
                  Measurable (someTailLaw total current) := by
                intro total current
                dsimp only [someTailLaw]
                exact measurable_measure_bind_param_variable
                  (R.measurable.comp measurable_snd)
                  (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
                  (by
                    let joint : (ℝ × AmbientSpace q.n) ×
                        (Bool × AmbientSpace q.n) →
                          Measure (Option (ℝ × AmbientSpace q.n)) := fun value =>
                      nextLaw total value.1.2 value.2
                    have hjoint : Measurable joint := by
                      dsimp only [joint, nextLaw]
                      apply Measurable.ite
                      · exact (measurable_fst.comp measurable_snd)
                          (measurableSet_singleton true)
                      · exact
                          (balancedRetryCollectLawAux_measurable_and_probability
                            B R hweight retryLimit retryLimit future).1.comp <|
                            ((measurable_const.add
                              (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                              (measurable_snd.comp measurable_fst))
                      · exact
                          (balancedRetryCollectLawAux_measurable_and_probability
                            B R hweight retryLimit attempts (future + 1)).1.comp <|
                            measurable_const.prodMk
                              (measurable_snd.comp measurable_fst)
                    exact hjoint)
              let tail (total : ℝ) (current : AmbientSpace q.n) :
                  Option (ℝ × AmbientSpace q.n) → MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun block =>
                match block with
                | none => .pure none
                | some block => someTail total current block
              let tailLaw (total : ℝ) (current : AmbientSpace q.n) :
                  Option (ℝ × AmbientSpace q.n) →
                    Measure (Option (ℝ × AmbientSpace q.n)) := fun block =>
                match block with
                | none => Measure.dirac none
                | some block => someTailLaw total current block
              have htailStrong : ∀ total current block,
                  (tail total current block).StronglyMeasurable oracle.query := by
                intro total current block
                cases block with
                | none =>
                    simp only [tail, MembershipOracleProgram.StronglyMeasurable]
                | some block => exact hsomeTailStrong total current block
              have htailEq : ∀ total current block,
                  (tail total current block).runEstimate oracle.query =
                    tailLaw total current block := by
                intro total current block
                cases block with
                | none =>
                    simp only [tail, tailLaw,
                      MembershipOracleProgram.runEstimate]
                | some block => exact hsomeTailEq total current block
              have htailLawMeasurable : ∀ total current,
                  Measurable (tailLaw total current) := by
                intro total current
                dsimp only [tailLaw]
                convert Measurable.optionElim
                  (Measure.dirac
                    (none : Option (ℝ × AmbientSpace q.n)))
                  (hsomeTailLawMeasurable total current) using 1
                ext block
                cases block <;> rfl
              have htailRun : ∀ total current, Measurable fun block =>
                  (tail total current block).runEstimate oracle.query := by
                intro total current
                rw [show (fun block =>
                    (tail total current block).runEstimate oracle.query) =
                  tailLaw total current by
                    funext block
                    exact htailEq total current block]
                exact htailLawMeasurable total current
              have htailDef : ∀ total current,
                  (fun block =>
                    match block with
                    | none => MembershipOracleProgram.pure none
                    | some (_, mixed) =>
                        (balancedAccuracyGaussianRejectionAttempt q sigma2
                          mixed).bind (next total mixed)) =
                    tail total current := by
                intro total current
                funext block
                cases block with
                | none => rfl
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    rfl
              have hblock := cappedAccuracyProperCollectWeights_semantics
                q I oracle hsigma2 (measurable_const :
                  Measurable fun _ : AmbientSpace q.n => (0 : ℝ))
                (proposalCap + 1) properStride 1
              have hsemantic : ∀ total current,
                  (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit (attempts + 1) (future + 1)
                    total current).runEstimate oracle.query =
                  balancedRetryCollectLawAux B R weight retryLimit
                    (attempts + 1) (future + 1) total current := by
                intro total current
                simp only [balancedAccuracyRetryCollectAux]
                rw [htailDef total current]
                change ((cappedAccuracyProperCollectWeights q sigma2
                  (fun _ => 0) (proposalCap + 1) properStride 1 current).bind
                    (tail total current)).runEstimate oracle.query = _
                rw [MembershipOracleProgram.runEstimate_bind oracle.query _
                  (tail total current) (hblock.2.1 current)
                  (htailStrong total current) (htailRun total current)]
                rw [cappedAccuracyProperCollectWeights_add_samples_semantics
                  q I oracle hsigma2 measurable_const proposalCap properStride 1
                    current]
                simp_rw [htailEq total current]
                change (B current).bind (tailLaw total current) = _
                rw [balancedRetryCollectLawAux]
                apply Measure.bind_congr_right
                filter_upwards with block
                cases block with
                | none => rfl
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    rfl
              constructor
              · intro total current
                simp only [balancedAccuracyRetryCollectAux]
                rw [htailDef total current]
                exact hblock.2.1 current |>.bind
                  (htailStrong total current) (htailRun total current)
              · exact hsemantic

/-- Public exact law of the finite balanced collector. -/
theorem balancedAccuracyRetryCollect_semantics
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
      retryLimit samples current).runEstimate oracle.query =
        balancedAccuracyRetryCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples current := by
  let raw := balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
    properStride retryLimit retryLimit samples 0 current
  let output : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
    fun result => .pure (balancedAccuracyRetryOutput q result)
  have hraw := balancedAccuracyRetryCollectAux_semantics q I oracle hsigma2
    hweight proposalCap properStride retryLimit retryLimit samples
  have houtputStrong : ∀ result,
      (output result).StronglyMeasurable oracle.query := by
    intro result
    trivial
  have houtputRun : Measurable fun result =>
      (output result).runEstimate oracle.query := by
    simp only [output, MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp
      (measurable_balancedAccuracyRetryOutput q)
  unfold balancedAccuracyRetryCollect balancedAccuracyRetryCollectLaw
  change (raw.bind output).runEstimate oracle.query = _
  rw [MembershipOracleProgram.runEstimate_bind oracle.query raw output
    (hraw.1 0 current) houtputStrong houtputRun]
  rw [hraw.2 0 current]
  exact Measure.bind_dirac_eq_map _ (measurable_balancedAccuracyRetryOutput q)

end ArlibCommunity.Algorithms.CV18
