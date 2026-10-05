/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance

/-!
# Approximation of finite balanced retries

This file separates cap failure from the successful payload of an optional
probability law.  It is the measure-theoretic decomposition used to compare a
capped proper-speedy block with its uncapped stationary counterpart.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

theorem MeasureLeUpTo.of_le_add
    {A : Type*} [MeasurableSpace A]
    {mu nu error : Measure A} {delta : ENNReal}
    (hle : mu ≤ nu + error) (hmass : error Set.univ ≤ delta) :
    MeasureLeUpTo mu nu delta :=
  ⟨error, hle, hmass⟩

theorem MeasureLeUpTo.map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu nu : Measure A} {delta : ENNReal} (h : MeasureLeUpTo mu nu delta)
    {f : A → B} (hf : Measurable f) :
    MeasureLeUpTo (mu.map f) (nu.map f) delta := by
  obtain ⟨error, hle, hmass⟩ := h
  refine ⟨error.map f, ?_, ?_⟩
  · calc
      mu.map f ≤ (nu + error).map f := Measure.map_mono hle hf
      _ = nu.map f + error.map f := Measure.map_add nu error hf
  · rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
    exact hmass

theorem MeasureLeUpTo.trans
    {A : Type*} [MeasurableSpace A]
    {mu nu xi : Measure A} {delta eta : ENNReal}
    (h₁ : MeasureLeUpTo mu nu delta)
    (h₂ : MeasureLeUpTo nu xi eta) :
    MeasureLeUpTo mu xi (delta + eta) := by
  obtain ⟨error₁, hle₁, hmass₁⟩ := h₁
  obtain ⟨error₂, hle₂, hmass₂⟩ := h₂
  refine ⟨error₁ + error₂, ?_, ?_⟩
  · calc
      mu ≤ nu + error₁ := hle₁
      _ ≤ (xi + error₂) + error₁ := add_le_add hle₂ le_rfl
      _ = xi + (error₁ + error₂) := by ac_rfl
  · rw [Measure.add_apply]
    exact add_le_add hmass₁ hmass₂

/-- Continuous Markov iteration is application of the corresponding kernel
power to the initial measure. -/
theorem iterate_eq_pow_bind
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (mu : Measure S) :
    ∀ t, Arlib.MarkovChains.iterate P mu t = mu.bind (P ^ t) := by
  intro t
  induction t with
  | zero =>
      simp only [Arlib.MarkovChains.iterate_zero, pow_zero]
      exact Measure.id_comp.symm
  | succ t ih =>
      rw [Arlib.MarkovChains.iterate_succ, ih, pow_succ']
      unfold Arlib.MarkovChains.step
      rw [Measure.bind_bind (P ^ t).measurable.aemeasurable
        P.measurable.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards with state
      exact (Kernel.comp_apply P (P ^ t) state).symm

theorem iterate_pow_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (mu : Measure S) (t : ℕ) :
    Arlib.MarkovChains.iterate (P ^ t) mu 1 =
      Arlib.MarkovChains.iterate P mu t := by
  rw [iterate_eq_pow_bind (P ^ t) mu 1,
    iterate_eq_pow_bind P mu t, pow_one]

noncomputable def optionSnd {S : Type*} : Option (ℝ × S) → Option S
  | none => none
  | some output => some output.2

theorem measurable_optionSnd {S : Type*} [MeasurableSpace S] :
    Measurable (optionSnd : Option (ℝ × S) → Option S) := by
  convert Measurable.optionElim none (measurable_some.comp measurable_snd) using 1
  ext value
  cases value <;> rfl

/-- The endpoint marginal of a front-recursive collector is the corresponding
ordinary Markov iterate. -/
theorem bind_frontMarkovCollectLaw_map_snd
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (samples : ℕ) (mu : Measure S) :
    (mu.bind (frontMarkovCollectLaw P f samples)).map Prod.snd =
      Arlib.MarkovChains.iterate P mu samples := by
  rw [bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap P hf samples mu]
  rw [Measure.map_map measurable_snd (by fun_prop)]
  convert Arlib.MarkovChains.markovSumLaw_map_fst P hf mu samples using 1
  ext stateSum
  rfl

/-- If the successful payload of an optional law is dominated by `nu`, then
the whole law is dominated by `nu.map some` plus precisely its failure mass
at `none`. -/
theorem optionMeasure_le_map_some_add_failure
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) (nu : Measure A)
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S) :
    L ≤ nu.map some + L {none} • Measure.dirac none := by
  apply Measure.le_iff.mpr
  intro S hS
  have hpre : MeasurableSet (some ⁻¹' S) := measurable_some hS
  have hmap : nu.map some S = nu (some ⁻¹' S) :=
    Measure.map_apply measurable_some hS
  by_cases hnone : none ∈ S
  · have hset : S = optionSomeEvent (some ⁻¹' S) ∪ {none} := by
      ext value
      cases value with
      | none => simp [hnone, optionSomeEvent]
      | some value => simp [optionSomeEvent]
    have hdisjoint : Disjoint (optionSomeEvent (some ⁻¹' S)) ({none} : Set (Option A)) := by
      rw [Set.disjoint_left]
      intro value hvalue hnoneValue
      have heq : value = none := by simpa using hnoneValue
      subst value
      simpa [optionSomeEvent] using hvalue
    have hsplit : L S = L (optionSomeEvent (some ⁻¹' S)) + L {none} := by
      calc
        L S = L (optionSomeEvent (some ⁻¹' S) ∪ {none}) := congrArg L hset
        _ = L (optionSomeEvent (some ⁻¹' S)) + L {none} :=
          measure_union hdisjoint measurableSet_option_none
    have herr : (L {none} • Measure.dirac none) S = L {none} := by
      rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
      simp [hnone]
    rw [Measure.add_apply, herr, hmap]
    rw [hsplit]
    exact add_le_add (hdom _ hpre) le_rfl
  · have hset : S = optionSomeEvent (some ⁻¹' S) := by
      ext value
      cases value with
      | none => simp [hnone, optionSomeEvent]
      | some value => simp [optionSomeEvent]
    have herr : (L {none} • Measure.dirac none) S = 0 := by
      rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
      simp [hnone]
    rw [Measure.add_apply, herr, add_zero, hmap, hset]
    exact hdom _ hpre

/-- Additive-domination form of `optionMeasure_le_map_some_add_failure`. -/
theorem optionMeasure_leUpTo_map_some
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) (nu : Measure A) {delta : ENNReal}
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S)
    (hfail : L {none} ≤ delta) :
    MeasureLeUpTo L (nu.map some) delta := by
  refine MeasureLeUpTo.of_le_add
    (optionMeasure_le_map_some_add_failure L nu hdom) ?_
  change L {none} * (Measure.dirac none) Set.univ ≤ delta
  rw [measure_univ, mul_one]
  exact hfail

/-- A capped one-sample proper block differs from its uncapped lazy-speedy
counterpart only through the explicit `none` failure outcome. -/
theorem bind_balancedAccuracyRetryBlockKernel_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
    let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
    MeasureLeUpTo
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
      ((mu.bind <| frontMarkovCollectLaw
        (P ^ properStride) f 1).map some)
      capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux K
    (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
  let L := mu.bind
    (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)
  let nu := mu.bind <| frontMarkovCollectLaw
    (P ^ properStride) f 1
  have hdom : ∀ A, MeasurableSet A → L (optionSomeEvent A) ≤ nu A := by
    intro A hA
    dsimp only [L, nu, balancedAccuracyRetryBlockKernel]
    simpa [K, delta, Q, P, f] using
      (bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
        K (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
        (measurable_accuracyImportanceWeight q I sigma2 measurable_const)
        proposalCap properStride 1 mu hA)
  exact optionMeasure_leUpTo_map_some L nu hdom (by simpa [L] using hfail)

/-- Endpoint-only form of the capped-block comparison. -/
theorem bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      ((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd)
      ((Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some)
      capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2)
  let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
  have h := bind_balancedAccuracyRetryBlockKernel_leUpTo_uncapped
    q I hsigma2 proposalCap properStride mu hfail
  have hmap := h.map (measurable_optionSnd (S := AmbientSpace q.n))
  have hendpoint :
      (mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map Prod.snd =
        Arlib.MarkovChains.iterate (P ^ properStride) mu 1 :=
    bind_frontMarkovCollectLaw_map_snd (P ^ properStride)
      (measurable_accuracyImportanceWeight q I sigma2 measurable_const) 1 mu
  have hnu :
      ((mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map some).map
          optionSnd =
        (Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some := by
    rw [Measure.map_map measurable_optionSnd measurable_some]
    rw [show (optionSnd ∘ some : ℝ × AmbientSpace q.n →
          Option (AmbientSpace q.n)) = some ∘ Prod.snd by
      funext output
      rfl]
    rw [← Measure.map_map measurable_some measurable_snd, hendpoint]
  rw [hnu] at hmap
  exact hmap

/-- Adding the speedy mixing error to the cap failure gives a stationary
endpoint comparison for one proper block. -/
theorem bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    {capError mixError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride)
      pi mixError) :
    MeasureLeUpTo
      ((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd)
      (pi.map some) (capError + mixError) := by
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2)
  have hcap :=
    bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
      q I hsigma2 proposalCap properStride mu hfail
  dsimp only at hcap
  rw [iterate_pow_one P mu properStride] at hcap
  have hmixSome : Arlib.TVLe
      ((Arlib.MarkovChains.iterate P mu properStride).map some)
      (pi.map some) mixError := hmix.map measurable_some
  exact hcap.trans (MeasureLeUpTo.of_tvLe hmixSome)

/-- Lift a probability kernel through `Option`, preserving `none` as an
absorbing failure outcome. -/
noncomputable def optionKernel
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) : Option S → Measure (Option T)
  | none => Measure.dirac none
  | some state => (R state).map some

theorem measurable_optionKernel
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) [IsMarkovKernel R] : Measurable (optionKernel R) := by
  have hsome : Measurable fun state => (R state).map some := by
    exact measurable_measure_map_param_variable R.measurable
      (fun state => IsMarkovKernel.isProbabilityMeasure state)
      (measurable_some.comp measurable_snd)
  convert Measurable.optionElim (Measure.dirac none) hsome using 1
  ext value
  cases value <;> rfl

instance optionKernel_isProbabilityMeasure
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) [IsMarkovKernel R] (state : Option S) :
    IsProbabilityMeasure (optionKernel R state) := by
  cases state with
  | none =>
      change IsProbabilityMeasure (Measure.dirac (none : Option T))
      infer_instance
  | some state =>
      dsimp only [optionKernel]
      let _ : IsProbabilityMeasure (R state) :=
        IsMarkovKernel.isProbabilityMeasure state
      exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

/-- One balanced KLS observation after a capped mixing block inherits the
same additive error. -/
theorem bind_balancedAccuracyRetryBlockKernel_trial_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    {capError mixError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride)
      pi mixError) :
    let R := balancedAccuracyGaussianRejectionKernel q I sigma2
    MeasureLeUpTo
      (((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd).bind (optionKernel R))
      ((pi.map some).bind (optionKernel R)) (capError + mixError) := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  apply MeasureLeUpTo.bind_same
    (bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
      q I hsigma2 proposalCap properStride mu pi hfail hmix)
    (measurable_optionKernel
      (balancedAccuracyGaussianRejectionKernel q I sigma2))
  intro state
  exact optionKernel_isProbabilityMeasure
    (balancedAccuracyGaussianRejectionKernel q I sigma2) state

/-- Recover the retained speedy state from either outcome of the executable
balanced rejection kernel. -/
noncomputable def balancedRetryRecover (q : VolumeParams) :
    Bool × AmbientSpace q.n → Bool × AmbientSpace q.n := fun result =>
  (result.1, accuracyScaleFactor q • result.2)

theorem measurable_balancedRetryRecover (q : VolumeParams) :
    Measurable (balancedRetryRecover q) := by
  exact measurable_fst.prodMk <|
    (measurable_const : Measurable fun _ : Bool × AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_snd

/-- Equivalent balanced decision law that returns the unscaled speedy state
on both branches. -/
noncomputable def balancedAccuracyDecisionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : Measure (Bool × AmbientSpace q.n) :=
  let accept := balancedAccuracyGaussianAcceptance q I sigma2 current
  accept • Measure.dirac (true, current) +
    (1 - accept) • Measure.dirac (false, current)

theorem measurable_balancedAccuracyDecisionLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (balancedAccuracyDecisionLaw q I sigma2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [balancedAccuracyDecisionLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  have htrue : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal) (true, current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk measurable_id)
  have hfalse : Measurable fun current : AmbientSpace q.n =>
      S.indicator (1 : Bool × AmbientSpace q.n → ENNReal) (false, current) :=
    (measurable_one.indicator hS).comp (measurable_const.prodMk measurable_id)
  have hacc := measurable_balancedAccuracyGaussianAcceptance q I sigma2
  exact (hacc.mul htrue).add ((measurable_const.sub hacc).mul hfalse)

noncomputable def balancedAccuracyDecisionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Kernel (AmbientSpace q.n) (Bool × AmbientSpace q.n) :=
  ⟨balancedAccuracyDecisionLaw q I sigma2,
    measurable_balancedAccuracyDecisionLaw q I sigma2⟩

instance balancedAccuracyDecisionKernel_isMarkovKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    [Fact (0 < sigma2)] :
    IsMarkovKernel (balancedAccuracyDecisionKernel q I sigma2) := by
  constructor
  intro current
  change IsProbabilityMeasure
    (balancedAccuracyDecisionLaw q I sigma2 current)
  constructor
  simp only [balancedAccuracyDecisionLaw,
    Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le]
  exact (balancedAccuracyGaussianAcceptance_le_half q I Fact.out current).trans
    (by norm_num)

theorem balancedAccuracyGaussianRejectionKernel_map_recover
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    (balancedAccuracyGaussianRejectionKernel q I sigma2 current).map
        (balancedRetryRecover q) =
      balancedAccuracyDecisionKernel q I sigma2 current := by
  have hc0 : accuracyScaleFactor q ≠ 0 := (accuracyScaleFactor_pos q).ne'
  have hrecover : Measurable (balancedRetryRecover q) :=
    measurable_balancedRetryRecover q
  change (balancedAccuracyGaussianRejectionLaw q I sigma2 current).map
      (balancedRetryRecover q) =
    balancedAccuracyDecisionLaw q I sigma2 current
  unfold balancedAccuracyGaussianRejectionLaw balancedAccuracyDecisionLaw
  rw [Measure.map_add _ _ hrecover, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hrecover, Measure.map_dirac' hrecover]
  have hcancel : accuracyScaleFactor q •
      ((accuracyScaleFactor q)⁻¹ • current) = current := by
    rw [← mul_smul, mul_inv_cancel₀ hc0, one_smul]
  change balancedAccuracyGaussianAcceptance q I sigma2 current •
        Measure.dirac (true, accuracyScaleFactor q •
          ((accuracyScaleFactor q)⁻¹ • current)) +
      (1 - balancedAccuracyGaussianAcceptance q I sigma2 current) •
        Measure.dirac (false, accuracyScaleFactor q •
          ((accuracyScaleFactor q)⁻¹ • current)) = _
  rw [hcancel]

/-- Both atoms of the balanced rejection law carry the same transformed
point. -/
theorem balancedAccuracyGaussianRejectionLaw_ae_snd
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    ∀ᵐ result ∂balancedAccuracyGaussianRejectionLaw q I sigma2 current,
      result.2 = (accuracyScaleFactor q)⁻¹ • current := by
  unfold balancedAccuracyGaussianRejectionLaw
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (ae_eq_dirac Prod.snd) _
  · exact Measure.ae_smul_measure (ae_eq_dirac Prod.snd) _

/-- Endpoint law of a single finite balanced transition.  On success it
returns the scaled Gaussian target; on rejection it retries from the retained
unscaled speedy state. -/
noncomputable def balancedAccuracyTransitionLawAux
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ) :
    ℕ → AmbientSpace q.n → Measure (Option (AmbientSpace q.n))
  | 0, _ => Measure.dirac none
  | attempts + 1, current =>
      (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
        current).bind fun block =>
        match block with
        | none => Measure.dirac none
        | some (_, mixed) =>
            (balancedAccuracyGaussianRejectionKernel q I sigma2 mixed).bind
              fun result =>
                if result.1 then Measure.dirac (some result.2)
                else balancedAccuracyTransitionLawAux q I sigma2 proposalCap
                  properStride attempts mixed

theorem balancedAccuracyTransitionLawAux_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) :
    ∀ attempts,
      Measurable (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride attempts) ∧
      ∀ current, IsProbabilityMeasure
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
          attempts current) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
  let R := balancedAccuracyGaussianRejectionKernel q I sigma2
  intro attempts
  induction attempts with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp measurable_const
      · intro current
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
  | succ attempts ih =>
      let nextResult : AmbientSpace q.n ×
          (Bool × AmbientSpace q.n) →
            Measure (Option (AmbientSpace q.n)) := fun value =>
        if value.2.1 then Measure.dirac (some value.2.2)
        else balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride attempts value.1
      have hnextResult : Measurable nextResult := by
        dsimp only [nextResult]
        apply Measurable.ite
        · exact (measurable_fst.comp measurable_snd)
            (measurableSet_singleton true)
        · exact Measure.measurable_dirac.comp <|
            measurable_some.comp (measurable_snd.comp measurable_snd)
        · exact ih.1.comp measurable_fst
      let someTail : ℝ × AmbientSpace q.n →
          Measure (Option (AmbientSpace q.n)) := fun block =>
        (R block.2).bind fun result => nextResult (block.2, result)
      have hsomeTail : Measurable someTail := by
        dsimp only [someTail]
        exact measurable_measure_bind_param_variable
          (R.measurable.comp measurable_snd)
          (fun block => IsMarkovKernel.isProbabilityMeasure block.2)
          (hnextResult.comp <|
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      let tail : Option (ℝ × AmbientSpace q.n) →
          Measure (Option (AmbientSpace q.n)) := fun block =>
        match block with
        | none => Measure.dirac none
        | some block => someTail block
      have htail : Measurable tail := by
        dsimp only [tail]
        convert Measurable.optionElim (Measure.dirac none) hsomeTail using 1
        ext block
        cases block <;> rfl
      have hlaw :
          balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
              (attempts + 1) =
            fun current => (B current).bind tail := by
        funext current
        simp only [balancedAccuracyTransitionLawAux]
        apply Measure.bind_congr_right
        filter_upwards with block
        cases block with
        | none => rfl
        | some block =>
            rcases block with ⟨ignored, mixed⟩
            dsimp only [tail, someTail]
      constructor
      · rw [hlaw]
        exact measurable_measure_bind_param_variable B.measurable
          (fun current => IsMarkovKernel.isProbabilityMeasure current)
          (htail.comp measurable_snd)
      · intro current
        rw [congrFun hlaw current]
        apply MeasureTheory.isProbabilityMeasure_bind htail.aemeasurable
        filter_upwards with block
        cases block with
        | none =>
            change IsProbabilityMeasure
              (Measure.dirac (none : Option (AmbientSpace q.n)))
            infer_instance
        | some block =>
            rcases block with ⟨ignored, mixed⟩
            dsimp only [tail, someTail]
            apply MeasureTheory.isProbabilityMeasure_bind
              (hnextResult.comp
                (measurable_const.prodMk measurable_id)).aemeasurable
            filter_upwards with result
            change IsProbabilityMeasure
              (if result.1 then Measure.dirac (some result.2)
               else balancedAccuracyTransitionLawAux q I sigma2 proposalCap
                properStride attempts mixed)
            cases hresult : result.1
            · simpa only [hresult, Bool.false_eq_true, if_false] using ih.2 mixed
            · simp only [hresult, if_true]
              infer_instance

/-- Mapping before a measurable continuation is the same as composing the
continuation with the map.  This small Giry-monad identity is convenient for
recovering the retained speedy point from the executable KLS output. -/
theorem Measure.map_bind_eq_bind_comp
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (mu : Measure A) {f : A → B} (hf : Measurable f)
    {G : B → Measure C} (hG : Measurable G) :
    (mu.map f).bind G = mu.bind (fun x => G (f x)) := by
  calc
    (mu.map f).bind G =
        (mu.bind fun x => Measure.dirac (f x)).bind G := by
      rw [Measure.bind_dirac_eq_map mu hf]
    _ = mu.bind fun x => (Measure.dirac (f x)).bind G :=
      Measure.bind_bind
        (Measure.measurable_dirac.comp hf).aemeasurable hG.aemeasurable
    _ = mu.bind (fun x => G (f x)) := by
      apply Measure.bind_congr_right
      filter_upwards with x
      exact Measure.dirac_bind hG (f x)

/-- Continuation after a recovered balanced decision: an accepted speedy
point is converted to its Gaussian target, while a rejected point consumes
one retry. -/
noncomputable def balancedAccuracyTransitionDecisionTail
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride attempts : ℕ) :
    Bool × AmbientSpace q.n → Measure (Option (AmbientSpace q.n)) :=
  fun result =>
    if result.1 then
      Measure.dirac (some ((accuracyScaleFactor q)⁻¹ • result.2))
    else
      balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
        attempts result.2

theorem balancedAccuracyTransitionDecisionTail_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) :
    Measurable (balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
      properStride attempts) ∧
    ∀ result, IsProbabilityMeasure
      (balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
        properStride attempts result) := by
  let E := balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
  have hE := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride attempts
  constructor
  · unfold balancedAccuracyTransitionDecisionTail
    apply Measurable.ite
    · exact measurable_fst (measurableSet_singleton true)
    · exact Measure.measurable_dirac.comp <|
        measurable_some.comp <|
          (measurable_const : Measurable fun _ : Bool × AmbientSpace q.n =>
            (accuracyScaleFactor q)⁻¹).smul measurable_snd
    · exact hE.1.comp measurable_snd
  · intro result
    unfold balancedAccuracyTransitionDecisionTail
    split
    · infer_instance
    · exact hE.2 result.2

/-- Preserve a failed block and otherwise apply the recovered balanced
decision continuation. -/
noncomputable def balancedAccuracyTransitionOptionTail
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride attempts : ℕ) :
    Option (Bool × AmbientSpace q.n) →
      Measure (Option (AmbientSpace q.n))
  | none => Measure.dirac none
  | some result => balancedAccuracyTransitionDecisionTail q I sigma2
      proposalCap properStride attempts result

theorem balancedAccuracyTransitionOptionTail_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ) :
    Measurable (balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
      properStride attempts) ∧
    ∀ result, IsProbabilityMeasure
      (balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
        properStride attempts result) := by
  have htail :=
    balancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts
  constructor
  · convert Measurable.optionElim
      (Measure.dirac (none : Option (AmbientSpace q.n))) htail.1 using 1
    ext result
    cases result <;> rfl
  · intro result
    cases result with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
    | some result => exact htail.2 result

/-- Exact recovered-decision form of the finite transition recursion. -/
theorem balancedAccuracyTransitionLawAux_succ_eq_recovered
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (current : AmbientSpace q.n) :
    balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
        (attempts + 1) current =
      (((balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
          current).map optionSnd).bind
        (optionKernel (balancedAccuracyDecisionKernel q I sigma2))).bind
          (balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
            properStride attempts) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
  let R := balancedAccuracyGaussianRejectionKernel q I sigma2
  let D := balancedAccuracyDecisionKernel q I sigma2
  let T := balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
    properStride attempts
  let OT := balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
    properStride attempts
  have hT :=
    (balancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hOT :=
    (balancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hoptionR := measurable_optionKernel R
  have hoptionD := measurable_optionKernel D
  have hpipeline :
      (((B current).map optionSnd).bind (optionKernel D)).bind OT =
        (B current).bind fun block =>
          (optionKernel D (optionSnd block)).bind OT := by
    calc
      (((B current).map optionSnd).bind (optionKernel D)).bind OT =
          ((B current).map optionSnd).bind fun state =>
            (optionKernel D state).bind OT :=
        Measure.bind_bind hoptionD.aemeasurable hOT.aemeasurable
      _ = (B current).bind fun block =>
          (optionKernel D (optionSnd block)).bind OT :=
        Measure.map_bind_eq_bind_comp (B current) measurable_optionSnd <|
          measurable_measure_bind_param_variable hoptionD
            (fun state => optionKernel_isProbabilityMeasure D state)
            (hOT.comp measurable_snd)
  rw [hpipeline]
  simp only [balancedAccuracyTransitionLawAux]
  apply Measure.bind_congr_right
  filter_upwards with block
  cases block with
  | none =>
      dsimp only [optionSnd, optionKernel]
      rw [Measure.dirac_bind hOT]
      rfl
  | some block =>
      rcases block with ⟨ignored, mixed⟩
      dsimp only [optionSnd, optionKernel]
      rw [Measure.map_bind_eq_bind_comp (D mixed) measurable_some hOT]
      calc
        (R mixed).bind (fun result =>
              if result.1 then Measure.dirac (some result.2)
              else balancedAccuracyTransitionLawAux q I sigma2 proposalCap
                properStride attempts mixed) =
            (R mixed).bind (fun result => T (balancedRetryRecover q result)) := by
          have hsecond : ∀ᵐ result ∂R mixed,
              result.2 = (accuracyScaleFactor q)⁻¹ • mixed := by
            exact balancedAccuracyGaussianRejectionLaw_ae_snd
              q I sigma2 mixed
          apply Measure.bind_congr_right
          filter_upwards [hsecond] with result hsecondResult
          unfold balancedRetryRecover T
            balancedAccuracyTransitionDecisionTail
          by_cases hresult : result.1 = true
          · simp only [hresult, if_true]
            have hc0 : accuracyScaleFactor q ≠ 0 :=
              (accuracyScaleFactor_pos q).ne'
            congr 2
            rw [← mul_smul, inv_mul_cancel₀ hc0, one_smul]
          · have hfalse : result.1 = false :=
              Bool.eq_false_of_not_eq_true hresult
            simp only [hfalse, Bool.false_eq_true, if_false]
            have hc0 : accuracyScaleFactor q ≠ 0 :=
              (accuracyScaleFactor_pos q).ne'
            congr 1
            rw [hsecondResult, ← mul_smul, mul_inv_cancel₀ hc0, one_smul]
        _ = ((R mixed).map (balancedRetryRecover q)).bind T :=
          (Measure.map_bind_eq_bind_comp (R mixed)
            (measurable_balancedRetryRecover q) hT).symm
        _ = (D mixed).bind T := by
          rw [balancedAccuracyGaussianRejectionKernel_map_recover]
        _ = (D mixed).bind (fun result => OT (some result)) := by
          apply Measure.bind_congr_right
          filter_upwards with result
          rfl

/-- Binding a pointwise sum is linear in the output kernel. -/
theorem measure_bind_add_right
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) {K L : A → Measure B}
  (hK : Measurable K) (hL : Measurable L) :
    mu.bind (fun x => K x + L x) = mu.bind K + mu.bind L := by
  ext S hS
  rw [Measure.bind_apply (m := mu) (f := fun x => K x + L x)
    hS (hK.add hL).aemeasurable]
  rw [Measure.add_apply,
    Measure.bind_apply hS hK.aemeasurable,
    Measure.bind_apply hS hL.aemeasurable]
  simp_rw [Measure.add_apply]
  exact lintegral_add_left ((Measure.measurable_coe hS).comp hK) _

/-- A bind into weighted point masses is a density change followed by a
measurable map. -/
theorem bind_smul_dirac_eq_withDensity_map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) {weight : A → ENNReal} (hweight : Measurable weight)
    {f : A → B} (hf : Measurable f) :
    mu.bind (fun x => weight x • Measure.dirac (f x)) =
      (mu.withDensity weight).map f := by
  have hkernel : Measurable fun x => weight x • Measure.dirac (f x) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hS]
    exact hweight.mul <| (measurable_one.indicator hS).comp hf
  ext S hS
  rw [Measure.bind_apply hS hkernel.aemeasurable,
    Measure.map_apply hf hS,
    withDensity_apply _ (hf hS)]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hS]
  rw [← lintegral_indicator (hf hS)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ S
  · simp [hx, Set.indicator_of_mem]
  · simp [hx, Set.indicator_of_notMem]

/-- The stationary balanced decision law is exactly the sum of its accepted
and rejected current-state submeasures. -/
theorem bind_balancedAccuracyDecisionKernel_eq_branches
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    mu.bind (balancedAccuracyDecisionKernel q I sigma2) =
      (balancedAcceptedStateMeasure q I sigma2 mu).map
          (fun x => (true, x)) +
        (balancedRejectedStateMeasure q I sigma2 mu).map
          (fun x => (false, x)) := by
  let accept := balancedAccuracyGaussianAcceptance q I sigma2
  let truePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (true, x)
  let falsePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (false, x)
  have haccept : Measurable accept :=
    measurable_balancedAccuracyGaussianAcceptance q I sigma2
  have hreject : Measurable fun x => 1 - accept x :=
    measurable_const.sub haccept
  have htrue : Measurable truePoint := measurable_const.prodMk measurable_id
  have hfalse : Measurable falsePoint := measurable_const.prodMk measurable_id
  have hKtrue : Measurable fun x =>
      accept x • Measure.dirac (truePoint x) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hS]
    exact haccept.mul <| (measurable_one.indicator hS).comp htrue
  have hKfalse : Measurable fun x =>
      (1 - accept x) • Measure.dirac (falsePoint x) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hS]
    exact hreject.mul <| (measurable_one.indicator hS).comp hfalse
  change mu.bind (fun x =>
      accept x • Measure.dirac (truePoint x) +
        (1 - accept x) • Measure.dirac (falsePoint x)) = _
  rw [measure_bind_add_right mu hKtrue hKfalse]
  rw [bind_smul_dirac_eq_withDensity_map mu haccept htrue,
    bind_smul_dirac_eq_withDensity_map mu hreject hfalse]
  rfl

/-- At stationarity, one recovered decision followed by the finite-retry
continuation is the accepted target submeasure plus the rejected branch
recursion. -/
theorem bind_stationaryDecision_transitionTail_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (pi : Measure (AmbientSpace q.n)) :
    (pi.bind (balancedAccuracyDecisionKernel q I sigma2)).bind
        (balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
          properStride attempts) =
      ((balancedAcceptedStateMeasure q I sigma2 pi).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some +
        (balancedRejectedStateMeasure q I sigma2 pi).bind
          (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts) := by
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let rejected := balancedRejectedStateMeasure q I sigma2 pi
  let truePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (true, x)
  let falsePoint : AmbientSpace q.n → Bool × AmbientSpace q.n :=
    fun x => (false, x)
  let T := balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
    properStride attempts
  let E := balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
    attempts
  have hT :=
    (balancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hE :=
    (balancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have htrue : Measurable truePoint := measurable_const.prodMk measurable_id
  have hfalse : Measurable falsePoint := measurable_const.prodMk measurable_id
  rw [bind_balancedAccuracyDecisionKernel_eq_branches]
  rw [measure_bind_add_left _ _ hT]
  rw [Measure.map_bind_eq_bind_comp accepted htrue hT,
    Measure.map_bind_eq_bind_comp rejected hfalse hT]
  have haccept : accepted.bind (fun x => T (truePoint x)) =
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some := by
    change accepted.bind (fun x =>
        Measure.dirac (some ((accuracyScaleFactor q)⁻¹ • x))) = _
    rw [Measure.bind_dirac_eq_map]
    · rw [Measure.map_map]
      · rfl
      · exact measurable_some
      · exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          (accuracyScaleFactor q)⁻¹).smul measurable_id
    · exact measurable_some.comp <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hrejected : rejected.bind (fun x => T (falsePoint x)) =
      rejected.bind E := by
    apply Measure.bind_congr_right
    filter_upwards with x
    rfl
  rw [haccept, hrejected]

/-- The `Option`-lifted stationary pipeline has the same law as applying the
decision kernel directly and then its non-optional continuation. -/
theorem bind_stationaryOptionDecision_transitionTail_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (pi : Measure (AmbientSpace q.n)) :
    (((pi.map some).bind
        (optionKernel (balancedAccuracyDecisionKernel q I sigma2))).bind
      (balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
        properStride attempts)) =
      (pi.bind (balancedAccuracyDecisionKernel q I sigma2)).bind
        (balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
          properStride attempts) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let D := balancedAccuracyDecisionKernel q I sigma2
  let T := balancedAccuracyTransitionDecisionTail q I sigma2 proposalCap
    properStride attempts
  let OT := balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
    properStride attempts
  have hD := D.measurable
  have hOD := measurable_optionKernel D
  have hT :=
    (balancedAccuracyTransitionDecisionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  have hOT :=
    (balancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  calc
    (((pi.map some).bind (optionKernel D)).bind OT) =
        (pi.map some).bind fun state => (optionKernel D state).bind OT :=
      Measure.bind_bind hOD.aemeasurable hOT.aemeasurable
    _ = pi.bind (fun x => (optionKernel D (some x)).bind OT) :=
      Measure.map_bind_eq_bind_comp pi measurable_some <|
        measurable_measure_bind_param_variable hOD
          (fun state => optionKernel_isProbabilityMeasure D state)
          (hOT.comp measurable_snd)
    _ = pi.bind (fun x => (D x).bind T) := by
      apply Measure.bind_congr_right
      filter_upwards with x
      dsimp only [optionKernel]
      rw [Measure.map_bind_eq_bind_comp (D x) measurable_some hOT]
      apply Measure.bind_congr_right
      filter_upwards with result
      rfl
    _ = (pi.bind D).bind T :=
      (Measure.bind_bind hD.aemeasurable hT.aemeasurable).symm

/-- Integrated recovered-recursion identity. -/
theorem bind_balancedAccuracyTransitionLawAux_succ_eq_pipeline
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) :
    rho.bind (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride (attempts + 1)) =
      ((((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd).bind
          (optionKernel (balancedAccuracyDecisionKernel q I sigma2))).bind
        (balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
          properStride attempts)) := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let B := balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride
  let D := balancedAccuracyDecisionKernel q I sigma2
  let OT := balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
    properStride attempts
  have hB := B.measurable
  have hOD := measurable_optionKernel D
  have hOT :=
    (balancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
  let BM : AmbientSpace q.n → Measure (Option (AmbientSpace q.n)) :=
    fun current => (B current).map optionSnd
  have hBM : Measurable BM := by
    exact measurable_measure_map_param_variable hB
      (fun current => IsMarkovKernel.isProbabilityMeasure current)
      (measurable_optionSnd.comp measurable_snd)
  have hBMprob : ∀ current, IsProbabilityMeasure (BM current) := by
    intro current
    dsimp only [BM]
    exact Measure.isProbabilityMeasure_map measurable_optionSnd.aemeasurable
  let BD : AmbientSpace q.n → Measure (Option (Bool × AmbientSpace q.n)) :=
    fun current => (BM current).bind (optionKernel D)
  have hBD : Measurable BD := by
    exact measurable_measure_bind_param_variable hBM hBMprob
      (hOD.comp measurable_snd)
  have hendpoint : rho.bind BM = (rho.bind B).map optionSnd := by
    calc
      rho.bind BM = rho.bind (fun current =>
          (B current).bind fun block => Measure.dirac (optionSnd block)) := by
        apply Measure.bind_congr_right
        filter_upwards with current
        dsimp only [BM]
        rw [Measure.bind_dirac_eq_map]
        exact measurable_optionSnd
      _ = (rho.bind B).bind (fun block => Measure.dirac (optionSnd block)) :=
        (Measure.bind_bind hB.aemeasurable
          (Measure.measurable_dirac.comp measurable_optionSnd).aemeasurable).symm
      _ = (rho.bind B).map optionSnd :=
        Measure.bind_dirac_eq_map _ measurable_optionSnd
  have hpoint : rho.bind
      (balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
        (attempts + 1)) =
      rho.bind (fun current =>
        ((((B current).map optionSnd).bind (optionKernel D)).bind OT)) := by
    apply Measure.bind_congr_right
    filter_upwards with current
    exact balancedAccuracyTransitionLawAux_succ_eq_recovered
      q I hsigma2 proposalCap properStride attempts current
  rw [hpoint]
  calc
    rho.bind (fun current =>
        ((((B current).map optionSnd).bind (optionKernel D)).bind OT)) =
      (rho.bind BD).bind OT := by
        change rho.bind (fun current => (BD current).bind OT) = _
        exact (Measure.bind_bind hBD.aemeasurable hOT.aemeasurable).symm
    _ = ((rho.bind BM).bind (optionKernel D)).bind OT := by
      rw [Measure.bind_bind hBM.aemeasurable hOD.aemeasurable]
    _ = ((((rho.bind B).map optionSnd).bind (optionKernel D)).bind OT) := by
      rw [hendpoint]

/-- One finite retry, including its capped block, is dominated by the exact
stationary accepted/rejected recurrence with the same additive block error. -/
theorem bind_balancedAccuracyTransitionLawAux_succ_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    {delta : ENNReal}
    (hblock : MeasureLeUpTo
      ((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) delta) :
    MeasureLeUpTo
      (rho.bind (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride (attempts + 1)))
      (((balancedAcceptedStateMeasure q I sigma2 pi).map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some +
        (balancedRejectedStateMeasure q I sigma2 pi).bind
          (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts)) delta := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let D := balancedAccuracyDecisionKernel q I sigma2
  let OT := balancedAccuracyTransitionOptionTail q I sigma2 proposalCap
    properStride attempts
  have hfirst := hblock.bind_same (measurable_optionKernel D)
    (fun state => optionKernel_isProbabilityMeasure D state)
  have hsecond := hfirst.bind_same
    (balancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).1
    (balancedAccuracyTransitionOptionTail_measurable_and_probability
      q I hsigma2 proposalCap properStride attempts).2
  rw [← bind_balancedAccuracyTransitionLawAux_succ_eq_pipeline
    q I hsigma2 proposalCap properStride attempts rho] at hsecond
  rw [bind_stationaryOptionDecision_transitionTail_eq
    q I hsigma2 proposalCap properStride attempts pi] at hsecond
  rw [bind_stationaryDecision_transitionTail_eq
    q I hsigma2 proposalCap properStride attempts pi] at hsecond
  exact hsecond

/-- Additive domination is preserved by scaling both measures. -/
theorem MeasureLeUpTo.smul
    {A : Type*} [MeasurableSpace A]
    {mu nu : Measure A} {delta c : ENNReal}
    (h : MeasureLeUpTo mu nu delta) :
    MeasureLeUpTo (c • mu) (c • nu) (c * delta) := by
  obtain ⟨error, hle, hmass⟩ := h
  refine ⟨c • error, ?_, ?_⟩
  · apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.smul_apply, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply]
    change c * mu S ≤ c * nu S + c * error S
    rw [← mul_add]
    exact mul_le_mul' le_rfl (Measure.le_iff.mp hle S hS)
  · rw [Measure.smul_apply]
    exact mul_le_mul' le_rfl hmass

/-- Adding an identical measure to both sides preserves additive
domination. -/
theorem MeasureLeUpTo.add_left
    {A : Type*} [MeasurableSpace A]
    {mu nu : Measure A} {delta : ENNReal}
    (xi : Measure A) (h : MeasureLeUpTo mu nu delta) :
    MeasureLeUpTo (xi + mu) (xi + nu) delta := by
  obtain ⟨error, hle, hmass⟩ := h
  refine ⟨error, ?_, hmass⟩
  calc
    xi + mu ≤ xi + (nu + error) := add_le_add le_rfl hle
    _ = (xi + nu) + error := by ac_rfl

/-- A finite nonzero measure is its mass times its normalization on the
whole space. -/
theorem measure_eq_mass_smul_condOn_univ
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    (h0 : mu Set.univ ≠ 0) (htop : mu Set.univ ≠ ⊤) :
    mu = mu Set.univ • Arlib.condOn mu Set.univ := by
  rw [Arlib.condOn_def, Measure.restrict_univ, smul_smul,
    ENNReal.mul_inv_cancel h0 htop, one_smul]

/-- Accepted and rejected stationary current-state masses sum to one. -/
theorem balancedAcceptedRejected_mass_add_eq_one
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi] :
    balancedAcceptedStateMeasure q I sigma2 pi Set.univ +
      balancedRejectedStateMeasure q I sigma2 pi Set.univ = 1 := by
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let D := balancedAccuracyDecisionKernel q I sigma2
  have hmass := congrArg (fun mu : Measure (Bool × AmbientSpace q.n) =>
      mu Set.univ)
    (bind_balancedAccuracyDecisionKernel_eq_branches q I sigma2 pi)
  rw [measure_bind_apply_univ pi D.measurable
    (fun x => IsMarkovKernel.isProbabilityMeasure x)] at hmass
  have htrue : Measurable fun x : AmbientSpace q.n => (true, x) :=
    measurable_const.prodMk measurable_id
  have hfalse : Measurable fun x : AmbientSpace q.n => (false, x) :=
    measurable_const.prodMk measurable_id
  rw [Measure.add_apply,
    Measure.map_apply htrue MeasurableSet.univ,
    Measure.map_apply hfalse MeasurableSet.univ,
    Set.preimage_univ, Set.preimage_univ] at hmass
  simpa only [measure_univ] using hmass.symm

/-- The unnormalized accepted target branch is its acceptance mass times the
normalized balanced accepted-target law. -/
theorem balancedAcceptedTargetSubmeasure_eq_mass_smul
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    let accepted := balancedAcceptedStateMeasure q I sigma2 pi
    let acceptedTarget := accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)
    acceptedTarget = accepted Set.univ •
      balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi := by
  dsimp only
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let acceptedTarget := accepted.map scale
  have hscale : Measurable scale := by
    dsimp only [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 128 : ℝ)).trans_le
      (by simpa [accepted] using hacceptedLower)
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    have hle := balancedAcceptedStateMeasure_le_half_smul q I hsigma2 pi
    exact ne_top_of_le_ne_top (by simp) <|
      Measure.le_iff'.mp hle Set.univ
  have htargetMass : acceptedTarget Set.univ = accepted Set.univ := by
    dsimp only [acceptedTarget]
    rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
  have htarget0 : acceptedTarget Set.univ ≠ 0 := by
    rw [htargetMass]
    exact haccepted0
  have htargetTop : acceptedTarget Set.univ ≠ ⊤ := by
    rw [htargetMass]
    exact hacceptedTop
  have hnormalize := measure_eq_mass_smul_condOn_univ acceptedTarget
    htarget0 htargetTop
  change acceptedTarget = accepted Set.univ •
    Arlib.condOn acceptedTarget Set.univ
  rw [← htargetMass]
  exact hnormalize

/-- Recursive additive error for balanced retries.  The base value `1` is
the certain failure when no attempts remain. -/
noncomputable def balancedRetryError (delta rejectMass : ENNReal) : ℕ → ENNReal
  | 0 => 1
  | attempts + 1 => delta + rejectMass *
      balancedRetryError delta rejectMass attempts

/-- Starting from the normalized stationary rejection branch, finite
balanced retries are dominated by the normalized accepted target.  The
recursive error records both block approximation and exhausting every
attempt. -/
theorem bind_balancedRejectedTransition_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {delta : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hblock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) delta) :
    let rejected := balancedRejectedStateMeasure q I sigma2 pi
    let rejectMass := rejected Set.univ
    let rejectedProb := Arlib.condOn rejected Set.univ
    ∀ attempts,
      MeasureLeUpTo
        (rejectedProb.bind
          (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride attempts))
        ((balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map some)
        (balancedRetryError delta rejectMass attempts) := by
  dsimp only
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let rejected := balancedRejectedStateMeasure q I sigma2 pi
  let acceptMass := accepted Set.univ
  let rejectMass := rejected Set.univ
  let rejectedProb := Arlib.condOn rejected Set.univ
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  let E := balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
  have hrejected0 : rejectMass ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le
      (by simpa [rejectMass, rejected] using hrejectedLower)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass, accepted, rejected] using
      balancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
  have hacceptedTarget :
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some =
        acceptMass • targetSome := by
    have hbase := balancedAcceptedTargetSubmeasure_eq_mass_smul
      q I hsigma2 pi hacceptedLower
    change (accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some = _
    rw [hbase, Measure.map_smul]
  have hrejectedNormalize : rejected = rejectMass • rejectedProb := by
    exact measure_eq_mass_smul_condOn_univ rejected hrejected0 hrejectedTop
  intro attempts
  induction attempts with
  | zero =>
      change MeasureLeUpTo
        (rejectedProb.bind fun _ =>
          Measure.dirac (none : Option (AmbientSpace q.n))) targetSome 1
      rw [Measure.bind_const, measure_univ, one_smul]
      refine ⟨Measure.dirac none, ?_, by simp⟩
      apply Measure.le_iff.mpr
      intro S hS
      rw [Measure.add_apply]
      exact le_add_left le_rfl
  | succ attempts ih =>
      have hone :=
        bind_balancedAccuracyTransitionLawAux_succ_leUpTo_stationary
          q I hsigma2 proposalCap properStride attempts rejectedProb pi hblock
      have hscaled := ih.smul (c := rejectMass)
      have hrejectedBind :
          rejected.bind (E attempts) =
            rejectMass • (rejectedProb.bind (E attempts)) := by
        rw [hrejectedNormalize, Measure.bind_smul]
      rw [← hrejectedBind] at hscaled
      have hadd := hscaled.add_left
        ((accepted.map
          (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some)
      have htargetSum :
          acceptMass • targetSome + rejectMass • targetSome = targetSome := by
        rw [← add_smul, hmass, one_smul]
      have hresult := hone.trans hadd
      rw [hacceptedTarget, htargetSum] at hresult
      simpa only [balancedRetryError] using hresult

/-- The recursive retry error is bounded by a linear accumulation of block
errors plus the probability of rejecting every attempt. -/
theorem balancedRetryError_le_nsmul_add_pow
    {delta rejectMass : ENNReal} (hrejectMass : rejectMass ≤ 1) :
    ∀ attempts,
      balancedRetryError delta rejectMass attempts ≤
        attempts • delta + rejectMass ^ attempts := by
  intro attempts
  induction attempts with
  | zero => simp [balancedRetryError]
  | succ attempts ih =>
      have hscale : rejectMass * (attempts • delta) ≤ attempts • delta := by
        calc
          rejectMass * (attempts • delta) ≤ 1 * (attempts • delta) :=
            mul_le_mul' hrejectMass le_rfl
          _ = attempts • delta := one_mul _
      calc
        balancedRetryError delta rejectMass (attempts + 1) =
            delta + rejectMass *
              balancedRetryError delta rejectMass attempts := rfl
        _ ≤ delta + rejectMass *
              (attempts • delta + rejectMass ^ attempts) :=
            add_le_add le_rfl (mul_le_mul' le_rfl ih)
        _ = delta + rejectMass * (attempts • delta) +
              rejectMass ^ (attempts + 1) := by
            rw [mul_add, pow_succ']
            exact (add_assoc _ _ _).symm
        _ ≤ delta + (attempts • delta) +
              rejectMass ^ (attempts + 1) :=
            add_le_add (add_le_add le_rfl hscale) le_rfl
        _ = (attempts + 1) • delta + rejectMass ^ (attempts + 1) := by
            rw [add_nsmul]
            simp only [one_nsmul]
            ac_rfl

/-- The stationary balanced rejection probability is at most `121/128`. -/
theorem balancedRejectedStateMeasure_mass_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    balancedRejectedStateMeasure q I sigma2 pi Set.univ ≤
      ENNReal.ofReal (121 / 128 : ℝ) := by
  let acceptMass := balancedAcceptedStateMeasure q I sigma2 pi Set.univ
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass] using
      balancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
  have hrejected : rejectMass = 1 - acceptMass := by
    exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
      (by simpa [add_comm] using hmass)
  change rejectMass ≤ ENNReal.ofReal (121 / 128 : ℝ)
  rw [hrejected]
  calc
    1 - acceptMass ≤ 1 - ENNReal.ofReal (7 / 128 : ℝ) :=
      tsub_le_tsub_left (by simpa [acceptMass] using hacceptedLower) 1
    _ = ENNReal.ofReal (121 / 128 : ℝ) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 7 / 128)]
      norm_num

/-- A finite balanced transition from any first-block law is dominated by
the same accepted target.  Subsequent rejected attempts use the normalized
stationary rejection branch. -/
theorem bind_balancedTransition_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) firstError)
    (hretryBlock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    MeasureLeUpTo
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map some)
      (firstError +
        balancedRejectedStateMeasure q I sigma2 pi Set.univ *
          balancedRetryError retryError
            (balancedRejectedStateMeasure q I sigma2 pi Set.univ) attempts) := by
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let rejected := balancedRejectedStateMeasure q I sigma2 pi
  let acceptMass := accepted Set.univ
  let rejectMass := rejected Set.univ
  let rejectedProb := Arlib.condOn rejected Set.univ
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  let E := balancedAccuracyTransitionLawAux q I sigma2 proposalCap properStride
  have hrejected0 : rejectMass ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le
      (by simpa [rejectMass, rejected] using hrejectedLower)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass, accepted, rejected] using
      balancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
  have hacceptedTarget :
      (accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some =
        acceptMass • targetSome := by
    have hbase := balancedAcceptedTargetSubmeasure_eq_mass_smul
      q I hsigma2 pi hacceptedLower
    change (accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some = _
    rw [hbase, Measure.map_smul]
  have hrejectedNormalize : rejected = rejectMass • rejectedProb :=
    measure_eq_mass_smul_condOn_univ rejected hrejected0 hrejectedTop
  have hretry := bind_balancedRejectedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride pi hacceptedLower hrejectedLower
      hretryBlock attempts
  have hscaled := hretry.smul (c := rejectMass)
  have hrejectedBind : rejected.bind (E attempts) =
      rejectMass • (rejectedProb.bind (E attempts)) := by
    rw [hrejectedNormalize, Measure.bind_smul]
  rw [← hrejectedBind] at hscaled
  have hadd := hscaled.add_left
    ((accepted.map (fun x => (accuracyScaleFactor q)⁻¹ • x)).map some)
  have hone :=
    bind_balancedAccuracyTransitionLawAux_succ_leUpTo_stationary
      q I hsigma2 proposalCap properStride attempts rho pi hfirstBlock
  have hresult := hone.trans hadd
  have htargetSum :
      acceptMass • targetSome + rejectMass • targetSome = targetSome := by
    rw [← add_smul, hmass, one_smul]
  rw [hacceptedTarget, htargetSum] at hresult
  simpa [rejectMass, rejected, targetSome, target] using hresult

/-- Convert the paper's multiplicative proper-proposal cutoff inequality into
an explicit cap-failure probability bound. -/
theorem bind_balancedAccuracyRetryBlockKernel_none_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    {capError : ENNReal}
    (hbudget : ((properStride : ℕ) : ENNReal) * M ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capError) :
    (mu.bind
      (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
        {none} ≤ capError := by
  let fail := (mu.bind
    (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
      {none}
  let coefficient := ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)
  have hmoment :=
    half_mul_natCast_mul_bind_accuracyCappedProperCollectLaw_none_le
      q I hsigma2
      (weight := accuracyImportanceWeight q I sigma2 (fun _ => 0))
      (measurable_accuracyImportanceWeight q I sigma2
        (measurable_const : Measurable fun _ : AmbientSpace q.n => (0 : ℝ)))
      hwarm proposalCap properStride 1
  have hmoment' : coefficient * fail ≤
      ((properStride : ℕ) : ENNReal) * M := by
    simpa [coefficient, fail, balancedAccuracyRetryBlockKernel] using hmoment
  have hcoeff0 : coefficient ≠ 0 := by
    simp [coefficient, hproposalCap.ne']
  have hcoeffTop : coefficient ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [coefficient])
  have hcombined : coefficient * fail ≤ coefficient * capError :=
    hmoment'.trans hbudget
  calc
    fail = coefficient⁻¹ * (coefficient * fail) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcoeff0 hcoeffTop, one_mul]
    _ ≤ coefficient⁻¹ * (coefficient * capError) :=
      mul_le_mul' le_rfl hcombined
    _ = capError := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcoeff0 hcoeffTop, one_mul]

end ArlibCommunity.Algorithms.CV18
