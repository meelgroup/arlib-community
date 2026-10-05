/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation

/-!
# Balanced executable transitions and CV18 approximate independence

This module turns the one-sided finite-retry approximation into the
probability/total-variation form consumed by the Markov-history version of
CV18 Lemma 7.17.  In particular, the normalized accepted branch is proved to
be a probability measure from the same explicit acceptance lower bound used
by the retry analysis.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The accepted target of a balanced phase is a probability law whenever
the stationary acceptance mass has the explicit positive lower bound used by
the finite-retry theorem. -/
theorem balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    IsProbabilityMeasure
      (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi) := by
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let scale : AmbientSpace q.n -> AmbientSpace q.n := fun x =>
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
  change IsProbabilityMeasure (Arlib.condOn acceptedTarget Set.univ)
  exact Arlib.isProbabilityMeasure_condOn acceptedTarget htarget0 htargetTop

/-- Total-variation form of the complete finite balanced transition.  The
error is exactly the first-block approximation plus the rejected-branch retry
error; no factor is lost when converting from additive domination because
both sides are probability measures. -/
theorem bind_balancedTransition_tvLe_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
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
    Arlib.TVLe
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map some)
      (firstError +
        balancedRejectedStateMeasure q I sigma2 pi Set.univ *
          balancedRetryError retryError
            (balancedRejectedStateMeasure q I sigma2 pi Set.univ) attempts) := by
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.1.aemeasurable (ae_of_all _ hK.2)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure (target.map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hdom := bind_balancedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride attempts rho pi
      hacceptedLower hrejectedLower hfirstBlock hretryBlock
  change Arlib.TVLe (rho.bind K) (target.map some) _
  exact hdom.to_tvLe

/-- A finite per-block error remains finite through any finite balanced retry
recurrence. -/
theorem balancedRetryError_ne_top {delta rejectMass : ENNReal}
    (hdelta : delta ≠ ⊤) (hrejectMass : rejectMass ≠ ⊤) :
    forall attempts, balancedRetryError delta rejectMass attempts ≠ ⊤ := by
  intro attempts
  induction attempts with
  | zero => simp [balancedRetryError]
  | succ attempts ih =>
      simp only [balancedRetryError]
      exact ENNReal.add_ne_top.mpr
        ⟨hdelta, ENNReal.mul_ne_top hrejectMass ih⟩

/-- A warm-start mixing bound and the paper's proper-proposal budget give the
stationary endpoint approximation needed by one balanced retry block. -/
theorem bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    {M capError mixError : ENNReal}
    (hwarm : Arlib.IsWarm M mu
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hbudget : ((properStride : ℕ) : ENNReal) * M ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride)
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2) mixError) :
    MeasureLeUpTo
      ((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      ((Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2).map some)
      (capError + mixError) := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmass0 := Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (accuracyPhaseTruncatedBody_convex q I sigma2)
    (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
    (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
    (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
    (figureOneProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hfail := bind_balancedAccuracyRetryBlockKernel_none_le_of_isWarm
    q I hsigma2 hwarm proposalCap properStride hproposalCap hbudget
  exact bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
    q I hsigma2 proposalCap properStride mu pi hfail hmix

/-- The retry block started from the normalized stationary rejection branch
has a completely concrete approximation bound.  Its warmness constant is
exactly `2`; the only remaining premises are the explicit walk-time and raw-
proposal budget inequalities. -/
theorem balancedRejectedRetryBlock_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (hproposalCap : 0 < proposalCap)
    {capError : ENNReal} {mixError : ℝ}
    (hmixError0 : 0 < mixError) (hmixError1 : mixError ≤ 1)
    (hwalk : 4 * ((Real.log 2 + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
        (properStride : ℝ))
    (hbudget : ((properStride : ℕ) : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capError) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let rejected := balancedRejectedStateMeasure q I sigma2 pi
    let rejectedProb := Arlib.condOn rejected Set.univ
    MeasureLeUpTo
      ((rejectedProb.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) (capError + ENNReal.ofReal mixError) := by
  dsimp only
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let rejected := balancedRejectedStateMeasure q I sigma2 pi
  let rejectedProb := Arlib.condOn rejected Set.univ
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmass0 := Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (accuracyPhaseTruncatedBody_convex q I sigma2)
    (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
    (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
    (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
    (figureOneProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hrejectedLower : (2 : ENNReal)⁻¹ ≤ rejected Set.univ := by
    simpa [rejected, pi] using
      balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hrejected0 : rejected Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < (2 : ENNReal)⁻¹).trans_le hrejectedLower
  have hrejectedTop : rejected Set.univ ≠ ⊤ := by
    have hle : rejected ≤ pi := by
      simpa [rejected] using
        balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  let _ : IsProbabilityMeasure rejectedProb :=
    Arlib.isProbabilityMeasure_condOn rejected hrejected0 hrejectedTop
  have hwarm : Arlib.IsWarm 2 rejectedProb pi := by
    simpa [rejectedProb, rejected, pi] using
      balancedRejectedStationary_isWarm q I hsigma2
  have hmixWithin := mixesWithin_balancedRejectedStationary_cv18
    q I hsigma2 hmixError0 hmixError1 hwalk
  have hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        rejectedProb properStride)
      pi (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, rejectedProb, rejected, pi]
      using hmixWithin
  exact
    bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
      q I hsigma2 proposalCap properStride hproposalCap rejectedProb
        hwarm hbudget hmix

private theorem approxIndepFun_balancedTransition_of_warm_blocks_aux
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hfirstError : firstError ≠ ⊤) (hretryError : retryError ≠ ⊤)
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu -> Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo
        ((mu.bind
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
    let rejectMass :=
      balancedRejectedStateMeasure q I sigma2 pi Set.univ
    let error := firstError + rejectMass *
      balancedRetryError retryError rejectMass attempts
    ApproxIndepFun (error + error).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1))) := by
  dsimp only
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let error := firstError + rejectMass *
    balancedRetryError retryError rejectMass attempts
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    dsimp only [rejectMass]
    have hle := balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  have hretryFinite :
      balancedRetryError retryError rejectMass attempts ≠ ⊤ :=
    balancedRetryError_ne_top hretryError hrejectedTop attempts
  have herror : error ≠ ⊤ := by
    dsimp only [error]
    exact ENNReal.add_ne_top.mpr
      ⟨hfirstError, ENNReal.mul_ne_top hrejectedTop hretryFinite⟩
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure targetSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
    rho hK.1 hK.2 targetSome herror
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  simpa [K, targetSome, target, error, rejectMass] using
    (bind_balancedTransition_leUpTo_acceptedTarget
      q I hsigma2 proposalCap properStride attempts mu pi
        hacceptedLower hrejectedLower
        (hfirstBlock mu hmu hwarm) hretryBlock)

/-- A base warm start, uniform speedy mixing from its `2`-warm
conditionings, and the concrete stationary-rejection estimate discharge every
analytic premise of the adjacent-sample independence theorem.  This is the
form used when the base law is the previous cooling phase's stationary law. -/
theorem approxIndepFun_balancedTransition_of_baseWarm_and_mixing
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    {M capFirst mixFirst capRetry : ENNReal} {mixRetry : ℝ}
    (hproposalCap : 0 < proposalCap)
    (hcapFirst : capFirst ≠ ⊤) (hmixFirstFinite : mixFirst ≠ ⊤)
    (hcapRetry : capRetry ≠ ⊤)
    (hbaseWarm : Arlib.IsWarm M rho
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hfirstBudget : ((properStride : ℕ) : ENNReal) * (2 * M) ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capFirst)
    (hmixFirst : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu ->
      Arlib.IsWarm (2 * M) mu
        (Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2) ->
      Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy
            (Arlib.MarkovChains.speedyMetropolisGaussian
              (accuracyPhaseTruncatedBody q I sigma2)
              (figureOneProposalRadius q sigma2) sigma2))
          mu properStride)
        (Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2) mixFirst)
    (hmixRetry0 : 0 < mixRetry) (hmixRetry1 : mixRetry ≤ 1)
    (hretryWalk : 4 * ((Real.log 2 + 2 * Real.log (1 / mixRetry)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤
        (properStride : ℝ))
    (hretryBudget : ((properStride : ℕ) : ENNReal) * 2 ≤
      (ENNReal.ofReal (1 / 2) * (proposalCap : ENNReal)) * capRetry) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
    let firstError := capFirst + mixFirst
    let retryError := capRetry + ENNReal.ofReal mixRetry
    let error := firstError + rejectMass *
      balancedRetryError retryError rejectMass attempts
    ApproxIndepFun (error + error).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1))) := by
  dsimp only
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hmass0 := Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
    (accuracyPhaseTruncatedBody_measurable q I sigma2)
    (accuracyPhaseTruncatedBody_convex q I sigma2)
    (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
    (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
    hdelta sigma2
  have hmasstop := Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
    (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
    (figureOneProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hfirstError : capFirst + mixFirst ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hcapFirst, hmixFirstFinite⟩
  have hretryError : capRetry + ENNReal.ofReal mixRetry ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hcapRetry, ENNReal.ofReal_ne_top⟩
  have hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [pi] using balancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ :=
    balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hfirstBlock : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu -> Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo
        ((mu.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (capFirst + mixFirst) := by
    intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    have hwarmPi : Arlib.IsWarm (2 * M) mu pi :=
      hwarm.trans hbaseWarm
    exact
      bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
        q I hsigma2 proposalCap properStride hproposalCap mu hwarmPi
          hfirstBudget (hmixFirst mu hmu hwarmPi)
  have hretryBlock := balancedRejectedRetryBlock_leUpTo_stationary
    q I hsigma2 proposalCap properStride hproposalCap
      hmixRetry0 hmixRetry1 hretryWalk hretryBudget
  simpa [pi] using
    (approxIndepFun_balancedTransition_of_warm_blocks_aux
      q I hsigma2 proposalCap properStride attempts rho pi
        hfirstError hretryError hacceptedLower hrejectedLower
        hfirstBlock hretryBlock)

/-- Concrete adjacent-sample form of CV18 Lemma 7.17(a) for the executable
balanced transition.  Every half-mass conditioning is `2`-warm; a uniform
first-block estimate for such starts and the stationary retry estimate place
both conditional and unconditional next laws near the same accepted target.
-/
theorem approxIndepFun_balancedTransition_of_warm_blocks
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hfirstError : firstError ≠ ⊤) (hretryError : retryError ≠ ⊤)
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu -> Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo
        ((mu.bind
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
    let rejectMass :=
      balancedRejectedStateMeasure q I sigma2 pi Set.univ
    let error := firstError + rejectMass *
      balancedRetryError retryError rejectMass attempts
    ApproxIndepFun (error + error).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1))) := by
  dsimp only
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let error := firstError + rejectMass *
    balancedRetryError retryError rejectMass attempts
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    dsimp only [rejectMass]
    have hle := balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  have hretryFinite :
      balancedRetryError retryError rejectMass attempts ≠ ⊤ :=
    balancedRetryError_ne_top hretryError hrejectedTop attempts
  have herror : error ≠ ⊤ := by
    dsimp only [error]
    exact ENNReal.add_ne_top.mpr
      ⟨hfirstError, ENNReal.mul_ne_top hrejectedTop hretryFinite⟩
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure targetSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
    rho hK.1 hK.2 targetSome herror
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  simpa [K, targetSome, target, error, rejectMass] using
    (bind_balancedTransition_leUpTo_acceptedTarget
      q I hsigma2 proposalCap properStride attempts mu pi
        hacceptedLower hrejectedLower
        (hfirstBlock mu hmu hwarm) hretryBlock)

/-- Executable retained-state form of CV18 Lemma 7.17(c).  The law `history`
may contain every preceding sample and phase estimator; only its measurable
retained speedy state is passed to the next balanced transition.  The theorem
then yields the paper's `3 k m nu` independence estimate for any measurable
accumulated product and next estimator. -/
theorem approxIndepFun_balancedTransition_history_of_warm_blocks
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H -> AmbientSpace q.n) (hstate : Measurable state)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hfirstError : firstError ≠ ⊤) (hretryError : retryError ≠ ⊤)
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu ->
      Arlib.IsWarm 2 mu (history.map state) ->
      MeasureLeUpTo
        ((mu.bind
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
        (pi.map some) retryError)
    (pastProduct : H -> ℝ)
    (nextEstimator : Option (AmbientSpace q.n) -> ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget :
      let rejectMass :=
        balancedRejectedStateMeasure q I sigma2 pi Set.univ
      let error := firstError + rejectMass *
        balancedRetryError retryError rejectMass attempts
      (error + error).toReal ≤ 3 * (k : ℝ) * (m : ℝ) * nu) :
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1) ∘ state)) := by
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let error := firstError + rejectMass *
    balancedRetryError retryError rejectMass attempts
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    dsimp only [rejectMass]
    have hle := balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  have hretryFinite :
      balancedRetryError retryError rejectMass attempts ≠ ⊤ :=
    balancedRetryError_ne_top hretryError hrejectedTop attempts
  have herror : error ≠ ⊤ := by
    dsimp only [error]
    exact ENNReal.add_ne_top.mpr
      ⟨hfirstError, ENNReal.mul_ne_top hrejectedTop hretryFinite⟩
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure targetSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo
    history state hstate hK.1 hK.2 targetSome herror ?_
      (pastProduct := pastProduct) (nextEstimator := nextEstimator)
      hpastProduct hnextEstimator k m nu
  · simpa [error, rejectMass] using hbudget
  · intro mu hmu hwarm
    let _ : IsProbabilityMeasure mu := hmu
    simpa [K, targetSome, target, error, rejectMass] using
      (bind_balancedTransition_leUpTo_acceptedTarget
        q I hsigma2 proposalCap properStride attempts mu pi
          hacceptedLower hrejectedLower
          (hfirstBlock mu hmu hwarm) hretryBlock)

#print axioms balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
#print axioms bind_balancedTransition_tvLe_acceptedTarget
#print axioms bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
#print axioms balancedRejectedRetryBlock_leUpTo_stationary
#print axioms approxIndepFun_balancedTransition_of_baseWarm_and_mixing
#print axioms approxIndepFun_balancedTransition_of_warm_blocks
#print axioms approxIndepFun_balancedTransition_history_of_warm_blocks

end ArlibCommunity.Algorithms.CV18
