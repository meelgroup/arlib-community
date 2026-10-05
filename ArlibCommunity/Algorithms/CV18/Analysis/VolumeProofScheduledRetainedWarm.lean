/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceMarginal
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAdjacentTransition

/-! # Warmness of the retained scheduled accepted state

The retained point is expanded by `accuracyScaleFactor⁻¹`; the next phase
contracts it again.  Thus its ideal live law is the normalized accepted
submeasure of the preceding speedy stationary law.  This file records the
constant needed by the chronological warm-start induction.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

/-- A slightly sharper version of the acceptance-mass transfer used in the
branch-mass layer.  The scheduled core error is much smaller than the generic
quarter used there. -/
theorem TVLe.withDensity_mass_ge_two_sevenths_cv18
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≤ ENNReal.ofReal (3 / 14 : ℝ))
    {accept : S → ENNReal} (haccept : Measurable accept)
    (haccept_one : ∀ x, accept x ≤ 1)
    (hnu : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (nu.withDensity accept) Set.univ) :
    ENNReal.ofReal (2 / 7 : ℝ) ≤
      (mu.withDensity accept) Set.univ := by
  have hweighted := TVLe.withDensity_le_one_cv18 h haccept haccept_one
  have hsum : ENNReal.ofReal (2 / 7 : ℝ) + epsilon ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (2 / 7 : ℝ) + ENNReal.ofReal (3 / 14 : ℝ) := by
        gcongr
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 2 / 7)
          (by norm_num : (0 : ℝ) ≤ 3 / 14)]
        norm_num
  have hadd : ENNReal.ofReal (2 / 7 : ℝ) + epsilon ≤
      (mu.withDensity accept) Set.univ + epsilon :=
    hsum.trans (hnu.trans (hweighted.right MeasurableSet.univ))
  exact ENNReal.le_of_add_le_add_right
    (ne_top_of_le_ne_top (by norm_num) hepsilon) hadd

/-- The scheduled unbalanced correction accepts with probability at least
`1/8`.  This sharper constant is what makes the subsequent balanced retained
state exactly `8`-warm, matching the stride already used by the executable. -/
theorem scheduledAccuracyPhase_stationary_acceptance_ge_one_eighth
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (1 / 8 : ℝ) ≤
      (pi.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let c := accuracyScaleFactor q
  let pi := ellGaussianProb K delta sigma2
  let core := c • K
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal := gaussianScaleAcceptance sigma2 c
  let source := (Arlib.condOn pi core).map scale
  let proposal := Arlib.condOn
    ((volume : Measure (AmbientSpace q.n)).withDensity
      (gaussianWeight (sigma2 / c ^ 2))) K
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hKmeas : MeasurableSet K := figureOneScheduledPhaseBody_measurable q I sigma2
  have hKconv : Convex ℝ K := figureOneScheduledPhaseBody_convex q I sigma2
  have hKcompact : IsCompact K := figureOneScheduledPhaseBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 := figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ := figureOneScheduledPhaseBody_volume_ne_top q I sigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hKmeas hKconv hKcompact.isBounded hK0
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hcoreMass : ENNReal.ofReal (7 / 16 : ℝ) ≤ pi core := by
    simpa [pi, core, K, delta, c] using
      figureOneScheduled_speedy_core_mass q I hsigma2
  have hcore0 : pi core ≠ 0 :=
    ne_of_gt ((by norm_num : 0 < ENNReal.ofReal (7 / 16 : ℝ)).trans_le hcoreMass)
  have hcoretop : pi core ≠ ⊤ := measure_ne_top pi core
  let _ : IsProbabilityMeasure (Arlib.condOn pi core) :=
    Arlib.isProbabilityMeasure_condOn pi hcore0 hcoretop
  let _ : IsProbabilityMeasure source :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hscaled : 0 < sigma2 / c ^ 2 := by positivity
  have hprop0 :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K ≠ 0 :=
    withDensity_gaussianWeight_ne_zero _ hK0
  have hproptop :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight (sigma2 / c ^ 2))) K ≠ ⊤ :=
    withDensity_gaussianWeight_ne_top hscaled hKmeas hKtop
  let _ : IsProbabilityMeasure proposal :=
    Arlib.isProbabilityMeasure_condOn _ hprop0 hproptop
  have hsourceTv : Arlib.TVLe source proposal
      (4 * ENNReal.ofReal (figureOneScheduledCoreError q)) := by
    simpa [source, proposal, pi, core, scale, K, delta, c] using
      figureOneScheduled_stationaryCoreMap_tv_proposal q I hsigma2
  have herr : 4 * ENNReal.ofReal (figureOneScheduledCoreError q) ≤
      ENNReal.ofReal (3 / 14 : ℝ) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    unfold figureOneScheduledCoreError
    nlinarith [figureOnePerSampleMixingError_le_one q]
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    apply ball_scheduledPhaseInradius_subset q I sigma2
    exact Metric.mem_ball_self (figureOneScheduledPhaseInradius_pos q hsigma2)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (proposal.withDensity g) Set.univ := by
    dsimp [proposal, g, c]
    exact half_le_condOn_gaussian_scaleAcceptance_mass_standardCore_cv18
      hn hKmeas hKconv hzero
      (by simpa [c, accuracyScaleFactor] using hprop0)
      (by simpa [c, accuracyScaleFactor] using hproptop)
  have hg : Measurable g := by
    dsimp [g]
    exact measurable_gaussianScaleAcceptance sigma2 c
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    dsimp [g]
    exact gaussianScaleAcceptance_le_one hsigma2 hc0
      (accuracyScaleFactor_le_one q) x
  have hsourceAccept : ENNReal.ofReal (2 / 7 : ℝ) ≤
      (source.withDensity g) Set.univ :=
    TVLe.withDensity_mass_ge_two_sevenths_cv18 hsourceTv herr hg hg1 hhalf
  have hrestrict : pi.restrict core = pi core • Arlib.condOn pi core := by
    rw [Arlib.condOn_def, smul_smul,
      ENNReal.mul_inv_cancel hcore0 hcoretop, one_smul]
  have hsourceScale :
      ((pi.restrict core).map scale).withDensity g =
        pi core • (source.withDensity g) := by
    rw [hrestrict, Measure.map_smul, withDensity_smul_measure]
  have hmeasure := map_withDensity_scheduledAccuracyRejectionAcceptance
    q I sigma2 pi
  have htotal := congrArg
    (fun mu : Measure (AmbientSpace q.n) => mu Set.univ) hmeasure
  have hscale : Measurable scale := by fun_prop
  rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ,
    hsourceScale, Measure.smul_apply, smul_eq_mul] at htotal
  calc
    ENNReal.ofReal (1 / 8 : ℝ) =
        ENNReal.ofReal (7 / 16 : ℝ) * ENNReal.ofReal (2 / 7 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7 / 16)]
      norm_num
    _ ≤ pi core * (source.withDensity g) Set.univ :=
      mul_le_mul hcoreMass hsourceAccept bot_le bot_le
    _ = (pi.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      htotal.symm

/-- The balanced stationary accepted branch has mass at least `1/16`. -/
theorem scheduledBalancedAcceptedStateMeasure_mass_ge_one_sixteenth
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (1 / 16 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  rw [scheduledBalancedAcceptedStateMeasure_eq_half_smul,
    Measure.smul_apply, smul_eq_mul]
  have h := scheduledAccuracyPhase_stationary_acceptance_ge_one_eighth
    q I hsigma2
  change ENNReal.ofReal (1 / 8 : ℝ) ≤
    (pi.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ at h
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  calc
    ENNReal.ofReal (1 / 16 : ℝ) =
        (2 : ENNReal)⁻¹ * ENNReal.ofReal (1 / 8 : ℝ) := by
      rw [← hhalf,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    _ ≤ (2 : ENNReal)⁻¹ *
        (pi.withDensity
          (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      mul_le_mul' le_rfl h

/-- Contracting the normalized retained accepted target recovers the
normalized accepted submeasure on the speedy state space. -/
theorem map_scheduledBalancedAcceptedTarget_scale_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) (pi : Measure (AmbientSpace q.n)) :
    let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
    (scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map
        (fun x => accuracyScaleFactor q • x) =
      (accepted Set.univ)⁻¹ • accepted := by
  dsimp only
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  let expand : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  have hexpand : Measurable expand := by fun_prop
  have hcontract : Measurable contract := by fun_prop
  have hc0 : accuracyScaleFactor q ≠ 0 := (accuracyScaleFactor_pos q).ne'
  unfold scheduledBalancedAccuracyGaussianAcceptedTargetLaw
  change (Arlib.condOn (accepted.map expand) Set.univ).map contract = _
  rw [Arlib.condOn_def, Measure.map_smul,
    Measure.map_apply hexpand MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_univ,
    Measure.map_map hcontract hexpand]
  congr 1
  change Measure.map (contract ∘ expand) accepted = accepted
  rw [show contract ∘ expand = id by
    funext x
    dsimp [expand, contract]
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul], Measure.map_id]

/-- The contracted ideal retained target is `8`-warm with respect to the
speedy stationary law.  The constant follows from balanced acceptance density
at most `1/2` and the sharpened success mass `1/16`. -/
theorem map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    Arlib.IsWarm 8
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map (fun x => accuracyScaleFactor q • x)) pi := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
  have hmass : ENNReal.ofReal (1 / 16 : ℝ) ≤ accepted Set.univ := by
    simpa [accepted, pi, K, delta] using
      scheduledBalancedAcceptedStateMeasure_mass_ge_one_sixteenth q I hsigma2
  have hinv : (accepted Set.univ)⁻¹ ≤ (16 : ENNReal) := by
    have h := ENNReal.inv_le_inv.2 hmass
    simpa using h
  have haccepted : accepted ≤ (2 : ENNReal)⁻¹ • pi := by
    simpa [accepted, pi] using
      scheduledBalancedAcceptedStateMeasure_le_half_smul
        q I hsigma2 pi
  rw [map_scheduledBalancedAcceptedTarget_scale_eq q I sigma2 pi]
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    (accepted Set.univ)⁻¹ * accepted S ≤
        (16 : ENNReal) * ((2 : ENNReal)⁻¹ * pi S) := by
      gcongr
      exact Measure.le_iff'.mp haccepted S
    _ = 8 * pi S := by
      have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      have hcoef : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
        rw [← hhalf, ← ENNReal.ofReal_ofNat 16,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
      rw [← mul_assoc, hcoef]

/-- After the scheduled contraction and one cooling increment, the retained
accepted target has exactly the phase-start warmness budget already used by
the concrete first-block theorem. -/
theorem map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let sigma2 := scheduleValue q phase
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let nextPi := ellGaussianProb
      (figureOneScheduledPhaseBody q I (scheduleValue q (phase + 1)))
      (figureOneScheduledProposalRadius q (scheduleValue q (phase + 1)))
      (scheduleValue q (phase + 1))
    Arlib.IsWarm (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi).map (fun x => accuracyScaleFactor q • x)) nextPi := by
  dsimp only
  have hsame := map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
    q I (scheduleValue_pos q phase)
  have hadj := scheduledPhase_speedyStationary_adjacent_isWarm q I phase
  have htrans := hsame.trans hadj
  convert htrans using 1
  rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]

/-- Concrete final-parameter transition domination before the KLS target is
replaced by the restricted Gaussian.  Keeping this accepted target is what
allows the chronological good path to remain warm phase after phase. -/
theorem bind_figureOneFinalScheduledBalancedTransition_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) rho
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu → Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo
        (mu.bind
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2
            (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
            (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
            (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
        ((scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
          (ellGaussianProb
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2)).map some)
        (figureOneCorrectedTransitionBudget q) := by
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  let attempts := figureOneSafeRetryCount q - 1
  let proposalCap :=
    figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let properStride :=
    figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hproposalCap : 0 < proposalCap := by
    simpa [proposalCap] using
      figureOneFinalScheduledBalancedParameters_proposalCap_pos q sigma2
  have hfirst : MeasureLeUpTo
      ((mu.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    exact scheduledBalancedFirstBlock_leUpTo_stationary
      q I hsigma2 proposalCap properStride attempts hproposalCap rho
        hbaseWarm
        (by
          simpa [properStride, attempts,
            figureOneFinalScheduledBalancedParameters_properStride] using
            figureOneScheduledCorrectedFirstWalkRequirement_le_stride
              q sigma2 attempts)
        (by
          simpa [properStride, proposalCap, attempts] using
            figureOneFinalScheduled_firstCapBudget q sigma2)
        mu hmu hwarm
  have hretry :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    simpa [K, delta, pi] using
      scheduledBalancedRejectedRetryBlock_leUpTo_stationary
        q I hsigma2 proposalCap properStride attempts hproposalCap
          (by
            simpa [properStride, attempts,
              figureOneFinalScheduledBalancedParameters_properStride] using
              figureOneScheduledCorrectedRetryWalkRequirement_le_stride
                q sigma2 attempts)
          (by
            simpa [properStride, proposalCap, attempts] using
              figureOneFinalScheduled_retryCapBudget q sigma2)
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 := by
    dsimp [K]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ := by
    dsimp [K]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [K, delta, pi] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hreject :
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ ≤
        ENNReal.ofReal (121 / 128 : ℝ) :=
    scheduledBalancedRejectedStateMeasure_mass_le
      q I hsigma2 pi haccepted
  have hrejectOne :
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ ≤ 1 :=
    hreject.trans (by norm_num)
  have htail :
      (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ) ^
          (attempts + 1) ≤ figureOneCorrectedRetryTailBudget q := by
    simpa [attempts] using figureOneSafeRetryTail_le q hreject
  have hdom := bind_scheduledBalancedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride attempts mu pi haccepted
      (scheduledBalancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi)
      hfirst hretry
  have hbudget := scheduledBalancedTransitionError_with_cap_le_budget
    q hrejectOne htail
  have hpre :
      (2 * figureOneCorrectedBlockBudget q attempts) +
          scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ *
            balancedRetryError (2 * figureOneCorrectedBlockBudget q attempts)
              (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ)
              attempts ≤ figureOneCorrectedTransitionBudget q := by
    exact (self_le_add_right _
      (scheduledBalancedStationaryTargetError q)).trans hbudget
  have hresult := hdom.mono_error hpre
  simpa [proposalCap, properStride, attempts,
    Nat.sub_add_cancel (figureOneSafeRetryCount_pos q), K, delta, pi] using hresult

/-- Optional retained-state kernel between consecutive samples of one
scheduled phase.  Failure is absorbing; a live retained point is contracted
back to the speedy state before the next balanced transition. -/
noncomputable def figureOneFinalScheduledRetainedOptionKernel
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Option (AmbientSpace q.n) → Measure (Option (AmbientSpace q.n))
  | none => Measure.dirac none
  | some current =>
      scheduledBalancedAccuracyTransitionLawAux q I sigma2
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
        (accuracyScaleFactor q • current)

theorem figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable (figureOneFinalScheduledRetainedOptionKernel q I sigma2) ∧
    ∀ state, IsProbabilityMeasure
      (figureOneFinalScheduledRetainedOptionKernel q I sigma2 state) := by
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hsome : Measurable fun current : AmbientSpace q.n =>
      scheduledBalancedAccuracyTransitionLawAux q I sigma2
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
        (accuracyScaleFactor q • current) := by
    exact htransition.1.comp <|
      (measurable_const : Measurable fun _ : AmbientSpace q.n =>
        accuracyScaleFactor q).smul measurable_id
  constructor
  · convert Measurable.optionElim
      (Measure.dirac (none : Option (AmbientSpace q.n))) hsome using 1
    ext state
    cases state <;> rfl
  · intro state
    cases state with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (AmbientSpace q.n)))
        infer_instance
    | some current => exact htransition.2 (accuracyScaleFactor q • current)

/-- The normalized accepted target is approximately invariant under one more
retained transition.  This is the integrated (not pointwise-Dirac) step used
by the paper's exact-chance argument. -/
theorem bind_figureOneFinalScheduledAcceptedTarget_retainedOptionKernel_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let pi := ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
    let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
      q I sigma2 pi
    MeasureLeUpTo
      ((target.map some).bind
        (figureOneFinalScheduledRetainedOptionKernel q I sigma2))
      (target.map some) (figureOneCorrectedTransitionBudget q) := by
  dsimp only
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
    q I sigma2 pi
  let contract : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let transition := scheduledBalancedAccuracyTransitionLawAux q I sigma2
    (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
    (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [pi] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I hsigma2
  let _ : IsProbabilityMeasure target :=
    scheduledBalancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi haccepted
  have hcontractWarm : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (target.map contract) pi := by
    have h8 : Arlib.IsWarm 8 (target.map contract) pi := by
      simpa [target, pi, contract] using
        map_scheduledBalancedAcceptedTarget_scale_isWarm_eight q I hsigma2
    apply h8.mono
    rw [← ENNReal.ofReal_ofNat 8]
    exact ENNReal.ofReal_le_ofReal <| by
      nlinarith [speedyAdjacentWarmConstant_one_le q]
  let _ : IsProbabilityMeasure (target.map contract) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable contract).aemeasurable
  have hstep :=
    bind_figureOneFinalScheduledBalancedTransition_leUpTo_acceptedTarget
      q I hsigma2 (target.map contract) hcontractWarm
        (target.map contract) inferInstance
        ((Arlib.IsWarm.refl (target.map contract)).mono (by norm_num))
  have hleft :
      (target.map some).bind
          (figureOneFinalScheduledRetainedOptionKernel q I sigma2) =
        (target.map contract).bind transition := by
    calc
      _ = target.bind (figureOneFinalScheduledRetainedOptionKernel
          q I sigma2 ∘ some) :=
        map_bind_eq_bind_comp_state target measurable_some
          (figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
            q I hsigma2).1
      _ = target.bind fun current => transition (contract current) := by
        apply Measure.bind_congr_right
        filter_upwards with current
        rfl
      _ = _ := (map_bind_eq_bind_comp_state target (by fun_prop : Measurable contract)
        (by
          exact (scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
            q I hsigma2
              (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
              (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
              (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)).1)).symm
  rw [hleft]
  simpa [pi, target, contract, transition] using hstep

/-- Repeating retained transitions accumulates only an additive exact-chance
loss.  In particular, bad mass is transported by the probability kernel and
is never doubled. -/
theorem iterated_figureOneFinalScheduledRetainedOptionKernel_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (actualInitial : Measure (Option (AmbientSpace q.n)))
    {initialError : ENNReal}
    (hinitial :
      let pi := ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2
      let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi
      MeasureLeUpTo actualInitial (target.map some) initialError) :
    ∀ samples,
      let pi := ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2
      let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw
        q I sigma2 pi
      MeasureLeUpTo
        (iteratedKernelLaw
          (fun _ => figureOneFinalScheduledRetainedOptionKernel q I sigma2)
          actualInitial samples)
        (target.map some)
        (initialError + samples • figureOneCorrectedTransitionBudget q) := by
  intro samples
  dsimp only
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
    (ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  let K := figureOneFinalScheduledRetainedOptionKernel q I sigma2
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hsigma2
  have hstep : MeasureLeUpTo ((target.map some).bind K)
      (target.map some) (figureOneCorrectedTransitionBudget q) := by
    simpa [target, K] using
      bind_figureOneFinalScheduledAcceptedTarget_retainedOptionKernel_leUpTo
        q I hsigma2
  induction samples with
  | zero => simpa [target] using hinitial
  | succ samples ih =>
      have hnext := MeasureLeUpTo.bind_then_replace ih K hK.1 hK.2 hstep
      change MeasureLeUpTo
        ((iteratedKernelLaw (fun _ =>
          figureOneFinalScheduledRetainedOptionKernel q I sigma2)
          actualInitial samples).bind K)
        (target.map some)
        (initialError + (samples + 1) • figureOneCorrectedTransitionBudget q)
      convert hnext using 1
      rw [succ_nsmul]
      ac_rfl

#print axioms TVLe.withDensity_mass_ge_two_sevenths_cv18
#print axioms scheduledAccuracyPhase_stationary_acceptance_ge_one_eighth
#print axioms scheduledBalancedAcceptedStateMeasure_mass_ge_one_sixteenth
#print axioms map_scheduledBalancedAcceptedTarget_scale_eq
#print axioms map_scheduledBalancedAcceptedTarget_scale_isWarm_eight
#print axioms map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm
#print axioms bind_figureOneFinalScheduledBalancedTransition_leUpTo_acceptedTarget
#print axioms bind_figureOneFinalScheduledAcceptedTarget_retainedOptionKernel_leUpTo
#print axioms iterated_figureOneFinalScheduledRetainedOptionKernel_leUpTo

end ArlibCommunity.Algorithms.CV18
