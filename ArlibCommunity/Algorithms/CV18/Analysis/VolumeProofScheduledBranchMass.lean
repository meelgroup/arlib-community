import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptanceMass

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

private theorem ofReal_one_half_scheduled :
    ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- At scheduled speedy stationarity, the unbalanced Gaussian correction
accepts with the same `7/64` lower bound used in CV18. -/
theorem scheduledAccuracyPhase_stationary_acceptance_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 64 : ℝ) ≤
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
      ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by
      nlinarith [figureOneScheduledCoreError_le_one_div_sixteen q])
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
  have hsourceAccept : ENNReal.ofReal (1 / 4 : ℝ) ≤
      (source.withDensity g) Set.univ :=
    TVLe.withDensity_mass_ge_quarter_cv18 hsourceTv herr hg hg1 hhalf
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
    ENNReal.ofReal (7 / 64 : ℝ) =
        ENNReal.ofReal (7 / 16 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7 / 16)]
      norm_num
    _ ≤ pi core * (source.withDensity g) Set.univ :=
      mul_le_mul hcoreMass hsourceAccept bot_le bot_le
    _ = (pi.withDensity
        (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      htotal.symm

theorem scheduledBalancedAcceptedStateMeasure_eq_half_smul
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    scheduledBalancedAcceptedStateMeasure q I sigma2 mu =
      (2 : ENNReal)⁻¹ •
        mu.withDensity
          (scheduledAccuracyGaussianRejectionAcceptance q I sigma2) := by
  unfold scheduledBalancedAcceptedStateMeasure
    scheduledBalancedAccuracyGaussianAcceptance
  change mu.withDensity
      ((2 : ENNReal)⁻¹ •
        scheduledAccuracyGaussianRejectionAcceptance q I sigma2) = _
  rw [withDensity_smul]
  exact measurable_scheduledAccuracyGaussianRejectionAcceptance q I sigma2

theorem scheduledBalancedAcceptedStateMeasure_mass_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := figureOneScheduledPhaseBody q I sigma2
    let delta := figureOneScheduledProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
  dsimp only
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  rw [scheduledBalancedAcceptedStateMeasure_eq_half_smul,
    Measure.smul_apply, smul_eq_mul]
  have h := scheduledAccuracyPhase_stationary_acceptance_ge q I hsigma2
  change ENNReal.ofReal (7 / 64 : ℝ) ≤
    (pi.withDensity
      (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ at h
  calc
    ENNReal.ofReal (7 / 128 : ℝ) =
        (2 : ENNReal)⁻¹ * ENNReal.ofReal (7 / 64 : ℝ) := by
      rw [← ofReal_one_half_scheduled,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    _ ≤ (2 : ENNReal)⁻¹ *
        (pi.withDensity
          (scheduledAccuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      mul_le_mul' le_rfl h

theorem scheduledBalancedRejectedStateMeasure_mass_ge_half
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu] :
    (2 : ENNReal)⁻¹ ≤
      scheduledBalancedRejectedStateMeasure q I sigma2 mu Set.univ := by
  unfold scheduledBalancedRejectedStateMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (2 : ENNReal)⁻¹ = ∫⁻ _x, (2 : ENNReal)⁻¹ ∂mu := by simp
    _ ≤ ∫⁻ x, 1 - scheduledBalancedAccuracyGaussianAcceptance
        q I sigma2 x ∂mu :=
      lintegral_mono fun x => by
        have h := scheduledBalancedAccuracyGaussianAcceptance_le_half
          q I hsigma2 x
        apply ENNReal.le_sub_of_add_le_left
          (ne_top_of_le_ne_top (by norm_num) h)
        calc
          scheduledBalancedAccuracyGaussianAcceptance q I sigma2 x +
              (2 : ENNReal)⁻¹ ≤
            (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := add_le_add_left h _
          _ = 1 := by
            rw [← ofReal_one_half_scheduled,
              ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
                (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num

/-- Scheduled accepted and rejected stationary current-state masses sum to one. -/
theorem scheduledBalancedAcceptedRejected_mass_add_eq_one
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi] :
    scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ +
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ = 1 := by
  unfold scheduledBalancedAcceptedStateMeasure scheduledBalancedRejectedStateMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_add_left
      (measurable_scheduledBalancedAccuracyGaussianAcceptance q I sigma2)]
  calc
    (∫⁻ x, scheduledBalancedAccuracyGaussianAcceptance q I sigma2 x +
        (1 - scheduledBalancedAccuracyGaussianAcceptance q I sigma2 x) ∂pi) =
        ∫⁻ _x, (1 : ENNReal) ∂pi := by
      apply lintegral_congr
      intro x
      exact add_tsub_cancel_of_le
        ((scheduledBalancedAccuracyGaussianAcceptance_le_half q I hsigma2 x).trans
          (by norm_num))
    _ = 1 := by simp

/-- The stationary scheduled balanced rejection probability is at most `121/128`. -/
theorem scheduledBalancedRejectedStateMeasure_mass_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ ≤
      ENNReal.ofReal (121 / 128 : ℝ) := by
  let acceptMass := scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ
  let rejectMass := scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ
  have hmass : acceptMass + rejectMass = 1 := by
    simpa [acceptMass, rejectMass] using
      scheduledBalancedAcceptedRejected_mass_add_eq_one q I hsigma2 pi
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

theorem scheduledBalancedAcceptedStateMeasure_le_half_smul
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) :
    scheduledBalancedAcceptedStateMeasure q I sigma2 mu ≤
      (2 : ENNReal)⁻¹ • mu := by
  rw [scheduledBalancedAcceptedStateMeasure_eq_half_smul]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA]
  calc
    (2 : ENNReal)⁻¹ *
        ∫⁻ x in A, scheduledAccuracyGaussianRejectionAcceptance
          q I sigma2 x ∂mu ≤
      (2 : ENNReal)⁻¹ * ∫⁻ _x in A, (1 : ENNReal) ∂mu := by
        gcongr
        exact scheduledAccuracyGaussianRejectionAcceptance_le_one
          q I hsigma2 _
    _ = (2 : ENNReal)⁻¹ * mu A := by rw [setLIntegral_one]

theorem scheduledBalancedRejectedStateMeasure_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) (mu : Measure (AmbientSpace q.n)) :
    scheduledBalancedRejectedStateMeasure q I sigma2 mu ≤ mu := by
  unfold scheduledBalancedRejectedStateMeasure
  apply Measure.le_iff.mpr
  intro A hA
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, 1 - scheduledBalancedAccuracyGaussianAcceptance
        q I sigma2 x ∂mu) ≤ ∫⁻ _x in A, (1 : ENNReal) ∂mu :=
      lintegral_mono fun _ => tsub_le_self
    _ = mu A := by rw [setLIntegral_one]

theorem scheduledBalancedAcceptedTargetSubmeasure_eq_mass_smul
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
    let acceptedTarget := accepted.map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)
    acceptedTarget = accepted Set.univ •
      scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi := by
  dsimp only
  let accepted := scheduledBalancedAcceptedStateMeasure q I sigma2 pi
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
    have hle := scheduledBalancedAcceptedStateMeasure_le_half_smul
      q I hsigma2 pi
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

#print axioms scheduledBalancedAcceptedStateMeasure_mass_ge
#print axioms scheduledBalancedAcceptedTargetSubmeasure_eq_mass_smul
#print axioms scheduledBalancedRejectedStateMeasure_mass_ge_half
#print axioms scheduledBalancedRejectedStateMeasure_mass_le

end ArlibCommunity.Algorithms.CV18
