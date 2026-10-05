/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyAcceptance

/-! # Rao--Blackwellized KLS correction for CV18

The executable rejection step can equivalently be used as an importance
weight on the unconditioned speedy chain.  This avoids conditioning the
threaded warm state after every accepted sample and makes the existing
dependent Markov-sum concentration theorem directly applicable.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The KLS acceptance probability, viewed as a real-valued observable. -/
noncomputable def accuracyAcceptanceWeight
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (x : AmbientSpace q.n) : ℝ :=
  (accuracyGaussianRejectionAcceptance q I sigma2 x).toReal

/-- Importance-weighted target observable evaluated on a speedy-chain state. -/
noncomputable def accuracyImportanceWeight
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (x : AmbientSpace q.n) : ℝ :=
  accuracyAcceptanceWeight q I sigma2 x *
    weight ((accuracyScaleFactor q)⁻¹ • x)

theorem measurable_accuracyAcceptanceWeight
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (accuracyAcceptanceWeight q I sigma2) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_accuracyGaussianRejectionAcceptance q I sigma2)

theorem accuracyAcceptanceWeight_nonneg
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (x : AmbientSpace q.n) :
    0 ≤ accuracyAcceptanceWeight q I sigma2 x :=
  ENNReal.toReal_nonneg

theorem accuracyAcceptanceWeight_le_one
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (x : AmbientSpace q.n) :
    accuracyAcceptanceWeight q I sigma2 x ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)

theorem measurable_accuracyImportanceWeight
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight) :
    Measurable (accuracyImportanceWeight q I sigma2 weight) := by
  exact (measurable_accuracyAcceptanceWeight q I sigma2).mul <|
    hweight.comp <| (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id

theorem accuracyImportanceWeight_nonneg
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    {weight : AmbientSpace q.n → ℝ} (hweight0 : ∀ x, 0 ≤ weight x)
    (x : AmbientSpace q.n) :
    0 ≤ accuracyImportanceWeight q I sigma2 weight x := by
  exact mul_nonneg (accuracyAcceptanceWeight_nonneg q I sigma2 x)
    (hweight0 _)

theorem accuracyImportanceWeight_le_one
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) {weight : AmbientSpace q.n → ℝ}
    (hweight0 : ∀ x, 0 ≤ weight x) (hweight1 : ∀ x, weight x ≤ 1)
    (x : AmbientSpace q.n) :
    accuracyImportanceWeight q I sigma2 weight x ≤ 1 := by
  calc
    accuracyImportanceWeight q I sigma2 weight x ≤
        1 * weight ((accuracyScaleFactor q)⁻¹ • x) := by
      exact mul_le_mul_of_nonneg_right
        (accuracyAcceptanceWeight_le_one q I hsigma2 x) (hweight0 _)
    _ ≤ 1 := by simpa using hweight1 ((accuracyScaleFactor q)⁻¹ • x)

/-- The mean of the real acceptance observable is the total mass of the
corresponding with-density subprobability measure. -/
theorem integral_accuracyAcceptanceWeight_eq_mass
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (mu : Measure (AmbientSpace q.n))
    [IsFiniteMeasure mu] :
    (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂mu) =
      ((mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2))
        Set.univ).toReal := by
  let accept := accuracyGaussianRejectionAcceptance q I sigma2
  have haccept : Measurable accept :=
    measurable_accuracyGaussianRejectionAcceptance q I sigma2
  have htop : ∀ᵐ x ∂mu, accept x < ⊤ :=
    Filter.Eventually.of_forall fun x => lt_of_le_of_lt
      (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)
      ENNReal.one_lt_top
  change (∫ x, (accept x).toReal ∂mu) = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    integral_toReal haccept.aemeasurable htop]

/-- The importance numerator is exactly the acceptance mass times the mean
under the normalized successful-output law.  This is the measure-theoretic
Rao--Blackwell identity behind replacing KLS retries by two empirical sums. -/
theorem integral_accuracyImportanceWeight_eq_acceptance_mul
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) [IsFiniteMeasure mu]
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (haccept0 :
      (mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2))
        Set.univ ≠ 0) :
    (∫ x, accuracyImportanceWeight q I sigma2 weight x ∂mu) =
      ((mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2))
          Set.univ).toReal *
        ∫ y, weight y ∂accuracyGaussianAcceptedTargetLaw q I sigma2 mu := by
  let accept := accuracyGaussianRejectionAcceptance q I sigma2
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let accepted : Measure (AmbientSpace q.n) :=
    (mu.withDensity accept).map scale
  let p := (mu.withDensity accept) Set.univ
  have haccept : Measurable accept :=
    measurable_accuracyGaussianRejectionAcceptance q I sigma2
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hpEq : accepted Set.univ = p := by
    dsimp [accepted, p]
    rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
  change p ≠ 0 at haccept0
  have hp0 : accepted Set.univ ≠ 0 := by rw [hpEq]; exact haccept0
  have hp_le : p ≤ mu Set.univ := by
    dsimp [p]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      (∫⁻ x, accept x ∂mu) ≤ ∫⁻ _x, (1 : ENNReal) ∂mu := by
        apply lintegral_mono
        exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2
      _ = mu Set.univ := lintegral_one
  have hptop : accepted Set.univ ≠ ⊤ := by
    rw [hpEq]
    exact ne_top_of_le_ne_top (measure_ne_top mu Set.univ) hp_le
  have hmeasure : accepted = accepted Set.univ •
      Arlib.condOn accepted Set.univ := by
    rw [Arlib.condOn_def, Measure.restrict_univ, smul_smul,
      ENNReal.mul_inv_cancel hp0 hptop, one_smul]
  have hleft :
      (∫ x, accuracyImportanceWeight q I sigma2 weight x ∂mu) =
        ∫ y, weight y ∂accepted := by
    change (∫ x, (accept x).toReal * weight (scale x) ∂mu) =
      ∫ y, weight y ∂accepted
    dsimp only [accepted]
    rw [integral_map hscale.aemeasurable hweight.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul haccept
      (Filter.Eventually.of_forall fun x => lt_of_le_of_lt
        (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x)
        ENNReal.one_lt_top)]
    simp only [smul_eq_mul]
  rw [hleft, hmeasure, integral_smul_measure, hpEq]
  rfl

/-- Dividing the importance numerator by the empirical target's acceptance
mass recovers exactly the mean under the normalized successful-output law. -/
theorem stationary_accuracyImportance_ratio_eq_accepted_mean
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    (∫ x, accuracyImportanceWeight q I sigma2 weight x ∂pi) /
        (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂pi) =
      ∫ y, weight y ∂accuracyGaussianAcceptedTargetLaw q I sigma2 pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  let p := (pi.withDensity
    (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ
  have hpLower : ENNReal.ofReal (7 / 64 : ℝ) ≤ p := by
    simpa [pi, K, delta, p] using
      accuracyPhase_stationary_acceptance_ge q I hsigma2
  have hp0 : p ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 64 : ℝ)).trans_le hpLower
  have hpReal0 : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨hp0, ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <| by
      dsimp [p]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      calc
        (∫⁻ x, accuracyGaussianRejectionAcceptance q I sigma2 x ∂pi) ≤
            ∫⁻ _x, (1 : ENNReal) ∂pi := by
          apply lintegral_mono
          exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2
        _ = pi Set.univ := lintegral_one⟩
  have hnum := integral_accuracyImportanceWeight_eq_acceptance_mul
    q I hsigma2 pi hweight hp0
  have hden := integral_accuracyAcceptanceWeight_eq_mass
    q I hsigma2 pi
  change _ / _ = _
  rw [hnum, hden]
  exact mul_div_cancel_left₀ _ hpReal0

/-- At speedy stationarity the normalized KLS output is already within the
concrete CV18 core-and-radial error of the desired truncated Gaussian.  The
positive mixing tolerance used by the general theorem costs only another
copy of the deliberately tiny `accuracyCoreError`; stationarity makes the
iterate itself exactly unchanged. -/
theorem accuracyPhase_stationaryAcceptedTargetLaw_tv
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    Arlib.TVLe
      (accuracyGaussianAcceptedTargetLaw q I sigma2 pi)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (96 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let mixError := accuracyCoreError q
  let deadline := 4 * ((Real.log (1 : ℝ) + 2 * Real.log (1 / mixError)) /
    (delta * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1
  let t := Nat.ceil deadline
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hwarm : Arlib.IsWarm (ENNReal.ofReal (1 : ℝ)) pi pi := by
    simpa using Arlib.IsWarm.refl pi
  have ht : 4 * ((Real.log (1 : ℝ) + 2 * Real.log (1 / mixError)) /
      (delta * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ) := by
    exact Nat.le_ceil deadline
  have hphase := accuracyGaussianAcceptedTargetLaw_tv_cv18
    q I hsigma2 (M := 1) (mixError := mixError) (mu0 := pi)
    (by norm_num) hwarm (accuracyCoreError_pos q)
    (accuracyCoreError_le_one_div_sixty_four q) (t := t) (by
      simpa [K, delta, pi, P, mixError, deadline, t] using ht)
  have hinv : Kernel.Invariant P pi := by
    dsimp [P, pi]
    exact (Arlib.MarkovChains.isReversible_lazy
      (Arlib.MarkovChains.isReversible_speedyMetropolisGaussian_prob
        (accuracyPhaseTruncatedBody_measurable q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)).invariant
  have hiterate : Arlib.MarkovChains.iterate P pi t = pi :=
    Arlib.MarkovChains.iterate_invariant hinv t
  dsimp only at hphase
  rw [show Arlib.MarkovChains.iterate P pi t = pi from hiterate] at hphase
  change Arlib.TVLe
      (accuracyGaussianAcceptedTargetLaw q I sigma2 pi)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (96 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16))
  change Arlib.TVLe
      (accuracyGaussianAcceptedTargetLaw q I sigma2 pi)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      _ at hphase
  convert hphase using 1 <;> ring

/-- Consequently, the ratio of the two stationary speedy-chain importance
means differs from the desired Gaussian expectation by only the explicit
CV18 truncation error. -/
theorem stationary_accuracyImportance_ratio_target_bias
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hweight0 : ∀ x, 0 ≤ weight x) (hweight1 : ∀ x, weight x ≤ 1) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
    |(∫ x, accuracyImportanceWeight q I sigma2 weight x ∂pi) /
          (∫ x, accuracyAcceptanceWeight q I sigma2 x ∂pi) -
        ∫ y, weight y
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))| ≤
      (96 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)).toReal := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let accept := accuracyGaussianRejectionAcceptance q I sigma2
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let accepted := (pi.withDensity accept).map scale
  let p := (pi.withDensity accept) Set.univ
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ 0 := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hpLower : ENNReal.ofReal (7 / 64 : ℝ) ≤ p := by
    simpa [pi, K, delta, p, accept] using
      accuracyPhase_stationary_acceptance_ge q I hsigma2
  have hp0 : p ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 64 : ℝ)).trans_le hpLower
  have hscale : Measurable scale := by
    dsimp [scale]
    fun_prop
  have haccept : Measurable accept := by
    exact measurable_accuracyGaussianRejectionAcceptance q I sigma2
  have hp_le : p ≤ pi Set.univ := by
    dsimp [p]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      (∫⁻ x, accept x ∂pi) ≤ ∫⁻ _x, (1 : ENNReal) ∂pi := by
        apply lintegral_mono
        intro x
        exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2 x
      _ = pi Set.univ := lintegral_one
  have hacceptedMass : accepted Set.univ = p := by
    dsimp [accepted]
    rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
  have haccepted0 : accepted Set.univ ≠ 0 := by rw [hacceptedMass]; exact hp0
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    rw [hacceptedMass]
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) hp_le
  let _ : IsProbabilityMeasure
      (accuracyGaussianAcceptedTargetLaw q I sigma2 pi) := by
    change IsProbabilityMeasure (Arlib.condOn accepted Set.univ)
    exact Arlib.isProbabilityMeasure_condOn accepted haccepted0 hacceptedTop
  have htv := accuracyPhase_stationaryAcceptedTargetLaw_tv q I hsigma2
  have hinter := htv.integral_le
    (ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩)
    hweight hweight0 hweight1
  have hratio := stationary_accuracyImportance_ratio_eq_accepted_mean
    q I hsigma2 hweight
  rw [hratio]
  exact hinter

end ArlibCommunity.Algorithms.CV18
