/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCorrectedErrorAllocation

/-!
# Schedule-targeted KLS accuracy parameters

The old KLS core and radial errors depend only on `n` and `eps`, whereas the
per-sample exact-chance budget also depends on the (unbounded) cooling-schedule
length.  This file chooses both errors from that actual per-sample budget and
defines the matching radial body and proposal radius.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- Core error consuming one eighth of the per-sample budget after the KLS
factor `96`. -/
noncomputable def figureOneScheduledCoreError (q : VolumeParams) : ℝ :=
  figureOnePerSampleMixingError q / 768

/-- Radial truncation error consuming a second eighth of the per-sample
budget. -/
noncomputable def figureOneScheduledRadialError (q : VolumeParams) : ℝ :=
  figureOnePerSampleMixingError q / 8

theorem figureOneScheduledCoreError_pos (q : VolumeParams) :
    0 < figureOneScheduledCoreError q := by
  unfold figureOneScheduledCoreError
  positivity [figureOnePerSampleMixingError_pos q]

theorem figureOneScheduledRadialError_pos (q : VolumeParams) :
    0 < figureOneScheduledRadialError q := by
  unfold figureOneScheduledRadialError
  positivity [figureOnePerSampleMixingError_pos q]

theorem figureOneScheduledCoreError_le_one_div_sixteen (q : VolumeParams) :
    figureOneScheduledCoreError q ≤ 1 / 16 := by
  unfold figureOneScheduledCoreError
  nlinarith [figureOnePerSampleMixingError_le_one q]

theorem figureOneScheduledCore_combined_le (q : VolumeParams) :
    8 * ENNReal.ofReal (figureOneScheduledCoreError q) +
        4 * ENNReal.ofReal (figureOneScheduledCoreError q) ≤
      ENNReal.ofReal (1 / 4 : ℝ) := by
  have hcore := figureOneScheduledCoreError_pos q
  rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_add (by positivity :
      0 ≤ 8 * figureOneScheduledCoreError q)
      (by positivity : 0 ≤ 4 * figureOneScheduledCoreError q)]
  apply ENNReal.ofReal_le_ofReal
  unfold figureOneScheduledCoreError
  nlinarith [figureOnePerSampleMixingError_le_one q]

/-- The stationary accepted-target correction now fits the quarter reserved
for it, uniformly in the schedule length and hence in `q.roundness`. -/
theorem figureOneScheduledTargetError_le (q : VolumeParams) :
    96 * ENNReal.ofReal (figureOneScheduledCoreError q) +
        ENNReal.ofReal (figureOneScheduledRadialError q) ≤
      figureOneCorrectedTargetBudget q := by
  have hnu := figureOnePerSampleMixingError_pos q
  have hleftTop :
      96 * ENNReal.ofReal (figureOneScheduledCoreError q) +
          ENNReal.ofReal (figureOneScheduledRadialError q) ≠ ∞ := by
    exact ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩
  have hrightTop : figureOneCorrectedTargetBudget q ≠ ∞ := by
    apply ENNReal.div_ne_top
    · simp [figureOneCorrectedTransitionBudget]
    · norm_num
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    figureOneCorrectedTargetBudget, figureOneCorrectedTransitionBudget,
    ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal (figureOneScheduledCoreError_pos q).le,
    ENNReal.toReal_ofReal (figureOneScheduledRadialError_pos q).le,
    ENNReal.toReal_ofReal hnu.le]
  unfold figureOneScheduledCoreError figureOneScheduledRadialError
  ring_nf
  exact le_rfl

/-- A common logarithmic scale large enough for both the core and radial
accuracy requirements. -/
noncomputable def figureOneScheduledAccuracyLog (q : VolumeParams) : ℝ :=
  max
    (protectedLog ((q.n : ℝ) / figureOneScheduledCoreError q))
    (protectedLog ((q.n : ℝ) / figureOneScheduledRadialError q))

theorem figureOneScheduledAccuracyLog_one_le (q : VolumeParams) :
    1 ≤ figureOneScheduledAccuracyLog q := by
  unfold figureOneScheduledAccuracyLog
  exact le_trans (le_max_left _ _)
    (le_max_left _ _)

noncomputable def figureOneScheduledPhaseRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  32 * Real.sqrt sigma2 *
    Real.sqrt ((q.n : ℝ) * figureOneScheduledAccuracyLog q)

noncomputable def figureOneScheduledPhaseBody
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Set (AmbientSpace q.n) :=
  truncatedBody q I ∩
    Metric.closedBall 0 (figureOneScheduledPhaseRadius q sigma2)

noncomputable def figureOneScheduledPhaseInradius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min 1 (figureOneScheduledPhaseRadius q sigma2)

noncomputable def figureOneScheduledProposalRadius
    (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min (Real.sqrt sigma2) 1 /
    (4096 * Real.sqrt
      ((q.n : ℝ) * figureOneScheduledAccuracyLog q))

/-- Exact generic speedy-mixing cost after the schedule-targeted proposal
radius is substituted. -/
noncomputable def figureOneScheduledWalkRequirement
    (q : VolumeParams) (sigma2 M mixError : ℝ) : ℝ :=
  4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
    (figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

theorem figureOneScheduledPhaseRadius_pos
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < figureOneScheduledPhaseRadius q sigma2 := by
  unfold figureOneScheduledPhaseRadius
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  positivity [figureOneScheduledAccuracyLog_one_le q]

theorem figureOneScheduledProposalRadius_pos
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < figureOneScheduledProposalRadius q sigma2 := by
  unfold figureOneScheduledProposalRadius
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  positivity [figureOneScheduledAccuracyLog_one_le q]

theorem figureOneScheduledPhaseBody_measurable
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    MeasurableSet (figureOneScheduledPhaseBody q I sigma2) :=
  (truncatedBody_measurable q I).inter measurableSet_closedBall

theorem figureOneScheduledPhaseBody_convex
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Convex ℝ (figureOneScheduledPhaseBody q I sigma2) :=
  (truncatedVolumeInput q I).body.convex.inter (convex_closedBall 0 _)

theorem figureOneScheduledPhaseBody_isCompact
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    IsCompact (figureOneScheduledPhaseBody q I sigma2) :=
  (truncatedVolumeInput q I).body.isCompact.inter_right isClosed_closedBall

theorem figureOneScheduledPhaseInradius_pos
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    0 < figureOneScheduledPhaseInradius q sigma2 := by
  unfold figureOneScheduledPhaseInradius
  exact lt_min one_pos (figureOneScheduledPhaseRadius_pos q hsigma2)

theorem ball_scheduledPhaseInradius_subset
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Metric.ball (0 : AmbientSpace q.n)
      (figureOneScheduledPhaseInradius q sigma2) ⊆
        figureOneScheduledPhaseBody q I sigma2 := by
  intro x hx
  have hdist : dist x 0 < figureOneScheduledPhaseInradius q sigma2 := by
    simpa [dist_comm] using hx
  refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
  · simpa [unitBall, Metric.mem_closedBall, dist_zero_right] using
      (le_of_lt hdist).trans (min_le_left _ _)
  · rw [Metric.mem_closedBall, dist_zero_right]
    simpa [dist_zero_right] using
      (le_of_lt hdist).trans (min_le_right _ _)

theorem figureOneScheduledPhaseBody_volume_ne_zero
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    volume (figureOneScheduledPhaseBody q I sigma2) ≠ 0 := by
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume (0 : AmbientSpace q.n)
    (figureOneScheduledPhaseInradius_pos q hsigma2)).trans_le
      (measure_mono (ball_scheduledPhaseInradius_subset q I sigma2))

theorem figureOneScheduledPhaseBody_volume_ne_top
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    volume (figureOneScheduledPhaseBody q I sigma2) ≠ ∞ :=
  (figureOneScheduledPhaseBody_isCompact q I sigma2).measure_lt_top.ne

theorem figureOneScheduledProposalRadius_le_inradiusStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hsmall : figureOneScheduledPhaseRadius q sigma2 ≤ 1) :
    figureOneScheduledProposalRadius q sigma2 ≤
      figureOneScheduledPhaseInradius q sigma2 / (2 * (q.n : ℝ)) := by
  let sigma := Real.sqrt sigma2
  let L := figureOneScheduledAccuracyLog q
  let b := Real.sqrt ((q.n : ℝ) * L)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsigma2
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ L := by
    simpa [L] using figureOneScheduledAccuracyLog_one_le q
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ^ 2 = (q.n : ℝ) * L := by
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  have hrho : figureOneScheduledPhaseInradius q sigma2 =
      32 * sigma * b := by
    rw [figureOneScheduledPhaseInradius, min_eq_right hsmall]
    rfl
  unfold figureOneScheduledProposalRadius
  change min sigma 1 / (4096 * b) ≤
    figureOneScheduledPhaseInradius q sigma2 / (2 * (q.n : ℝ))
  rw [hrho]
  apply (div_le_iff₀ (by positivity : 0 < 4096 * b)).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (q.n : ℝ))).2
  calc
    min sigma 1 * (2 * (q.n : ℝ)) ≤
        sigma * (2 * (q.n : ℝ)) := by gcongr; exact min_le_left _ _
    _ ≤ (32 * sigma * b) * (4096 * b) := by
      rw [show (32 * sigma * b) * (4096 * b) =
        sigma * (131072 * b ^ 2) by ring, hb2]
      apply mul_le_mul_of_nonneg_left _ hsigma.le
      nlinarith

/-- The matched body/radius pair preserves the conductance product bound, so
the old polynomial mixing-rate proof only acquires the new logarithm. -/
theorem figureOneScheduledRadius_mul_proposal_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneScheduledPhaseRadius q sigma2 *
        figureOneScheduledProposalRadius q sigma2 ≤ sigma2 / 9 := by
  let b := Real.sqrt ((q.n : ℝ) * figureOneScheduledAccuracyLog q)
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hb : 0 < b := by
    dsimp [b]
    positivity [figureOneScheduledAccuracyLog_one_le q]
  have hmin : min (Real.sqrt sigma2) 1 ≤ Real.sqrt sigma2 := min_le_left _ _
  have hcancel :
      figureOneScheduledPhaseRadius q sigma2 *
          figureOneScheduledProposalRadius q sigma2 =
        Real.sqrt sigma2 * min (Real.sqrt sigma2) 1 / 128 := by
    unfold figureOneScheduledPhaseRadius figureOneScheduledProposalRadius
    change (32 * Real.sqrt sigma2 * b) *
      (min (Real.sqrt sigma2) 1 / (4096 * b)) = _
    field_simp [hb.ne']
    ring
  rw [hcancel]
  have hsqrt := Real.sq_sqrt hsigma2.le
  have hmul : Real.sqrt sigma2 * min (Real.sqrt sigma2) 1 ≤ sigma2 := by
    calc
      _ ≤ Real.sqrt sigma2 * Real.sqrt sigma2 :=
        mul_le_mul_of_nonneg_left hmin (Real.sqrt_nonneg _)
      _ = sigma2 := by nlinarith
  nlinarith

/-- The enlarged schedule-targeted body has precisely the radial error used
in `figureOneScheduledTargetError_le`. -/
theorem figureOneScheduled_tail_coefficient_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Real.exp (-(figureOneScheduledPhaseRadius q sigma2) ^ 2 /
        (4 * sigma2)) * Real.sqrt 2 ^ q.n ≤
      figureOneScheduledRadialError q := by
  let L := figureOneScheduledAccuracyLog q
  let radial := figureOneScheduledRadialError q
  let ratio := (q.n : ℝ) / radial
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hn1 : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hr : 0 < radial := by
    simpa [radial] using figureOneScheduledRadialError_pos q
  have hrle : radial ≤ 1 / 8 := by
    dsimp [radial, figureOneScheduledRadialError]
    nlinarith [figureOnePerSampleMixingError_le_one q]
  have hratio : 1 < ratio := by
    dsimp [ratio]
    rw [lt_div_iff₀ hr]
    nlinarith
  have hlog : 0 < Real.log ratio := Real.log_pos hratio
  have hL1 : 1 ≤ L := by
    simpa [L] using figureOneScheduledAccuracyLog_one_le q
  have hLlog : Real.log ratio ≤ L := by
    dsimp [L, ratio, radial, figureOneScheduledAccuracyLog]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hradius :
      (figureOneScheduledPhaseRadius q sigma2) ^ 2 / (4 * sigma2) =
        256 * (q.n : ℝ) * L := by
    unfold figureOneScheduledPhaseRadius
    change (32 * Real.sqrt sigma2 *
      Real.sqrt ((q.n : ℝ) * L)) ^ 2 / (4 * sigma2) = _
    rw [mul_pow, mul_pow, Real.sq_sqrt hsigma2.le,
      Real.sq_sqrt (mul_nonneg hn.le (le_trans zero_le_one hL1))]
    field_simp [hsigma2.ne']
    ring
  have hsqrt2 : Real.sqrt 2 ≤ Real.exp 1 := by
    have hsqrt2le2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 2,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hsqrt2le2.trans Real.exp_one_gt_two.le
  have hpow : Real.sqrt 2 ^ q.n ≤ Real.exp (q.n : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ q.n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt2 _
      _ = Real.exp (q.n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hexp :
      Real.exp (-(256 * (q.n : ℝ) * L) + (q.n : ℝ)) ≤
        Real.exp (-Real.log ratio) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinv : Real.exp (-Real.log ratio) = radial / (q.n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (lt_trans zero_lt_one hratio)]
    dsimp [ratio]
    field_simp
  rw [show -(figureOneScheduledPhaseRadius q sigma2) ^ 2 /
      (4 * sigma2) =
        -((figureOneScheduledPhaseRadius q sigma2) ^ 2 /
          (4 * sigma2)) by ring, hradius]
  calc
    Real.exp (-(256 * (q.n : ℝ) * L)) * Real.sqrt 2 ^ q.n ≤
        Real.exp (-(256 * (q.n : ℝ) * L)) * Real.exp (q.n : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-(256 * (q.n : ℝ) * L) + (q.n : ℝ)) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-Real.log ratio) := hexp
    _ = radial / (q.n : ℝ) := hinv
    _ ≤ radial := by
      exact div_le_self hr.le hn1
    _ = figureOneScheduledRadialError q := rfl

theorem figureOneScheduled_gaussianIntegral_tail_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (∫ x in truncatedBody q I \
        Metric.closedBall 0 (figureOneScheduledPhaseRadius q sigma2),
        gaussianDensity sigma2 x) ≤
      figureOneScheduledRadialError q *
        gaussianIntegral (truncatedBody q I) sigma2 := by
  have hK := truncatedBody_measurable q I
  have htail := gaussianIntegral_tail_radius_le hK hsigma2
    (figureOneScheduledPhaseRadius_pos q hsigma2).le
  have hscale := gaussianIntegral_scaling_le (truncatedBody q I) hK
    (truncatedVolumeInput q I).body.convex
    (unitBall_subset_truncatedBody q I (by simp [unitBall]))
    hsigma2 (by linarith : sigma2 ≤ 2 * sigma2)
  have hsqrt : Real.sqrt ((2 * sigma2) / sigma2) = Real.sqrt 2 := by
    congr 1
    field_simp [hsigma2.ne']
  rw [hsqrt] at hscale
  calc
    _ ≤ Real.exp (-(figureOneScheduledPhaseRadius q sigma2) ^ 2 /
          (4 * sigma2)) *
        gaussianIntegral (truncatedBody q I) (2 * sigma2) := htail
    _ ≤ Real.exp (-(figureOneScheduledPhaseRadius q sigma2) ^ 2 /
          (4 * sigma2)) *
        (Real.sqrt 2 ^ q.n *
          gaussianIntegral (truncatedBody q I) sigma2) := by gcongr
    _ = (Real.exp (-(figureOneScheduledPhaseRadius q sigma2) ^ 2 /
          (4 * sigma2)) * Real.sqrt 2 ^ q.n) *
        gaussianIntegral (truncatedBody q I) sigma2 := by ring
    _ ≤ figureOneScheduledRadialError q *
        gaussianIntegral (truncatedBody q I) sigma2 := by
      exact mul_le_mul_of_nonneg_right
        (figureOneScheduled_tail_coefficient_le q hsigma2)
        (gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2).le

theorem truncatedGaussianProbability_scheduledPhase_compl_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (figureOneScheduledPhaseBody q I sigma2)ᶜ ≤
        ENNReal.ofReal (figureOneScheduledRadialError q) := by
  let K : Set (AmbientSpace q.n) := truncatedBody q I
  let R : ℝ := figureOneScheduledPhaseRadius q sigma2
  let Z : ℝ := gaussianIntegral K sigma2
  let nu : ℝ := figureOneScheduledRadialError q
  have hZ : 0 < Z := by
    dsimp [Z, K]
    exact gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2
  have hnu : 0 ≤ nu := by
    exact (figureOneScheduledRadialError_pos q).le
  have hset : (figureOneScheduledPhaseBody q I sigma2)ᶜ ∩ K =
      K \ Metric.closedBall 0 R := by
    ext x
    simp only [figureOneScheduledPhaseBody, K, R, mem_inter_iff,
      mem_compl_iff, mem_diff]
    tauto
  rw [truncatedGaussianProbability_apply q I hsigma2
    (figureOneScheduledPhaseBody_measurable q I sigma2).compl]
  change (ENNReal.ofReal Z)⁻¹ *
      ∫⁻ x in (figureOneScheduledPhaseBody q I sigma2)ᶜ ∩ K,
        ENNReal.ofReal (gaussianDensity sigma2 x) ≤ ENNReal.ofReal nu
  rw [hset]
  have hf := integrable_gaussianDensity (n := q.n) hsigma2
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  have htailReal :
      (∫ x in K \ Metric.closedBall 0 R, gaussianDensity sigma2 x) ≤
        nu * Z := by
    simpa [K, R, nu, Z] using
      figureOneScheduled_gaussianIntegral_tail_le q I hsigma2
  have htailENN : ENNReal.ofReal
      (∫ x in K \ Metric.closedBall 0 R, gaussianDensity sigma2 x) ≤
        ENNReal.ofReal nu * ENNReal.ofReal Z := by
    rw [← ENNReal.ofReal_mul hnu]
    exact ENNReal.ofReal_le_ofReal htailReal
  calc
    _ ≤ (ENNReal.ofReal Z)⁻¹ *
        (ENNReal.ofReal nu * ENNReal.ofReal Z) :=
      mul_le_mul' le_rfl htailENN
    _ = ENNReal.ofReal nu := by
      have hZ0 : ENNReal.ofReal Z ≠ 0 :=
        (ENNReal.ofReal_pos.2 hZ).ne'
      have hZtop : ENNReal.ofReal Z ≠ ∞ := ENNReal.ofReal_ne_top
      calc
        _ = ENNReal.ofReal nu *
            ((ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal Z) := by ac_rfl
        _ = ENNReal.ofReal nu := by
          rw [ENNReal.inv_mul_cancel hZ0 hZtop, mul_one]

/-- Full probability-level radial replacement at the schedule-dependent
budget. -/
theorem TVLe.scheduledPhase_condOn_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Arlib.TVLe
      (Arlib.condOn
        (truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))
        (figureOneScheduledPhaseBody q I sigma2))
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (ENNReal.ofReal (figureOneScheduledRadialError q)) := by
  let mu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let S : Set (AmbientSpace q.n) :=
    figureOneScheduledPhaseBody q I sigma2
  let epsilon := ENNReal.ofReal (figureOneScheduledRadialError q)
  have hS : MeasurableSet S := figureOneScheduledPhaseBody_measurable q I sigma2
  have hepsilon : epsilon < 1 := by
    rw [ENNReal.ofReal_lt_one]
    unfold figureOneScheduledRadialError
    nlinarith [figureOnePerSampleMixingError_pos q,
      figureOnePerSampleMixingError_le_one q]
  have hcompl : mu Sᶜ ≤ epsilon := by
    simpa [mu, S, epsilon] using
      truncatedGaussianProbability_scheduledPhase_compl_le q I hsigma2
  have hS0 : mu S ≠ 0 := by
    intro hzero
    have hsum : mu S + mu Sᶜ = 1 := by
      rw [measure_add_measure_compl hS, measure_univ]
    have hone : mu Sᶜ = 1 := by simpa [hzero] using hsum
    exact (not_le_of_gt hepsilon) (hone ▸ hcompl)
  exact TVLe.condOn_of_compl_le_cv18 mu hS hS0 hcompl

/-- The smaller proposal satisfies KLS's paper-step condition at the
schedule-targeted core error. -/
theorem figureOneScheduledProposalRadius_le_coreStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneScheduledProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt ((q.n : ℝ) *
        Real.log ((q.n : ℝ) / figureOneScheduledCoreError q))) := by
  let L := figureOneScheduledAccuracyLog q
  let d := Real.sqrt ((q.n : ℝ) *
    Real.log ((q.n : ℝ) / figureOneScheduledCoreError q))
  let b := Real.sqrt ((q.n : ℝ) * L)
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hcore := figureOneScheduledCoreError_pos q
  have hratio : 1 < (q.n : ℝ) / figureOneScheduledCoreError q := by
    rw [lt_div_iff₀ hcore]
    have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    nlinarith [figureOneScheduledCoreError_le_one_div_sixteen q]
  have hlog : 0 < Real.log ((q.n : ℝ) /
      figureOneScheduledCoreError q) := Real.log_pos hratio
  have hLlog : Real.log ((q.n : ℝ) / figureOneScheduledCoreError q) ≤ L := by
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : 0 < b := by
    dsimp [b, L]
    positivity [figureOneScheduledAccuracyLog_one_le q]
  have hdb : d ≤ b := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hLlog hn.le
  unfold figureOneScheduledProposalRadius
  change min (Real.sqrt sigma2) 1 / (4096 * b) ≤ 1 / (8 * d)
  calc
    _ ≤ 1 / (4096 * b) := by
      gcongr
      exact min_le_right _ _
    _ ≤ 1 / (8 * d) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith

#print axioms figureOneScheduledTargetError_le
#print axioms figureOneScheduledRadius_mul_proposal_le
#print axioms figureOneScheduled_tail_coefficient_le
#print axioms TVLe.scheduledPhase_condOn_truncatedGaussian
#print axioms figureOneScheduledProposalRadius_le_coreStep

end ArlibCommunity.Algorithms.CV18
