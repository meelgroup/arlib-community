import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStrongStepMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofWarmStart

/-!
# Accuracy-dependent radial cores for CV18

The paper analyzes `K ∩ 4 sigma sqrt(n) B`, which gives only an
accuracy-independent tail.  For the executable theorem we instead use the
larger radius `32 sigma sqrt(n L)`, where
`L = protectedLog (n / eps)`.  Figure 1's `1 / (4096 sqrt(n L))`
proposal factor keeps `R * delta` bounded by `sigma^2 / 128`, so the same
conductance argument applies while the discarded Gaussian tail becomes small
enough for global error composition.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

noncomputable def accuracyPhaseRadius (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  32 * Real.sqrt sigma2 *
    Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))

noncomputable def accuracyPhaseTruncatedBody (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) : Set (AmbientSpace q.n) :=
  truncatedBody q I ∩ Metric.closedBall 0 (accuracyPhaseRadius q sigma2)

/-- The largest centered inball inherited simultaneously from the input's
unit inball and the accuracy-dependent radial cutoff. -/
noncomputable def accuracyPhaseInradius (q : VolumeParams) (sigma2 : ℝ) : ℝ :=
  min 1 (accuracyPhaseRadius q sigma2)

theorem accuracyPhaseRadius_pos (q : VolumeParams) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) : 0 < accuracyPhaseRadius q sigma2 := by
  unfold accuracyPhaseRadius
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 0 < protectedLog ((q.n : ℝ) / q.eps) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem accuracyPhaseTruncatedBody_measurable (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    MeasurableSet (accuracyPhaseTruncatedBody q I sigma2) :=
  (truncatedBody_measurable q I).inter measurableSet_closedBall

theorem accuracyPhaseTruncatedBody_convex (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    Convex ℝ (accuracyPhaseTruncatedBody q I sigma2) :=
  (truncatedVolumeInput q I).body.convex.inter (convex_closedBall 0 _)

theorem accuracyPhaseTruncatedBody_isCompact (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    IsCompact (accuracyPhaseTruncatedBody q I sigma2) :=
  (truncatedVolumeInput q I).body.isCompact.inter_right isClosed_closedBall

theorem accuracyPhaseTruncatedBody_volume_ne_top (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    volume (accuracyPhaseTruncatedBody q I sigma2) ≠ ⊤ :=
  (accuracyPhaseTruncatedBody_isCompact q I sigma2).measure_lt_top.ne

theorem accuracyPhaseTruncatedBody_norm_le (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} {x : AmbientSpace q.n}
    (hx : x ∈ accuracyPhaseTruncatedBody q I sigma2) :
    ‖x‖ ≤ accuracyPhaseRadius q sigma2 := by
  simpa [accuracyPhaseTruncatedBody, Metric.mem_closedBall, dist_zero_right] using hx.2

theorem accuracyPhaseTruncatedBody_volume_ne_zero (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    volume (accuracyPhaseTruncatedBody q I sigma2) ≠ 0 := by
  have hradius : 0 < accuracyPhaseRadius q sigma2 :=
    accuracyPhaseRadius_pos q hsigma2
  have hsmall : 0 < min 1 (accuracyPhaseRadius q sigma2) :=
    lt_min one_pos hradius
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume (0 : AmbientSpace q.n) hsmall).trans_le
    (measure_mono fun x hx => by
      have hdist_one : dist x 0 ≤ 1 :=
        (le_of_lt hx).trans (min_le_left _ _)
      have hdist_radius : dist x 0 ≤ accuracyPhaseRadius q sigma2 :=
        (le_of_lt hx).trans (min_le_right _ _)
      refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
      · simpa [unitBall, Metric.mem_closedBall, dist_comm] using hdist_one
      · simpa [Metric.mem_closedBall, dist_comm] using hdist_radius)

theorem accuracyPhaseInradius_pos (q : VolumeParams) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) : 0 < accuracyPhaseInradius q sigma2 := by
  exact lt_min one_pos (accuracyPhaseRadius_pos q hsigma2)

theorem ball_accuracyPhaseInradius_subset (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    Metric.ball (0 : AmbientSpace q.n) (accuracyPhaseInradius q sigma2) ⊆
      accuracyPhaseTruncatedBody q I sigma2 := by
  intro x hx
  have hdist : dist x 0 < accuracyPhaseInradius q sigma2 := by
    simpa [dist_comm] using hx
  have hnorm : ‖x‖ < accuracyPhaseInradius q sigma2 := by
    simpa [dist_zero_right] using hdist
  refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
  · rw [unitBall, Metric.mem_closedBall, dist_zero_right]
    exact hnorm.le.trans (min_le_left _ _)
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm.le.trans (min_le_right _ _)

/-- Figure 1's proposal radius satisfies the Lovász--Vempala average-local-
conductance scale relative to the actual (possibly sub-unit) phase inball. -/
theorem figureOneProposalRadius_le_accuracyPhaseLVStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      min (Real.sqrt sigma2) (accuracyPhaseInradius q sigma2) /
        (4096 * Real.sqrt q.n) := by
  let sigma : ℝ := Real.sqrt sigma2
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsigma2
  have hnR : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hnL : 1 ≤ (q.n : ℝ) * L := by nlinarith
  have hsqrt1 : 1 ≤ Real.sqrt ((q.n : ℝ) * L) := by
    simpa using Real.sqrt_le_sqrt hnL
  have hsigmaR : sigma ≤ accuracyPhaseRadius q sigma2 := by
    unfold accuracyPhaseRadius
    change sigma ≤ 32 * sigma * Real.sqrt ((q.n : ℝ) * L)
    nlinarith
  have hmin : min sigma (accuracyPhaseInradius q sigma2) = min sigma 1 := by
    apply le_antisymm
    · exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    · apply le_min (min_le_left _ _)
      exact le_min (min_le_right _ _) ((min_le_left _ _).trans hsigmaR)
  rw [hmin]
  unfold figureOneProposalRadius
  change min sigma 1 / (4096 * Real.sqrt ((q.n : ℝ) * L)) ≤
    min sigma 1 / (4096 * Real.sqrt q.n)
  apply div_le_div_of_nonneg_left (le_min hsigma.le zero_le_one)
  · positivity
  · have hmul : (q.n : ℝ) ≤ (q.n : ℝ) * L := by nlinarith
    nlinarith [Real.sqrt_le_sqrt hmul]

/-- Figure 1's proposal is also small enough for the exact homothetic-core
rejection used to turn a speedy sample into an ordinary Gaussian sample. -/
theorem figureOneProposalRadius_le_accuracyPhaseCoreStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hsmall : accuracyPhaseRadius q sigma2 ≤ 1) :
    figureOneProposalRadius q sigma2 ≤
      accuracyPhaseInradius q sigma2 / (2 * (q.n : ℝ)) := by
  let sigma : ℝ := Real.sqrt sigma2
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  let b : ℝ := Real.sqrt ((q.n : ℝ) * L)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsigma2
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ^ 2 = (q.n : ℝ) * L := by
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  have hrho : accuracyPhaseInradius q sigma2 = 32 * sigma * b := by
    rw [accuracyPhaseInradius, min_eq_right hsmall]
    rfl
  have hmin : min sigma 1 ≤ sigma := min_le_left _ _
  unfold figureOneProposalRadius
  change min sigma 1 / (4096 * b) ≤
    accuracyPhaseInradius q sigma2 / (2 * (q.n : ℝ))
  rw [hrho]
  apply (div_le_iff₀ (by positivity : 0 < 4096 * b)).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (q.n : ℝ))).2
  calc
    min sigma 1 * (2 * (q.n : ℝ)) ≤
        sigma * (2 * (q.n : ℝ)) := by gcongr
    _ ≤ (32 * sigma * b) * (4096 * b) := by
      rw [show (32 * sigma * b) * (4096 * b) =
          sigma * (131072 * b ^ 2) by ring, hb2]
      apply mul_le_mul_of_nonneg_left _ hsigma.le
      nlinarith

/-- The Gaussian-weighted average local conductance on every accuracy phase
core is at least one half, including phases whose inradius is below one. -/
theorem half_mul_gaussianWeight_le_accuracyPhaseEllGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ENNReal.ofReal (1 / 2) *
        (∫⁻ x in accuracyPhaseTruncatedBody q I sigma2,
          Arlib.MarkovChains.gaussianWeight sigma2 x) ≤
      Arlib.MarkovChains.ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2 Set.univ := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have h :=
    Arlib.MarkovChains.half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct_radius
      hn2 (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isClosed
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      (accuracyPhaseInradius_pos q hsigma2)
      (ball_accuracyPhaseInradius_subset q I sigma2)
      hsigma hdelta (figureOneProposalRadius_le_accuracyPhaseLVStep q hsigma2)
  simpa [Real.sq_sqrt hsigma2.le] using h

theorem gaussianDensity_tail_radius_pointwise {n : ℕ} {s R : ℝ}
    (hs : 0 < s) (hR : 0 ≤ R) {x : AmbientSpace n}
    (hx : x ∉ Metric.closedBall 0 R) :
    gaussianDensity s x ≤
      Real.exp (-(R ^ 2) / (4 * s)) * gaussianDensity (2 * s) x := by
  have hxnorm : R < ‖x‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hx_sq : R ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg x]
  rw [gaussianDensity, gaussianDensity, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  field_simp
  nlinarith

/-- Radial tail domination on any measurable set: one half of the Gaussian
exponent pays for the radius and the other half becomes a variance-doubled
Gaussian. -/
theorem gaussianIntegral_tail_radius_le {n : ℕ}
    {K : Set (AmbientSpace n)} (hK : MeasurableSet K)
    {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) :
    (∫ x in K \ Metric.closedBall 0 R, gaussianDensity s x) ≤
      Real.exp (-(R ^ 2) / (4 * s)) * gaussianIntegral K (2 * s) := by
  let c : ℝ := Real.exp (-(R ^ 2) / (4 * s))
  have hf := integrable_gaussianDensity (n := n) hs
  have hg := integrable_gaussianDensity (n := n) (show 0 < 2 * s by positivity)
  have htail : MeasurableSet (K \ Metric.closedBall (0 : AmbientSpace n) R) :=
    hK.diff measurableSet_closedBall
  calc
    (∫ x in K \ Metric.closedBall 0 R, gaussianDensity s x) ≤
        ∫ x in K \ Metric.closedBall 0 R, c * gaussianDensity (2 * s) x := by
      apply MeasureTheory.setIntegral_mono_on hf.integrableOn
        (hg.const_mul c).integrableOn htail
      intro x hx
      exact gaussianDensity_tail_radius_pointwise hs hR hx.2
    _ ≤ ∫ x in K, c * gaussianDensity (2 * s) x := by
      apply MeasureTheory.setIntegral_mono_set (hg.const_mul c).integrableOn
      · filter_upwards with x
        exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      · filter_upwards with x
        exact fun hx => hx.1
    _ = c * ∫ x in K, gaussianDensity (2 * s) x := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rw [gaussianIntegral_eq_setIntegral hK]

theorem accuracyPhase_tail_coefficient_le (q : VolumeParams)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Real.exp (-(accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2)) *
        Real.sqrt 2 ^ q.n ≤ (q.eps / (q.n : ℝ)) ^ 16 := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  let ratio : ℝ := (q.n : ℝ) / q.eps
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hratio : 0 < ratio := by
    dsimp [ratio]
    exact div_pos hn0 q.heps.1
  have hL1 : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hLlog : Real.log ratio ≤ L := by
    dsimp [L, ratio]
    exact le_max_right _ _
  have hsqs : Real.sqrt sigma2 ^ 2 = sigma2 := Real.sq_sqrt hsigma2.le
  have hnL0 : 0 ≤ (q.n : ℝ) * L :=
    mul_nonneg hn0.le (le_trans zero_le_one hL1)
  have hsqnL : Real.sqrt ((q.n : ℝ) * L) ^ 2 = (q.n : ℝ) * L :=
    Real.sq_sqrt hnL0
  have hradius :
      (accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2) =
        256 * (q.n : ℝ) * L := by
    unfold accuracyPhaseRadius
    change (32 * Real.sqrt sigma2 *
      Real.sqrt ((q.n : ℝ) * L)) ^ 2 / (4 * sigma2) = _
    rw [mul_pow, mul_pow, hsqs, hsqnL]
    field_simp [hsigma2.ne']
    ring
  have hsqrt2 : Real.sqrt 2 ≤ Real.exp 1 := by
    have hsqrt2le2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hsqrt2le2.trans Real.exp_one_gt_two.le
  have hpow : Real.sqrt 2 ^ q.n ≤ Real.exp (q.n : ℝ) := by
    calc
      Real.sqrt 2 ^ q.n ≤ Real.exp 1 ^ q.n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt2 _
      _ = Real.exp (q.n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hexact : Real.exp (-16 * Real.log ratio) =
      (q.eps / (q.n : ℝ)) ^ 16 := by
    have hrinv : ratio⁻¹ = q.eps / (q.n : ℝ) := by
      dsimp [ratio]
      field_simp
    calc
      Real.exp (-16 * Real.log ratio) =
          Real.exp (-Real.log ratio) ^ 16 := by
        rw [show -16 * Real.log ratio =
          (16 : ℕ) * (-Real.log ratio) by norm_num, Real.exp_nat_mul]
      _ = ratio⁻¹ ^ 16 := by rw [Real.exp_neg, Real.exp_log hratio]
      _ = (q.eps / (q.n : ℝ)) ^ 16 := by rw [hrinv]
  rw [show -(accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2) =
      -((accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2)) by ring, hradius]
  calc
    Real.exp (-(256 * (q.n : ℝ) * L)) * Real.sqrt 2 ^ q.n ≤
        Real.exp (-(256 * (q.n : ℝ) * L)) * Real.exp (q.n : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-(256 * (q.n : ℝ) * L) + (q.n : ℝ)) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-16 * L) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ Real.exp (-16 * Real.log ratio) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (q.eps / (q.n : ℝ)) ^ 16 := hexact

/-- The enlarged radial core discards at most the paper's local error scale
`(eps / n)^16` of the restricted Gaussian partition function. -/
theorem accuracyPhase_gaussianIntegral_tail_le (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (∫ x in truncatedBody q I \
        Metric.closedBall 0 (accuracyPhaseRadius q sigma2),
        gaussianDensity sigma2 x) ≤
      (q.eps / (q.n : ℝ)) ^ 16 *
        gaussianIntegral (truncatedBody q I) sigma2 := by
  have hK := truncatedBody_measurable q I
  have htail := gaussianIntegral_tail_radius_le hK hsigma2
    (accuracyPhaseRadius_pos q hsigma2).le
  have hscale := gaussianIntegral_scaling_le (truncatedBody q I) hK
    (truncatedVolumeInput q I).body.convex
    (unitBall_subset_truncatedBody q I (by simp [unitBall]))
    hsigma2 (by linarith : sigma2 ≤ 2 * sigma2)
  have hsqrt : Real.sqrt ((2 * sigma2) / sigma2) = Real.sqrt 2 := by
    congr 1
    field_simp [hsigma2.ne']
  rw [hsqrt] at hscale
  calc
    (∫ x in truncatedBody q I \
        Metric.closedBall 0 (accuracyPhaseRadius q sigma2),
        gaussianDensity sigma2 x) ≤
      Real.exp (-(accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2)) *
        gaussianIntegral (truncatedBody q I) (2 * sigma2) := htail
    _ ≤ Real.exp (-(accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2)) *
        (Real.sqrt 2 ^ q.n * gaussianIntegral (truncatedBody q I) sigma2) := by
      gcongr
    _ = (Real.exp (-(accuracyPhaseRadius q sigma2) ^ 2 / (4 * sigma2)) *
        Real.sqrt 2 ^ q.n) * gaussianIntegral (truncatedBody q I) sigma2 := by ring
    _ ≤ (q.eps / (q.n : ℝ)) ^ 16 *
        gaussianIntegral (truncatedBody q I) sigma2 := by
      exact mul_le_mul_of_nonneg_right
        (accuracyPhase_tail_coefficient_le q hsigma2)
        (gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2).le

/-- Probability form of the accuracy-dependent phase-tail estimate. -/
theorem truncatedGaussianProbability_accuracyPhase_compl_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (accuracyPhaseTruncatedBody q I sigma2)ᶜ ≤
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16) := by
  let K : Set (AmbientSpace q.n) := truncatedBody q I
  let R : ℝ := accuracyPhaseRadius q sigma2
  let Z : ℝ := gaussianIntegral K sigma2
  let nu : ℝ := (q.eps / (q.n : ℝ)) ^ 16
  have hZ : 0 < Z := by
    dsimp [Z, K]
    exact gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2
  have hnu : 0 ≤ nu := by dsimp [nu]; positivity
  have hset : (accuracyPhaseTruncatedBody q I sigma2)ᶜ ∩ K =
      K \ Metric.closedBall 0 R := by
    ext x
    simp only [accuracyPhaseTruncatedBody, K, R, mem_inter_iff, mem_compl_iff,
      mem_diff]
    tauto
  rw [truncatedGaussianProbability_apply q I hsigma2
    (accuracyPhaseTruncatedBody_measurable q I sigma2).compl]
  change (ENNReal.ofReal Z)⁻¹ *
      ∫⁻ x in (accuracyPhaseTruncatedBody q I sigma2)ᶜ ∩ K,
        ENNReal.ofReal (gaussianDensity sigma2 x) ≤ ENNReal.ofReal nu
  rw [hset]
  have hf := integrable_gaussianDensity (n := q.n) hsigma2
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  have htailReal :
      (∫ x in K \ Metric.closedBall 0 R, gaussianDensity sigma2 x) ≤ nu * Z := by
    simpa [K, R, nu, Z] using accuracyPhase_gaussianIntegral_tail_le q I hsigma2
  have htailENN : ENNReal.ofReal
      (∫ x in K \ Metric.closedBall 0 R, gaussianDensity sigma2 x) ≤
        ENNReal.ofReal nu * ENNReal.ofReal Z := by
    rw [← ENNReal.ofReal_mul hnu]
    exact ENNReal.ofReal_le_ofReal htailReal
  calc
    (ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal
      (∫ x in K \ Metric.closedBall 0 R, gaussianDensity sigma2 x) ≤
      (ENNReal.ofReal Z)⁻¹ *
        (ENNReal.ofReal nu * ENNReal.ofReal Z) := mul_le_mul' le_rfl htailENN
    _ = ENNReal.ofReal nu := by
      have hZ0 : ENNReal.ofReal Z ≠ 0 := (ENNReal.ofReal_pos.2 hZ).ne'
      have hZtop : ENNReal.ofReal Z ≠ ⊤ := ENNReal.ofReal_ne_top
      calc
        (ENNReal.ofReal Z)⁻¹ * (ENNReal.ofReal nu * ENNReal.ofReal Z) =
            ENNReal.ofReal nu * ((ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal Z) := by
          ac_rfl
        _ = ENNReal.ofReal nu := by
          rw [ENNReal.inv_mul_cancel hZ0 hZtop, mul_one]

/-- Conditioning a probability measure on an event loses at most the mass of
the discarded complement.  This is the elementary TV bridge needed to pass
from mixing on a radial core back to the untruncated phase target. -/
theorem TVLe.condOn_of_compl_le_cv18 {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : Set Omega} (hS : MeasurableSet S) (hS0 : mu S ≠ 0)
    {epsilon : ENNReal} (hcompl : mu Sᶜ <= epsilon) :
    Arlib.TVLe (Arlib.condOn mu S) mu epsilon := by
  let _ : IsProbabilityMeasure (Arlib.condOn mu S) :=
    Arlib.isProbabilityMeasure_condOn mu hS0 (measure_ne_top mu S)
  apply (Arlib.tvLe_of_forall_le (μ := mu) (ν := Arlib.condOn mu S) ?_).symm
  intro T hT
  have hinter : mu (T ∩ S) <= Arlib.condOn mu S T := by
    rw [Arlib.condOn_apply mu hS hT]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hS0) (Or.inl (measure_ne_top mu S))).2
    calc
      mu (T ∩ S) * mu S <= mu (T ∩ S) * 1 := by
        gcongr
        exact prob_le_one
      _ = mu (T ∩ S) := mul_one _
  calc
    mu T <= mu ((T ∩ S) ∪ Sᶜ) := by
      apply measure_mono
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hx, hxS⟩
      · exact Or.inr hxS
    _ <= mu (T ∩ S) + mu Sᶜ := measure_union_le _ _
    _ <= Arlib.condOn mu S T + epsilon := add_le_add hinter hcompl

/-- The accuracy-dependent phase target is within `(eps / n)^16` in total
variation of the full truncated Gaussian target used by the ideal estimator. -/
theorem TVLe.accuracyPhase_condOn_truncatedGaussian_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Arlib.TVLe
      (Arlib.condOn
        (truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))
        (accuracyPhaseTruncatedBody q I sigma2))
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  let mu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let S : Set (AmbientSpace q.n) := accuracyPhaseTruncatedBody q I sigma2
  let epsilon : ENNReal := ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)
  have hS : MeasurableSet S := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hratio0 : 0 <= q.eps / (q.n : ℝ) :=
    div_nonneg q.heps.1.le (Nat.cast_nonneg q.n)
  have hratio1 : q.eps / (q.n : ℝ) < 1 := by
    have hn3 : (3 : ℝ) <= q.n := by exact_mod_cast q.dim_ok
    apply (div_lt_one (by positivity)).2
    exact q.heps.2.trans_le (by linarith)
  have hepsilon1 : epsilon < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ hratio0 hratio1 (by norm_num)
  have hcompl : mu Sᶜ <= epsilon := by
    simpa [mu, S, epsilon] using
      truncatedGaussianProbability_accuracyPhase_compl_le q I hsigma2
  have hS0 : mu S ≠ 0 := by
    intro hzero
    have hsum : mu S + mu Sᶜ = 1 := by
      rw [measure_add_measure_compl hS, measure_univ]
    have hcompl_one : mu Sᶜ = 1 := by simpa [hzero] using hsum
    exact (not_le_of_gt hepsilon1) (hcompl_one ▸ hcompl)
  exact TVLe.condOn_of_compl_le_cv18 mu hS hS0 hcompl

/-- Normalizing the abstract Gaussian density on an accuracy phase core is
the same law as conditioning the executable full-body Gaussian target on
that core. -/
theorem condOn_gaussian_accuracyPhase_eq_truncatedGaussian
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Arlib.condOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight sigma2))
        (accuracyPhaseTruncatedBody q I sigma2) =
      Arlib.condOn
        (truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))
        (accuracyPhaseTruncatedBody q I sigma2) := by
  let Z : ENNReal :=
    ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2)
  have hZreal : 0 < gaussianIntegral (truncatedBody q I) sigma2 :=
    gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2
  have hZ0 : Z⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hZtop : Z⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.2 hZreal).ne'
  have hsub : accuracyPhaseTruncatedBody q I sigma2 ⊆ truncatedBody q I :=
    fun _ hx => hx.1
  rw [truncatedGaussianProbability_toMeasure q I hsigma2]
  change _ = Arlib.condOn (Z⁻¹ • truncatedGaussianMeasure q I sigma2) _
  rw [Arlib.MarkovChains.condOn_smul_cv18 _
    (accuracyPhaseTruncatedBody_measurable q I sigma2) hZ0 hZtop]
  unfold truncatedGaussianMeasure
  rw [← restrict_withDensity (truncatedBody_measurable q I)]
  rw [Arlib.MarkovChains.condOn_restrict_eq_condOn_of_subset_cv18 _
    (accuracyPhaseTruncatedBody_measurable q I sigma2) hsub]
  congr 2
  funext x
  simp [gaussianDensity_eq, Arlib.MarkovChains.gaussianWeight,
    Arlib.MarkovChains.gaussianWeightReal]

/-- The executable proposal and accuracy-dependent radius obey the product
condition used by the generalized conductance proof. -/
theorem accuracyPhaseRadius_mul_figureOneProposalRadius_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    accuracyPhaseRadius q sigma2 * figureOneProposalRadius q sigma2 ≤
      sigma2 / 9 := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  let b : ℝ := Real.sqrt ((q.n : ℝ) * L)
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 0 < L := by
    dsimp [L]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hsqrt0 : 0 ≤ Real.sqrt sigma2 := Real.sqrt_nonneg _
  have hmin : min (Real.sqrt sigma2) 1 ≤ Real.sqrt sigma2 := min_le_left _ _
  have hcancel :
      accuracyPhaseRadius q sigma2 * figureOneProposalRadius q sigma2 =
        Real.sqrt sigma2 * min (Real.sqrt sigma2) 1 / 128 := by
    unfold accuracyPhaseRadius figureOneProposalRadius
    change (32 * Real.sqrt sigma2 * b) *
        (min (Real.sqrt sigma2) 1 / (4096 * b)) = _
    field_simp [hb.ne']
    ring
  rw [hcancel]
  have hsq : Real.sqrt sigma2 ^ 2 = sigma2 := Real.sq_sqrt hsigma2.le
  have hmul : Real.sqrt sigma2 * min (Real.sqrt sigma2) 1 ≤ sigma2 := by
    calc
      Real.sqrt sigma2 * min (Real.sqrt sigma2) 1 ≤
          Real.sqrt sigma2 * Real.sqrt sigma2 :=
        mul_le_mul_of_nonneg_left hmin hsqrt0
      _ = sigma2 := by nlinarith
  nlinarith

theorem figureOneProposalRadius_le_sigma_div_eight_sqrt
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      Real.sqrt sigma2 / (8 * Real.sqrt q.n) :=
  figureOneProposalRadius_le_phaseMixingStep q hsigma2

/-- Warm-start speedy mixing on the enlarged accuracy-dependent radial core.
The rate is unchanged from the paper-radius theorem. -/
theorem mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.speedyMetropolisGaussian
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2))
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
      mu0 t (ENNReal.ofReal eps) := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hR : 0 ≤ accuracyPhaseRadius q sigma2 :=
    (accuracyPhaseRadius_pos q hsigma2).le
  have hwarm' : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) (Real.sqrt sigma2 ^ 2)) := by
    simpa [Real.sq_sqrt hsigma2.le] using hwarm
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_radiusStepProduct_cv18
      hn2 hsigma hdelta
      (figureOneProposalRadius_le_sigma_div_eight_sqrt q hsigma2)
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      hR (fun _ hx => accuracyPhaseTruncatedBody_norm_le q I hx)
      (by simpa [Real.sq_sqrt hsigma2.le] using
        accuracyPhaseRadius_mul_figureOneProposalRadius_le q hsigma2)
      hM hwarm' heps0 heps1 ht
  simpa [Real.sq_sqrt hsigma2.le] using hmix

/-- Complete phase-local sampler in the sub-unit-radius branch.  Speedy
mixing is followed by the paper's two exact rejection stages and then the
negligible accuracy-core truncation is removed. -/
theorem accuracyPhaseSampleToGaussian_smallRadius_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (hsmall : accuracyPhaseRadius q sigma2 ≤ 1)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError1 : mixError ≤ 1 / 32)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmixPhase := mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 hM hwarm hmixError0 (hmixError1.trans (by norm_num)) ht
  have hmix : Arlib.TVLe mu
      (Arlib.MarkovChains.ellGaussianProb K delta sigma2)
      (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, mu, P, K, delta] using hmixPhase
  have hKmeas : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hKconv : Convex ℝ K := accuracyPhaseTruncatedBody_convex q I sigma2
  have hKcompact : IsCompact K := accuracyPhaseTruncatedBody_isCompact q I sigma2
  have hK0 : volume K ≠ 0 := accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2
  have hKtop : volume K ≠ ⊤ := accuracyPhaseTruncatedBody_volume_ne_top q I sigma2
  have hrho : 0 < accuracyPhaseInradius q sigma2 :=
    accuracyPhaseInradius_pos q hsigma2
  have hball : Metric.ball (0 : AmbientSpace q.n)
      (accuracyPhaseInradius q sigma2) ⊆ K :=
    ball_accuracyPhaseInradius_subset q I sigma2
  have hmass0 : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero hKmeas hKconv
      hKcompact.isBounded hK0 hdelta sigma2
  have hmasstop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18 hKtop delta hsigma2
  let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
  have hc0 : 0 < c := by
    have hnR : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
    dsimp [c]
    have : 1 / (2 * (q.n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hscaled : 0 < sigma2 / c ^ 2 := by positivity
  have hprop0 :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (Arlib.MarkovChains.gaussianWeight (sigma2 / c ^ 2))) K ≠ 0 :=
    Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _ hK0
  have hproptop :
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (Arlib.MarkovChains.gaussianWeight (sigma2 / c ^ 2))) K ≠ ⊤ :=
    Arlib.MarkovChains.withDensity_gaussianWeight_ne_top hscaled hKmeas hKtop
  have htransfer := Arlib.MarkovChains.TVLe.speedyToGaussian_twoStage_cv18
    hn hKmeas hKconv hrho hball hdelta
      (figureOneProposalRadius_le_accuracyPhaseCoreStep q hsigma2 hsmall)
      hsigma2 hmass0 hmasstop
      (by simpa [c] using hprop0) (by simpa [c] using hproptop)
      hmix ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hmixError1)
  have htarget := TVLe.accuracyPhase_condOn_truncatedGaussian_cv18 q I hsigma2
  rw [condOn_gaussian_accuracyPhase_eq_truncatedGaussian q I hsigma2] at htransfer
  exact htransfer.trans htarget

/-- Complete phase-local sampler in the unit-inball branch.  This is the KLS
core-defect route used by CV18 once the accuracy-dependent radial core has
radius at least one. -/
theorem accuracyPhaseSampleToGaussian_largeRadius_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 coreError mixError : ℝ} (hsigma2 : 0 < sigma2)
    (hlarge : 1 ≤ accuracyPhaseRadius q sigma2)
    (hcoreError0 : 0 < coreError) (hcoreError16 : coreError ≤ 1 / 16)
    (hpaperStep : figureOneProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / coreError))))
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError1 : mixError ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ))
    (hcombined : 8 * ENNReal.ofReal mixError +
      4 * ENNReal.ofReal coreError ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError + 32 * ENNReal.ofReal coreError +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmixPhase := mixesWithin_accuracyPhaseTruncatedBody_figureOne_cv18
    q I hsigma2 hM hwarm hmixError0 hmixError1 ht
  have hmix : Arlib.TVLe mu
      (Arlib.MarkovChains.ellGaussianProb K delta sigma2)
      (ENNReal.ofReal mixError) := by
    simpa [Arlib.MarkovChains.MixesWithin, mu, P, K, delta] using hmixPhase
  have hunit : Metric.closedBall (0 : AmbientSpace q.n) 1 ⊆ K := by
    intro x hx
    refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
    · simpa [unitBall] using hx
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hx1 : ‖x‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      exact hx1.trans hlarge
  have htransfer :=
    Arlib.MarkovChains.TVLe.speedyToGaussian_of_paperStep_of_body_cv18
      hn (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isClosed
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2)
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2)
      hunit hdelta (Real.sqrt_pos.2 hsigma2)
      hcoreError0 hcoreError16 hpaperStep
      (by simpa [Real.sq_sqrt hsigma2.le] using hmix)
      ENNReal.ofReal_ne_top hcombined
  have htransfer' := htransfer
  simp only [Real.sq_sqrt hsigma2.le] at htransfer'
  have htarget := TVLe.accuracyPhase_condOn_truncatedGaussian_cv18 q I hsigma2
  rw [condOn_gaussian_accuracyPhase_eq_truncatedGaussian q I hsigma2] at htransfer'
  exact htransfer'.trans htarget

end ArlibCommunity.Algorithms.CV18
