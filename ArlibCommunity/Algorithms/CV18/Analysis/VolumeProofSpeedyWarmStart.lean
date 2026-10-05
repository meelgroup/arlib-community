import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing

/-!
# Warm starts for successive CV18 speedy phases

CV18 carries the endpoint of the speedy walk from one cooling phase to the
next.  The paper states warmness for the ordinary restricted Gaussians, while
the speedy mixing theorem needs warmness for the `ell`-weighted stationary
laws.  This file supplies the missing geometric bridge.  Its first ingredient
is the exact comparison of local conductances when both the body and proposal
radius grow.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise
open Arlib MarkovChains

/-- If the body and proposal radius both grow, the old local conductance is at
most the ratio of proposal-ball volumes times the new local conductance. -/
theorem ell_le_ballVolumeRatio_of_subset {n : ℕ}
    {K L : Set (EuclideanSpace ℝ (Fin n))} {delta Delta : ℝ}
    (hdelta : 0 < delta) (hDelta : 0 < Delta) (hsubK : K ⊆ L)
    (hrad : delta ≤ Delta) (x : EuclideanSpace ℝ (Fin n)) :
    ell K delta x ≤
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) /
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta)) * ell L Delta x := by
  have hnum : volume (Metric.ball x delta ∩ K) ≤
      volume (Metric.ball x Delta ∩ L) := by
    apply measure_mono
    intro y hy
    exact ⟨Metric.ball_subset_ball hrad hy.1, hsubK hy.2⟩
  have hvD0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume 0 hDelta)
  have hvDt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [ell_apply, volume_ball_eq x delta, ell_apply, volume_ball_eq x Delta]
  calc
    volume (Metric.ball x delta ∩ K) /
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta) ≤
        volume (Metric.ball x Delta ∩ L) /
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta) :=
      ENNReal.div_le_div_right hnum _
    _ = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) /
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta)) *
          (volume (Metric.ball x Delta ∩ L) /
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      symm
      calc
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta))⁻¹ *
              (volume (Metric.ball x Delta ∩ L) *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta))⁻¹) =
            (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta))⁻¹) *
              (volume (Metric.ball x Delta ∩ L) *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta))⁻¹) := by
          ac_rfl
        _ = volume (Metric.ball x Delta ∩ L) *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta))⁻¹ := by
          rw [ENNReal.mul_inv_cancel hvD0 hvDt, one_mul]

/-- Exact scaling of Euclidean proposal-ball volumes. -/
theorem volume_ball_ratio_eq_ofReal_pow {n : ℕ}
    {delta Delta : ℝ} (hdelta : 0 < delta) (hDelta : 0 < Delta) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Delta) /
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) delta) =
      ENNReal.ofReal ((Delta / delta) ^ n) := by
  have hratio : 0 < Delta / delta := div_pos hDelta hdelta
  have hdecomp : Delta = (Delta / delta) * delta := by
    field_simp
  have hv := Measure.addHaar_ball_mul_of_pos volume
    (0 : EuclideanSpace ℝ (Fin n)) hratio delta
  rw [← hdecomp] at hv
  rw [hv]
  simpa [finrank_euclideanSpace_fin] using
    (ENNReal.mul_div_cancel_right
      (a := ENNReal.ofReal ((Delta / delta) ^ n))
      (ne_of_gt (Metric.measure_ball_pos volume
        (0 : EuclideanSpace ℝ (Fin n)) hdelta)) measure_ball_lt_top.ne)

/-- Power-form local-conductance comparison.  This is the precise geometric
factor omitted when CV18 moves a speedy endpoint between phases. -/
theorem ell_le_radiusRatioPow_of_subset {n : ℕ}
    {K L : Set (EuclideanSpace ℝ (Fin n))} {delta Delta : ℝ}
    (hdelta : 0 < delta) (hDelta : 0 < Delta) (hsubK : K ⊆ L)
    (hrad : delta ≤ Delta) (x : EuclideanSpace ℝ (Fin n)) :
    ell K delta x ≤ ENNReal.ofReal ((Delta / delta) ^ n) * ell L Delta x := by
  simpa [volume_ball_ratio_eq_ofReal_pow hdelta hDelta] using
    ell_le_ballVolumeRatio_of_subset hdelta hDelta hsubK hrad x

theorem accuracyPhaseRadius_mono (q : VolumeParams) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    accuracyPhaseRadius q s ≤ accuracyPhaseRadius q t := by
  unfold accuracyPhaseRadius
  gcongr

theorem accuracyPhaseTruncatedBody_mono (q : VolumeParams) (I : VolumeInput q.n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    accuracyPhaseTruncatedBody q I s ⊆ accuracyPhaseTruncatedBody q I t := by
  intro x hx
  exact ⟨hx.1, Metric.closedBall_subset_closedBall
    (accuracyPhaseRadius_mono q hs hst) hx.2⟩

theorem figureOneProposalRadius_mono (q : VolumeParams) {s t : ℝ}
    (hst : s ≤ t) :
    figureOneProposalRadius q s ≤ figureOneProposalRadius q t := by
  unfold figureOneProposalRadius
  apply div_le_div_of_nonneg_right
  · exact min_le_min (Real.sqrt_le_sqrt hst) le_rfl
  · positivity

/-- One executable cooling update increases variance by at most a factor two.
The fixed-rate branch uses `n ≥ 3`; the accelerated branch uses the invariant
that every schedule value is at most the terminal variance. -/
theorem scheduleValue_succ_le_two_mul (q : VolumeParams) (k : ℕ) :
    scheduleValue q (k + 1) ≤ 2 * scheduleValue q k := by
  let s := scheduleValue q k
  have hs : 0 < s := scheduleValue_pos q k
  have hsT : s ≤ terminalVariance q := scheduleValue_le_terminal q k
  rw [show scheduleValue q (k + 1) = nextVariance q s by
    simpa [s] using scheduleValue_succ q k]
  unfold nextVariance
  refine (min_le_right _ _).trans ?_
  unfold coolingRate
  split_ifs with hsone
  · have hn : (1 : ℝ) ≤ q.n := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
    have hinv : 1 / (q.n : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hn
    nlinarith
  · have hT : 0 < terminalVariance q := terminalVariance_pos' q
    have hratio : s / (2 * terminalVariance q) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    nlinarith

/-- Consecutive proposal radii grow by at most `sqrt 2`. -/
theorem figureOneProposalRadius_succ_le_sqrtTwo_mul
    (q : VolumeParams) (k : ℕ) :
    figureOneProposalRadius q (scheduleValue q (k + 1)) ≤
      Real.sqrt 2 * figureOneProposalRadius q (scheduleValue q k) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht2s : t ≤ 2 * s := by
    simpa [s, t] using scheduleValue_succ_le_two_mul q k
  let D : ℝ :=
    4096 * Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))
  have hD : 0 < D := by
    dsimp [D]
    have hn : (0 : ℝ) < q.n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
    have hL : 0 < protectedLog ((q.n : ℝ) / q.eps) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  unfold figureOneProposalRadius
  change min (Real.sqrt t) 1 / D ≤ Real.sqrt 2 * (min (Real.sqrt s) 1 / D)
  apply (div_le_iff₀ hD).2
  rw [mul_assoc, div_mul_cancel₀ _ hD.ne']
  by_cases hsone : 1 ≤ s
  · have htone : 1 ≤ t := hsone.trans hst
    rw [min_eq_right (Real.one_le_sqrt.mpr hsone),
      min_eq_right (Real.one_le_sqrt.mpr htone)]
    simpa using (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2))
  · have hslt : s < 1 := lt_of_not_ge hsone
    have hsqrt_s_le : Real.sqrt s ≤ 1 := by
      exact Real.sqrt_le_one.mpr hslt.le
    rw [min_eq_left hsqrt_s_le]
    calc
      min (Real.sqrt t) 1 ≤ Real.sqrt t := min_le_left _ _
      _ ≤ Real.sqrt (2 * s) := Real.sqrt_le_sqrt ht2s
      _ = Real.sqrt 2 * Real.sqrt s := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Hence the exact radius quotient appearing in the local-conductance bridge
is at most `sqrt 2`. -/
theorem figureOneProposalRadius_succ_ratio_le_sqrtTwo
    (q : VolumeParams) (k : ℕ) :
    figureOneProposalRadius q (scheduleValue q (k + 1)) /
        figureOneProposalRadius q (scheduleValue q k) ≤ Real.sqrt 2 := by
  exact (div_le_iff₀
    (figureOneProposalRadius_pos q (scheduleValue_pos q k))).2
    (by simpa [mul_comm] using figureOneProposalRadius_succ_le_sqrtTwo_mul q k)

/-- The actual CV18 cooling schedule gives the sharper fixed-rate radius
factor.  Above variance one both proposal radii have already saturated, while
below variance one the update is at most multiplication by `1 + 1 / n`. -/
theorem figureOneProposalRadius_succ_le_fixedFactor_mul
    (q : VolumeParams) (k : ℕ) :
    figureOneProposalRadius q (scheduleValue q (k + 1)) ≤
      Real.sqrt (1 + 1 / (q.n : ℝ)) *
        figureOneProposalRadius q (scheduleValue q k) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  let D : ℝ :=
    4096 * Real.sqrt ((q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps))
  have hD : 0 < D := by
    dsimp [D]
    have hL : 0 < protectedLog ((q.n : ℝ) / q.eps) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  unfold figureOneProposalRadius
  change min (Real.sqrt t) 1 / D ≤
    Real.sqrt (1 + 1 / (q.n : ℝ)) * (min (Real.sqrt s) 1 / D)
  apply (div_le_iff₀ hD).2
  rw [mul_assoc, div_mul_cancel₀ _ hD.ne']
  by_cases hsone : 1 ≤ s
  · have htone : 1 ≤ t := hsone.trans hst
    rw [min_eq_right (Real.one_le_sqrt.mpr hsone),
      min_eq_right (Real.one_le_sqrt.mpr htone)]
    simpa using Real.one_le_sqrt.mpr
      (show (1 : ℝ) ≤ 1 + 1 / (q.n : ℝ) by positivity)
  · have hslt : s < 1 := lt_of_not_ge hsone
    have htbound : t ≤ s * (1 + 1 / (q.n : ℝ)) := by
      rw [show t = nextVariance q s by
        simpa [s, t] using scheduleValue_succ q k]
      unfold nextVariance coolingRate
      rw [if_pos hslt.le]
      exact min_le_right _ _
    have hsqrt_s_le : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hslt.le
    rw [min_eq_left hsqrt_s_le]
    calc
      min (Real.sqrt t) 1 ≤ Real.sqrt t := min_le_left _ _
      _ ≤ Real.sqrt (s * (1 + 1 / (q.n : ℝ))) :=
        Real.sqrt_le_sqrt htbound
      _ = Real.sqrt s * Real.sqrt (1 + 1 / (q.n : ℝ)) := by
        rw [Real.sqrt_mul hs.le]
      _ = Real.sqrt (1 + 1 / (q.n : ℝ)) * Real.sqrt s := mul_comm _ _

/-- Consequently the full `n`-dimensional proposal-volume ratio is bounded
by the universal `exp (1/2)`, rather than the exponential `(sqrt 2)^n` bound
obtained from the coarse two-fold variance comparison. -/
theorem figureOneProposalRadius_succ_ratio_pow_le_expHalf
    (q : VolumeParams) (k : ℕ) :
    (figureOneProposalRadius q (scheduleValue q (k + 1)) /
        figureOneProposalRadius q (scheduleValue q k)) ^ q.n ≤
      Real.exp (1 / 2) := by
  have hratio :
      figureOneProposalRadius q (scheduleValue q (k + 1)) /
          figureOneProposalRadius q (scheduleValue q k) ≤
        Real.sqrt (1 + 1 / (q.n : ℝ)) := by
    exact (div_le_iff₀
      (figureOneProposalRadius_pos q (scheduleValue_pos q k))).2
      (by simpa [mul_comm] using
        figureOneProposalRadius_succ_le_fixedFactor_mul q k)
  have hratio0 : 0 ≤
      figureOneProposalRadius q (scheduleValue q (k + 1)) /
        figureOneProposalRadius q (scheduleValue q k) :=
    div_nonneg
      (figureOneProposalRadius_pos q (scheduleValue_pos q (k + 1))).le
      (figureOneProposalRadius_pos q (scheduleValue_pos q k)).le
  exact (pow_le_pow_left₀ hratio0 hratio q.n).trans
    (fixedRate_sqrt_factor_le q.n
      (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok))

/-- The local conductance of one accuracy phase is pointwise controlled by
that of the next phase, with the exact proposal-radius growth factor. -/
theorem accuracyPhase_ell_adjacent_le (q : VolumeParams) (I : VolumeInput q.n)
    (k : ℕ) (x : AmbientSpace q.n) :
    ell (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k)) x ≤
      ENNReal.ofReal
          ((figureOneProposalRadius q (scheduleValue q (k + 1)) /
            figureOneProposalRadius q (scheduleValue q k)) ^ q.n) *
        ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x := by
  have hs : 0 < scheduleValue q k := scheduleValue_pos q k
  have ht : 0 < scheduleValue q (k + 1) := scheduleValue_pos q (k + 1)
  have hst : scheduleValue q k ≤ scheduleValue q (k + 1) :=
    scheduleValue_mono q (Nat.le_add_right k 1)
  exact ell_le_radiusRatioPow_of_subset
    (figureOneProposalRadius_pos q hs)
    (figureOneProposalRadius_pos q ht)
    (accuracyPhaseTruncatedBody_mono q I hs.le hst)
    (figureOneProposalRadius_mono q hst) x

/-- Dimension-only form of the adjacent local-conductance comparison. -/
theorem accuracyPhase_ell_adjacent_le_sqrtTwoPow
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) (x : AmbientSpace q.n) :
    ell (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k)) x ≤
      ENNReal.ofReal ((Real.sqrt 2) ^ q.n) *
        ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x := by
  refine (accuracyPhase_ell_adjacent_le q I k x).trans ?_
  have hpow :
      (figureOneProposalRadius q (scheduleValue q (k + 1)) /
        figureOneProposalRadius q (scheduleValue q k)) ^ q.n ≤
          (Real.sqrt 2) ^ q.n :=
    pow_le_pow_left₀
      (div_nonneg
      (figureOneProposalRadius_pos q (scheduleValue_pos q (k + 1))).le
      (figureOneProposalRadius_pos q (scheduleValue_pos q k)).le)
      (figureOneProposalRadius_succ_ratio_le_sqrtTwo q k) q.n
  exact mul_le_mul'
    (ENNReal.ofReal_le_ofReal hpow) le_rfl

/-- Universal-constant form of the adjacent local-conductance comparison. -/
theorem accuracyPhase_ell_adjacent_le_expHalf
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) (x : AmbientSpace q.n) :
    ell (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k)) x ≤
      ENNReal.ofReal (Real.exp (1 / 2)) *
        ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x := by
  refine (accuracyPhase_ell_adjacent_le q I k x).trans ?_
  exact mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      (figureOneProposalRadius_succ_ratio_pow_le_expHalf q k)) le_rfl

/-! ## Normalization bridge -/

/-- Domination of two finite unnormalised measures, together with a bound on
the ratio of their total masses, gives warmness of their normalisations. -/
theorem isWarm_normalize_of_le_smul {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} {A B : ENNReal}
    (hmu0 : mu Set.univ ≠ 0) (hmutop : mu Set.univ ≠ ⊤)
    (hnu0 : nu Set.univ ≠ 0) (hnutop : nu Set.univ ≠ ⊤)
    (hdom : mu ≤ A • nu) (hmass : nu Set.univ ≤ B * mu Set.univ) :
    IsWarm (A * B)
      ((mu Set.univ)⁻¹ • mu) ((nu Set.univ)⁻¹ • nu) := by
  intro S hS
  change (mu Set.univ)⁻¹ * mu S ≤
    (A * B) * ((nu Set.univ)⁻¹ * nu S)
  have hdomS : mu S ≤ A * nu S := by
    simpa [Measure.smul_apply, smul_eq_mul] using
      Measure.le_iff.mp hdom S hS
  calc
    (mu Set.univ)⁻¹ * mu S ≤ (mu Set.univ)⁻¹ * (A * nu S) :=
      mul_le_mul' le_rfl hdomS
    _ = A * (nu Set.univ / mu Set.univ) *
          ((nu Set.univ)⁻¹ * nu S) := by
      rw [div_eq_mul_inv]
      symm
      calc
        A * (nu Set.univ * (mu Set.univ)⁻¹) *
              ((nu Set.univ)⁻¹ * nu S) =
            (nu Set.univ * (nu Set.univ)⁻¹) *
              ((mu Set.univ)⁻¹ * (A * nu S)) := by
          ac_rfl
        _ = (mu Set.univ)⁻¹ * (A * nu S) := by
          rw [ENNReal.mul_inv_cancel hnu0 hnutop, one_mul]
    _ ≤ A * B * ((nu Set.univ)⁻¹ * nu S) := by
      apply mul_le_mul'
      · exact mul_le_mul' le_rfl
          ((ENNReal.div_le_iff hmu0 hmutop).2 (by simpa [mul_comm] using hmass))
      · exact le_rfl

/-- Pointwise domination of the `ell * Gaussian` densities on nested bodies
lifts to domination of the corresponding unnormalised speedy measures. -/
theorem ellGaussianMeasure_le_smul_of_subset {n : ℕ}
    {K L : Set (AmbientSpace n)} (hK : MeasurableSet K)
    (hL : MeasurableSet L) (hsub : K ⊆ L)
    {delta Delta s t : ℝ} {A : ENNReal}
    (hpoint : ∀ x ∈ K,
      ell K delta x * gaussianWeight s x ≤
        A * (ell L Delta x * gaussianWeight t x)) :
    ellGaussianMeasure K delta s ≤ A • ellGaussianMeasure L Delta t := by
  rw [Measure.le_iff]
  intro S hS
  rw [ellGaussianMeasure, ellGaussianMeasure,
    Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hS, withDensity_apply _ hS,
    Measure.restrict_restrict hS, Measure.restrict_restrict hS]
  have hmeasNew : Measurable fun x : AmbientSpace n =>
      ell L Delta x * gaussianWeight t x :=
    measurable_ell_mul_gaussianWeight hL Delta t
  have hsetSub : S ∩ K ⊆ S ∩ L := by
    intro x hx
    exact ⟨hx.1, hsub hx.2⟩
  calc
    ∫⁻ x in S ∩ K, ell K delta x * gaussianWeight s x ≤
        ∫⁻ x in S ∩ K, A * (ell L Delta x * gaussianWeight t x) := by
      apply setLIntegral_mono'
      · exact hS.inter hK
      · intro x hx
        exact hpoint x hx.2
    _ ≤ ∫⁻ x in S ∩ L, A * (ell L Delta x * gaussianWeight t x) := by
      exact lintegral_mono'
        (Measure.restrict_mono hsetSub
          (le_rfl : (volume : Measure (AmbientSpace n)) ≤ volume)) le_rfl
    _ = A * ∫⁻ x in S ∩ L, ell L Delta x * gaussianWeight t x := by
      rw [lintegral_const_mul _ hmeasNew]

/-- The unnormalised speedy stationary measure of one accuracy phase is
dominated by `(sqrt 2)^n` times that of the next phase. -/
theorem accuracyPhase_ellGaussianMeasure_adjacent_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k))
        (scheduleValue q k) ≤
      ENNReal.ofReal ((Real.sqrt 2) ^ q.n) •
        ellGaussianMeasure
          (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1)))
          (scheduleValue q (k + 1)) := by
  have hs : 0 < scheduleValue q k := scheduleValue_pos q k
  have hst : scheduleValue q k ≤ scheduleValue q (k + 1) :=
    scheduleValue_mono q (Nat.le_add_right k 1)
  apply ellGaussianMeasure_le_smul_of_subset
    (accuracyPhaseTruncatedBody_measurable q I (scheduleValue q k))
    (accuracyPhaseTruncatedBody_measurable q I (scheduleValue q (k + 1)))
    (accuracyPhaseTruncatedBody_mono q I hs.le hst)
  intro x hx
  calc
    ell (accuracyPhaseTruncatedBody q I (scheduleValue q k))
          (figureOneProposalRadius q (scheduleValue q k)) x *
        gaussianWeight (scheduleValue q k) x ≤
      (ENNReal.ofReal ((Real.sqrt 2) ^ q.n) *
        ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x) *
        gaussianWeight (scheduleValue q k) x := by
      exact mul_le_mul' (accuracyPhase_ell_adjacent_le_sqrtTwoPow q I k x) le_rfl
    _ ≤ ENNReal.ofReal ((Real.sqrt 2) ^ q.n) *
        (ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x *
          gaussianWeight (scheduleValue q (k + 1)) x) := by
      rw [mul_assoc]
      apply mul_le_mul' le_rfl
      exact mul_le_mul' le_rfl
        (gaussianWeight_mono_variance_cv18 hs hst x)

/-- Sharp, dimension-independent domination of successive unnormalised speedy
stationary measures. -/
theorem accuracyPhase_ellGaussianMeasure_adjacent_le_expHalf
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k))
        (scheduleValue q k) ≤
      ENNReal.ofReal (Real.exp (1 / 2)) •
        ellGaussianMeasure
          (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1)))
          (scheduleValue q (k + 1)) := by
  have hs : 0 < scheduleValue q k := scheduleValue_pos q k
  have hst : scheduleValue q k ≤ scheduleValue q (k + 1) :=
    scheduleValue_mono q (Nat.le_add_right k 1)
  apply ellGaussianMeasure_le_smul_of_subset
    (accuracyPhaseTruncatedBody_measurable q I (scheduleValue q k))
    (accuracyPhaseTruncatedBody_measurable q I (scheduleValue q (k + 1)))
    (accuracyPhaseTruncatedBody_mono q I hs.le hst)
  intro x hx
  calc
    ell (accuracyPhaseTruncatedBody q I (scheduleValue q k))
          (figureOneProposalRadius q (scheduleValue q k)) x *
        gaussianWeight (scheduleValue q k) x ≤
      (ENNReal.ofReal (Real.exp (1 / 2)) *
        ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x) *
        gaussianWeight (scheduleValue q k) x := by
      exact mul_le_mul' (accuracyPhase_ell_adjacent_le_expHalf q I k x) le_rfl
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) *
        (ell (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
          (figureOneProposalRadius q (scheduleValue q (k + 1))) x *
          gaussianWeight (scheduleValue q (k + 1)) x) := by
      rw [mul_assoc]
      apply mul_le_mul' le_rfl
      exact mul_le_mul' le_rfl
        (gaussianWeight_mono_variance_cv18 hs hst x)

/-! ## Adjacent normalising constants -/

/-- The accuracy core contains at least half of the phase's ordinary
restricted-Gaussian mass.  The actual tail estimate is far stronger; half is
the convenient constant needed for warmness. -/
theorem accuracyPhase_full_gaussianIntegral_le_two_core
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    gaussianIntegral (truncatedBody q I) sigma2 ≤
      2 * gaussianIntegral (accuracyPhaseTruncatedBody q I sigma2) sigma2 := by
  let K : Set (AmbientSpace q.n) := truncatedBody q I
  let B : Set (AmbientSpace q.n) :=
    Metric.closedBall 0 (accuracyPhaseRadius q sigma2)
  let full : ℝ := gaussianIntegral K sigma2
  let core : ℝ := gaussianIntegral (K ∩ B) sigma2
  let tail : ℝ := ∫ x in K \ B, gaussianDensity sigma2 x
  let nu : ℝ := (q.eps / (q.n : ℝ)) ^ 16
  have hf := integrable_gaussianDensity (n := q.n) hsigma2
  have hdecomp : core + tail = full := by
    dsimp [core, tail, full]
    rw [gaussianIntegral_eq_setIntegral (truncatedBody_measurable q I),
      gaussianIntegral_eq_setIntegral
        ((truncatedBody_measurable q I).inter measurableSet_closedBall)]
    exact integral_inter_add_sdiff measurableSet_closedBall hf.integrableOn
  have htail : tail ≤ nu * full := by
    simpa [tail, nu, full, K, B] using
      accuracyPhase_gaussianIntegral_tail_le q I hsigma2
  have hratio : q.eps / (q.n : ℝ) ≤ 1 / 3 := by
    have hnpos : (0 : ℝ) < q.n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
    have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    apply (div_le_iff₀ hnpos).2
    nlinarith [q.heps.2.le]
  have hratio0 : 0 ≤ q.eps / (q.n : ℝ) := by
    exact div_nonneg q.heps.1.le (Nat.cast_nonneg q.n)
  have hnu : nu ≤ 1 / 2 := by
    dsimp [nu]
    calc
      (q.eps / (q.n : ℝ)) ^ 16 ≤ (1 / 3 : ℝ) ^ 16 :=
        pow_le_pow_left₀ hratio0 hratio 16
      _ ≤ 1 / 2 := by norm_num
  have hfull0 : 0 ≤ full := by
    dsimp [full]
    rw [gaussianIntegral_eq_setIntegral (truncatedBody_measurable q I)]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  dsimp [core, K, B] at *
  unfold accuracyPhaseTruncatedBody
  nlinarith

/-- Consecutive full-body Gaussian partition functions grow by at most the
paper's `exp(1/2)` warm-start constant. -/
theorem gaussianIntegral_adjacent_le_expHalf
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) ≤
      Real.exp (1 / 2) *
        gaussianIntegral (truncatedBody q I) (scheduleValue q k) := by
  have hw := scheduleValue_adjacent_warm q I k
    (0 : AmbientSpace q.n)
    (unitBall_subset_truncatedBody q I (by simp [unitBall]))
  have hZs : 0 < gaussianIntegral (truncatedBody q I) (scheduleValue q k) :=
    gaussianIntegral_pos q (truncatedVolumeInput q I) (scheduleValue_pos q k)
  have hZt : 0 < gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) :=
    gaussianIntegral_pos q (truncatedVolumeInput q I) (scheduleValue_pos q (k + 1))
  simp only [gaussianDensity, norm_zero, zero_pow, Nat.ofNat_pos,
    zero_div, neg_zero, Real.exp_zero] at hw
  field_simp [hZs.ne', hZt.ne'] at hw
  simpa [mul_comm, mul_left_comm, mul_assoc] using hw

/-- Real and ENNReal presentations of a Gaussian partition function agree. -/
theorem lintegral_gaussianWeight_eq_ofReal_gaussianIntegral {n : ℕ}
    {K : Set (AmbientSpace n)} (hK : MeasurableSet K)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ x in K, gaussianWeight s x) =
      ENNReal.ofReal (gaussianIntegral K s) := by
  have hf := integrable_gaussianDensity (n := n) hs
  have hpoint : gaussianWeight s = fun x : AmbientSpace n =>
      ENNReal.ofReal (gaussianDensity s x) := by
    funext x
    simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]
  rw [hpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  exact gaussianIntegral_eq_setIntegral hK s |>.symm

/-- Dropping `ell ≤ 1` bounds the speedy normaliser by the ordinary Gaussian
mass on the same phase body. -/
theorem ellGaussianMeasure_univ_le_gaussianMass {n : ℕ}
    {K : Set (AmbientSpace n)} (delta s : ℝ) :
    ellGaussianMeasure K delta s Set.univ ≤
      ∫⁻ x in K, gaussianWeight s x := by
  rw [ellGaussianMeasure_univ]
  exact lintegral_mono fun x => by
    simpa using mul_le_mul' (ell_le_one K delta x) le_rfl

/-- Successive speedy normalising constants differ by at most
`4 * exp(1/2)`.  Two factors of two pay respectively for the radial accuracy
core and for average local conductance. -/
theorem accuracyPhase_ellGaussianMass_adjacent_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    ellGaussianMeasure
        (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
        (figureOneProposalRadius q (scheduleValue q (k + 1)))
        (scheduleValue q (k + 1)) Set.univ ≤
      (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) *
        ellGaussianMeasure
          (accuracyPhaseTruncatedBody q I (scheduleValue q k))
          (figureOneProposalRadius q (scheduleValue q k))
          (scheduleValue q k) Set.univ := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let Ks := accuracyPhaseTruncatedBody q I s
  let Kt := accuracyPhaseTruncatedBody q I t
  let ds := figureOneProposalRadius q s
  let dt := figureOneProposalRadius q t
  let Gs : ENNReal := ∫⁻ x in Ks, gaussianWeight s x
  let Gt : ENNReal := ∫⁻ x in Kt, gaussianWeight t x
  let Fs : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight s x
  let Ft : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight t x
  let zs : ENNReal := ellGaussianMeasure Ks ds s Set.univ
  let zt : ENNReal := ellGaussianMeasure Kt dt t Set.univ
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hGtFt : Gt ≤ Ft := by
    dsimp [Gt, Ft, Kt]
    exact lintegral_mono_set fun _ hx => hx.1
  have hFtFs : Ft ≤ ENNReal.ofReal (Real.exp (1 / 2)) * Fs := by
    rw [show Ft = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) t) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) ht]
    rw [show Fs = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hs]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [s, t] using gaussianIntegral_adjacent_le_expHalf q I k)
  have hFsGs : Fs ≤ ENNReal.ofReal 2 * Gs := by
    rw [show Fs = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hs]
    rw [show Gs = ENNReal.ofReal
        (gaussianIntegral Ks s) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (by dsimp [Ks]; exact accuracyPhaseTruncatedBody_measurable q I s) hs]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [s, Ks] using accuracyPhase_full_gaussianIntegral_le_two_core q I hs)
  have hztGt : zt ≤ Gt := by
    dsimp [zt, Gt]
    exact ellGaussianMeasure_univ_le_gaussianMass dt t
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * Gs ≤ zs := by
    simpa [s, Ks, ds, Gs, zs] using
      half_mul_gaussianWeight_le_accuracyPhaseEllGaussian q I hs
  have hGsZs : Gs ≤ ENNReal.ofReal 2 * zs := by
    calc
      Gs = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2 : ℝ) * Gs) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal 2 * zs := mul_le_mul' le_rfl hhalf
  change zt ≤ (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) * zs
  calc
    zt ≤ Gt := hztGt
    _ ≤ Ft := hGtFt
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * Fs := hFtFs
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * (ENNReal.ofReal 2 * Gs) :=
      mul_le_mul' le_rfl hFsGs
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) *
        (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * zs)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hGsZs)
    _ = (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) * zs := by
      have hfour : ENNReal.ofReal 2 * ENNReal.ofReal 2 = ENNReal.ofReal 4 := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [← hfour]
      ac_rfl

/-- A real-valued warmness constant for carrying speedy endpoints between
successive cooling phases. -/
noncomputable def speedyAdjacentWarmConstant (q : VolumeParams) : ℝ :=
  Real.exp (1 / 2) * (4 * Real.exp (1 / 2))

theorem speedyAdjacentWarmConstant_pos (q : VolumeParams) :
    0 < speedyAdjacentWarmConstant q := by
  unfold speedyAdjacentWarmConstant
  positivity

/-- **The missing CV18 warm-start bridge.**  The speedy stationary law of one
accuracy phase is warm with respect to the speedy stationary law of the next
phase.  This is the hypothesis actually required by the speedy mixing theorem,
and it does not follow merely from warmness of the ordinary Gaussians. -/
theorem accuracyPhase_speedyStationary_adjacent_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ) :
    IsWarm (ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I (scheduleValue q k))
        (figureOneProposalRadius q (scheduleValue q k))
        (scheduleValue q k))
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I (scheduleValue q (k + 1)))
        (figureOneProposalRadius q (scheduleValue q (k + 1)))
        (scheduleValue q (k + 1))) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let Ks := accuracyPhaseTruncatedBody q I s
  let Kt := accuracyPhaseTruncatedBody q I t
  let ds := figureOneProposalRadius q s
  let dt := figureOneProposalRadius q t
  let mus := ellGaussianMeasure Ks ds s
  let muNext := ellGaussianMeasure Kt dt t
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := scheduleValue_pos q (k + 1)
  have hds : 0 < ds := figureOneProposalRadius_pos q hs
  have hdt : 0 < dt := figureOneProposalRadius_pos q ht
  have hmus0 : mus Set.univ ≠ 0 := by
    dsimp [mus]
    exact ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I s)
      (accuracyPhaseTruncatedBody_convex q I s)
      (accuracyPhaseTruncatedBody_isCompact q I s).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hs) hds s
  have hmut0 : muNext Set.univ ≠ 0 := by
    dsimp [muNext]
    exact ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I t)
      (accuracyPhaseTruncatedBody_convex q I t)
      (accuracyPhaseTruncatedBody_isCompact q I t).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I ht) hdt t
  have hmusto : mus Set.univ ≠ ⊤ := by
    dsimp [mus]
    exact ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I s) ds hs
  have hmutto : muNext Set.univ ≠ ⊤ := by
    dsimp [muNext]
    exact ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I t) dt ht
  have hdom : mus ≤ ENNReal.ofReal (Real.exp (1 / 2)) • muNext := by
    simpa [mus, muNext, Ks, Kt, ds, dt, s, t] using
      accuracyPhase_ellGaussianMeasure_adjacent_le_expHalf q I k
  have hmass : muNext Set.univ ≤
      (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (1 / 2))) * mus Set.univ := by
    simpa [mus, muNext, Ks, Kt, ds, dt, s, t] using
      accuracyPhase_ellGaussianMass_adjacent_le q I k
  have hw := isWarm_normalize_of_le_smul hmus0 hmusto hmut0 hmutto hdom hmass
  change IsWarm (ENNReal.ofReal (speedyAdjacentWarmConstant q))
    ((mus Set.univ)⁻¹ • mus) ((muNext Set.univ)⁻¹ • muNext)
  convert hw using 1
  unfold speedyAdjacentWarmConstant
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]







end ArlibCommunity.Algorithms.CV18
