import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialCoupling
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunMixing

/-!
# The first CV18 speedy warm start

There is no preceding speedy stationary law for the first cooling phase.  We
condition the initial restricted Gaussian on the centered inball guaranteed by
the input and the radial accuracy cutoff.  The discarded mass is controlled by
the already-proved initial/radial Gaussian tails.  On the surviving inball a
simple inscribed-ball argument gives the pointwise local-conductance floor
`2^{-n}`.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal Pointwise
open Arlib MarkovChains

/-- Every point of a closed ball has local conductance at least `2^{-n}` for
proposal radius at most the body radius.  The body may be any superset of that
ball. -/
theorem ofReal_halfPow_le_ell_of_closedBall_subset {n : ℕ}
    {K : Set (AmbientSpace n)} {rho delta : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) (hdeltarho : delta ≤ rho)
    (hballK : Metric.closedBall (0 : AmbientSpace n) rho ⊆ K)
    {x : AmbientSpace n} (hx : x ∈ Metric.closedBall 0 rho) :
    ENNReal.ofReal (((1 : ℝ) / 2) ^ n) ≤ ell K delta x := by
  have hxn : ‖x‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hdelta2 : 0 < delta / 2 := by linarith
  have hcoef : 0 < 1 - delta / (2 * rho) := by
    have : delta / (2 * rho) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    linarith
  set w : AmbientSpace n := (1 - delta / (2 * rho)) • x with hw
  have hwsub : w - x = (-(delta / (2 * rho))) • x := by
    rw [hw]
    module
  have hwx : dist w x = delta / (2 * rho) * ‖x‖ := by
    rw [dist_eq_norm, hwsub, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : 0 < delta / (2 * rho))]
  have hwnorm : ‖w‖ = (1 - delta / (2 * rho)) * ‖x‖ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
  have hwxle : dist w x ≤ delta / 2 := by
    rw [hwx]
    calc
      delta / (2 * rho) * ‖x‖ ≤ delta / (2 * rho) * rho := by
        gcongr
      _ = delta / 2 := by field_simp [hrho.ne']
  have hsub : Metric.ball w (delta / 2) ⊆ Metric.ball x delta ∩ K := by
    intro y hy
    have hyw : dist y w < delta / 2 := Metric.mem_ball.1 hy
    refine ⟨?_, hballK ?_⟩
    · rw [Metric.mem_ball]
      calc
        dist y x ≤ dist y w + dist w x := dist_triangle _ _ _
        _ < delta / 2 + delta / 2 := by linarith
        _ = delta := by ring
    · rw [Metric.mem_closedBall]
      have hw0 : dist w (0 : AmbientSpace n) =
          (1 - delta / (2 * rho)) * ‖x‖ := by
        rw [dist_zero_right, hwnorm]
      apply le_of_lt
      calc
        dist y (0 : AmbientSpace n) ≤ dist y w + dist w 0 := dist_triangle _ _ _
        _ < delta / 2 + (1 - delta / (2 * rho)) * ‖x‖ := by
          rw [hw0]
          linarith
        _ ≤ delta / 2 + (1 - delta / (2 * rho)) * rho := by gcongr
        _ = rho := by field_simp [hrho.ne']; ring
  have hbx0 : volume (Metric.ball x delta) ≠ 0 :=
    (Metric.measure_ball_pos volume x hdelta).ne'
  have hbxt : volume (Metric.ball x delta) ≠ ⊤ := measure_ball_lt_top.ne
  have hvw : volume (Metric.ball w (delta / 2)) =
      ENNReal.ofReal ((delta / 2) ^ n) *
        volume (Metric.ball (0 : AmbientSpace n) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (AmbientSpace n)) w hdelta2
    rwa [finrank_euclideanSpace_fin] at h
  have hvx : volume (Metric.ball x delta) =
      ENNReal.ofReal (delta ^ n) *
        volume (Metric.ball (0 : AmbientSpace n) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (AmbientSpace n)) x hdelta
    rwa [finrank_euclideanSpace_fin] at h
  have hpow : ((1 : ℝ) / 2) ^ n * delta ^ n = (delta / 2) ^ n := by
    rw [← mul_pow]
    ring_nf
  rw [ell_apply, ENNReal.le_div_iff_mul_le (Or.inl hbx0) (Or.inl hbxt)]
  calc
    ENNReal.ofReal (((1 : ℝ) / 2) ^ n) * volume (Metric.ball x delta) =
        ENNReal.ofReal ((delta / 2) ^ n) *
          volume (Metric.ball (0 : AmbientSpace n) 1) := by
      rw [hvx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpow]
    _ = volume (Metric.ball w (delta / 2)) := hvw.symm
    _ ≤ volume (Metric.ball x delta ∩ K) := measure_mono hsub

/-- Figure 1's proposal radius fits inside the accuracy phase inball. -/
theorem figureOneProposalRadius_le_accuracyPhaseInradius
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤ accuracyPhaseInradius q sigma2 := by
  have h := figureOneProposalRadius_le_accuracyPhaseLVStep q hsigma2
  let a := min (Real.sqrt sigma2) (accuracyPhaseInradius q sigma2)
  let D : ℝ := 4096 * Real.sqrt q.n
  have hD : 1 ≤ D := by
    have hn : (1 : ℝ) ≤ q.n := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
    have hsqrtn : 1 ≤ Real.sqrt (q.n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hn
    dsimp [D]
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact le_min (Real.sqrt_nonneg _) (accuracyPhaseInradius_pos q hsigma2).le
  calc
    figureOneProposalRadius q sigma2 ≤ a / D := by simpa [a, D] using h
    _ ≤ a := (div_le_self ha0 hD)
    _ ≤ accuracyPhaseInradius q sigma2 := min_le_right _ _

/-- Pointwise conductance floor on the initial phase's guaranteed inball. -/
theorem initial_accuracyPhase_ell_floor (q : VolumeParams) (I : VolumeInput q.n)
    {x : AmbientSpace q.n}
    (hx : x ∈ Metric.closedBall 0
      (accuracyPhaseInradius q (initialVariance q))) :
    ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) ≤
      ell (accuracyPhaseTruncatedBody q I (initialVariance q))
        (figureOneProposalRadius q (initialVariance q)) x := by
  exact ofReal_halfPow_le_ell_of_closedBall_subset
    (accuracyPhaseInradius_pos q (initialVariance_pos q))
    (figureOneProposalRadius_pos q (initialVariance_pos q))
    (figureOneProposalRadius_le_accuracyPhaseInradius q (initialVariance_pos q))
    (fun y hy => by
      have hnorm : ‖y‖ ≤ accuracyPhaseInradius q (initialVariance q) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy
      refine ⟨unitBall_subset_truncatedBody q I ?_, ?_⟩
      · rw [unitBall, Metric.mem_closedBall, dist_zero_right]
        exact hnorm.trans (min_le_left _ _)
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hnorm.trans (min_le_right _ _)) hx

/-! ## Mass discarded by the initial inball restriction -/

theorem initialGaussianSamplingMeasure_unitBall_compl_le
    (q : VolumeParams) :
    initialGaussianSamplingMeasure q (unitBall q.n)ᶜ ≤
      ENNReal.ofReal (q.eps / 64) := by
  simp only [unitBall]
  rw [initialGaussianSamplingMeasure_apply q
    (measurableSet_closedBall : MeasurableSet
      (Metric.closedBall (0 : AmbientSpace q.n) 1)).compl]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (initialGaussianIntegral_pos q)]
  simpa [unitBall] using initial_tail_mass_le q

/-- After normalising on the truncated body, the initial Gaussian still puts
at most `eps/32` outside the unit ball. -/
theorem initialTruncatedGaussian_unitBall_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
        (unitBall q.n)ᶜ ≤ ENNReal.ofReal (q.eps / 32) := by
  let mu : Measure (AmbientSpace q.n) := initialGaussianSamplingMeasure q
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
  let c : ENNReal := ENNReal.ofReal
    (gaussianIntegral (truncatedBody q I) (initialVariance q) /
      initialGaussianIntegral q)
  have hrel := initialGaussianSamplingMeasure_restrict_truncatedBody q I
  have htailK : mu (truncatedBody q I)ᶜ ≤ ENNReal.ofReal (q.eps / 64) := by
    simpa [mu] using initialGaussianSamplingMeasure_truncatedBody_compl_le q I
  have hhalf_ofReal : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hepshalf : ENNReal.ofReal (q.eps / 64) ≤ 1 / 2 := by
    rw [hhalf_ofReal]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [q.heps.2.le]
  have hhalfK : 1 / 2 ≤ mu (truncatedBody q I) := by
    have h := half_le_measure_compl
      (sigma := mu) (S := (truncatedBody q I)ᶜ)
      (truncatedBody_measurable q I).compl (htailK.trans hepshalf)
    simpa using h
  have hcEq : c = mu (truncatedBody q I) := by
    have h := congrArg (fun m : Measure (AmbientSpace q.n) => m Set.univ) hrel
    simpa [mu, nu, c, Measure.restrict_apply_univ,
      Measure.smul_apply, smul_eq_mul] using h.symm
  have hhalfC : 1 / 2 ≤ c := by
    calc
      1 / 2 ≤ mu (truncatedBody q I) := hhalfK
      _ = c := hcEq.symm
  let A : Set (AmbientSpace q.n) := (unitBall q.n)ᶜ
  have hrelA := congrArg (fun m : Measure (AmbientSpace q.n) => m A) hrel
  have hAK : mu (A ∩ truncatedBody q I) = c * nu A := by
    rw [Measure.restrict_apply (by
      dsimp [A]
      exact measurableSet_closedBall.compl)] at hrelA
    simpa [A, mu, nu, c, Measure.smul_apply, smul_eq_mul] using hrelA
  have hprod : c * nu A ≤ ENNReal.ofReal (q.eps / 64) := by
    rw [← hAK]
    exact (measure_mono Set.inter_subset_left).trans (by
      simpa [A, mu] using initialGaussianSamplingMeasure_unitBall_compl_le q)
  have htwoHalf : (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  change nu A ≤ ENNReal.ofReal (q.eps / 32)
  calc
    nu A = 2 * ((1 / 2 : ENNReal) * nu A) := by
      rw [hhalf_ofReal, ← mul_assoc, htwoHalf, one_mul]
    _ ≤ 2 * (c * nu A) := by gcongr
    _ ≤ 2 * ENNReal.ofReal (q.eps / 64) := by gcongr
    _ = ENNReal.ofReal (q.eps / 32) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- The first phase's guaranteed inball loses only the sum of the ordinary
initial tail and the accuracy radial tail. -/
theorem initialTruncatedGaussian_accuracyInball_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
      (Metric.closedBall 0
        (accuracyPhaseInradius q (initialVariance q)))ᶜ ≤
      ENNReal.ofReal (q.eps / 32) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16) := by
  by_cases hR : accuracyPhaseRadius q (initialVariance q) ≤ 1
  · have hbody : accuracyPhaseTruncatedBody q I (initialVariance q) =
        Metric.closedBall 0 (accuracyPhaseRadius q (initialVariance q)) := by
      ext x
      constructor
      · exact fun hx => hx.2
      · intro hx
        refine ⟨unitBall_subset_truncatedBody q I ?_, hx⟩
        rw [unitBall, Metric.mem_closedBall, dist_zero_right]
        have : ‖x‖ ≤ accuracyPhaseRadius q (initialVariance q) := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx
        exact this.trans hR
    rw [accuracyPhaseInradius, min_eq_right hR, ← hbody]
    exact (truncatedGaussianProbability_accuracyPhase_compl_le
      q I (initialVariance_pos q)).trans (le_add_left le_rfl)
  · have hR1 : 1 ≤ accuracyPhaseRadius q (initialVariance q) := le_of_not_ge hR
    rw [accuracyPhaseInradius, min_eq_left hR1]
    exact (initialTruncatedGaussian_unitBall_compl_le q I).trans
      (le_add_right le_rfl)

theorem initialTruncatedGaussian_accuracyInball_compl_le_half
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
      (Metric.closedBall 0
        (accuracyPhaseInradius q (initialVariance q)))ᶜ ≤ 1 / 2 := by
  refine (initialTruncatedGaussian_accuracyInball_compl_le q I).trans ?_
  have hratio : q.eps / (q.n : ℝ) ≤ 1 / 3 := by
    have hn : (0 : ℝ) < q.n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
    apply (div_le_iff₀ hn).2
    have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    nlinarith [q.heps.2.le]
  have hratio0 : 0 ≤ q.eps / (q.n : ℝ) :=
    div_nonneg q.heps.1.le (Nat.cast_nonneg q.n)
  rw [← ENNReal.ofReal_add
    (div_nonneg q.heps.1.le (by norm_num : (0 : ℝ) ≤ 32))
    (pow_nonneg hratio0 16)]
  have hhalf_ofReal : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf_ofReal]
  apply ENNReal.ofReal_le_ofReal
  calc
    q.eps / 32 + (q.eps / (q.n : ℝ)) ^ 16 ≤
        1 / 32 + (1 / 3 : ℝ) ^ 16 := by
      gcongr
      exact q.heps.2.le
    _ ≤ 1 / 2 := by norm_num

/-! ## Initial warmness -/

noncomputable def initialSpeedyWarmConstant (q : VolumeParams) : ℝ :=
  2 * (2 : ℝ) ^ q.n

theorem initialSpeedyWarmConstant_pos (q : VolumeParams) :
    0 < initialSpeedyWarmConstant q := by
  unfold initialSpeedyWarmConstant
  positivity

/-- The initial truncated Gaussian restricted to the guaranteed phase inball
is `2^n`-dominated by the first speedy stationary law. -/
theorem initialTruncatedGaussian_inball_dom_speedy
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let good : Set (AmbientSpace q.n) :=
      Metric.closedBall 0 (accuracyPhaseInradius q (initialVariance q))
    let pi : Measure (AmbientSpace q.n) :=
      ellGaussianProb
        (accuracyPhaseTruncatedBody q I (initialVariance q))
        (figureOneProposalRadius q (initialVariance q)) (initialVariance q)
    ∀ A, MeasurableSet A →
      sigma (A ∩ good) ≤ ENNReal.ofReal ((2 : ℝ) ^ q.n) * pi A := by
  dsimp only
  intro A hA
  let s := initialVariance q
  let K := accuracyPhaseTruncatedBody q I s
  let good := Metric.closedBall (0 : AmbientSpace q.n) (accuracyPhaseInradius q s)
  let delta := figureOneProposalRadius q s
  let F : ENNReal := ENNReal.ofReal (gaussianIntegral (truncatedBody q I) s)
  let z : ENNReal := ellGaussianMeasure K delta s Set.univ
  let N : ENNReal := ∫⁻ x in A ∩ good, gaussianWeight s x
  let E : ENNReal := ellGaussianMeasure K delta s A
  let C : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ q.n)
  have hs : 0 < s := initialVariance_pos q
  have hgoodK : good ⊆ K := by
    intro x hx
    dsimp [good, K, s] at hx ⊢
    have hnorm : ‖x‖ ≤ accuracyPhaseInradius q (initialVariance q) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact ⟨unitBall_subset_truncatedBody q I (by
      rw [unitBall, Metric.mem_closedBall, dist_zero_right]
      exact hnorm.trans (min_le_left _ _)), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnorm.trans (min_le_right _ _)⟩
  have hzF : z ≤ F := by
    calc
      z ≤ ∫⁻ x in K, gaussianWeight s x :=
        ellGaussianMeasure_univ_le_gaussianMass delta s
      _ ≤ ∫⁻ x in truncatedBody q I, gaussianWeight s x :=
        lintegral_mono_set (fun _ hx => hx.1)
      _ = F := by
        dsimp [F]
        exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
          (truncatedBody_measurable q I) hs
  have hfloor : ∀ x ∈ good,
      ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) ≤ ell K delta x := by
    intro x hx
    simpa [s, K, good, delta] using initial_accuracyPhase_ell_floor q I hx
  have hCtheta : C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n) = 1 := by
    dsimp [C]
    rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q.n)]
    rw [← ENNReal.ofReal_one]
    congr 1
    rw [← mul_pow]
    norm_num
  have hNE : N ≤ C * E := by
    dsimp [N, E]
    rw [ellGaussianMeasure, withDensity_apply _ hA,
      Measure.restrict_restrict hA]
    have hmeasEll : Measurable fun x : AmbientSpace q.n =>
        ell K delta x * gaussianWeight s x :=
      measurable_ell_mul_gaussianWeight
        (by dsimp [K]; exact accuracyPhaseTruncatedBody_measurable q I s) delta s
    rw [← lintegral_const_mul _ hmeasEll]
    calc
      (∫⁻ x in A ∩ good, gaussianWeight s x) ≤
          ∫⁻ x in A ∩ good, C * (ell K delta x * gaussianWeight s x) := by
        apply setLIntegral_mono'
        · exact hA.inter measurableSet_closedBall
        · intro x hx
          calc
            gaussianWeight s x = 1 * gaussianWeight s x := (one_mul _).symm
            _ = (C * ENNReal.ofReal (((1 : ℝ) / 2) ^ q.n)) *
                gaussianWeight s x := by rw [hCtheta]
            _ ≤ C * (ell K delta x * gaussianWeight s x) := by
              rw [mul_assoc]
              exact mul_le_mul' le_rfl (mul_le_mul' (hfloor x hx.2) le_rfl)
      _ ≤ ∫⁻ x in A ∩ K, C * (ell K delta x * gaussianWeight s x) := by
        exact lintegral_mono_set (fun x hx => ⟨hx.1, hgoodK hx.2⟩)
  rw [truncatedGaussianProbability_apply q I hs (hA.inter measurableSet_closedBall)]
  have hweightEq : (fun x : AmbientSpace q.n =>
      ENNReal.ofReal (gaussianDensity s x)) = gaussianWeight s := by
    funext x
    simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]
  rw [show (A ∩ good) ∩ truncatedBody q I = A ∩ good by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, (hgoodK hx.2).1⟩]
  simp_rw [hweightEq]
  change F⁻¹ * N ≤ C * (z⁻¹ * E)
  calc
    F⁻¹ * N ≤ F⁻¹ * (C * E) := mul_le_mul' le_rfl hNE
    _ = C * (F⁻¹ * E) := by ac_rfl
    _ ≤ C * (z⁻¹ * E) := by
      exact mul_le_mul' le_rfl (mul_le_mul' (ENNReal.inv_le_inv.2 hzF) le_rfl)

/-- Conditioning away the small initial exceptional set gives a probability
law that is warm for the first speedy phase. -/
theorem initialAccuracySpeedy_restrictOff_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let bad : Set (AmbientSpace q.n) :=
      (Metric.closedBall 0
        (accuracyPhaseInradius q (initialVariance q)))ᶜ
    IsWarm (ENNReal.ofReal (initialSpeedyWarmConstant q))
      (restrictOff sigma bad)
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I (initialVariance q))
        (figureOneProposalRadius q (initialVariance q)) (initialVariance q)) := by
  dsimp only
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
  let good : Set (AmbientSpace q.n) :=
    Metric.closedBall 0 (accuracyPhaseInradius q (initialVariance q))
  let bad : Set (AmbientSpace q.n) := goodᶜ
  let pi : Measure (AmbientSpace q.n) :=
    ellGaussianProb
      (accuracyPhaseTruncatedBody q I (initialVariance q))
      (figureOneProposalRadius q (initialVariance q)) (initialVariance q)
  have hbad : sigma bad ≤ 1 / 2 := by
    simpa [sigma, bad, good] using
      initialTruncatedGaussian_accuracyInball_compl_le_half q I
  have hdom : ∀ A : Set (AmbientSpace q.n), MeasurableSet A →
      sigma (A \ bad) ≤ ENNReal.ofReal ((2 : ℝ) ^ q.n) * pi A := by
    intro A hA
    have h := initialTruncatedGaussian_inball_dom_speedy q I A hA
    simpa [sigma, pi, bad, good, Set.diff_compl] using h
  have hw := isWarm_restrictOff (sigma := sigma) (pi := pi)
    (measurableSet_closedBall.compl) hbad hdom
  simpa [initialSpeedyWarmConstant, sigma, pi, bad, good,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using hw

/-- The restriction moves the initial target by at most the already-budgeted
initial-inball tail. -/
theorem initialAccuracySpeedy_restrictOff_tvLe
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let bad : Set (AmbientSpace q.n) :=
      (Metric.closedBall 0
        (accuracyPhaseInradius q (initialVariance q)))ᶜ
    TVLe (restrictOff sigma bad) sigma
      (ENNReal.ofReal (q.eps / 32) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  exact (tvLe_restrictOff measurableSet_closedBall.compl
    (initialTruncatedGaussian_accuracyInball_compl_le_half q I)).symm.mono
      (initialTruncatedGaussian_accuracyInball_compl_le q I)

end ArlibCommunity.Algorithms.CV18
