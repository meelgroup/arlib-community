/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialSpeedyWarmStart

/-! # A constant-warm interior start for the first CV18 speedy phase -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Metric Set
open scoped ENNReal
open Arlib Arlib.MarkovChains

/-- Half of the centered inradius available in the first accuracy phase. -/
noncomputable def initialSpeedyInteriorRadius (q : VolumeParams) : ℝ :=
  accuracyPhaseInradius q (initialVariance q) / 2

theorem initialSpeedyInteriorRadius_pos (q : VolumeParams) :
    0 < initialSpeedyInteriorRadius q := by
  unfold initialSpeedyInteriorRadius
  exact div_pos (accuracyPhaseInradius_pos q (initialVariance_pos q)) (by norm_num)

theorem figureOneInitialProposalRadius_le_interiorRadius (q : VolumeParams) :
    figureOneProposalRadius q (initialVariance q) ≤
      initialSpeedyInteriorRadius q := by
  have h := figureOneProposalRadius_le_accuracyPhaseLVStep q (initialVariance_pos q)
  have hsqrt : (2 : ℝ) ≤ 4096 * Real.sqrt q.n := by
    have hn : (1 : ℝ) ≤ q.n := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
    have hs : 1 ≤ Real.sqrt (q.n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hn
    nlinarith
  have hmin : min (Real.sqrt (initialVariance q))
      (accuracyPhaseInradius q (initialVariance q)) ≤
      accuracyPhaseInradius q (initialVariance q) := min_le_right _ _
  calc
    figureOneProposalRadius q (initialVariance q) ≤
        min (Real.sqrt (initialVariance q))
            (accuracyPhaseInradius q (initialVariance q)) /
          (4096 * Real.sqrt q.n) := h
    _ ≤ accuracyPhaseInradius q (initialVariance q) /
          (4096 * Real.sqrt q.n) := by gcongr
    _ ≤ accuracyPhaseInradius q (initialVariance q) / 2 := by
      exact div_le_div_of_nonneg_left
        (accuracyPhaseInradius_pos q (initialVariance_pos q)).le
        (by norm_num) hsqrt
    _ = initialSpeedyInteriorRadius q := rfl

/-- Every proposal from the half-inball remains inside the first phase body,
so the local conductance is exactly one rather than merely `2^{-n}`. -/
theorem initialAccuracyPhase_ell_eq_one
    (q : VolumeParams) (I : VolumeInput q.n)
    {x : AmbientSpace q.n}
    (hx : x ∈ Metric.closedBall 0 (initialSpeedyInteriorRadius q)) :
    ell (accuracyPhaseTruncatedBody q I (initialVariance q))
      (figureOneProposalRadius q (initialVariance q)) x = 1 := by
  let rho := accuracyPhaseInradius q (initialVariance q)
  let delta := figureOneProposalRadius q (initialVariance q)
  have hdelta : 0 < delta := figureOneProposalRadius_pos q (initialVariance_pos q)
  have hsub : Metric.ball x delta ⊆
      accuracyPhaseTruncatedBody q I (initialVariance q) := by
    intro y hy
    apply ball_accuracyPhaseInradius_subset q I (initialVariance q)
    rw [Metric.mem_ball]
    have hyx : dist y x < delta := Metric.mem_ball.1 hy
    have hx0 : dist x 0 ≤ rho / 2 := by
      simpa [initialSpeedyInteriorRadius, rho] using hx
    have hd : delta ≤ rho / 2 := by
      simpa [delta, rho, initialSpeedyInteriorRadius] using
        figureOneInitialProposalRadius_le_interiorRadius q
    calc
      dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ < delta + rho / 2 := by linarith
      _ ≤ rho := by linarith
  rw [ell_apply, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.div_self (Metric.measure_ball_pos volume x hdelta).ne'
      measure_ball_lt_top.ne]

/-- The half-inball is still many Gaussian standard deviations wide at the
initial variance.  This coarse `1/8` tail coefficient is enough for constant
warmness. -/
theorem initialInterior_tail_coefficient_le (q : VolumeParams) :
    Real.exp (-(initialSpeedyInteriorRadius q) ^ 2 /
        (4 * initialVariance q)) * Real.sqrt 2 ^ q.n ≤ 1 / 8 := by
  let s := initialVariance q
  let R := accuracyPhaseRadius q s
  let L := protectedLog ((q.n : ℝ) / q.eps)
  have hs : 0 < s := initialVariance_pos q
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hn0 : (0 : ℝ) < q.n := by linarith
  have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hsqrt2 : Real.sqrt 2 ≤ Real.exp 1 := by
    have hle : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 2,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hle.trans Real.exp_one_gt_two.le
  have hpow : Real.sqrt 2 ^ q.n ≤ Real.exp (q.n : ℝ) := by
    calc
      Real.sqrt 2 ^ q.n ≤ Real.exp 1 ^ q.n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt2 _
      _ = Real.exp (q.n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hexp8 : Real.exp (-8) ≤ (1 : ℝ) / 8 := by
    calc
      Real.exp (-8) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 1 / 64 := exp_neg_six_le_one_div_64
      _ ≤ 1 / 8 := by norm_num
  by_cases hR : R ≤ 1
  · have hsqs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have hnL0 : 0 ≤ (q.n : ℝ) * L := by positivity
    have hsqnL : Real.sqrt ((q.n : ℝ) * L) ^ 2 = (q.n : ℝ) * L :=
      Real.sq_sqrt hnL0
    have hradius : (R / 2) ^ 2 / (4 * s) = 64 * (q.n : ℝ) * L := by
      dsimp [R, accuracyPhaseRadius]
      change (32 * Real.sqrt s * Real.sqrt ((q.n : ℝ) * L) / 2) ^ 2 /
        (4 * s) = _
      rw [div_pow, mul_pow, mul_pow, hsqs, hsqnL]
      field_simp [hs.ne']
      ring
    have hinterior : initialSpeedyInteriorRadius q = R / 2 := by
      simp [initialSpeedyInteriorRadius, accuracyPhaseInradius, s, R, min_eq_right hR]
    rw [hinterior, show -(R / 2) ^ 2 / (4 * s) =
      -((R / 2) ^ 2 / (4 * s)) by ring, hradius]
    calc
      Real.exp (-(64 * (q.n : ℝ) * L)) * Real.sqrt 2 ^ q.n ≤
          Real.exp (-(64 * (q.n : ℝ) * L)) * Real.exp (q.n : ℝ) := by
        gcongr
      _ = Real.exp (-(64 * (q.n : ℝ) * L) + (q.n : ℝ)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (-8) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ 1 / 8 := hexp8
  · have hR1 : 1 ≤ R := le_of_not_ge hR
    have hinterior : initialSpeedyInteriorRadius q = 1 / 2 := by
      simp [initialSpeedyInteriorRadius, accuracyPhaseInradius, s, R,
        min_eq_left hR1]
    have hsform : s = q.eps / (64 * (q.n : ℝ)) := rfl
    rw [hinterior]
    have hexponent : -((1 / 2 : ℝ) ^ 2) / (4 * s) =
        -(4 * (q.n : ℝ) / q.eps) := by
      rw [hsform]
      field_simp [q.heps.1.ne', hn0.ne']
      ring
    rw [hexponent]
    calc
      Real.exp (-(4 * (q.n : ℝ) / q.eps)) * Real.sqrt 2 ^ q.n ≤
          Real.exp (-(4 * (q.n : ℝ) / q.eps)) * Real.exp (q.n : ℝ) := by
        gcongr
      _ = Real.exp (-(4 * (q.n : ℝ) / q.eps) + (q.n : ℝ)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (-8) := by
        apply Real.exp_le_exp.mpr
        have he : q.eps ≤ 1 := q.heps.2.le
        have hdiv : 4 * (q.n : ℝ) ≤ 4 * (q.n : ℝ) / q.eps := by
          rw [le_div_iff₀ q.heps.1]
          nlinarith
        nlinarith
      _ ≤ 1 / 8 := hexp8

/-- The full initial Gaussian puts at most one eighth of its mass outside the
half-inball. -/
theorem initialGaussian_interior_tail_le (q : VolumeParams) :
    (∫ x in (Metric.closedBall (0 : AmbientSpace q.n)
        (initialSpeedyInteriorRadius q))ᶜ,
        gaussianDensity (initialVariance q) x) ≤
      (1 / 8 : ℝ) * initialGaussianIntegral q := by
  let s := initialVariance q
  let r := initialSpeedyInteriorRadius q
  have hs : 0 < s := initialVariance_pos q
  have hr : 0 ≤ r := (initialSpeedyInteriorRadius_pos q).le
  have htail := gaussianIntegral_tail_radius_le
    (K := (Set.univ : Set (AmbientSpace q.n))) MeasurableSet.univ hs hr
  have hscale := gaussianIntegral_scaling_le
    (Set.univ : Set (AmbientSpace q.n)) MeasurableSet.univ convex_univ
    (Set.mem_univ (0 : AmbientSpace q.n)) hs (by linarith : s ≤ 2 * s)
  have hsqrt : Real.sqrt ((2 * s) / s) = Real.sqrt 2 := by
    congr 1
    field_simp [hs.ne']
  rw [hsqrt] at hscale
  have hZ : gaussianIntegral (Set.univ : Set (AmbientSpace q.n)) s =
      initialGaussianIntegral q := by
    simpa [s, initialGaussianIntegral] using gaussianIntegral_univ (n := q.n) hs
  have hset : (Metric.closedBall (0 : AmbientSpace q.n) r)ᶜ =
      (Set.univ : Set (AmbientSpace q.n)) \ Metric.closedBall 0 r := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_univ, true_and]
  calc
    (∫ x in (Metric.closedBall (0 : AmbientSpace q.n) r)ᶜ,
        gaussianDensity s x) =
        ∫ x in (Set.univ : Set (AmbientSpace q.n)) \
          Metric.closedBall 0 r, gaussianDensity s x := by
      rw [hset]
    _ ≤ Real.exp (-(r ^ 2) / (4 * s)) *
        gaussianIntegral (Set.univ : Set (AmbientSpace q.n)) (2 * s) := htail
    _ ≤ Real.exp (-(r ^ 2) / (4 * s)) *
        (Real.sqrt 2 ^ q.n * gaussianIntegral Set.univ s) := by
      gcongr
    _ = (Real.exp (-(r ^ 2) / (4 * s)) * Real.sqrt 2 ^ q.n) *
        gaussianIntegral Set.univ s := by ring
    _ ≤ (1 / 8 : ℝ) * gaussianIntegral Set.univ s := by
      apply mul_le_mul_of_nonneg_right
      · simpa [s, r] using initialInterior_tail_coefficient_le q
      · rw [gaussianIntegral_univ hs]
        exact (Real.rpow_pos_of_pos (by positivity) _).le
    _ = (1 / 8 : ℝ) * initialGaussianIntegral q := by rw [hZ]

/-- The first restricted Gaussian loses at most one quarter of its mass when
conditioned onto the half-inball. -/
theorem initialTruncatedGaussian_interior_compl_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n))
      (Metric.closedBall 0 (initialSpeedyInteriorRadius q))ᶜ ≤
        ENNReal.ofReal (1 / 4 : ℝ) := by
  let s := initialVariance q
  let K := truncatedBody q I
  let B := Metric.closedBall (0 : AmbientSpace q.n) (initialSpeedyInteriorRadius q)
  let Z := gaussianIntegral K s
  let Zfull := initialGaussianIntegral q
  let tail := ∫ x in K \ B, gaussianDensity s x
  have hs : 0 < s := initialVariance_pos q
  have hK : MeasurableSet K := truncatedBody_measurable q I
  have htail : tail ≤ (1 / 8 : ℝ) * Zfull := by
    calc
      tail ≤ ∫ x in Bᶜ, gaussianDensity s x := by
        apply setIntegral_mono_set (integrable_gaussianDensity hs).integrableOn
        · filter_upwards with x
          exact (Real.exp_pos _).le
        · filter_upwards with x
          intro hx
          exact hx.2
      _ ≤ (1 / 8 : ℝ) * Zfull := by
        simpa [s, B, Zfull] using initialGaussian_interior_tail_le q
  have hZ0 : 0 < Z := by
    dsimp [Z, K, s]
    exact gaussianIntegral_pos q (truncatedVolumeInput q I) (initialVariance_pos q)
  have hrel := volume_proof_truncated_initial_tail q I
  have hZfull : Zfull ≤ 2 * Z := by
    have hupper : Zfull ≤ (1 + q.eps / 32) * Z := by
      simpa [Zfull, Z, K, s, RelativeApprox, Arlib.relErr] using hrel.2
    calc
      Zfull ≤ (1 + q.eps / 32) * Z := hupper
      _ ≤ 2 * Z := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [q.heps.2.le]) hZ0.le
  have htailZ : tail ≤ (1 / 4 : ℝ) * Z := by
    calc
      tail ≤ (1 / 8 : ℝ) * Zfull := htail
      _ ≤ (1 / 8 : ℝ) * (2 * Z) := by gcongr
      _ = (1 / 4 : ℝ) * Z := by ring
  rw [truncatedGaussianProbability_apply q I hs measurableSet_closedBall.compl]
  have hset : Bᶜ ∩ K = K \ B := by ext x; simp [and_comm]
  rw [show (Metric.closedBall (0 : AmbientSpace q.n)
      (initialSpeedyInteriorRadius q))ᶜ = Bᶜ by rfl, hset]
  have hInt : IntegrableOn (gaussianDensity s) (K \ B) :=
    (integrable_gaussianDensity hs).integrableOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (K \ B)] gaussianDensity s :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  change (ENNReal.ofReal Z)⁻¹ * ENNReal.ofReal tail ≤ ENNReal.ofReal (1 / 4 : ℝ)
  rw [← ENNReal.ofReal_inv_of_pos hZ0,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Z⁻¹)]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_mul_eq_div, div_le_iff₀ hZ0]
  simpa [mul_comm] using htailZ

/-- On the interior event, the initial restricted Gaussian is pointwise
dominated by the first speedy stationary probability with coefficient one. -/
theorem initialTruncatedGaussian_interior_dom_speedy
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let good := Metric.closedBall (0 : AmbientSpace q.n)
      (initialSpeedyInteriorRadius q)
    let pi := ellGaussianProb
      (accuracyPhaseTruncatedBody q I (initialVariance q))
      (figureOneProposalRadius q (initialVariance q)) (initialVariance q)
    ∀ A, MeasurableSet A → sigma (A ∩ good) ≤ pi A := by
  dsimp only
  intro A hA
  let s := initialVariance q
  let K := accuracyPhaseTruncatedBody q I s
  let delta := figureOneProposalRadius q s
  let good := Metric.closedBall (0 : AmbientSpace q.n) (initialSpeedyInteriorRadius q)
  let F := ENNReal.ofReal (gaussianIntegral (truncatedBody q I) s)
  let z := ellGaussianMeasure K delta s Set.univ
  let N := ∫⁻ x in A ∩ good, gaussianWeight s x
  let E := ellGaussianMeasure K delta s A
  have hs : 0 < s := initialVariance_pos q
  have hgoodK : good ⊆ K := by
    intro x hx
    apply ball_accuracyPhaseInradius_subset q I s
    have hx' : dist x 0 ≤ initialSpeedyInteriorRadius q := by
      simpa [good] using hx
    exact lt_of_le_of_lt hx' (by
      dsimp [initialSpeedyInteriorRadius, s]
      have h := accuracyPhaseInradius_pos q (initialVariance_pos q)
      linarith)
  have hzF : z ≤ F := by
    calc
      z ≤ ∫⁻ x in K, gaussianWeight s x :=
        ellGaussianMeasure_univ_le_gaussianMass delta s
      _ ≤ ∫⁻ x in truncatedBody q I, gaussianWeight s x :=
        lintegral_mono_set fun _ hx => hx.1
      _ = F := lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hs
  have hNE : N ≤ E := by
    dsimp [N, E]
    rw [ellGaussianMeasure, withDensity_apply _ hA,
      Measure.restrict_restrict hA]
    calc
      (∫⁻ x in A ∩ good, gaussianWeight s x) =
          ∫⁻ x in A ∩ good, ell K delta x * gaussianWeight s x := by
        apply setLIntegral_congr_fun (hA.inter measurableSet_closedBall)
        intro x hx
        change gaussianWeight s x = ell K delta x * gaussianWeight s x
        rw [show ell K delta x = 1 by
          simpa [K, delta, s, good] using initialAccuracyPhase_ell_eq_one q I hx.2,
          one_mul]
      _ ≤ ∫⁻ x in A ∩ K, ell K delta x * gaussianWeight s x :=
        lintegral_mono_set fun x hx => ⟨hx.1, hgoodK hx.2⟩
  rw [truncatedGaussianProbability_apply q I hs
    (hA.inter measurableSet_closedBall)]
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
  change F⁻¹ * N ≤ z⁻¹ * E
  calc
    F⁻¹ * N ≤ F⁻¹ * E := by gcongr
    _ ≤ z⁻¹ * E := by gcongr

/-- The conditioned initial law is universally `2`-warm for the first
speedy phase. -/
theorem initialAccuracySpeedy_interior_restrictOff_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) :
    let sigma : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
    let bad := (Metric.closedBall (0 : AmbientSpace q.n)
      (initialSpeedyInteriorRadius q))ᶜ
    IsWarm (2 : ENNReal) (restrictOff sigma bad)
      (ellGaussianProb
        (accuracyPhaseTruncatedBody q I (initialVariance q))
        (figureOneProposalRadius q (initialVariance q)) (initialVariance q)) := by
  dsimp only
  let sigma : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (initialVariance q) (initialVariance_pos q)
  let good := Metric.closedBall (0 : AmbientSpace q.n) (initialSpeedyInteriorRadius q)
  let bad := goodᶜ
  let pi := ellGaussianProb
    (accuracyPhaseTruncatedBody q I (initialVariance q))
    (figureOneProposalRadius q (initialVariance q)) (initialVariance q)
  have hbad : sigma bad ≤ 1 / 2 := by
    calc
      sigma bad ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
        simpa [sigma, bad, good] using initialTruncatedGaussian_interior_compl_le q I
      _ ≤ 1 / 2 := by
        rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hdom : ∀ A : Set (AmbientSpace q.n), MeasurableSet A →
      sigma (A \ bad) ≤ 1 * pi A := by
    intro A hA
    have h := initialTruncatedGaussian_interior_dom_speedy q I A hA
    simpa [sigma, pi, bad, good, Set.diff_compl] using h
  have hw := isWarm_restrictOff (sigma := sigma) (pi := pi)
    (measurableSet_closedBall.compl) hbad hdom
  simpa [sigma, pi, bad, good] using hw

end ArlibCommunity.Algorithms.CV18
