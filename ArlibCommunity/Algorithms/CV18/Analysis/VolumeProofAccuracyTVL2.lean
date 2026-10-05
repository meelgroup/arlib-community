/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceMoments

/-! # Total-variation transfer for unbounded CV18 observables

The KLS accepted law is close in total variation to the desired Gaussian and
is also uniformly warm with respect to it.  Total variation alone controls
only bounded observables.  Truncating a nonnegative observable and using the
warm second-moment bound on the two tails gives the interpolation estimate
needed for the (unbounded) Gaussian ratio weights.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A TV bound plus warm domination transfers the expectation of a
nonnegative `L²` observable.  The free truncation level `T` is retained so
later phase estimates can optimize it against their concrete TV error. -/
theorem TVLe.integral_nonnegative_le_of_isWarm_secondMoment
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon M : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    (hM : M ≠ ⊤) (hwarm : Arlib.IsWarm M mu nu)
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfmem : MemLp f 2 nu) {T : Real} (hT : 0 < T) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
      epsilon.toReal * T +
        (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / T := by
  let cut : S → ℝ := fun x => min (f x) T
  let g : S → ℝ := fun x => cut x / T
  have hle : mu ≤ M • nu :=
    (Arlib.MarkovChains.isWarm_iff_le_smul _ _).1 hwarm
  have hfmemLarge : MemLp f 2 (M • nu) := hfmem.smul_measure hM
  have hfmemMu : MemLp f 2 mu := hfmemLarge.mono_measure hle
  have hfintNu : Integrable f nu := hfmem.integrable (by norm_num)
  have hfintMu : Integrable f mu := hfmemMu.integrable (by norm_num)
  have hcutMeas : Measurable cut := by
    dsimp [cut]
    exact hf.min measurable_const
  have hcut0 : ∀ x, 0 ≤ cut x := by
    intro x
    dsimp [cut]
    exact le_min (hf0 x) hT.le
  have hcutT : ∀ x, cut x ≤ T := by
    intro x
    exact min_le_right _ _
  have hcutIntMu : Integrable cut mu := by
    refine Integrable.mono' (integrable_const T)
      hcutMeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hcut0 x)]
    exact hcutT x
  have hcutIntNu : Integrable cut nu := by
    refine Integrable.mono' (integrable_const T)
      hcutMeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hcut0 x)]
    exact hcutT x
  have hgMeas : Measurable g := hcutMeas.div_const T
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    exact div_nonneg (hcut0 x) hT.le
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    exact (div_le_one hT).2 (hcutT x)
  have hmiddleScaled := htv.integral_le hepsilon hgMeas hg0 hg1
  have hcutEqMu : (∫ x, cut x ∂mu) = T * ∫ x, g x ∂mu := by
    rw [show cut = fun x => T * g x by
      funext x
      dsimp [g]
      field_simp [hT.ne']]
    exact integral_const_mul T g
  have hcutEqNu : (∫ x, cut x ∂nu) = T * ∫ x, g x ∂nu := by
    rw [show cut = fun x => T * g x by
      funext x
      dsimp [g]
      field_simp [hT.ne']]
    exact integral_const_mul T g
  have hmiddle : |(∫ x, cut x ∂mu) - ∫ x, cut x ∂nu| ≤
      epsilon.toReal * T := by
    rw [hcutEqMu, hcutEqNu, ← mul_sub, abs_mul,
      abs_of_pos hT, mul_comm]
    exact mul_le_mul_of_nonneg_right hmiddleScaled hT.le
  have htailPoint : ∀ x, 0 ≤ f x - cut x := by
    intro x
    dsimp [cut]
    exact sub_nonneg.mpr (min_le_left _ _)
  have htailSq : ∀ x, f x - cut x ≤ f x ^ 2 / T := by
    intro x
    dsimp [cut]
    by_cases h : f x <= T
    · rw [min_eq_left h]
      simpa using div_nonneg (sq_nonneg (f x)) hT.le
    · rw [min_eq_right (le_of_not_ge h)]
      rw [le_div_iff₀ hT]
      nlinarith [sq_nonneg (f x), hf0 x]
  have hsqIntNu : Integrable (fun x => f x ^ 2) nu := hfmem.integrable_sq
  have hsqIntMu : Integrable (fun x => f x ^ 2) mu := hfmemMu.integrable_sq
  have htailIntMu : Integrable (fun x => f x - cut x) mu :=
    hfintMu.sub hcutIntMu
  have htailIntNu : Integrable (fun x => f x - cut x) nu :=
    hfintNu.sub hcutIntNu
  have htailMu : |(∫ x, f x ∂mu) - ∫ x, cut x ∂mu| ≤
      M.toReal * (∫ x, f x ^ 2 ∂nu) / T := by
    rw [← integral_sub hfintMu hcutIntMu,
      abs_of_nonneg (integral_nonneg htailPoint)]
    calc
      (∫ x, f x - cut x ∂mu) ≤
          ∫ x, f x ^ 2 / T ∂mu := by
        apply integral_mono htailIntMu (hsqIntMu.div_const T)
        exact htailSq
      _ = (∫ x, f x ^ 2 ∂mu) / T := by
        rw [integral_div]
      _ ≤ (M.toReal * (∫ x, f x ^ 2 ∂nu)) / T := by
        exact div_le_div_of_nonneg_right
          (integral_sq_le_of_isWarm_cv18 hM hwarm hfmem) hT.le
      _ = M.toReal * (∫ x, f x ^ 2 ∂nu) / T := rfl
  have htailNu : |(∫ x, cut x ∂nu) - ∫ x, f x ∂nu| ≤
      (∫ x, f x ^ 2 ∂nu) / T := by
    rw [abs_sub_comm, ← integral_sub hfintNu hcutIntNu,
      abs_of_nonneg (integral_nonneg htailPoint)]
    calc
      (∫ x, f x - cut x ∂nu) ≤
          ∫ x, f x ^ 2 / T ∂nu := by
        apply integral_mono htailIntNu (hsqIntNu.div_const T)
        exact htailSq
      _ = (∫ x, f x ^ 2 ∂nu) / T := by
        rw [integral_div]
  calc
    |(∫ x, f x ∂mu) - ∫ x, f x ∂nu| =
        |((∫ x, f x ∂mu) - ∫ x, cut x ∂mu) +
          ((∫ x, cut x ∂mu) - ∫ x, cut x ∂nu) +
          ((∫ x, cut x ∂nu) - ∫ x, f x ∂nu)| := by ring_nf
    _ ≤ |(∫ x, f x ∂mu) - ∫ x, cut x ∂mu| +
          |(∫ x, cut x ∂mu) - ∫ x, cut x ∂nu| +
          |(∫ x, cut x ∂nu) - ∫ x, f x ∂nu| := by
      exact (abs_add_three _ _ _)
    _ ≤ (M.toReal * (∫ x, f x ^ 2 ∂nu) / T) +
          (epsilon.toReal * T) +
          ((∫ x, f x ^ 2 ∂nu) / T) := by gcongr
    _ = epsilon.toReal * T +
          (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / T := by ring

/-- Square-root form of the preceding truncation estimate.  Supplying
`epsilon.toReal ≤ eta²` avoids divisions by the (often syntactically large)
TV error in every cooling phase. -/
theorem TVLe.integral_nonnegative_le_of_isWarm_secondMoment_sqrt
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon M : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    (hM : M ≠ ⊤) (hwarm : Arlib.IsWarm M mu nu)
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfmem : MemLp f 2 nu) {eta : ℝ} (heta : 0 < eta)
    (hepsEta : epsilon.toReal ≤ eta ^ 2) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
      eta * (1 + (M.toReal + 1) * ∫ x, f x ^ 2 ∂nu) := by
  have hbase := TVLe.integral_nonnegative_le_of_isWarm_secondMoment
    htv hepsilon hM hwarm hf hf0 hfmem (T := eta⁻¹) (inv_pos.mpr heta)
  have hsq : 0 ≤ ∫ x, f x ^ 2 ∂nu :=
    integral_nonneg fun x => sq_nonneg (f x)
  calc
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
        epsilon.toReal * eta⁻¹ +
          (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / eta⁻¹ := hbase
    _ ≤ eta + (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) * eta := by
      have hfirst : epsilon.toReal * eta⁻¹ ≤ eta := by
        rw [mul_inv_le_iff₀ heta]
        simpa [pow_two] using hepsEta
      have hsecond :
          (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / eta⁻¹ =
            (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) * eta := by
        field_simp [heta.ne']
      rw [hsecond]
      exact add_le_add hfirst le_rfl
    _ = eta * (1 + (M.toReal + 1) * ∫ x, f x ^ 2 ∂nu) := by ring

/-- Signed version of the TV--warmness interpolation estimate.  Splitting an
observable into its positive and negative parts costs a factor two only in
the bounded TV term; the two squared tails recombine exactly to `f²`.  This
is the form needed for centered cooling-ratio observables. -/
theorem TVLe.integral_le_of_isWarm_secondMoment
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon M : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    (hM : M ≠ ⊤) (hwarm : Arlib.IsWarm M mu nu)
    {f : S → ℝ} (hf : Measurable f) (hfmem : MemLp f 2 nu)
    {T : ℝ} (hT : 0 < T) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
      2 * epsilon.toReal * T +
        (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / T := by
  let fp : S → ℝ := fun x => max (f x) 0
  let fn : S → ℝ := fun x => max (-f x) 0
  have hfpMeas : Measurable fp := hf.max measurable_const
  have hfnMeas : Measurable fn := hf.neg.max measurable_const
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hfpMem : MemLp fp 2 nu := by simpa [fp] using hfmem.pos_part
  have hfnMem : MemLp fn 2 nu := by simpa [fn] using hfmem.neg_part
  have hle : mu ≤ M • nu :=
    (Arlib.MarkovChains.isWarm_iff_le_smul _ _).1 hwarm
  have hfmemMu : MemLp f 2 mu :=
    (hfmem.smul_measure hM).mono_measure hle
  have hfpMemMu : MemLp fp 2 mu := by simpa [fp] using hfmemMu.pos_part
  have hfnMemMu : MemLp fn 2 mu := by simpa [fn] using hfmemMu.neg_part
  have hfDecomp : f = fun x => fp x - fn x := by
    funext x
    dsimp [fp, fn]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -f x ≤ 0)]
      ring
    · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -f x)]
      ring
  have hpos := TVLe.integral_nonnegative_le_of_isWarm_secondMoment
    htv hepsilon hM hwarm hfpMeas hfp0 hfpMem hT
  have hneg := TVLe.integral_nonnegative_le_of_isWarm_secondMoment
    htv hepsilon hM hwarm hfnMeas hfn0 hfnMem hT
  have hsquares :
      (∫ x, fp x ^ 2 ∂nu) + ∫ x, fn x ^ 2 ∂nu =
        ∫ x, f x ^ 2 ∂nu := by
    rw [← integral_add hfpMem.integrable_sq hfnMem.integrable_sq]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [fp, fn]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -f x ≤ 0)]
      ring
    · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -f x)]
      ring
  have hdecompMu : (∫ x, f x ∂mu) =
      (∫ x, fp x ∂mu) - ∫ x, fn x ∂mu := by
    rw [hfDecomp, integral_sub
      (hfpMemMu.integrable (by norm_num))
      (hfnMemMu.integrable (by norm_num))]
  have hdecompNu : (∫ x, f x ∂nu) =
      (∫ x, fp x ∂nu) - ∫ x, fn x ∂nu := by
    rw [hfDecomp, integral_sub
      (hfpMem.integrable (by norm_num))
      (hfnMem.integrable (by norm_num))]
  rw [hdecompMu, hdecompNu]
  calc
    |((∫ x, fp x ∂mu) - ∫ x, fn x ∂mu) -
        ((∫ x, fp x ∂nu) - ∫ x, fn x ∂nu)| =
        |((∫ x, fp x ∂mu) - ∫ x, fp x ∂nu) -
          ((∫ x, fn x ∂mu) - ∫ x, fn x ∂nu)| := by ring_nf
    _ ≤ |(∫ x, fp x ∂mu) - ∫ x, fp x ∂nu| +
          |(∫ x, fn x ∂mu) - ∫ x, fn x ∂nu| := abs_sub _ _
    _ ≤ (epsilon.toReal * T +
          (M.toReal + 1) * (∫ x, fp x ^ 2 ∂nu) / T) +
        (epsilon.toReal * T +
          (M.toReal + 1) * (∫ x, fn x ^ 2 ∂nu) / T) :=
      add_le_add hpos hneg
    _ = 2 * epsilon.toReal * T +
        (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / T := by
      rw [← hsquares]
      ring

/-- Homogeneous square-root form for a signed observable.  Unlike the
nonnegative estimate above, this bound vanishes with the `L²` scale `R`; it
therefore preserves the phase-amortized variance accounting of CV18. -/
theorem TVLe.integral_le_of_isWarm_secondMoment_sqrt
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon M : ENNReal}
    (htv : Arlib.TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    (hM : M ≠ ⊤) (hwarm : Arlib.IsWarm M mu nu)
    {f : S → ℝ} (hf : Measurable f) (hfmem : MemLp f 2 nu)
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hepsEta : epsilon.toReal ≤ eta ^ 2)
    (hsecond : (∫ x, f x ^ 2 ∂nu) ≤ R ^ 2) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
      (M.toReal + 3) * eta * R := by
  have hbase := TVLe.integral_le_of_isWarm_secondMoment
    htv hepsilon hM hwarm hf hfmem (T := R / eta) (div_pos hR heta)
  have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hsq0 : 0 ≤ ∫ x, f x ^ 2 ∂nu :=
    integral_nonneg fun x => sq_nonneg (f x)
  have hfirst :
      2 * epsilon.toReal * (R / eta) ≤ 2 * eta * R := by
    rw [show 2 * epsilon.toReal * (R / eta) =
      (2 * epsilon.toReal * R) / eta by ring]
    apply (div_le_iff₀ heta).2
    have hmul := mul_le_mul_of_nonneg_right hepsEta hR.le
    nlinarith
  have hsecondTerm :
      (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / (R / eta) ≤
        (M.toReal + 1) * R ^ 2 / (R / eta) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsecond (by positivity))
      (div_pos hR heta).le
  calc
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
        2 * epsilon.toReal * (R / eta) +
          (M.toReal + 1) * (∫ x, f x ^ 2 ∂nu) / (R / eta) := hbase
    _ ≤ 2 * eta * R + (M.toReal + 1) * R ^ 2 / (R / eta) :=
      add_le_add hfirst hsecondTerm
    _ = (M.toReal + 3) * eta * R := by
      field_simp [heta.ne', hR.ne']
      ring

/-- Square-root scale of the stationary KLS core and radial TV defects. -/
noncomputable def accuracyAcceptedBiasScale (q : VolumeParams) : ℝ :=
  16 * Real.sqrt (accuracyCoreError q) + (q.eps / (q.n : ℝ)) ^ 8

theorem accuracyAcceptedBiasScale_pos (q : VolumeParams) :
    0 < accuracyAcceptedBiasScale q := by
  unfold accuracyAcceptedBiasScale
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hratio : 0 < q.eps / (q.n : ℝ) := div_pos q.heps.1 hn
  positivity

theorem accuracyPhase_stationary_tvError_toReal_le_biasScale_sq
    (q : VolumeParams) :
    (96 * ENNReal.ofReal (accuracyCoreError q) +
      ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)).toReal ≤
        accuracyAcceptedBiasScale q ^ 2 := by
  let a := Real.sqrt (accuracyCoreError q)
  let b := (q.eps / (q.n : ℝ)) ^ 8
  have hcore : 0 ≤ accuracyCoreError q := (accuracyCoreError_pos q).le
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha2 : a ^ 2 = accuracyCoreError q := by
    dsimp [a]
    exact Real.sq_sqrt hcore
  have hb2 : b ^ 2 = (q.eps / (q.n : ℝ)) ^ 16 := by
    dsimp [b]
    ring
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hcore,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ (q.eps / (q.n : ℝ)) ^ 16)]
  change 96 * accuracyCoreError q + (q.eps / (q.n : ℝ)) ^ 16 ≤
    (16 * a + b) ^ 2
  rw [← ha2, ← hb2]
  nlinarith [mul_nonneg ha hb]

/-- The stationary executable KLS accepted-output law is a genuine
probability measure. -/
theorem accuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsProbabilityMeasure
      (accuracyGaussianAcceptedTargetLaw q I sigma2
        (Arlib.MarkovChains.ellGaussianProb
          (accuracyPhaseTruncatedBody q I sigma2)
          (figureOneProposalRadius q sigma2) sigma2)) := by
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := Arlib.MarkovChains.ellGaussianProb K delta sigma2
  let accepted :=
    (pi.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)
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
  have hmassTop : Arlib.MarkovChains.ellGaussianMeasure K delta sigma2
      Set.univ ≠ ⊤ := by
    dsimp [K]
    exact Arlib.MarkovChains.ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  have hlower : ENNReal.ofReal (7 / 64 : ℝ) ≤ accepted Set.univ := by
    have h := accuracyPhase_stationary_acceptance_ge q I hsigma2
    dsimp [accepted]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ]
    simpa [pi, K, delta] using h
  have hzero : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 64 : ℝ)).trans_le hlower
  have htop : accepted Set.univ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (measure_ne_top pi Set.univ)
    dsimp [accepted]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    calc
      (∫⁻ x, accuracyGaussianRejectionAcceptance q I sigma2 x ∂pi) ≤
          ∫⁻ _x, (1 : ENNReal) ∂pi := by
        exact lintegral_mono <|
          accuracyGaussianRejectionAcceptance_le_one q I hsigma2
      _ = pi Set.univ := lintegral_one
  change IsProbabilityMeasure (Arlib.condOn accepted Set.univ)
  exact Arlib.isProbabilityMeasure_condOn accepted hzero htop

/-- Concrete stationary bias bound for every nonnegative target `L²`
observable.  The constant `65` is the cost of the proved `64`-warm accepted
law; the accuracy scale is exponentially smaller than any phase allocation
used by Figure 1. -/
theorem stationary_accuracyAcceptedTarget_integral_bias_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {f : AmbientSpace q.n → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfmem : MemLp f 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    |(∫ x, f x ∂accuracyGaussianAcceptedTargetLaw q I sigma2 pi) -
      ∫ x, f x ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))| ≤
      accuracyAcceptedBiasScale q *
        (1 + 65 * ∫ x, f x ^ 2
          ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
            Measure (AmbientSpace q.n))) := by
  dsimp only
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let mu := accuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let _ : IsProbabilityMeasure mu :=
    accuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_stationary q I hsigma2
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have htv : Arlib.TVLe mu nu
      (96 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
    simpa [mu, nu, pi] using
      accuracyPhase_stationaryAcceptedTargetLaw_tv q I hsigma2
  have hwarm : Arlib.IsWarm 64 mu nu := by
    simpa [mu, nu, pi] using
      stationary_accuracyAcceptedTarget_isWarm q I hsigma2
  have h := TVLe.integral_nonnegative_le_of_isWarm_secondMoment_sqrt
    htv (ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩)
    (by norm_num : (64 : ENNReal) ≠ ⊤) hwarm hf hf0
    (by simpa [nu] using hfmem)
    (accuracyAcceptedBiasScale_pos q)
    (accuracyPhase_stationary_tvError_toReal_le_biasScale_sq q)
  convert h using 1 <;> norm_num [mu, nu, pi]

/-- Homogeneous stationary accepted-law bias for a signed observable.  A
target `L²` bound `R²` yields an expectation defect proportional to `R`, with
no additive per-phase term. -/
theorem stationary_accuracyAcceptedTarget_integral_bias_le_sqrt_secondMoment
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {f : AmbientSpace q.n → ℝ} (hf : Measurable f)
    (hfmem : MemLp f 2
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    {R : ℝ} (hR : 0 < R)
    (hsecond : (∫ x, f x ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) ≤ R ^ 2) :
    let pi := Arlib.MarkovChains.ellGaussianProb
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2
    |(∫ x, f x ∂accuracyGaussianAcceptedTargetLaw q I sigma2 pi) -
      ∫ x, f x ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))| ≤
      67 * accuracyAcceptedBiasScale q * R := by
  dsimp only
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let mu := accuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let nu : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I sigma2 hsigma2
  let _ : IsProbabilityMeasure mu :=
    accuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_stationary q I hsigma2
  let _ : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  have htv : Arlib.TVLe mu nu
      (96 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
    simpa [mu, nu, pi] using
      accuracyPhase_stationaryAcceptedTargetLaw_tv q I hsigma2
  have hwarm : Arlib.IsWarm 64 mu nu := by
    simpa [mu, nu, pi] using
      stationary_accuracyAcceptedTarget_isWarm q I hsigma2
  have h := TVLe.integral_le_of_isWarm_secondMoment_sqrt
    htv (ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩)
    (by norm_num : (64 : ENNReal) ≠ ⊤) hwarm hf
    (by simpa [nu] using hfmem)
    (accuracyAcceptedBiasScale_pos q) hR
    (accuracyPhase_stationary_tvError_toReal_le_biasScale_sq q)
    (by simpa [nu] using hsecond)
  convert h using 1 <;> norm_num [mu, nu, pi]

end ArlibCommunity.Algorithms.CV18
