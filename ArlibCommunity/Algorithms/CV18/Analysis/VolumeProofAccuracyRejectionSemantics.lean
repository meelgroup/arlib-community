/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyKLS
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyProperProgram

/-! # Accepted-output semantics of the executable CV18 KLS correction -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise

/-- The `true` slice of one executable KLS rejection attempt is precisely the
input law weighted by its acceptance probability and mapped by the homothety.
This is the missing semantic link between `accuracyGaussianRejectionKernel`
and the normalized measure in `accuracyPhaseSampleToGaussian_cv18`. -/
theorem accuracyGaussianRejectionKernel_true_prod
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (mu : Measure (AmbientSpace q.n)) {B : Set (AmbientSpace q.n)}
    (hB : MeasurableSet B) :
    (mu.bind (accuracyGaussianRejectionKernel q I sigma2))
        ({true} ×ˢ B) =
      ((mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => (accuracyScaleFactor q)⁻¹ • x)) B := by
  have hscale : Measurable (fun x : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹ • x) :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have hprod : MeasurableSet ({true} ×ˢ B) :=
    (measurableSet_singleton true).prod hB
  rw [Measure.bind_apply hprod
    (accuracyGaussianRejectionKernel q I sigma2).measurable.aemeasurable]
  rw [Measure.map_apply hscale hB,
    withDensity_apply _ (hscale hB)]
  rw [← lintegral_indicator (hscale hB)]
  apply lintegral_congr
  intro current
  change (accuracyGaussianRejectionLaw q I sigma2 current) ({true} ×ˢ B) = _
  simp only [accuracyGaussianRejectionLaw, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hprod]
  by_cases ht : (accuracyScaleFactor q)⁻¹ • current ∈ B
  · simp [ht, Set.indicator_of_mem, hprod]
  · simp [ht, Set.indicator_of_notMem, hprod]

/-- The accepted subprobability measure is exactly the homothetic-core
proposal used by the analytic KLS theorem, before normalization. -/
theorem map_withDensity_accuracyRejectionAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let c := accuracyScaleFactor q
    (mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
        (fun x => c⁻¹ • x) =
      ((mu.restrict (c • K)).map (fun x => c⁻¹ • x)).withDensity
        (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let c := accuracyScaleFactor q
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal :=
    Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c
  have hc0 : 0 < c := by simpa [c] using accuracyScaleFactor_pos q
  have hK : MeasurableSet K := accuracyPhaseTruncatedBody_measurable q I sigma2
  have hcore : MeasurableSet (c • K) :=
    ((isClosedMap_smul_of_ne_zero hc0.ne') K
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isClosed).measurableSet
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n => c⁻¹).smul
      measurable_id
  have hg : Measurable g := by
    dsimp [g]
    exact Arlib.MarkovChains.measurable_gaussianScaleAcceptance sigma2 c
  have haccept : accuracyGaussianRejectionAcceptance q I sigma2 =
      (c • K).indicator (fun x => g (scale x)) := by
    funext x
    unfold accuracyGaussianRejectionAcceptance
    dsimp only [c, K, scale, g]
    by_cases hx : (accuracyScaleFactor q)⁻¹ • x ∈
        accuracyPhaseTruncatedBody q I sigma2
    · have hxcore : x ∈ accuracyScaleFactor q •
          accuracyPhaseTruncatedBody q I sigma2 :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne' _ _).2 hx
      simp [hx, hxcore]
    · have hxcore : x ∉ accuracyScaleFactor q •
          accuracyPhaseTruncatedBody q I sigma2 := fun h =>
        hx ((Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne' _ _).1 h)
      simp [hx, hxcore]
  ext B hB
  rw [Measure.map_apply hscale hB, withDensity_apply _ (hscale hB),
    withDensity_apply _ hB]
  rw [← lintegral_indicator hB]
  have hBg : Measurable (B.indicator g) := hg.indicator hB
  rw [lintegral_map' hBg.aemeasurable hscale.aemeasurable]
  change (∫⁻ x in scale ⁻¹' B,
      accuracyGaussianRejectionAcceptance q I sigma2 x ∂mu) =
    ∫⁻ x in c • K, B.indicator g (scale x) ∂mu
  rw [← lintegral_indicator (hscale hB), ← lintegral_indicator hcore,
    haccept]
  apply lintegral_congr
  intro x
  by_cases hxB : scale x ∈ B <;> by_cases hxK : x ∈ c • K <;>
    simp [hxB, hxK]

/-- Normalized law of the target point returned by a successful executable
KLS rejection attempt. -/
noncomputable def accuracyGaussianAcceptedTargetLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  Arlib.condOn
    ((mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
      (fun x => (accuracyScaleFactor q)⁻¹ • x)) Set.univ

/-- The normalized executable accepted-output law is definitionally the same
probability law analyzed by the two-stage KLS phase theorem. -/
theorem accuracyGaussianAcceptedTargetLaw_eq_kls
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n))
    (hcore0 : mu (accuracyScaleFactor q •
      accuracyPhaseTruncatedBody q I sigma2) ≠ 0)
    (hcoretop : mu (accuracyScaleFactor q •
      accuracyPhaseTruncatedBody q I sigma2) ≠ ⊤) :
    accuracyGaussianAcceptedTargetLaw q I sigma2 mu =
      let K := accuracyPhaseTruncatedBody q I sigma2
      let c := accuracyScaleFactor q
      Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let c := accuracyScaleFactor q
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x => c⁻¹ • x
  let g : AmbientSpace q.n → ENNReal :=
    Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c
  have hscale : Measurable scale := by
    dsimp [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n => c⁻¹).smul
      measurable_id
  have hproposal :
      ((Arlib.condOn mu (c • K)).map scale).withDensity g =
        (mu (c • K))⁻¹ •
          (((mu.restrict (c • K)).map scale).withDensity g) := by
    rw [Arlib.condOn_def, Measure.map_smul, withDensity_smul_measure]
  rw [hproposal]
  have hunscaled := map_withDensity_accuracyRejectionAcceptance q I sigma2 mu
  change Arlib.condOn
      ((mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)).map
        scale) Set.univ = _
  rw [← hunscaled]
  symm
  exact Arlib.MarkovChains.condOn_smul_cv18 _ MeasurableSet.univ
    (ENNReal.inv_ne_zero.mpr hcoretop) (ENNReal.inv_ne_top.mpr hcore0)

set_option maxHeartbeats 800000 in
/-- The phase TV theorem now stated directly for the normalized successful
output of the executable rejection kernel. -/
theorem accuracyGaussianAcceptedTargetLaw_tv_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    Arlib.TVLe
      (accuracyGaussianAcceptedTargetLaw q I sigma2 mu)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError +
        32 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let mu := Arlib.MarkovChains.iterate P mu0 t
  have hcore0 : mu (accuracyScaleFactor q • K) ≠ 0 := by
    simpa [mu, P, K, delta] using
      accuracyPhase_iterate_core_ne_zero q I hsigma2 hM hwarm
        hmixError0 hmixError64 ht
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  let _ : Fact (0 < delta) := ⟨hdelta⟩
  let _ : Fact (0 < sigma2) := ⟨hsigma2⟩
  let _ : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hcoretop : mu (accuracyScaleFactor q • K) ≠ ⊤ :=
    measure_ne_top mu _
  rw [accuracyGaussianAcceptedTargetLaw_eq_kls q I sigma2 _ hcore0 hcoretop]
  simpa only [accuracyScaleFactor] using
    accuracyPhaseSampleToGaussian_cv18 q I hsigma2 hM hwarm
      hmixError0 hmixError64 ht

end ArlibCommunity.Algorithms.CV18
