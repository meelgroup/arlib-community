/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKernelBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStrongStepMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.OneDimSharp

/-!
# Conditional sharp mixing bridge for the executable CV18 walk

This module isolates the exact hypotheses under which the sharp direct-Metropolis
conductance theorem applies to Figure One's *implemented* fixed-step walk.  The executable
kernel uses the fixed `truncatedBody`, rather than the phase-local radial truncation used by
the speedy-walk analysis.  Consequently the local-conductance floor and the Gaussian-scale
outer-radius condition below are genuine additional hypotheses; they are deliberately not
hidden in an unconditional-looking theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib Arlib.MarkovChains Metric Set
open scoped ENNReal

/-- The stationary probability measure used by the abstract Metropolis kernel is exactly
the normalized restricted Gaussian used by the executable CV18 development. -/
theorem truncatedGaussianProbability_eq_uniformOn_gaussianWeight
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) :
    (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) =
      Arlib.uniformOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (gaussianWeight sigma2))
        (truncatedBody q I) := by
  rw [truncatedGaussianProbability_toMeasure q I hsigma2,
    Arlib.uniformOn_def, restrict_withDensity (truncatedBody_measurable q I)]
  have hdensity :
      (gaussianWeight sigma2 : AmbientSpace q.n → ENNReal) =
        fun x => ENNReal.ofReal (gaussianDensity sigma2 x) := by
    funext x
    rw [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]
  rw [hdensity]
  congr 1
  congr 1
  calc
    ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2) =
        truncatedGaussianMeasure q I sigma2 Set.univ :=
      (truncatedGaussianMeasure_apply_univ q I hsigma2).symm
    _ = (((volume : Measure (AmbientSpace q.n)).withDensity
          (fun x => ENNReal.ofReal (gaussianDensity sigma2 x))).restrict
            (truncatedBody q I)) Set.univ := by
      rw [restrict_withDensity (truncatedBody_measurable q I)]
      rfl
    _ = ((volume : Measure (AmbientSpace q.n)).withDensity
        (fun x => ENNReal.ofReal (gaussianDensity sigma2 x)))
          (truncatedBody q I) := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp

/-- Sharp warm-start mixing for the exact fixed-step kernel executed by Figure One.

The three hypotheses `hell`, `hfloor`, and `hRσ` are exactly the hypotheses that prevent
this result from applying to the current unconditional CV18 input model. -/
theorem mixesWithin_truncatedMetropolisKernel_figureOne_direct_cv18
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 R theta : ℝ} (hsigma2 : 0 < sigma2) (hR : 0 ≤ R)
    (hKR : ∀ x ∈ truncatedBody q I, ‖x‖ ≤ R)
    (hell : ∀ x ∈ truncatedBody q I,
      ENNReal.ofReal theta ≤
        ell (truncatedBody q I) (figureOneProposalRadius q sigma2) x)
    (hfloor : 1 ≤
      20 * Real.exp (-(2 * R * figureOneProposalRadius q sigma2 +
          figureOneProposalRadius q sigma2 ^ 2) / (2 * sigma2)) *
        (1 / 4) * theta)
    (hRσ : Real.sqrt 3 * R ≤ 2 * Real.sqrt sigma2 * Real.sqrt q.n)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (truncatedMetropolisKernel q I oracle sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) mu0 t (ENNReal.ofReal eps) := by
  have hn2 : 2 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hdelta : 0 < figureOneProposalRadius q sigma2 :=
    figureOneProposalRadius_pos q hsigma2
  have hsigma : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  have hdeltaSigma : figureOneProposalRadius q sigma2 ≤
      Real.sqrt sigma2 / (8 * Real.sqrt q.n) :=
    figureOneProposalRadius_le_phaseMixingStep q hsigma2
  have hKtop : volume (truncatedBody q I) ≠ ⊤ :=
    (truncatedVolumeInput q I).body.isCompact.measure_lt_top.ne
  have hK0 : volume (truncatedBody q I) ≠ 0 := by
    apply ne_of_gt
    exact (Metric.measure_ball_pos volume (0 : AmbientSpace q.n) (by norm_num)).trans_le
      (measure_mono fun x hx =>
        unitBall_subset_truncatedBody q I (Metric.ball_subset_closedBall hx))
  let pi : Measure (AmbientSpace q.n) :=
    Arlib.uniformOn
      ((volume : Measure (AmbientSpace q.n)).withDensity
        (gaussianWeight sigma2))
      (truncatedBody q I)
  have hpi : pi =
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
    exact (truncatedGaussianProbability_eq_uniformOn_gaussianWeight
      q I hsigma2).symm
  let _ : IsProbabilityMeasure pi := hpi ▸ inferInstance
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_uniformOn_gaussian (le_trans (by norm_num) hn2)
      (truncatedBody_measurable q I)
      hK0 hKtop hsigma2
  have hcond : ENNReal.ofReal
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ≤
      conductance
        (metropolisGaussian (truncatedBody q I)
          (figureOneProposalRadius q sigma2) sigma2) pi := by
    dsimp [pi]
    simpa [Real.sq_sqrt hsigma2.le] using
      (Arlib.conductance_metropolisGaussian_sharp_sqrt_ge_of_convex
        hn2 hsigma hdelta hdeltaSigma hR
        (truncatedBody_measurable q I)
        (truncatedVolumeInput q I).body.convex hKR hKtop hK0 hell
        (by simpa [Real.sq_sqrt hsigma2.le] using hfloor) hRσ)
  have hwarm' : IsWarm (ENNReal.ofReal M) mu0 pi := by simpa [hpi] using hwarm
  have hmix : MixesWithin
      (lazy (metropolisGaussian (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2))
      pi mu0 t (ENNReal.ofReal eps) :=
    mixesWithin_lazy_of_conductance_sqrt hn2 hsigma hdelta hdeltaSigma
      (isReversible_metropolisGaussian (truncatedBody_measurable q I)
        (figureOneProposalRadius q sigma2) sigma2)
      ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm' heps0 heps1 hcond ht
  rw [← truncatedMetropolisKernel_eq_lazy_metropolisGaussian
    q I oracle hsigma2, hpi] at hmix
  exact hmix

/-- Additive-domination form of the conditional direct mixing theorem, ready for the
`MeasureLeUpTo` premise used by the retained-history formulation of CV18 Lemma 7.17(c). -/
theorem measureLeUpTo_iterate_truncatedMetropolisKernel_figureOne_direct_cv18
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 R theta : ℝ} (hsigma2 : 0 < sigma2) (hR : 0 ≤ R)
    (hKR : ∀ x ∈ truncatedBody q I, ‖x‖ ≤ R)
    (hell : ∀ x ∈ truncatedBody q I,
      ENNReal.ofReal theta ≤
        ell (truncatedBody q I) (figureOneProposalRadius q sigma2) x)
    (hfloor : 1 ≤
      20 * Real.exp (-(2 * R * figureOneProposalRadius q sigma2 +
          figureOneProposalRadius q sigma2 ^ 2) / (2 * sigma2)) *
        (1 / 4) * theta)
    (hRσ : Real.sqrt 3 * R ≤ 2 * Real.sqrt sigma2 * Real.sqrt q.n)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MeasureLeUpTo
      (iterate (truncatedMetropolisKernel q I oracle sigma2) mu0 t)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (ENNReal.ofReal eps) := by
  exact MeasureLeUpTo.of_tvLe
    (mixesWithin_truncatedMetropolisKernel_figureOne_direct_cv18
      q I oracle hsigma2 hR hKR hell hfloor hRσ hM hwarm heps0 heps1 ht)

/-- Continuous Markov iteration is application of the corresponding kernel power.  This
local spelling keeps the direct executable bridge independent of the capped-retry modules. -/
theorem iterate_eq_bind_kernel_pow_direct
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (mu : Measure S) :
    ∀ t, iterate P mu t = mu.bind (P ^ t) := by
  intro t
  induction t with
  | zero =>
      simp only [iterate_zero, pow_zero]
      exact Measure.id_comp.symm
  | succ t ih =>
      rw [iterate_succ, ih, pow_succ']
      unfold step
      rw [Measure.bind_bind (P ^ t).measurable.aemeasurable
        P.measurable.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards with state
      exact (Kernel.comp_apply P (P ^ t) state).symm

/-- Retained-history form of Lemma 7.17(c) for a fixed-step Markov block.

If the retained-state marginal is `warmMarginal`-warm for `pi`, conditioning on any
half-probability history event makes the next block start at most
`2 * warmMarginal`-warm for `pi`.  A mixing theorem at precisely that warmness therefore
supplies the `MeasureLeUpTo` premise of the generic Lemma 7.17(c) result. -/
theorem approxIndepFun_accumulatedProduct_nextEstimator_of_fixedWalkMixing
    {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (state : H → S) (hstate : Measurable state)
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : Measure S) [IsProbabilityMeasure pi]
    (t : ℕ) {warmMarginal delta : ENNReal}
    (hstateWarm : IsWarm warmMarginal (rho.map state) pi)
    (hdelta : delta ≠ ⊤)
    (hmix : ∀ mu : Measure S, IsProbabilityMeasure mu →
      IsWarm (2 * warmMarginal) mu pi →
      MeasureLeUpTo (iterate P mu t) pi delta)
    (pastProduct : H → ℝ) (nextEstimator : S → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget : (delta + delta).toReal ≤
      3 * (k : ℝ) * (m : ℝ) * nu) :
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw rho ((P ^ t) ∘ state)) := by
  have hpowProb : ∀ x : S, IsProbabilityMeasure ((P ^ t) x) := by
    intro x
    have heq : iterate P (Measure.dirac x) t = (P ^ t) x := by
      rw [iterate_eq_bind_kernel_pow_direct P (Measure.dirac x) t,
        Measure.dirac_bind (P ^ t).measurable]
    rw [← heq]
    infer_instance
  refine approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo
    rho state hstate (P ^ t).measurable
    hpowProb pi hdelta ?_
      pastProduct nextEstimator hpastProduct hnextEstimator k m nu hbudget
  intro mu hmu hwarm
  have hwarmPi : IsWarm (2 * warmMarginal) mu pi :=
    hwarm.trans hstateWarm
  rw [← iterate_eq_bind_kernel_pow_direct P mu t]
  exact hmix mu hmu hwarmPi

#print axioms truncatedGaussianProbability_eq_uniformOn_gaussianWeight
#print axioms mixesWithin_truncatedMetropolisKernel_figureOne_direct_cv18
#print axioms measureLeUpTo_iterate_truncatedMetropolisKernel_figureOne_direct_cv18
#print axioms approxIndepFun_accumulatedProduct_nextEstimator_of_fixedWalkMixing

end ArlibCommunity.Algorithms.CV18
