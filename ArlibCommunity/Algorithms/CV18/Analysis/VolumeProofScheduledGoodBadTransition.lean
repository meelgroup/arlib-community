/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledConcreteTransition

/-! # Scheduled transitions from a good/bad phase-start decomposition

The executable history can carry a small cap-failure submeasure, so its
retained-state marginal need not itself be literally warm.  This file replaces
that false premise by a warm good part and an explicitly charged bad mass.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

/-- Fill the portion of a probability law not covered by its good part with
stationary mass.  The result is a probability law, stays warm, and dominates
the original law up to precisely the bad mass. -/
theorem exists_warm_probability_measureLeUpTo_of_le_good_add_bad
    {Omega : Type*} [MeasurableSpace Omega]
    (mu good bad pi : Measure Omega)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi] [IsFiniteMeasure bad]
    {M N eta : ENNReal}
    (hle : mu ≤ good + bad) (hgood : Arlib.IsWarm M good pi)
    (hbad : bad Set.univ ≤ eta) (hMN : M + 1 ≤ N) :
    ∃ nu : Measure Omega, IsProbabilityMeasure nu ∧
      Arlib.IsWarm N nu pi ∧ MeasureLeUpTo mu nu eta := by
  let residual := mu - bad
  let missing := 1 - residual Set.univ
  let nu := residual + missing • pi
  have hresidualLe : residual ≤ good := by
    exact Measure.sub_le_of_le_add hle
  have hmuLe : mu ≤ residual + bad := by
    exact (Measure.sub_le_iff_le_add (μ := mu) (ν := bad)
      (ξ := residual)).mp le_rfl
  have hresidualMass : residual Set.univ ≤ 1 := by
    calc
      residual Set.univ ≤ mu Set.univ :=
        Measure.le_iff'.mp (Measure.sub_le (μ := mu) (ν := bad)) Set.univ
      _ = 1 := measure_univ
  have hnuUniv : nu Set.univ = 1 := by
    rw [show nu = residual + missing • pi by rfl,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      show pi Set.univ = 1 by exact measure_univ, mul_one]
    exact add_tsub_cancel_of_le hresidualMass
  let hnuProb : IsProbabilityMeasure nu := ⟨hnuUniv⟩
  have hnuWarm : Arlib.IsWarm N nu pi := by
    intro S hS
    rw [show nu = residual + missing • pi by rfl,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    calc
      residual S + missing * pi S ≤ good S + missing * pi S := by
        exact add_le_add (Measure.le_iff'.mp hresidualLe S) le_rfl
      _ ≤ M * pi S + 1 * pi S := by
        gcongr
        · exact hgood S hS
        · exact tsub_le_self
      _ = (M + 1) * pi S := by rw [add_mul]
      _ ≤ N * pi S := by gcongr
  have hmuNu : MeasureLeUpTo mu nu eta := by
    refine ⟨bad, ?_, hbad⟩
    calc
      mu ≤ residual + bad := hmuLe
      _ ≤ nu + bad := by
        gcongr
        exact Measure.le_add_right le_rfl
  exact ⟨nu, hnuProb, hnuWarm, hmuNu⟩

/-- A two-warm law relative to a phase-start marginal inherits a good/bad
decomposition with twice the bad mass. -/
theorem bind_figureOneFinalScheduledBalancedTransition_leUpTo_of_good_bad
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rho mu good bad : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu] [IsFiniteMeasure bad]
    {M eta : ENNReal}
    (hmuWarm : Arlib.IsWarm 2 mu rho)
    (hrho : rho ≤ good + bad)
    (hgood : Arlib.IsWarm M good
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hbad : bad Set.univ ≤ eta)
    (hM : 2 * M + 1 ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) :
    MeasureLeUpTo
      (mu.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q + 2 * eta) := by
  let pi := ellGaussianProb
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  let good2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • good
  let bad2 : Measure (AmbientSpace q.n) := (2 : ENNReal) • bad
  let _ : IsFiniteMeasure bad2 :=
    { measure_univ_lt_top := by
        rw [show bad2 = (2 : ENNReal) • bad by rfl,
          Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top bad Set.univ) }
  have hmuSplit : mu ≤ good2 + bad2 := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul]
    calc
      mu S ≤ 2 * rho S := hmuWarm S hS
      _ ≤ 2 * (good S + bad S) := by
        gcongr
        exact Measure.le_iff'.mp hrho S
      _ = 2 * good S + 2 * bad S := mul_add _ _ _
  have hgood2 : Arlib.IsWarm (2 * M) good2 pi := by
    intro S hS
    rw [show good2 = (2 : ENNReal) • good by rfl,
      Measure.smul_apply, smul_eq_mul]
    calc
      2 * good S ≤ 2 * (M * pi S) := by gcongr; exact hgood S hS
      _ = (2 * M) * pi S := by ac_rfl
  have hbad2 : bad2 Set.univ ≤ 2 * eta := by
    rw [show bad2 = (2 : ENNReal) • bad by rfl,
      Measure.smul_apply, smul_eq_mul]
    gcongr
  obtain ⟨nu, hnuProb, hnuWarm, hmuNu⟩ :=
    exists_warm_probability_measureLeUpTo_of_le_good_add_bad
      mu good2 bad2 pi hmuSplit hgood2 hbad2 hM
  let _ : IsProbabilityMeasure nu := hnuProb
  let K := scheduledBalancedAccuracyTransitionLawAux q I sigma2
    (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
    (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
    (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hK := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  have hfirst : MeasureLeUpTo (mu.bind K) (nu.bind K) (2 * eta) :=
    hmuNu.bind_same (by simpa [K] using hK.1)
      (fun x => by simpa [K] using hK.2 x)
  let _ : IsProbabilityMeasure (nu.bind K) :=
    isProbabilityMeasure_bind (by simpa [K] using hK.1.aemeasurable)
      (ae_of_all _ fun x => by simpa [K] using hK.2 x)
  have hnuTV := bind_figureOneFinalScheduledBalancedTransition_tvLe
    q I hsigma2 nu hnuWarm nu hnuProb
      ((Arlib.IsWarm.refl nu).mono (by norm_num))
  have hsecond : MeasureLeUpTo
      (nu.bind K)
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q) := by
    apply MeasureLeUpTo.of_tvLe
    simpa [K] using hnuTV
  simpa [K, add_comm] using hfirst.trans hsecond

/-- Probability-law corollary of the good/bad additive domination theorem. -/
theorem bind_figureOneFinalScheduledBalancedTransition_tvLe_of_good_bad
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rho mu good bad : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu] [IsFiniteMeasure bad]
    {M eta : ENNReal}
    (hmuWarm : Arlib.IsWarm 2 mu rho)
    (hrho : rho ≤ good + bad)
    (hgood : Arlib.IsWarm M good
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (hbad : bad Set.univ ≤ eta)
    (hM : 2 * M + 1 ≤
      ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) :
    Arlib.TVLe
      (mu.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q + 2 * eta) := by
  have hK := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2
      (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
      (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
      (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)
  let _ : IsProbabilityMeasure
      (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
        (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
        (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
        (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2))) :=
    isProbabilityMeasure_bind hK.1.aemeasurable (ae_of_all _ hK.2)
  let _ : IsProbabilityMeasure
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  exact (bind_figureOneFinalScheduledBalancedTransition_leUpTo_of_good_bad
    q I hsigma2 rho mu good bad hmuWarm hrho hgood hbad hM).to_tvLe

#print axioms exists_warm_probability_measureLeUpTo_of_le_good_add_bad
#print axioms bind_figureOneFinalScheduledBalancedTransition_leUpTo_of_good_bad
#print axioms bind_figureOneFinalScheduledBalancedTransition_tvLe_of_good_bad

end ArlibCommunity.Algorithms.CV18
