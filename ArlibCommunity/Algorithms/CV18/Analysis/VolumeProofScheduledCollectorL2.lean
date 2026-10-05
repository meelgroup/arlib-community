/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryNonnegative
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer

/-!
# Finite L² bounds for the executable scheduled phase collector

This file isolates the purely probabilistic part of the phase `L²` proof.
If every successful one-sample transition lands where the importance weight
is bounded by `B`, the finite collector's averaged observation is also in
`[0,B]`; hence it is square-integrable.  The remaining geometric support
statement is only about one scheduled transition endpoint.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Read the scalar observation from an optional phase result, assigning zero
to a failed phase. -/
def scheduledBalancedPhaseRatio : Option (ℝ × AmbientSpace n) → ℝ
  | none => 0
  | some result => result.1

theorem measurable_scheduledBalancedPhaseRatio :
    Measurable (scheduledBalancedPhaseRatio (n := n)) := by
  convert Measurable.optionElim (0 : ℝ) measurable_fst using 1
  funext result
  cases result <;> rfl

/-- Upper-bound predicate for an optional accumulated collector result. -/
def ScheduledCollectedTotalLe (total : ℝ) (samples : ℕ) (B : ℝ) :
    Option (ℝ × AmbientSpace n) → Prop
  | none => True
  | some result => result.1 ≤ total + (samples : ℝ) * B

theorem measurableSet_scheduledCollectedTotalLe
    (total : ℝ) (samples : ℕ) (B : ℝ) :
    MeasurableSet {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalLe total samples B result} := by
  let A : Set (ℝ × AmbientSpace n) :=
    {result | result.1 ≤ total + (samples : ℝ) * B}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_fst measurable_const
  rw [show {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalLe total samples B result} =
      {none} ∪ optionSomeEvent A by
    ext result
    cases result <;> simp [ScheduledCollectedTotalLe, optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

/-- A one-transition AE weight bound propagates through the exact finite
collector recursion. -/
theorem scheduledBalancedTransitionCollectLaw_ae_total_le
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) {B : ℝ}
    (hstep : ∀ current,
      ∀ᵐ result ∂scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride retryLimit current,
        match result with
        | none => True
        | some target => weight target ≤ B) :
    ∀ samples total current,
      ∀ᵐ result ∂scheduledBalancedTransitionCollectLaw q I sigma2 weight
          proposalCap properStride retryLimit samples total current,
        ScheduledCollectedTotalLe total samples B result := by
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  intro samples
  induction samples with
  | zero =>
      intro total current
      unfold scheduledBalancedTransitionCollectLaw
      apply (ae_dirac_iff
        (measurableSet_scheduledCollectedTotalLe total 0 B)).2
      simp [ScheduledCollectedTotalLe]
  | succ samples ih =>
      intro total current
      let tail : Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
        match result with
        | none => Measure.dirac none
        | some target =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target)
      have htail : Measurable tail := by
        dsimp only [tail]
        have hcollect :=
          (scheduledBalancedTransitionCollectLaw_measurable_and_probability
            q I hsigma2 hweight proposalCap properStride retryLimit samples).1
        have hsome : Measurable fun target : AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target) :=
          hcollect.comp <| (measurable_const.add hweight).prodMk <|
            (measurable_const : Measurable fun _ : AmbientSpace q.n =>
              accuracyScaleFactor q).smul measurable_id
        convert Measurable.optionElim
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
        ext result
        cases result <;> rfl
      let good : Set (Option (ℝ × AmbientSpace q.n)) :=
        {result | ScheduledCollectedTotalLe total (samples + 1) B result}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledCollectedTotalLe total (samples + 1) B
      change ∀ᵐ result ∂
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit current).bind tail,
        ScheduledCollectedTotalLe total (samples + 1) B result
      apply MeasureTheory.mem_ae_iff.mpr
      change ((scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit current).bind tail) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl htail.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hstep current] with result hresult
      cases result with
      | none =>
          change (Measure.dirac
            (none : Option (ℝ × AmbientSpace q.n))) goodᶜ = 0
          rw [Measure.dirac_apply' _ hgood.compl]
          simp [good, ScheduledCollectedTotalLe]
      | some target =>
          change weight target ≤ B at hresult
          have htailBound :
              ∀ᵐ output ∂scheduledBalancedTransitionCollectLaw q I sigma2
                  weight proposalCap properStride retryLimit samples
                  (total + weight target) (accuracyScaleFactor q • target),
                ScheduledCollectedTotalLe total (samples + 1) B output := by
            filter_upwards [ih (total + weight target)
              (accuracyScaleFactor q • target)] with output houtput
            cases output with
            | none => trivial
            | some output =>
                dsimp only [ScheduledCollectedTotalLe] at houtput ⊢
                push_cast
                nlinarith
          change (scheduledBalancedTransitionCollectLaw q I sigma2 weight
            proposalCap properStride retryLimit samples
            (total + weight target) (accuracyScaleFactor q • target)) goodᶜ = 0
          exact MeasureTheory.mem_ae_iff.mp htailBound

/-- The executable average of a nonnegative, one-step bounded importance
weight is square-integrable.  This is independent of mixing and retry
constants; those enter only when proving the one-step support premise. -/
theorem memLp_scheduledBalancedTransitionCollect_average
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (proposalCap properStride retryLimit samples : ℕ)
    (hsamples : 0 < samples) (current : AmbientSpace q.n) {B : ℝ}
    (hB : 0 ≤ B)
    (hstep : ∀ state,
      ∀ᵐ result ∂scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride retryLimit state,
        match result with
        | none => True
        | some target => weight target ≤ B) :
    MemLp scheduledBalancedPhaseRatio 2
      ((scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples 0 current).map
          (balancedCoolingAverage samples)) := by
  let source := scheduledBalancedTransitionCollectLaw q I sigma2 weight
    proposalCap properStride retryLimit samples 0 current
  let average := balancedCoolingAverage (n := q.n) samples
  let law := source.map average
  let _ : IsProbabilityMeasure source :=
    (scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit samples).2 0 current
  let _ : IsProbabilityMeasure law := by
    dsimp only [law]
    exact Measure.isProbabilityMeasure_map
      (measurable_balancedCoolingAverage samples).aemeasurable
  have htotal0 := scheduledBalancedTransitionCollectLaw_ae_total_nonnegative
    q I hsigma2 hweight hweight0 proposalCap properStride retryLimit
      samples 0 current (by norm_num)
  have htotalB := scheduledBalancedTransitionCollectLaw_ae_total_le
    q I hsigma2 hweight proposalCap properStride retryLimit hstep
      samples 0 current
  have hratio0 : ∀ᵐ result ∂law, 0 ≤ scheduledBalancedPhaseRatio result := by
    dsimp only [law]
    have hset : MeasurableSet
        {result : Option (ℝ × AmbientSpace q.n) |
          0 ≤ scheduledBalancedPhaseRatio result} :=
      measurable_scheduledBalancedPhaseRatio measurableSet_Ici
    apply (ae_map_iff (measurable_balancedCoolingAverage samples).aemeasurable
      hset).2
    filter_upwards [htotal0] with result hresult
    cases result with
    | none => simp [average, balancedCoolingAverage, scheduledBalancedPhaseRatio]
    | some result =>
        simpa [average, balancedCoolingAverage, scheduledBalancedPhaseRatio] using
          div_nonneg hresult (Nat.cast_nonneg samples)
  have hratioB : ∀ᵐ result ∂law,
      scheduledBalancedPhaseRatio result ≤ B := by
    dsimp only [law]
    have hset : MeasurableSet
        {result : Option (ℝ × AmbientSpace q.n) |
          scheduledBalancedPhaseRatio result ≤ B} :=
      measurable_scheduledBalancedPhaseRatio measurableSet_Iic
    apply (ae_map_iff (measurable_balancedCoolingAverage samples).aemeasurable
      hset).2
    filter_upwards [htotalB] with result hresult
    cases result with
    | none => simpa [average, balancedCoolingAverage,
          scheduledBalancedPhaseRatio] using hB
    | some result =>
        dsimp only [ScheduledCollectedTotalLe] at hresult
        simp only [average, balancedCoolingAverage, scheduledBalancedPhaseRatio]
        rw [div_le_iff₀ (by exact_mod_cast hsamples)]
        simpa [mul_comm] using hresult
  exact memLp_two_of_ae_nonnegative_le measurable_scheduledBalancedPhaseRatio
    hB hratio0 hratioB

#print axioms scheduledBalancedTransitionCollectLaw_ae_total_le
#print axioms memLp_scheduledBalancedTransitionCollect_average

end ArlibCommunity.Algorithms.CV18
