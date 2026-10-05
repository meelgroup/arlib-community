/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianEndpointMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedSupport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRawMeanApprox

/-!
# Sharp terminal moments of finite retained endpoints

At the terminal phase the uniform ratio is bounded by `exp (1/2)` on every
successful retained endpoint.  Hence the exact-chance endpoint comparison
transfers both its mean and its second moment with their sharp additive
errors.  These are the terminal coordinate inputs for CV18 equation (6).
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- Total variation transfers a squared observable when its common bound is
known almost everywhere under both probability measures. -/
theorem Arlib.TVLe.integral_sq_le_of_ae_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0mu : ∀ᵐ x ∂mu, 0 ≤ f x)
    (hfBmu : ∀ᵐ x ∂mu, f x ≤ B)
    (hf0nu : ∀ᵐ x ∂nu, 0 ≤ f x)
    (hfBnu : ∀ᵐ x ∂nu, f x ≤ B) :
    |(∫ x, f x ^ 2 ∂mu) - ∫ x, f x ^ 2 ∂nu| ≤
      B ^ 2 * epsilon.toReal := by
  let g : S → ℝ := fun x => min (max 0 (f x)) B
  have hg : Measurable g := (measurable_const.max hf).min measurable_const
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    le_min (le_max_left _ _) hB.le
  have hgB : ∀ x, g x ≤ B := fun x => min_le_right _ _
  have hgeqmu : ∀ᵐ x ∂mu, g x = f x := by
    filter_upwards [hf0mu, hfBmu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  have hgeqnu : ∀ᵐ x ∂nu, g x = f x := by
    filter_upwards [hf0nu, hfBnu] with x hx0 hxB
    simp only [g, max_eq_right hx0, min_eq_left hxB]
  have hsqmu : ∀ᵐ x ∂mu, g x ^ 2 = f x ^ 2 := by
    filter_upwards [hgeqmu] with x hx
    rw [hx]
  have hsqnu : ∀ᵐ x ∂nu, g x ^ 2 = f x ^ 2 := by
    filter_upwards [hgeqnu] with x hx
    rw [hx]
  rw [← integral_congr_ae hsqmu, ← integral_congr_ae hsqnu]
  exact Arlib.TVLe.integral_sq_le_of_nonnegative_le
    h hepsilon hg hB hg0 hgB

/-- The zero-filled terminal weight lies in `[0, exp (1/2)]` under every
finite exact-start retained endpoint law. -/
theorem retainedOptionWeight_uniform_terminal_ae_bounds_iterated
    (q : VolumeParams) (I : VolumeInput q.n) (samples : ℕ) :
    ∀ᵐ result ∂iteratedKernelLaw
      (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q (terminalPhaseSteps q)))
      ((truncatedGaussianProbability q I
        (scheduleValue q (terminalPhaseSteps q))
        (scheduleValue_pos q (terminalPhaseSteps q)) :
          Measure (AmbientSpace q.n)).map some)
      samples,
      0 ≤ retainedOptionWeight (uniformRatioWeight (terminalVariance q)) result ∧
        retainedOptionWeight (uniformRatioWeight (terminalVariance q)) result ≤
          Real.exp (1 / 2) := by
  filter_upwards [
    iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_ae_mem
      q I (terminalPhaseSteps q) samples] with result hresult
  cases result with
  | none => exact ⟨by simp [retainedOptionWeight], (Real.exp_pos _).le⟩
  | some x =>
      rw [retainedOptionWeight]
      rw [uniformRatioWeight_eq_sample q I (terminalVariance q) hresult]
      have hx := uniformRatio_terminal_bounds q I hresult
      exact ⟨le_trans (by norm_num) hx.1, hx.2⟩

/-- The same zero-filled bound under the exact terminal Gaussian mapped into
the optional state space. -/
theorem retainedOptionWeight_uniform_terminal_ae_bounds_exactSome
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∀ᵐ result ∂(truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some,
      0 ≤ retainedOptionWeight (uniformRatioWeight (terminalVariance q)) result ∧
        retainedOptionWeight (uniformRatioWeight (terminalVariance q)) result ≤
          Real.exp (1 / 2) := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q)
  let f : Option (AmbientSpace q.n) → ℝ :=
    retainedOptionWeight (uniformRatioWeight (terminalVariance q))
  have hf : Measurable f := measurable_retainedOptionWeight
    (measurable_uniformRatioWeight (terminalVariance q))
  have hsource :=
    truncatedGaussianProbability_terminal_ae_uniformRatio_bounds q I
  have h0source : ∀ᵐ x ∂exact, 0 ≤ f (some x) := by
    filter_upwards [hsource] with x hx
    simpa [f, retainedOptionWeight] using le_trans (by norm_num) hx.1
  have hBsource : ∀ᵐ x ∂exact, f (some x) ≤ Real.exp (1 / 2) := by
    filter_upwards [hsource] with x hx
    simpa [f, retainedOptionWeight] using hx.2
  have h0 : ∀ᵐ result ∂exact.map some, 0 ≤ f result :=
    (ae_map_iff measurable_some.aemeasurable (hf measurableSet_Ici)).2 h0source
  have hB : ∀ᵐ result ∂exact.map some, f result ≤ Real.exp (1 / 2) :=
    (ae_map_iff measurable_some.aemeasurable (hf measurableSet_Iic)).2 hBsource
  simpa [exact, f] using h0.and hB

/-- A terminal retained endpoint mean differs from the exact terminal mean
by at most the bounded-observable exact-chance error. -/
theorem integral_iterated_retainedOption_uniform_terminal_abs_sub_ideal_le
    (q : VolumeParams) (I : VolumeInput q.n) (samples : ℕ) :
    |(∫ result, retainedOptionWeight
          (uniformRatioWeight (terminalVariance q)) result
        ∂iteratedKernelLaw
          (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
            (terminalVariance q))
          ((truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some)
          samples) - figureOneIdealPhaseMean q I .terminal| ≤
      Real.exp (1 / 2) *
        (2 * scheduledBalancedStationaryTargetError q +
          samples • figureOneCorrectedTransitionBudget q).toReal := by
  let s := scheduleValue q (terminalPhaseSteps q)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s
      (scheduleValue_pos q (terminalPhaseSteps q))
  let exactSome : Measure (Option (AmbientSpace q.n)) := exact.map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let actual := iteratedKernelLaw (fun _ => K) exactSome samples
  let epsilon := 2 * scheduledBalancedStationaryTargetError q +
    samples • figureOneCorrectedTransitionBudget q
  let f : Option (AmbientSpace q.n) → ℝ :=
    retainedOptionWeight (uniformRatioWeight (terminalVariance q))
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure exactSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q (terminalPhaseSteps q))
  let _ : IsProbabilityMeasure actual :=
    iteratedKernelLaw_isProbabilityMeasure (fun _ => K) exactSome inferInstance
      (fun _ => hK.1) (fun _ => hK.2) samples
  have htv : Arlib.TVLe actual exactSome epsilon := by
    simpa [actual, exactSome, exact, K, epsilon, s] using
      (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
        q I (terminalPhaseSteps q) samples).to_tvLe
  have hepsilonTop : epsilon ≠ ⊤ := by
    dsimp [epsilon]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by norm_num) <|
        ne_top_of_le_ne_top
          (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
          (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top
  have hactualBounds :=
    retainedOptionWeight_uniform_terminal_ae_bounds_iterated q I samples
  have hexactBounds :=
    retainedOptionWeight_uniform_terminal_ae_bounds_exactSome q I
  have hactual0 : ∀ᵐ result ∂actual, 0 ≤ f result := by
    simpa [actual, exactSome, exact, K, s, f] using
      hactualBounds.mono fun _ hx => hx.1
  have hactualB : ∀ᵐ result ∂actual, f result ≤ Real.exp (1 / 2) := by
    simpa [actual, exactSome, exact, K, s, f] using
      hactualBounds.mono fun _ hx => hx.2
  have hexact0 : ∀ᵐ result ∂exactSome, 0 ≤ f result := by
    simpa [exactSome, exact, s, f, scheduleValue_terminalPhaseSteps] using
      hexactBounds.mono fun _ hx => hx.1
  have hexactB : ∀ᵐ result ∂exactSome, f result ≤ Real.exp (1 / 2) := by
    simpa [exactSome, exact, s, f, scheduleValue_terminalPhaseSteps] using
      hexactBounds.mono fun _ hx => hx.2
  have htransfer := Arlib.TVLe.integral_le_of_ae_nonnegative_le htv
    hepsilonTop (measurable_retainedOptionWeight
      (measurable_uniformRatioWeight (terminalVariance q)))
    (Real.exp_pos _) hactual0 hactualB hexact0 hexactB
  have hexactMean : (∫ result, f result ∂exactSome) =
      figureOneIdealPhaseMean q I .terminal := by
    rw [integral_map measurable_some.aemeasurable
      (measurable_retainedOptionWeight
        (measurable_uniformRatioWeight (terminalVariance q))).aestronglyMeasurable]
    simpa [f, exactSome, exact, s, Function.comp_def, retainedOptionWeight,
      figureOneIdealPhaseMean, scheduleValue_terminalPhaseSteps] using
      uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)
  rw [hexactMean] at htransfer
  simpa [actual, exactSome, exact, K, epsilon, f, s,
    scheduleValue_terminalPhaseSteps] using htransfer

/-- A terminal retained endpoint second moment keeps the sharp terminal
factor, plus the explicit squared-support exact-chance error. -/
theorem integral_iterated_retainedOption_uniform_terminal_sq_le
    (q : VolumeParams) (I : VolumeInput q.n) (samples : ℕ) :
    (∫ result, retainedOptionWeight
          (uniformRatioWeight (terminalVariance q)) result ^ 2
        ∂iteratedKernelLaw
          (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
            (terminalVariance q))
          ((truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n)).map some)
          samples) ≤
      Real.exp (1 / 2) * (figureOneIdealPhaseMean q I .terminal) ^ 2 +
        Real.exp (1 / 2) ^ 2 *
          (2 * scheduledBalancedStationaryTargetError q +
            samples • figureOneCorrectedTransitionBudget q).toReal := by
  let s := scheduleValue q (terminalPhaseSteps q)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s
      (scheduleValue_pos q (terminalPhaseSteps q))
  let exactSome : Measure (Option (AmbientSpace q.n)) := exact.map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let actual := iteratedKernelLaw (fun _ => K) exactSome samples
  let epsilon := 2 * scheduledBalancedStationaryTargetError q +
    samples • figureOneCorrectedTransitionBudget q
  let f : Option (AmbientSpace q.n) → ℝ :=
    retainedOptionWeight (uniformRatioWeight (terminalVariance q))
  let _ : IsProbabilityMeasure exact := inferInstance
  let _ : IsProbabilityMeasure exactSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I (scheduleValue_pos q (terminalPhaseSteps q))
  let _ : IsProbabilityMeasure actual :=
    iteratedKernelLaw_isProbabilityMeasure (fun _ => K) exactSome inferInstance
      (fun _ => hK.1) (fun _ => hK.2) samples
  have htv : Arlib.TVLe actual exactSome epsilon := by
    simpa [actual, exactSome, exact, K, epsilon, s] using
      (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
        q I (terminalPhaseSteps q) samples).to_tvLe
  have hepsilonTop : epsilon ≠ ⊤ := by
    dsimp [epsilon]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by norm_num) <|
        ne_top_of_le_ne_top
          (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
          (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top
  have hactualBounds :=
    retainedOptionWeight_uniform_terminal_ae_bounds_iterated q I samples
  have hexactBounds :=
    retainedOptionWeight_uniform_terminal_ae_bounds_exactSome q I
  have hactual0 : ∀ᵐ result ∂actual, 0 ≤ f result := by
    simpa [actual, exactSome, exact, K, s, f] using
      hactualBounds.mono fun _ hx => hx.1
  have hactualB : ∀ᵐ result ∂actual, f result ≤ Real.exp (1 / 2) := by
    simpa [actual, exactSome, exact, K, s, f] using
      hactualBounds.mono fun _ hx => hx.2
  have hexact0 : ∀ᵐ result ∂exactSome, 0 ≤ f result := by
    simpa [exactSome, exact, s, f, scheduleValue_terminalPhaseSteps] using
      hexactBounds.mono fun _ hx => hx.1
  have hexactB : ∀ᵐ result ∂exactSome, f result ≤ Real.exp (1 / 2) := by
    simpa [exactSome, exact, s, f, scheduleValue_terminalPhaseSteps] using
      hexactBounds.mono fun _ hx => hx.2
  have htransfer := Arlib.TVLe.integral_sq_le_of_ae_nonnegative_le htv
    hepsilonTop (measurable_retainedOptionWeight
      (measurable_uniformRatioWeight (terminalVariance q)))
    (Real.exp_pos _) hactual0 hactualB hexact0 hexactB
  have hexactSecond : (∫ result, f result ^ 2 ∂exactSome) =
      ∫ x, uniformRatioWeight (terminalVariance q) x ^ 2 ∂exact := by
    rw [integral_map measurable_some.aemeasurable
      ((measurable_retainedOptionWeight
        (measurable_uniformRatioWeight (terminalVariance q))).pow_const 2).aestronglyMeasurable]
    rfl
  have hidealMean : (∫ x, uniformRatioWeight (terminalVariance q) x ∂exact) =
      figureOneIdealPhaseMean q I .terminal := by
    simpa [exact, s, figureOneIdealPhaseMean,
      scheduleValue_terminalPhaseSteps] using
      uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)
  have hidealSecond : (∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
      ∂exact) ≤ Real.exp (1 / 2) *
        (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
    have hbase := uniformRatioWeight_terminal_secondMoment_le q I
    have hm := uniformRatioWeight_terminal_mean_one_le q I
    have hbase' : (∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
        ∂exact) ≤ Real.exp (1 / 2) *
          (∫ x, uniformRatioWeight (terminalVariance q) x ∂exact) := by
      simpa [exact, s, scheduleValue_terminalPhaseSteps] using hbase
    have hm' : 1 ≤
        ∫ x, uniformRatioWeight (terminalVariance q) x ∂exact := by
      simpa [exact, s, scheduleValue_terminalPhaseSteps] using hm
    have hmSq : (∫ x, uniformRatioWeight (terminalVariance q) x ∂exact) ≤
        (∫ x, uniformRatioWeight (terminalVariance q) x ∂exact) ^ 2 := by
      nlinarith [hm']
    rw [← hidealMean]
    exact hbase'.trans <|
      mul_le_mul_of_nonneg_left hmSq (Real.exp_pos _).le
  have hupper := (abs_le.mp htransfer).2
  rw [hexactSecond] at hupper
  have hactual : (∫ result, f result ^ 2 ∂actual) ≤
      (∫ x, uniformRatioWeight (terminalVariance q) x ^ 2 ∂exact) +
        Real.exp (1 / 2) ^ 2 * epsilon.toReal := by
    linarith
  have hfinal := hactual.trans (add_le_add hidealSecond le_rfl)
  simpa [actual, exactSome, exact, K, epsilon, f, s,
    scheduleValue_terminalPhaseSteps] using hfinal

#print axioms Arlib.TVLe.integral_sq_le_of_ae_nonnegative_le
#print axioms integral_iterated_retainedOption_uniform_terminal_abs_sub_ideal_le
#print axioms integral_iterated_retainedOption_uniform_terminal_sq_le

end ArlibCommunity.Algorithms.CV18
